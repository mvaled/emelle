open Base

type t = {
    mutable vargen : int;
    mutable registers : (string, int) Env.t;
    typedefs : (Ident.t, Type.def) Env.t;
  }

let fresh_register st =
  st.vargen <- st.vargen + 1;
  st.vargen - 1

let with_registers f st tbl =
  let old = st.registers in
  st.registers <- Env.extend tbl st.registers;
  let result = f st in
  st.registers <- old;
  result

let idx_of_constr st typename con =
  match Env.find st.typedefs typename with
  | Some (Algebraic adt) ->
     begin match Hashtbl.find adt.constr_names con with
     | Some idx -> Ok idx
     | None -> Error (Sequence.return (Message.Unknown_constr(typename, con)))
     end
  | Some (Alias _) -> Error (Sequence.return (Message.Expected_adt typename))
  | None -> Error (Sequence.return (Message.Unresolved_type typename))

let rec pattern_of_ast_pattern st (_, node) =
  let open Result.Monad_infix in
  match node with
  | Ast.Con(typename, con, pats) ->
     let f next acc =
       acc >>= fun pats ->
       pattern_of_ast_pattern st next >>| fun pat ->
       pat::pats
     in
     idx_of_constr st typename con >>= fun idx ->
     List.fold_right ~f:f ~init:(Ok []) pats >>| fun patterns ->
     Pattern.Con(typename, idx, patterns)
  | Ast.Var _ -> Ok Pattern.Wild
  | Ast.Wild -> Ok Pattern.Wild

(** Walk the pattern and map identifiers to fresh registers *)
let rec gen_registers st (_, node) =
  let (>>=) = Result.(>>=) in
  match node with
  | Ast.Con(_, _, args) ->
     List.fold ~f:(
         fun acc pat -> acc >>= fun () -> gen_registers st pat
       ) ~init:(Ok ()) args
  | Ast.Var id ->
     (* Map the identifer to its register *)
     let reg = fresh_register st in
     if Env.define st.registers id reg then
       Ok ()
     else
       Error (Sequence.return (Message.Redefined_id (Ident.Local id)))
  | Ast.Wild -> Ok ()

(** Walk the pattern and compile it into a term that assumes that all pattern
    matches are successful  *)
let rec term_of_ast_pattern st def cont (ann, node) =
  let (>>=) = Result.(>>=) in
  let (>>|) = Result.(>>|) in
  let term =
    match node with
    | Ast.Con(typename, constr, args) ->
       let rec outer_loop idx arg_regs = function
         | [] ->
            let rec inner_loop = function
              | [] -> Ok cont
              | ((arg, reg)::xs) ->
                 inner_loop xs >>= fun cont ->
                 term_of_ast_pattern st (Term.Var reg) cont arg
            in inner_loop arg_regs
         | (arg::args) ->
            idx_of_constr st typename constr >>= fun constr_idx ->
            let reg = fresh_register st in
            let def = Term.Select(typename, constr_idx, idx, def) in
            let body = outer_loop (idx + 1) ((arg, reg)::arg_regs) args in
            body >>| fun body -> Term.Let(reg, def, body)
       in outer_loop 0 [] args
    | Ast.Var id ->
       (* Map the idetifier to its register *)
       begin match Env.find st.registers id with
       | Some reg -> Ok (Term.Let(reg, def, cont))
       | None ->
          Error (Sequence.return Message.Unreachable)
       end
    | Ast.Wild ->
       let reg = fresh_register st in
       Ok (Term.Let(reg, def, cont))
  in term >>| fun term -> Term.Ann { ann = ann; term = term }

let rec term_of_expr st (ann, node) =
  let (>>=) = Result.(>>=) in
  let (>>|) = Result.(>>|) in
  let term =
    match node with
    | Ast.App(f, x) ->
       begin match term_of_expr st f, term_of_expr st x with
       | Ok f, Ok x -> Ok (Term.App(f, x))
       | (Error e, Ok _) | (Ok _, Error e) -> Error e
       | Error e1, Error e2 -> Error (Sequence.append e1 e2)
       end

    | Ast.Case(test, cases) ->
       term_of_expr st test >>= fun test ->
       let rows_result =
         List.fold_right ~f:(fun (pat, _) acc ->
             acc >>= fun (i, list) ->
             pattern_of_ast_pattern st pat >>| fun pat ->
             (i + 1), Pattern.{ first_pattern = pat
                              ; rest_patterns = []
                              ; action = i }::list
           ) ~init:(Ok (0, [])) cases
       in
       rows_result >>= fun (_, rows) ->
       let branches =
         List.fold_left
           ~f:(fun acc (pat, expr) ->
             acc >>= fun acc ->
             with_registers (fun st ->
                 gen_registers st pat >>= fun () ->
                 term_of_expr st expr >>= fun body ->
                 term_of_ast_pattern st test body pat >>| fun term ->
                 term::acc
               ) st (Hashtbl.create (module String))
           ) ~init:(Ok []) cases
       in
       branches >>= fun branches ->
       let branches = Array.of_list branches in
       begin match Pattern.decision_tree_of_matrix st.typedefs rows with
       | Some tree -> Ok (Term.Case([test], tree, branches))
       | None -> Error (Sequence.return (Message.Unreachable))
       end

    | Ast.Lam(pat, body) ->
       pattern_of_ast_pattern st pat >>= fun pat' ->
       let reg = fresh_register st in
       let matrix = [
           Pattern.{ first_pattern = pat'
                   ; rest_patterns = []
                   ; action = 0 }
         ]
       in
       begin match Pattern.decision_tree_of_matrix st.typedefs matrix with
       | Some tree ->
          with_registers (fun st ->
              gen_registers st pat >>= fun () ->
              term_of_expr st body >>= fun body ->
              term_of_ast_pattern st (Term.Var reg) body pat >>| fun body ->
              Term.Lam(reg, Term.Case([Term.Var reg], tree, [|body|]))
            ) st (Hashtbl.create (module String))
       | None -> Error (Sequence.return (Message.Unreachable))
       end

    | Ast.Let(bindings, body) ->
       let rec f = function
         | [] -> term_of_expr st body
         | (pat, def)::xs ->
            gen_registers st pat >>= fun () ->
            term_of_expr st def >>= fun def ->
            f xs >>= fun cont ->
            term_of_ast_pattern st def cont pat
       in
       with_registers (fun _ -> f bindings) st (Hashtbl.create (module String))

    | Ast.Let_rec(bindings, body) ->
       let hashtbl = Hashtbl.create (module String) in
       List.iter ~f:(fun (str, _) ->
           Hashtbl.add_exn hashtbl ~key:str ~data:(fresh_register st)
         ) bindings;
       with_registers (fun st -> term_of_expr st body) st hashtbl

    | Ast.Var id ->
       begin match id with
       | Local str ->
          begin match Env.find st.registers str with
          | Some reg -> Ok (Term.Var reg)
          | None -> Error (Sequence.return (Message.Unresolved_id id))
          end
       | Path _ -> Error (Sequence.return (Message.Unimplemented "path"))
       end

  in term >>| fun term -> (Term.Ann { ann = ann; term = term })
