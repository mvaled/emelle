open Base

type 'cmp t =
  { mutable vargen : int
  ; structure : Module.t
  ; symtable : Symtable.t }

(** Create a fresh desugarer state *)
let create structure symtable =
  { vargen = 0
  ; structure
  ; symtable }

let fresh_register st =
  st.vargen <- st.vargen + 1;
  st.vargen - 1

(** Convert an Ast.monotype into an Type.t *)
let rec normalize st tvars (_, node) =
  let open Result.Monad_infix in
  match node with
  | Ast.TApp(constr, arg) ->
     normalize st tvars constr >>= fun constr ->
     normalize st tvars arg >>| fun arg ->
     Type.of_node (Type.App(constr, arg))
  | Ast.TArrow -> Ok (Type.of_node (Type.Prim Type.Arrow))
  | Ast.TFloat -> Ok (Type.of_node (Type.Prim Type.Float))
  | Ast.TInt -> Ok (Type.of_node (Type.Prim Type.Int))
  | Ast.TNominal path ->
     begin match Module.resolve_path Module.find_type st.structure path with
     | Some ident -> Ok (Type.of_node (Type.Nominal ident))
     | None -> Error Sequence.empty
     end
  | Ast.TVar name ->
     match Hashtbl.find tvars name with
     | Some tvar -> Ok tvar
     | None -> Error Sequence.empty

(** Convert an Ast.adt into a Type.adt *)
let type_adt_of_ast_adt st kvargen adt =
  let open Result.Monad_infix in
  let tvargen = Type.create_vargen () in
  let tvar_map = Hashtbl.create (module String) in
  let constr_map = Hashtbl.create (module String) in
  List.fold_right ~f:(fun str acc ->
      acc >>= fun list ->
      let tvar =
        Type.fresh_var tvargen (-1) (Kind.Var (Kind.fresh_var kvargen))
      in
      match
        Hashtbl.add tvar_map ~key:str ~data:(Type.of_node (Type.Var tvar))
      with
      | `Duplicate -> Error Sequence.empty
      | `Ok -> Ok (tvar::list)
    ) ~init:(Ok []) adt.Ast.typeparams
  >>= fun tvar_list ->
  List.fold_right ~f:(fun (name, product) acc ->
      acc >>= fun (list, idx) ->
      match Hashtbl.add constr_map ~key:name ~data:idx with
      | `Duplicate -> Error Sequence.empty
      | `Ok ->
         List.fold_right ~f:(fun ty acc ->
             acc >>= fun list ->
             normalize st tvar_map ty >>| fun ty ->
             ty::list
           ) ~init:(Ok []) product
         >>| fun product ->
         ((name, product)::list, idx + 1)
    ) ~init:(Ok ([], 0)) adt.Ast.constrs
  >>| fun (constrs, _) ->
  let constrs = Array.of_list constrs in
  Type.{ name =
           begin match st.structure.Module.prefix with
           | Some prefix -> Ident.Dot(prefix, adt.Ast.name)
           | None -> Ident.Root(adt.Ast.name)
           end
       ; typeparams = tvar_list
       ; constr_names = constr_map
       ; constrs }

(** [pattern_of_ast_pattern state map reg ast_pat] converts [ast_pat] from an
    [Ast.pattern] to [Term.ml] while collecting bound identifiers in [map],
    returning `Error` if a data constructor or type isn't defined. *)
let rec term_pattern_of_ast_pattern st map reg (_, node) =
  let open Result.Monad_infix in
  match node with
  | Ast.Con(constr_path, pats) ->
     let f next acc =
       acc >>= fun (pats, map) ->
       let reg = fresh_register st in
       term_pattern_of_ast_pattern st map reg next >>| fun (pat, map) ->
       (pat::pats, map)
     in
     begin match
       Module.resolve_path Module.find_constr st.structure constr_path
     with
     | None -> Error (Sequence.return (Message.Unresolved_path constr_path))
     | Some (typename, idx) ->
        List.fold_right ~f:f ~init:(Ok ([], map)) pats >>| fun (pats, map) ->
        (Term.{node = Term.Con(typename, idx, pats); reg = Some reg}, map)
     end
  | Ast.Var name ->
     begin match Map.add map ~key:name ~data:reg with
     | `Ok map -> Ok (Term.{node = Term.Wild; reg = Some reg}, map)
     | `Duplicate -> Error (Sequence.return (Message.Redefined_name name))
     end
  | Ast.Wild -> Ok (Term.{node = Term.Wild; reg = Some reg}, map)

(** [term_of_expr desugarer env expr] converts [expr] from an [Ast.expr] to a
    [Term.t]. *)
let rec term_of_expr st env (ann, node) =
  let open Result.Monad_infix in
  let term =
    match node with
    | Ast.App(f, x) ->
       begin match term_of_expr st env f, term_of_expr st env x with
       | Ok f, Ok x -> Ok (Term.App(f, x))
       | (Error e, Ok _) | (Ok _, Error e) -> Error e
       | Error e1, Error e2 -> Error (Sequence.append e1 e2)
       end

    | Ast.Case(discriminant, cases) ->
       term_of_expr st env discriminant >>= fun discriminant ->
       List.fold_right
         ~f:(fun (pat, expr) acc ->
           acc >>= fun cases ->
           let map = Map.empty (module String) in
           (* The register to store the pattern match result in *)
           let reg = fresh_register st in
           term_pattern_of_ast_pattern st map reg pat >>= fun (pat, map) ->
           Env.in_scope_with (fun env ->
               term_of_expr st env expr
             ) map env >>| fun body ->
           (pat, [], body)::cases
         ) ~init:(Ok []) cases >>| fun cases ->
       Term.Case(discriminant, [], cases)

    | Ast.Lam((_, patterns, _) as case, cases) ->
       let reg = fresh_register st in
       let regs = List.map ~f:(fun _ -> fresh_register st) patterns in
       let handle_branch (pat, pats, expr) =
         let map = Map.empty (module String) in
         let tmp_reg = fresh_register st in
         term_pattern_of_ast_pattern st map tmp_reg pat >>= fun (pat, map) ->
         List.fold_right ~f:(fun pat acc ->
             acc >>= fun (list, map) ->
             let reg = fresh_register st in
             term_pattern_of_ast_pattern st map reg pat >>| fun (pat, map) ->
             (pat::list, map)
           ) ~init:(Ok ([], map)) pats >>= fun (pats, map) ->
         Env.in_scope_with (fun env ->
             term_of_expr st env expr
           ) map env >>| fun term ->
         (pat, pats, term)
       in
       List.fold_right ~f:(fun branch acc ->
           acc >>= fun rows ->
           handle_branch branch >>| fun row ->
           row::rows
         ) ~init:(Ok []) (case::cases) >>| fun cases ->
       let case_term =
         Term.Case(Term.Var reg, List.map ~f:(fun x -> Term.Var x) regs, cases)
       in
       List.fold_right ~f:(fun reg body ->
           Term.Lam(reg, body)
         ) ~init:case_term (reg::regs)

    | Ast.Let(bindings, body) ->
       let rec f map = function
         | [] -> Env.in_scope_with (fun env -> term_of_expr st env body) map env
         | (pat, def)::bindings ->
            term_of_expr st env def >>= fun def ->
            let reg = fresh_register st in
            term_pattern_of_ast_pattern st map reg pat >>= fun (pat, map) ->
            f map bindings >>| fun cont ->
            Term.Case(def, [], [(pat, [], cont)])
       in f (Map.empty (module String)) bindings

    | Ast.Let_rec(bindings, body) ->
       let bindings =
         List.fold_right ~f:(fun (str, expr) acc ->
             acc >>= fun (list, env) ->
             let reg = fresh_register st in
             match Env.add env str reg with
             | Some env -> Ok ((reg, expr)::list, env)
             | None ->
                Error (Sequence.return (Message.Redefined_name str))
           ) ~init:(Ok ([], env)) bindings;
       in
       bindings >>= fun (bindings, env) ->
       Env.in_scope (fun env ->
           let bindings =
             List.fold_right ~f:(fun (reg, expr) acc ->
                 acc >>= fun list ->
                 term_of_expr st env expr >>| fun term ->
                 (reg, term)::list
               ) ~init:(Ok []) bindings
           in
           bindings >>= fun bindings ->
           term_of_expr st env body >>| fun body ->
           Term.Let_rec(bindings, body)
         ) env

    | Ast.Var ((prefix, name) as path) ->
       match prefix with
       | [] -> (* Unqualified name *)
          begin match Env.find env name with
          (* Found in the local environment *)
          | Some reg -> Ok (Term.Var reg)
          | None ->
             (* Search in the current structure *)
             match Module.find_val st.structure name with
             | Some ident -> Ok (Term.Extern_var ident)
             | None -> Error (Sequence.return (Message.Unresolved_path path))
          end
       | _ -> (* Qualified name *)
          match Module.resolve_path Module.find_val st.structure path with
          | None -> Ok (Term.Extern_var (Ident.of_path path))
          | Some ident -> Ok (Term.Extern_var ident)

  in term >>| fun term -> (Term.Ann { ann = ann; term = term })
