open Base

type t =
  { vargen : Register.gen
  ; packages : (string, Package.t) Hashtbl.t
  ; package : Package.t }

(** Create a fresh desugarer state *)
let create package packages =
  { vargen = Register.create_gen ()
  ; package
  ; packages }

let find f st = function
  | Ast.Internal str ->
     begin match f st.package str with
     | None -> None
     | Some x -> Some ((st.package.Package.name, str), x)
     end
  | Ast.External(pack_name, item_name) ->
     match Hashtbl.find st.packages pack_name with
     | None -> None
     | Some package ->
        match f package item_name with
        | None -> None
        | Some x -> Some ((pack_name, item_name), x)

let fresh_register st name = Register.fresh st.vargen name

(** [pattern_of_ast_pattern state map reg ast_pat] converts [ast_pat] from an
    [Ast.pattern] to [Term.ml] while collecting bound identifiers in [map],
    returning [Error] if a data constructor or type isn't defined. *)
let rec term_pattern_of_ast_pattern st map reg_opt (_, node) =
  let open Result.Monad_infix in
  match node with
  | Ast.Con(constr_path, pats) ->
     let f next acc =
       acc >>= fun (pats, map) ->
       term_pattern_of_ast_pattern st map None next >>| fun (pat, map) ->
       (pat::pats, map)
     in
     begin match find Package.find_adt st constr_path with
     | None -> Error (Sequence.return (Message.Unresolved_path constr_path))
     | Some (_, (adt, idx)) ->
        List.fold_right ~f:f ~init:(Ok ([], map)) pats >>| fun (pats, map) ->
        (Term.{node = Term.Con(adt, idx, pats); reg = reg_opt}, map)
     end
  | Ast.Var name ->
     let reg =
       match reg_opt with
       | Some reg -> reg
       | None -> fresh_register st (Some name)
     in
     begin match Map.add map ~key:name ~data:reg with
     | `Ok map -> Ok (Term.{node = Term.Wild; reg = Some reg}, map)
     | `Duplicate -> Error (Sequence.return (Message.Redefined_name name))
     end
  | Ast.Wild -> Ok (Term.{node = Term.Wild; reg = reg_opt}, map)

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

    | Ast.Case(scrutinee, cases) ->
       term_of_expr st env scrutinee >>= fun scrutinee ->
       List.fold_right
         ~f:(fun (pat, expr) acc ->
           acc >>= fun cases ->
           let map = Map.empty (module String) in
           term_pattern_of_ast_pattern st map None pat >>= fun (pat, map) ->
           Env.in_scope_with (fun env ->
               term_of_expr st env expr
             ) map env
           >>| fun body ->
           let regs =
             Map.fold ~f:(fun ~key:_ ~data:reg acc ->
                 Set.add acc reg
               ) ~init:(Set.empty (module Register)) map
           in
           (pat, [], regs, body)::cases
         ) ~init:(Ok []) cases >>| fun cases ->
       Term.Case(scrutinee, [], cases)

    | Ast.Lam((_, patterns, _) as case, cases) ->
       let reg = fresh_register st None in
       let regs = List.map ~f:(fun _ -> fresh_register st None) patterns in
       let handle_branch (pat, pats, expr) =
         let map = Map.empty (module String) in
         term_pattern_of_ast_pattern st map None pat >>= fun (pat, map) ->
         List.fold_right ~f:(fun pat acc ->
             acc >>= fun (list, map) ->
             term_pattern_of_ast_pattern st map None pat >>| fun (pat, map) ->
             (pat::list, map)
           ) ~init:(Ok ([], map)) pats >>= fun (pats, map) ->
         Env.in_scope_with (fun env ->
             term_of_expr st env expr
           ) map env >>| fun term ->
         let regs =
           Map.fold ~f:(fun ~key:_ ~data:reg acc ->
               Set.add acc reg
             ) ~init:(Set.empty (module Register)) map
         in (pat, pats, regs, term)
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

    | Ast.Let((pat, def), bindings, body) ->
       (* Transform

              let p1 = e1
              and p2 = e2
              ... pN = eN
              in body

          into

              case e1, e2, ... eN with
              | p1, p2, ... pN -> body

          What should the semantics be regarding diverging RHS expressions and
          refutable patterns? One would expect the let bindings' RHS to
          evaluate and match with its LHS pattern from top to bottom, but with
          the case desugar, all of the RHS expressions evaluate before any of
          them match with the LHS pattern. Is this desugar sensible? *)
       term_of_expr st env def >>= fun def ->
       term_pattern_of_ast_pattern st (Map.empty (module String)) None pat
       >>= fun (pat, map) ->
       List.fold_right ~f:(fun (pat, def) acc ->
           acc >>= fun (map, discrs, pats) ->
           term_of_expr st env def >>= fun def ->
           term_pattern_of_ast_pattern st map None pat
           >>| fun (pat, map) ->
           (map, def::discrs, pat::pats)
         ) ~init:(Ok (map, [], [])) bindings
       >>= fun (map, discrs, pats) ->
       Env.in_scope_with (fun env -> term_of_expr st env body) map env
       >>| fun body ->
       let regs =
         Map.fold ~f:(fun ~key:_ ~data:reg acc ->
             Set.add acc reg
           ) ~init:(Set.empty (module Register)) map
       in Term.Case(def, discrs, [pat, pats, regs, body])

    | Ast.Let_rec(bindings, body) ->
       let bindings =
         List.fold_right ~f:(fun (str, expr) acc ->
             acc >>= fun (list, env) ->
             let reg = fresh_register st (Some str) in
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

    | Ast.Var qual_id ->
       match qual_id with
       | Ast.Internal name -> (* Unqualified name *)
          begin match Env.find env name with
          (* Found in the local environment *)
          | Some reg -> Ok (Term.Var reg)
          | None -> Error (Sequence.return (Message.Unresolved_path qual_id))
          end
       | Ast.External _ -> (* Qualified name *)
          match find Package.find_val st qual_id with
          | Some (ident, (ty, _)) -> Ok (Term.Extern_var(ident, ty))
          | None -> Error (Sequence.return (Message.Unresolved_path qual_id))

  in term >>| fun term -> (Term.Ann { ann = ann; term = term })
