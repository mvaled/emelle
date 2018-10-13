open Base

type t =
  { desugarer : Desugar.t
  ; typechecker : Typecheck.t
  ; packages : (string, Package.t) Hashtbl.t
  ; package : Package.t }

let compile self env =
  let open Result.Monad_infix in
  function
  | Ast.Adt adt ->
     Typecheck.type_adt_of_ast_adt self.typechecker adt >>= fun adt ->
     Package.add_adt self.package adt >>| fun () ->
     env
  | Ast.Let bindings ->
     List.fold
       ~f:(fun acc (pat, expr) ->
         acc >>= fun (env, list) ->
         let map = Map.empty (module String) in
         Desugar.term_pattern_of_ast_pattern self.desugarer map None pat
         >>= fun (pat, map) ->
         Env.in_scope_with (fun env ->
             Desugar.term_of_expr self.desugarer env expr
           ) map env
         >>= fun term ->
         Typecheck.infer self.typechecker term
         >>= fun lambda ->
         let matrix = [
             Pattern.{first_pattern = pat; rest_patterns = []; action = () }
           ]
         in
         Pattern.decision_tree_of_matrix [[0]] matrix >>| fun tree ->
         (env, Package.Let(tree, lambda)::list)
       ) ~init:(Ok (env, [])) bindings
     >>| fun (env, bindings) ->
     List.iter ~f:(Package.add_command self.package) bindings;
     env
  | Ast.Let_rec bindings ->
     (* The two List.fold(_left)s cancel out the list reversal *)
     List.fold
       ~f:(fun acc (name, expr) ->
         acc >>= fun (env, list) ->
         let reg = Desugar.fresh_register self.desugarer in
         match Env.add env name reg with
         | None -> Error (Sequence.return (Message.Redefined_name name))
         | Some env -> Ok (env, (reg, expr)::list)
       ) ~init:(Ok (env, [])) bindings
     >>= fun (env, bindings) ->
     List.fold ~f:(fun acc (reg, expr) ->
         acc >>= fun list ->
         Desugar.term_of_expr self.desugarer env expr >>= fun term ->
         Typecheck.infer self.typechecker term >>| fun lambda ->
         (reg, lambda)::list
       ) ~init:(Ok []) bindings
     >>| fun bindings ->
     Package.add_command self.package (Package.Let_rec bindings);
     env
