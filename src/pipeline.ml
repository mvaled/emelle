open Base

type t =
  { desugarer : Desugar.t
  ; typechecker : Typecheck.t
  ; packages : (string, Package.t) Hashtbl.t
  ; package : Package.t }

let create name packages =
  let package = Package.create name in
  let _ = Hashtbl.add packages ~key:name ~data:package in
  { desugarer = Desugar.create package packages
  ; typechecker = Typecheck.create package packages
  ; package
  ; packages }

let precompile self =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc next ->
      acc >>= fun () ->
      match next with
      | Ast.Adt adt ->
         let kvar = Kind.fresh_var self.typechecker.Typecheck.kvargen in
         Package.add_typedef
           self.package adt.Ast.name (Package.Todo (Kind.Var kvar))
      | _ -> Ok ()
    ) ~init:(Ok ())

let compile_item self env =
  let open Result.Monad_infix in
  function
  | Ast.Adt adt ->
     Typecheck.type_adt_of_ast_adt self.typechecker adt >>= fun adt ->
     begin match Package.find_typedef self.package adt.Type.name with
     | None -> Error (Sequence.return Message.Unreachable)
     | Some ptr ->
        match !ptr with
        | Package.Compiled _ ->
           Error (Sequence.return (Message.Redefined_name adt.Type.name))
        | Package.Todo kind ->
           Typecheck.unify_kinds kind (Type.kind_of_adt adt) >>= fun () ->
           Package.add_constrs self.package adt >>| fun () ->
           ptr := Package.Compiled (Type.Manifest adt);
           env
     end
  | Ast.Let bindings ->
     List.fold ~f:(fun acc (pat, expr) ->
         acc >>= fun (map, list) ->
         Desugar.term_pattern_of_ast_pattern self.desugarer map None pat
         >>= fun (pat, map) ->
         Desugar.term_of_expr self.desugarer env expr
         >>= fun term ->
         Typecheck.infer self.typechecker term
         >>= fun lambda ->
         let matrix = [
             Pattern.{first_pattern = pat; rest_patterns = []; action = () }
           ]
         in
         Pattern.decision_tree_of_matrix [[0]] matrix >>| fun tree ->
         (map, Package.Let(tree, lambda)::list)
       ) ~init:(Ok (Map.empty (module String), [])) bindings
     >>= fun (map, bindings) ->
     Map.fold ~f:(fun ~key:key ~data:data acc ->
         acc >>= fun env ->
         match Env.add env key data with
         | Some env -> Ok env
         | None -> Error (Sequence.return (Message.Redefined_name key))
       ) ~init:(Ok env) map
     >>| fun env ->
     List.iter ~f:(Package.add_command self.package) bindings;
     env
  | Ast.Let_rec bindings ->
     (* The two List.fold(_left)s cancel out the list reversal *)
     List.fold ~f:(fun acc (name, expr) ->
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

let export self env =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc name ->
      acc >>= fun () ->
      match Env.find env name with
      | None ->
         Error (Sequence.return (Message.Unresolved_path (Ast.Internal name)))
      | Some idx ->
         match Hashtbl.find self.typechecker.Typecheck.env idx with
         | None -> Error (Sequence.return Message.Unreachable)
         | Some ty ->
            match Package.add_val self.package name ty idx with
            | Some () -> Ok ()
            | None -> Error (Sequence.return (Message.Reexported_name name))
    ) ~init:(Ok ())

let compile packages name ast_package =
  let open Result.Monad_infix in
  let st = create name packages in
  precompile st ast_package.Ast.items
  >>= fun () ->
  List.fold ~f:(fun acc item ->
      acc >>= fun env ->
      compile_item st env item
    ) ~init:(Ok (Env.empty (module String))) ast_package.Ast.items
  >>= fun env ->
  export st env ast_package.Ast.exports
