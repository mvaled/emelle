open Base

type command =
  | Let of
      Lambda.t
      * Lambda.t list
      * int Pattern.decision_tree
      * (int, Int.comparator_witness) Set.t
  | Let_rec of (int * Lambda.t) list

type t =
  { desugarer : Desugar.t
  ; typechecker : Typecheck.t
  ; bytecomp : Bytecode.t
  ; packages : (string, Package.t) Hashtbl.t
  ; package : Package.t }

let create name packages =
  let package = Package.create name in
  let _ = Hashtbl.add packages ~key:name ~data:package in
  { desugarer = Desugar.create package packages
  ; typechecker = Typecheck.create package packages
  ; bytecomp = Bytecode.create ()
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

let export self env =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc name ->
      acc >>= fun () ->
      match Env.find env name with
      | None ->
         Error (Sequence.return (Message.Unresolved_path (Ast.Internal name)))
      | Some idx ->
         match Hashtbl.find self.typechecker.Typecheck.env idx with
         | None ->
            Error (Sequence.return (Message.Unreachable "Pipeline export"))
         | Some ty ->
            match Package.add_val self.package name ty idx with
            | Some () -> Ok ()
            | None -> Error (Sequence.return (Message.Reexported_name name))
    ) ~init:(Ok ())

let compile_items self env items exports =
  let open Result.Monad_infix in
  let commands = Queue.create () in
  let rec loop env = function
    | (Ast.Adt adt)::rest ->
       Typecheck.type_adt_of_ast_adt self.typechecker adt >>= fun adt ->
       begin match Package.find_typedef self.package adt.Type.name with
       | None -> Error (Sequence.return (Message.Unreachable "Pipeline ADT"))
       | Some ptr ->
          match !ptr with
          | Package.Compiled _ ->
             Error (Sequence.return (Message.Redefined_name adt.Type.name))
          | Package.Todo kind ->
             Typecheck.unify_kinds kind (Type.kind_of_adt adt) >>= fun () ->
             Package.add_constrs self.package adt >>= fun () ->
             ptr := Package.Compiled (Type.Manifest adt);
             loop env rest
       end

    | (Ast.Let((pat, scrut), bindings))::rest ->
       let map = Map.empty (module String) in
       Desugar.term_pattern_of_ast_pattern self.desugarer map None pat
       >>= fun (pat, map) ->
       Desugar.term_of_expr self.desugarer env scrut
       >>= fun scrut ->
       Typecheck.infer self.typechecker scrut >>= fun scrut ->
       Typecheck.infer_pattern
         self.typechecker (Typecheck.gen self.typechecker scrut.Lambda.ty) pat
       >>= fun () ->
       List.fold_right ~f:(fun (pat, scrut) acc ->
           acc >>= fun (map, scruts, pats) ->
           Desugar.term_of_expr self.desugarer env scrut >>= fun scrut ->
           Desugar.term_pattern_of_ast_pattern self.desugarer map None pat
           >>= fun (pat, map) ->
           Typecheck.infer self.typechecker scrut
           >>= fun scrut ->
           Typecheck.infer_pattern self.typechecker
             (Typecheck.gen self.typechecker scrut.Lambda.ty) pat
           >>| fun () -> (map, scrut::scruts, pat::pats)
         ) ~init:(Ok (map, [], [])) bindings
       >>= fun (map, scruts, pats) ->
       let matrix =
         [ { Pattern.first_pattern = pat
           ; rest_patterns = pats
           ; bindings = Map.empty (module Int)
           ; action = 0 } ]
       in
       Pattern.decision_tree_of_matrix
         (let (occurrences, _) =
            List.fold ~f:(fun (list, i) _ ->
                ((Pattern.Nil i)::list, i + 1)
              ) ~init:([], 0) (scrut::scruts)
          in occurrences) matrix >>= fun decision_tree ->
       Map.fold ~f:(fun ~key:key ~data:data acc ->
           acc >>= fun env ->
           match Env.add env key data with
           | Some env -> Ok env
           | None -> Error (Sequence.return (Message.Redefined_name key))
         ) ~init:(Ok env) map
       >>= fun env ->
       let regs =
         Map.fold ~f:(fun ~key:_ ~data:reg acc ->
             Set.add acc reg
           ) ~init:(Set.empty (module Int)) map
       in
       Queue.enqueue commands (Let(scrut, scruts, decision_tree, regs));
       loop env rest

    | (Ast.Let_rec bindings)::rest ->
       (* The two List.fold(_left)s cancel out the list reversal *)
       List.fold ~f:(fun acc (name, expr) ->
           acc >>= fun (env, list) ->
           let reg = Desugar.fresh_register self.desugarer in
           match Env.add env name reg with
           | None -> Error (Sequence.return (Message.Redefined_name name))
           | Some env ->
              let tvar = Typecheck.fresh_tvar self.typechecker in
              match Hashtbl.add self.typechecker.env ~key:reg ~data:tvar with
              | `Duplicate ->
                 Error (Sequence.return
                          (Message.Unreachable "Pipeline let rec"))
              | `Ok -> Ok (env, (reg, expr)::list)
         ) ~init:(Ok (env, [])) bindings
       >>= fun (env, bindings) ->
       List.fold ~f:(fun acc (reg, expr) ->
           acc >>= fun list ->
           Desugar.term_of_expr self.desugarer env expr >>= fun term ->
           Typecheck.infer self.typechecker term >>| fun lambda ->
           (reg, lambda)::list
         ) ~init:(Ok []) bindings
       >>= fun bindings ->
       List.iter ~f:(fun (lhs, _) ->
           Hashtbl.change self.typechecker.env lhs ~f:(function
               | Some ty -> Some (Typecheck.gen self.typechecker ty)
               | None -> None
             )
         ) bindings;
       Queue.enqueue commands (Let_rec bindings);
       loop env rest

    | [] ->
       let rec f = function
         | (Let(scrut, scruts, tree, bindings))::rest ->
            Bytecode.compile_case self.bytecomp scrut scruts tree
              [bindings, ()] (fun () -> f rest)
         | (Let_rec(bindings))::rest ->
            Bytecode.compile_letrec self.bytecomp bindings
              (fun _ -> f rest)
         | [] ->
            export self env exports
            >>= fun () -> Ok (Bytecode.Box [])
       in f (Queue.to_list commands)

  in loop env items

let compile packages name ast_package =
  let open Result.Monad_infix in
  let st = create name packages in
  precompile st ast_package.Ast.items
  >>= fun () ->
  compile_items
    st (Env.empty (module String)) ast_package.Ast.items ast_package.Ast.exports
