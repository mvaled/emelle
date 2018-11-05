open Base

type command =
  | Let of
      Lambda.t list
      * int Pattern.decision_tree
      * (Register.t, Register.comparator_witness) Set.t
  | Let_rec of (Register.t * Lambda.t) list

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

let export self env exports =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc name ->
      acc >>= fun (i, list) ->
      match Env.find env name with
      | None ->
         Error (Sequence.return (Message.Unresolved_path (Ast.Internal name)))
      | Some reg ->
         match Hashtbl.find self.typechecker.Typecheck.env reg with
         | None ->
            Error (Sequence.return (Message.Unreachable "Pipeline export 1"))
         | Some ty ->
            match Hashtbl.find self.bytecomp.Bytecode.ctx reg with
            | None ->
               Error
                 (Sequence.return (Message.Unreachable "Pipeline export 2"))
            | Some operand ->
               match Package.add_val self.package name ty i with
               | Some () -> Ok (i + 1, operand::list)
               | None -> Error (Sequence.return (Message.Reexported_name name))
    ) ~init:(Ok (0, [])) exports
  >>| fun (_, operands) ->
  Bytecode.Box (List.rev operands)

let compile_item self env commands item ~cont =
  let open Result.Monad_infix in
  match item with
  | Ast.Let bindings ->
     Desugar.desugar_let_bindings self.desugarer env bindings
     >>= fun (map, scruts, regs, pats) ->
     List.fold_right ~f:(fun scrut acc ->
         acc >>= fun list ->
         Typecheck.in_new_level (fun checker ->
             Typecheck.infer_term checker (-1) scrut
           ) self.typechecker >>| fun expr ->
         expr::list
       ) ~init:(Ok []) scruts >>= fun scruts ->
     Typecheck.infer_branch self.typechecker (-1) scruts pats >>= fun () ->
     let matrix =
       [ { Pattern.patterns = pats
         ; bindings = Map.empty (module Register)
         ; action = 0 } ]
     in
     Pattern.decision_tree_of_matrix
       (let (occurrences, _) =
          List.fold ~f:(fun (list, i) _ ->
              ((Pattern.Nil i)::list, i + 1)
            ) ~init:([], 0) scruts
        in occurrences) matrix >>= fun decision_tree ->
     Map.fold ~f:(fun ~key:key ~data:data acc ->
         acc >>= fun env ->
         match Env.add env key data with
         | Some env -> Ok env
         | None -> Error (Sequence.return (Message.Redefined_name key))
       ) ~init:(Ok env) map
     >>= fun env ->
     cont env ((Let(scruts, decision_tree, regs))::commands)

  | Ast.Let_rec bindings ->
     Desugar.desugar_rec_bindings self.desugarer env bindings
     >>= fun (env, bindings) ->
     Typecheck.infer_rec_bindings self.typechecker (-1) bindings
     >>= fun bindings ->
     List.fold ~f:(fun acc (lhs, _) ->
         acc >>= fun () ->
         match Hashtbl.find self.typechecker.env lhs with
         | Some ty ->
            Typecheck.gen self.typechecker (-1) ty >>| fun polyty ->
            let _ = Hashtbl.set self.typechecker.env ~key:lhs ~data:polyty in
            ()
         | None -> Error Sequence.empty
       ) ~init:(Ok ()) bindings
     >>= fun () -> cont env ((Let_rec bindings)::commands)

  | Ast.Type(adt, adts) ->
     List.fold ~f:(fun acc adt ->
         acc >>= fun () ->
         let kvar = Kind.fresh_var self.typechecker.Typecheck.kvargen in
         Package.add_typedef
           self.package adt.Ast.name (Package.Todo (Kind.Var kvar))
       ) ~init:(Ok ()) (adt::adts) >>= fun () ->
     List.fold ~f:(fun acc adt ->
         acc >>= fun () ->
         Typecheck.type_adt_of_ast_adt self.typechecker adt >>= fun adt ->
         match Package.find_typedef self.package adt.Type.name with
         | None -> Error (Sequence.return (Message.Unreachable "Pipeline ADT"))
         | Some ptr ->
            match !ptr with
            | Package.Compiled _ ->
               Error (Sequence.return (Message.Redefined_name adt.Type.name))
            | Package.Todo kind ->
               Typecheck.unify_kinds kind (Type.kind_of_adt adt) >>= fun () ->
               Package.add_constrs self.package adt >>= fun () ->
               ptr := Package.Compiled (Type.Manifest adt);
               Ok ()
       ) ~init:(Ok ()) (adt::adts) >>= fun () ->
     cont env commands

let compile_items self env items exports =
  let rec loop env list = function
    | item::items ->
       compile_item self env list item ~cont:(fun env list ->
           loop env list items
         )
    | [] ->
       (* The accumulator is a function *)
       List.fold ~f:(fun callback next self ->
           match next with
           | Let(scruts, tree, bindings) ->
              Bytecode.compile_case self.bytecomp scruts tree
                [bindings, ()] (fun () -> callback self)
           | Let_rec(bindings) ->
              Bytecode.compile_letrec self.bytecomp bindings
                (fun _ -> callback self)
         ) ~init:(fun self -> export self env exports) list self
  in loop env [] items

let compile packages name ast_package =
  let st = create name packages in
  compile_items
    st (Env.empty (module String)) ast_package.Ast.items ast_package.Ast.exports
