open Base

type command =
  | Let of
      Lambda.t list * Pattern.decision_tree
      * (Ident.t, Ident.comparator_witness) Set.t
  | Let_rec of (Ident.t * Lambda.t) list

type t =
  { elaborator : Elab.t
  ; typechecker : Typecheck.t
  ; a_normalizer : Anf.t
  ; packages : (string, Package.t) Hashtbl.t
  ; package : Package.t }

let create name packages =
  let package = Package.create name in
  let _ = Hashtbl.add packages ~key:name ~data:package in
  { elaborator = Elab.create package packages
  ; typechecker = Typecheck.create package packages
  ; a_normalizer = Anf.create ()
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
            match Hashtbl.find self.a_normalizer.Anf.ctx reg with
            | None ->
               Error
                 (Sequence.return (Message.Unreachable "Pipeline export 2"))
            | Some operand ->
               match Package.add_val self.package name ty i with
               | Some () -> Ok (i + 1, operand::list)
               | None -> Error (Sequence.return (Message.Reexported_name name))
    ) ~init:(Ok (0, [])) exports
  >>| fun (_, operands) ->
  Anf.Box (List.rev operands)

let compile_item self env commands item ~cont =
  let open Result.Monad_infix in
  match item with
  | Ast.Let bindings ->
     Elab.elab_let_bindings self.elaborator env bindings
     >>= fun (map, scruts, regs, pats) ->
     List.fold_right ~f:(fun scrut acc ->
         acc >>= fun list ->
         Typecheck.in_new_let_level (fun checker ->
             Typecheck.infer_term checker scrut
           ) self.typechecker >>| fun expr ->
         expr::list
       ) ~init:(Ok []) scruts >>= fun scruts ->
     Typecheck.infer_branch self.typechecker scruts pats >>= fun () ->
     let matrix =
       [ { Pattern.patterns = pats
         ; bindings = Map.empty (module Ident)
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
     Elab.elab_rec_bindings self.elaborator env bindings
     >>= fun (env, bindings) ->
     Typecheck.infer_rec_bindings self.typechecker bindings
     >>= fun bindings ->
     List.iter ~f:(fun (lhs, _) ->
         Hashtbl.change self.typechecker.env lhs ~f:(function
             | Some ty -> Some (Typecheck.gen self.typechecker ty)
             | None -> None
           )
       ) bindings;
     cont env ((Let_rec bindings)::commands)

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
  let open Result.Monad_infix in
  let rec loop env list = function
    | item::items ->
       compile_item self env list item ~cont:(fun env list ->
           loop env list items
         )
    | [] ->
       (* The accumulator is a function *)
       let rec loop2 = function
         | Let(scruts, tree, bindings)::rest ->
            Anf.compile_case self.a_normalizer scruts tree
              ~cont:(fun (scruts, tree) ->
                Anf.compile_branch self.a_normalizer bindings ~cont:(fun () ->
                    loop2 rest >>| fun body ->
                    Anf.Return (Anf.Case(scruts, tree, [|body|]))
                  )
              )
         | Let_rec(bindings)::rest ->
            Anf.compile_letrec self.a_normalizer bindings
              ~cont:(fun bindings ->
                loop2 rest >>| fun body ->
                Anf.Let_rec(bindings, body)
              )
         | [] -> export self env exports
       in loop2 (List.rev list)
  in loop env [] items

let compile packages name ast_package =
  let st = create name packages in
  compile_items
    st (Env.empty (module String)) ast_package.Ast.items ast_package.Ast.exports
