open Base

type 'a command =
  | Let of
      'a Lambda.t list * 'a Pattern.matrix
      * (Ident.t, Ident.comparator_witness) Set.t
  | Let_rec of (Ident.t * 'a Lambda.t) list

type t =
  { elaborator : Elab.t
  ; typechecker : Typecheck.t
  ; lowerer : Lower.t
  ; packages : (string, Package.t) Hashtbl.t
  ; package : Package.t }

let create name packages =
  let package = Package.create name in
  let _ = Hashtbl.add packages ~key:name ~data:package in
  { elaborator = Elab.create package packages
  ; typechecker = Typecheck.create package packages
  ; lowerer = Lower.create None
  ; package
  ; packages }

let export self env Ast.{ ann; exports; _ } =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc name ->
      acc >>= fun (i, list) ->
      match Env.find env name with
      | None ->
         Error (Sequence.return (Message.Unresolved_path (Ast.Internal name)))
      | Some reg ->
         match Hashtbl.find self.typechecker.Typecheck.env reg with
         | None -> Message.unreachable "Pipeline export 1"
         | Some ty ->
            match Hashtbl.find self.lowerer.Lower.ctx reg with
            | None -> Message.unreachable "Pipeline export 2"
            | Some operand ->
               match Package.add_val self.package name ty i with
               | Some () -> Ok (i + 1, operand::list)
               | None -> Error (Sequence.return (Message.Reexported_name name))
    ) ~init:(Ok (0, [])) exports
  >>| fun (_, operands) ->
  Lower.make_break self.lowerer ann (Anf.Box (List.rev operands))

let compile_item self env commands item ~cont =
  let open Result.Monad_infix in
  match item with
  | Ast.Let bindings ->
     Elab.elab_let_bindings self.elaborator env bindings
     >>= fun (map, scruts, ids, pats) ->
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
     Map.fold ~f:(fun ~key:key ~data:data acc ->
         acc >>= fun env ->
         match Env.add env key data with
         | Some env -> Ok env
         | None -> Error (Sequence.return (Message.Redefined_name key))
       ) ~init:(Ok env) map
     >>= fun env ->
     cont env ((Let(scruts, matrix, ids))::commands)

  | Ast.Let_rec bindings ->
     Elab.elab_rec_bindings self.elaborator env bindings
     >>= fun (env, bindings) ->
     Typecheck.infer_rec_bindings self.typechecker bindings
     >>= fun bindings ->
     List.iter ~f:(fun (lhs, _) ->
         match Hashtbl.find self.typechecker.env lhs with
         | Some ty -> Typecheck.gen self.typechecker ty
         | None -> ()
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

let compile_package self env (Ast.{ ann; items; _ } as package) =
  let open Result.Monad_infix in
  let rec loop env list = function
    | item::items ->
       compile_item self env list item ~cont:(fun env list ->
           loop env list items
         )
    | [] ->
       let rec loop2 = function
         | Let(scruts, matrix, bindings)::rest ->
            Lower.compile_case self.lowerer scruts matrix
              ~cont:(fun (scruts, tree) ->
                Lower.compile_branch self.lowerer bindings >>= fun params ->
                loop2 rest >>| fun body ->
                Lower.make_break
                  self.lowerer ann (Anf.Case(scruts, tree, [params, body]))
              )
         | Let_rec(bindings)::rest ->
            Lower.compile_letrec self.lowerer bindings ~cont:(fun bindings ->
                loop2 rest >>| fun body ->
                { Anf.ann; instr = Anf.Let_rec(bindings, body) }
              )
         | [] -> export self env package
       in loop2 (List.rev list)
  in loop env [] items

let compile packages name ast_package =
  let open Result.Monad_infix in
  let st = create name packages in
  compile_package
    st (Env.empty (module String)) ast_package
  >>= Ssa_of_anf.compile_module
