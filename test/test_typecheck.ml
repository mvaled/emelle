open Base
open Emelle

let monotypes =
  [ Type.of_node (Type.Prim Type.Int)
  ; Type.of_node (Type.Prim Type.Float)
  ; Type.arrow
      (Type.of_node (Type.Prim Type.Int))
      (Type.of_node (Type.Prim Type.Int))
  ]

let not_monotypes =
  [ Type.of_node (Type.Prim Type.Arrow)
  ; Type.of_node
      (Type.App(Type.of_node (Type.Prim Type.Arrow),
                Type.of_node (Type.Prim Type.Int))
      )
  ]

let rec is_mono = function
  | Kind.Mono -> true
  | Kind.Var { kind = Some kind; _ } -> is_mono kind
  | _ -> false

let () =
  let f x =
    let symtable = Symtable.create () in
    let structure = Module.create None in
    let checker = Typecheck.create symtable structure in
    match Typecheck.kind_of_type checker x with
    | Ok kind -> assert (is_mono kind)
    | Error _ -> assert false
  in List.iter ~f:f monotypes

let () =
  let f x =
    let symtable = Symtable.create () in
    let structure = Module.create None in
    let checker = Typecheck.create symtable structure in
    match Typecheck.kind_of_type checker x with
    | Ok kind -> assert (not (is_mono kind))
    | Error _ -> assert false
  in List.iter ~f:f not_monotypes
