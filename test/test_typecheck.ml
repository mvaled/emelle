open Base
open Emelle

let create_checker () =
  Typecheck.{ types = Hashtbl.create (module Ident)
            ; env = Hashtbl.create (module Int)
            ; level = 0
            ; tvargen = ref 0
            ; kvargen = ref 0 }

let monotypes =
  [ Type.Prim Type.Int
  ; Type.Prim Type.Float
  ; Type.App
      ( Type.App(Type.Prim Type.Arrow, Type.Prim Type.Int)
      , Type.Prim Type.Int )
  ]

let not_monotypes =
  [ Type.Prim Type.Arrow
  ; Type.App(Type.Prim Type.Arrow, Type.Prim Type.Int) ]

let rec is_mono = function
  | Kind.Mono -> true
  | Kind.Var { kind = Some kind; _ } -> is_mono kind
  | _ -> false

let () =
  let f x =
    let checker = create_checker () in
    match Typecheck.kind_of_type checker x with
    | Ok kind -> assert (is_mono kind)
    | Error _ -> assert false
  in List.iter ~f:f monotypes

let () =
  let f x =
    let checker = create_checker () in
    match Typecheck.kind_of_type checker x with
    | Ok kind -> assert (not (is_mono kind))
    | Error _ -> assert false
  in List.iter ~f:f not_monotypes
