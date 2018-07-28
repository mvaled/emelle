open Base

type prim =
  | Arrow
  | Int
  | Float
[@@deriving compare]

type unassigned_var = {
    id : int;
    mutable level : int;
  }

type t =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var ref

and var =
  | Unassigned of unassigned_var
  | Assigned of t

type algebraic = (Ident.t, (t array * int)) Hashtbl.t

type def = Alias of t | Algebraic of algebraic

let equal_prim x y = (compare_prim x y) = 0
