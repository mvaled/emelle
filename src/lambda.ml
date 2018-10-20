open Base

type t = {ty : Type.t; expr : expr}

and expr =
  | App of t * t
  | Case of t * t list * int Pattern.decision_tree * branch list
  | Extern_var of Ident.t
  | Lam of int * t
  | Let_rec of (int * t) list * t
  | Let of int * t * t
  | Local_var of int

and branch = (int, Int.comparator_witness) Set.t * t
