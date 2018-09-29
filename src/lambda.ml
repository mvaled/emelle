open Base

type t = {ty : Type.t; expr : expr}
and expr =
  | App of t * t
  | Case of t * t list * t Pattern.decision_tree
  | Extern_var of Ident.t
  | Lam of int * t
  | Let_rec of (int * t) list * t
  | Let of int * t * t
  | Local_var of int
