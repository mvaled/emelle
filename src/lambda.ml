open Base

type t = {ty : Type.t; expr : expr}

and expr =
  | App of t * t
  | Case of t * t list * int Pattern.decision_tree * branch list
  | Extern_var of Ident.t
  | Lam of Register.t * t
  | Let_rec of (Register.t * t) list * t
  | Let of Register.t * t * t
  | Local_var of Register.t

and branch = (Register.t, Register.comparator_witness) Set.t * t
