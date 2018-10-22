open Base

type t = {
    ty : Type.t;
    expr : expr
  }

and expr =
  | App of t * t
  | Case of t * t list * int Pattern.decision_tree * (bindings * t) list
  | Extern_var of Ident.t
  | Lam of Register.t * t
  | Let_rec of (Register.t * t) list * t
  | Let of Register.t * t * t
  | Lit of Literal.t
  | Local_var of Register.t

and bindings = (Register.t, Register.comparator_witness) Set.t

and structure = {
    items : struct_item list
  }

and struct_item =
  | Adt_item of Type.adt list
  | Let_item of t * t list * bindings * Pattern.t * Pattern.t list
  | Let_rec_item of (Register.t * t) list
