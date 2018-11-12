open Base

type t = {
    ty : Type.t;
    expr : expr
  }

and expr =
  | App of t * t
  | Assign of t * t
  | Case of t list * Pattern.decision_tree * (bindings * t) list
  | Constr of int
  | Extern_var of Path.t
  | Lam of Ident.t * t
  | Let_rec of (Ident.t * t) list * t
  | Let of Ident.t * t * t
  | Lit of Literal.t
  | Local_var of Ident.t
  | Prim of string
  | Ref of t
  | Seq of t * t

and bindings = (Ident.t, Ident.comparator_witness) Set.t
