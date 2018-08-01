open Base

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t list * Pattern.decision_tree * 'a t array
  | Lam of int * 'a t
  | Let of 'a bind_group * 'a t
  | Let_rec of 'a bind_group list * 'a t
  | Select of Ident.t * Ident.t * int * 'a t
  | Var of int

and 'a bind_group = (int * 'a t) list
