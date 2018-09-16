open Base

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t list * Pattern.decision_tree * 'a t array
  | Extern_var of Ident.t
  | Lam of int * 'a t
  | Let of int * 'a t * 'a t
  | Let_rec of 'a bind_group * 'a t
  | Select of Ident.t * int * int * 'a t
  | Var of int

and 'a bind_group = (int * 'a t) list
