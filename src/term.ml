module Symboltbl = Hashtbl.Make(Ident)

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t list * Pattern.decision_tree * 'a t array
  | Lam of Ident.t * 'a t
  | Let of 'a bind_group * 'a t
  | Let_rec of 'a bind_group list * 'a t
  | Select of Ident.t * int * 'a t
  | Var of Ident.t

and 'a bind_group = (Ident.t * 'a t) list
