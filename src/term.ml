module Symboltbl = Hashtbl.Make(Ident)

type 'a t =
  | Ann of {annot : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t * 'a t Symboltbl.t
  | Lam of Ident.t * 'a t
  | Let of 'a bind_group * 'a t
  | Let_rec of 'a bind_group list * 'a t
  | Unpack of Ident.t * int * 'a t
  | Var of Ident.t

and 'a bind_group = (Ident.t * 'a t) list
