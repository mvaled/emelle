open Base

type 'a pattern = 'a * 'a pattern'
and 'a pattern' =
  | Con of Ident.t * string * 'a pattern list
  | Var of string
  | Wild

type 'a expr = 'a * 'a expr'
and 'a expr' =
  | App of 'a expr * 'a expr
  | Case of 'a expr * ('a pattern * 'a expr) list
  | Lam of 'a pattern * 'a expr
  | Let of ('a pattern * 'a expr) list * 'a expr
  | Let_rec of (string * 'a expr) list * 'a expr
  | Var of Ident.t
