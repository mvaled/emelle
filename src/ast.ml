open Base

type 'a pattern = 'a * 'a pattern'
and 'a pattern' =
  | Con of Ident.t * Ident.t * 'a pattern list
  | Var of string
  | Wild

type 'a expr = 'a * 'a expr'
and 'a expr' =
  | App of 'a expr * 'a expr
  | Case of 'a expr * ('a pattern * 'a expr) list
  | Lam of 'a pattern * 'a expr
  | Let of 'a expr
  | Let_rec of 'a expr
  | Var of Ident.t
