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

type state = {
    mutable vargen : int;
  }

let fresh_id st =
  let ret = Ident.Autogen st.vargen in
  st.vargen <- st.vargen + 1;
  ret

let rec pattern_of_ast_pattern (_, node) =
  match node with
  | Con(typename, con, pats) ->
     Pattern.Con(typename, con, List.map ~f:pattern_of_ast_pattern pats)
  | Var _ -> Pattern.Wild
  | Wild -> Pattern.Wild

let undefined = failwith ""
