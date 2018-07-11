type 'a pattern = 'a * 'a pattern'
and 'a pattern' =
  | Con of Ident.t * 'a pattern list
  | Var of string
  | Wild

type 'a expr = 'a * 'a expr'
and 'a expr' =
  | App of 'a expr * 'a expr
  | Case of 'a expr
  | Lam of 'a expr
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
