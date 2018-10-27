open Base

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t list * 'a t branch list
  | Extern_var of Ident.t * Type.t
  | Lam of Register.t * 'a t
  | Let of Register.t * 'a t * 'a t
  | Let_rec of 'a bind_group * 'a t
  | Lit of Literal.t
  | Var of Register.t

and 'a bind_group = (Register.t * 'a t) list

and reg_set = (Register.t, Register.comparator_witness) Set.t

and 'a branch = Pattern.t list * reg_set * 'a
