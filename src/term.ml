open Base

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Assign of 'a t * 'a t
  | Case of 'a t list * 'a t branch list
  | Constr of Type.adt * int
  | Extern_var of Ident.t * Type.t
  | Lam of Register.t * 'a t
  | Let of Register.t * 'a t * 'a t
  | Let_rec of 'a bind_group * 'a t
  | Lit of Literal.t
  | Prim of string * 'a Ast.polytype
  | Ref of 'a t
  | Seq of 'a t * 'a t
  | Var of Register.t

and 'a bind_group = (Register.t * 'a t) list

and reg_set = (Register.t, Register.comparator_witness) Set.t

and 'a branch = Pattern.t list * reg_set * 'a
