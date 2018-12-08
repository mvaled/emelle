open Base

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Assign of 'a t * 'a t
  | Case of 'a t list * 'a t branch list
  | Constr of Type.adt * int
  | Extern_var of Path.t * Type.t
  | Lam of Ident.t * 'a t
  | Let of Ident.t * 'a t * 'a t
  | Let_rec of 'a bind_group * 'a t
  | Lit of Literal.t
  | Prim of string * 'a Ast.polytype
  | Ref
  | Seq of 'a t * 'a t
  | Var of Ident.t

and 'a bind_group = (Ident.t * 'a t) list

and id_set = (Ident.t, Ident.comparator_witness) Set.t

and 'a branch = Pattern.t list * id_set * 'a
