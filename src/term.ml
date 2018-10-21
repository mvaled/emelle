open Base

type pattern =
  { node : pattern'
  ; reg : Register.t option}
and pattern' =
  | Con of Type.adt * int * pattern list (** Constructor pattern *)
  | Or of pattern * pattern
  | Wild (** Wildcard pattern *)

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t * 'a t list * 'a branch list
  | Extern_var of Ident.t * Type.t
  | Lam of Register.t * 'a t
  | Let of Register.t * 'a t * 'a t
  | Let_rec of 'a bind_group * 'a t
  | Var of Register.t

and 'a bind_group = (Register.t * 'a t) list

and 'a branch =
  pattern * pattern list
  * (Register.t, Register.comparator_witness) Set.t * 'a t
