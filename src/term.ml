open Base

type pattern =
  { node : pattern'
  ; reg : int option}
and pattern' =
  | Con of Type.adt * int * pattern list (** Constructor pattern *)
  | Or of pattern * pattern
  | Wild (** Wildcard pattern *)

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t * 'a t list * 'a branch list
  | Extern_var of Ident.t * Type.t
  | Lam of int * 'a t
  | Let of int * 'a t * 'a t
  | Let_rec of 'a bind_group * 'a t
  | Var of int

and 'a bind_group = (int * 'a t) list

and 'a branch =
  pattern * pattern list * (int, Int.comparator_witness) Set.t * 'a t
