open Base

type 'a t =
  | Ann of {ann : 'a; term: 'a t}
  | App of 'a t * 'a t
  | Case of 'a t list * 'a decision_tree
  | Extern_var of Ident.t
  | Lam of int * 'a t
  | Let of int * 'a t * 'a t
  | Let_rec of 'a bind_group * 'a t
  | Var of int

and 'a bind_group = (int * 'a t) list

(** Like a list, an occurrence is either empty or an integer followed by an
    occurence *)
and occurrence = int list
and occurrences = occurrence list

and 'a decision_tree =
  | Fail
  | Leaf of int option list * 'a t
  | Switch of
      occurrence * int option * Type.adt
      * (int, 'a decision_tree) Hashtbl.t * 'a decision_tree
  | Swap of int * 'a decision_tree
