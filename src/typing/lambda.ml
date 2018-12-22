open Base

type bindings = (Ident.t, Ident.comparator_witness) Set.t

type ('ann, 'a) expr =
  | App of 'a * 'a
  | Assign of 'a * 'a
  | Case of 'a list * 'ann Pattern.matrix * (bindings * 'a) list
  | Constr of int * int
  | Extern_var of Path.t
  | Lam of Ident.t * 'a
  | Let_rec of (Ident.t * 'a) list * 'a
  | Let of Ident.t * 'a * 'a
  | Lit of Literal.t
  | Local_var of Ident.t
  | Prim of string
  | Ref
  | Seq of 'a * 'a

type 'a t = {
    ann : 'a;
    ty : Type.t;
    expr : ('a, 'a t) expr
  }
