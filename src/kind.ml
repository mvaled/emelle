open Base

type mutability =
  | Const
  | Mut
[@@deriving sexp]

type t =
  | Mono
  | Poly of t * mutability ref * t
  | Var of var
[@@deriving sexp]
and var =
  { id : int
  ; mutable kind : t option }

type vargen = int ref

let create_vargen () = ref 0

let fresh_var vargen =
  let id = !vargen in
  vargen := id + 1;
  { id = id; kind = None }

let rec curry input_ks output_k =
  match input_ks with
  | [] -> output_k
  | (k, mut)::ks -> Poly(k, mut, curry ks output_k)

let rec occurs kvar = function
  | Mono -> false
  | Poly(k1, _, k2) -> occurs kvar k1 || occurs kvar k2
  | Var { id; _ } when id = kvar.id -> true
  | Var { kind = Some kind; _ } -> occurs kvar kind
  | Var { kind = None; _ } -> false

let rec refresh = function
  | Poly(k0, mut, k1) ->
     Poly(refresh k0, ref !mut, k1)
  | Var { kind = Some kind; _ } -> refresh kind
  | kind -> kind
