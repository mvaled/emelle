open Base

type generalizability =
  | Const
  | Mut
[@@deriving sexp]

type t =
  | Mono
  | Poly of t * generalizability ref * t
  | Var of var
[@@deriving sexp]
and var =
  { id : int
  ; mutable kind : t option }

type vargen = int ref

let create_vargen () = ref 0

let fresh_var vargen =
  vargen := !vargen + 1;
  { id = !vargen - 1; kind = None }

let rec curry input_ks output_k =
  match input_ks with
  | [] -> output_k
  | (k::ks) -> Poly(k, ref Const, curry ks output_k)

let rec occurs kvar = function
  | Mono -> false
  | Poly(k1, _, k2) -> occurs kvar k1 || occurs kvar k2
  | Var { id; _ } when id = kvar.id -> true
  | Var { kind = Some kind; _ } -> occurs kvar kind
  | Var { kind = None; _ } -> false

let rec refresh = function
  | Mono -> Mono
  | Poly(k1, g, k2) ->
     Poly(refresh k1, ref !g, k2)
  | Var { kind = Some kind; _ } -> refresh kind
  | Var { kind = None; _ } as var -> var
