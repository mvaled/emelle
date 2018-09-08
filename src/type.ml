open Base

type prim =
  | Arrow
  | Int
  | Float
[@@deriving compare, sexp]

type t =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var
[@@deriving sexp]
and var =
  { id : int
  ; mutable ty : t option
  ; mutable level : int
  ; kind : Kind.t }
[@@deriving sexp]

type vargen = int ref

module Var = struct
  type t = var
  [@@deriving sexp]

  type gen = vargen

  let compare l r = compare l.id r.id
  let hash x = x.id
end

type adt =
  { typeparams: var list
  ; constr_names: (string, int) Hashtbl.t
  ; constrs: (string * t array) array }

let equal_prim x y = (compare_prim x y) = 0

let create_vargen () = { contents = 0 }

let fresh_var vargen level kind =
  vargen := !vargen + 1;
  { id = !vargen - 1; ty = None; level; kind = kind }

(** [with_params ty \[a; b; ...; z\]] is (... ((ty a) b) ...z) *)
let with_params ty =
  List.fold ~f:(fun acc param -> App(acc, param)) ~init:ty

(** [curry \[a; b; ...; z\] ty] is a -> b -> ... z -> ty.
    [curry \[\] ty] is ty. *)
let rec curry input_tys output_ty =
  match input_tys with
  | [] -> output_ty
  | (ty::tys) -> App(App(Prim Arrow, ty), curry tys output_ty)

(** Given an ADT and one of its constructors, return the constructor's type *)
let type_of_constr ident adt constr =
  let _, product = adt.constrs.(constr) in
  let output_ty =
    with_params (Nominal ident) (List.map ~f:(fun x -> Var x) adt.typeparams)
  in curry (Array.to_list product) output_ty

let kind_of_adt adt =
  Kind.curry (List.map ~f:(fun uvar -> uvar.kind) adt.typeparams) Kind.Mono

(** Perform the occurs check, returning true if the typevar occurs in the type.
    Adjusts the levels of unassigned typevars when necessary. *)
let rec occurs tvar = function
  | App(tcon, targ) -> occurs tvar tcon || occurs tvar targ
  | Nominal _ -> false
  | Prim _ -> false
  | Var { id; _ } when id = tvar.id -> true
  | Var { ty = Some ty; _ } -> occurs tvar ty
  | Var ({ ty = None; _ } as tvar2) ->
     if tvar2.level > tvar.level then (
       tvar2.level <- tvar.level
     );
     false
