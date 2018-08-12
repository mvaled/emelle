open Base

type prim =
  | Arrow
  | Int
  | Float
[@@deriving compare]

module UVar = struct
  type id =
    | Annotated of int
    | Gen of int
  [@@deriving compare, hash, sexp]

  type t = {
      id : id;
      mutable level : int [@compare.ignore][@hash.ignore];
      name : string option [@compare.ignore][@hash.ignore];
    }
  [@@deriving compare, hash, sexp]
end

type t =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var ref

and var =
  | Unassigned of UVar.t
  | Assigned of t

type adt = {
    typeparams: UVar.t list;
    constr_names: (string, int) Hashtbl.t;
    constr_types: t array array;
  }

type def =
  | Algebraic of adt
  | Alias of t

let equal_prim x y = (compare_prim x y) = 0

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
  let product = adt.constr_types.(constr) in
  let f uvar = Var (ref (Unassigned uvar)) in
  let output_ty = with_params (Nominal ident) (List.map ~f:f adt.typeparams) in
  curry (Array.to_list product) output_ty
