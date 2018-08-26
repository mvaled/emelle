open Base

type kind =
  | Mono
  | Poly of kind * kind
[@@deriving sexp]

let rec equals_kind k1 k2 =
  match k1, k2 with
  | Mono, Mono -> true
  | Poly(a, b), Poly(c, d) -> equals_kind a c && equals_kind b d
  | _ -> false

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
      kind : kind [@compare.ignore][@hash.ignore];
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

type adt =
  { typeparams: UVar.t list
  ; constr_names: (string, int) Hashtbl.t
  ; constrs: (string * t array) array }

let equal_prim x y = (compare_prim x y) = 0

let of_uvar uvar = Var (ref (Unassigned uvar))

(** [with_params ty \[a; b; ...; z\]] is (... ((ty a) b) ...z) *)
let with_params ty =
  List.fold ~f:(fun acc param -> App(acc, param)) ~init:ty

let rec curry_kinds input_ks output_k =
  match input_ks with
  | [] -> output_k
  | (k::ks) -> Poly(k, curry_kinds ks output_k)

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
    with_params (Nominal ident) (List.map ~f:of_uvar adt.typeparams)
  in curry (Array.to_list product) output_ty
