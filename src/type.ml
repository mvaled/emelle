open Base

type prim =
  | Arrow
  | Int
  | Float
[@@deriving compare]

type unassigned_var = {
    id : int;
    mutable level : int;
  }
[@@deriving compare, sexp]

module UVar = struct
  type t = unassigned_var
  [@@deriving sexp]

  let compare x y = compare x.id y.id
  let hash x = x.id
end

type t =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var ref

and var =
  | Unassigned of unassigned_var
  | Assigned of t

type adt = {
    typeparams: unassigned_var list;
    constrs: (string, (t array * int)) Hashtbl.t;
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

(** Given an ADT and one of its constructors, return Some the constructor's type
    or None if the constructor doesn't belong to the ADT *)
let type_of_constr ident adt constr =
  match Hashtbl.find adt.constrs constr with
  | Some (product, _) ->
     let f uvar = Var (ref (Unassigned uvar)) in
     let output_ty =
       with_params (Nominal ident) (List.map ~f:f adt.typeparams)
     in Some (curry (Array.to_list product) output_ty)
  | None -> None
