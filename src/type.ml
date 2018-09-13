open Base

type prim =
  | Arrow
  | Int
  | Float
[@@deriving compare, sexp]

type t =
  { mutable level_opt : int option
  ; node : t' }
[@@deriving sexp]
and t' =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var
[@@deriving sexp]
and var =
  { id : int
  ; mutable level : int
  ; mutable ty : t option
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
  List.fold
    ~f:(fun acc param ->
      { level_opt = None; node = App(acc, param) }
    ) ~init:ty

(** [curry \[a; b; ...; z\] ty] is a -> b -> ... z -> ty.
    [curry \[\] ty] is ty. *)
let rec curry input_tys output_ty =
  match input_tys with
  | [] -> output_ty
  | (ty::tys) ->
     { level_opt = None
     ; node = App
                ( { level_opt = None
                  ; node = App({ level_opt = None; node = Prim Arrow}, ty) }
              , curry tys output_ty) }

(** Given an ADT and one of its constructors, return the constructor's type *)
let type_of_constr ident adt constr =
  let _, product = adt.constrs.(constr) in
  let output_ty =
    with_params
      { level_opt = None; node = Nominal ident }
      (List.map ~f:(fun x -> { level_opt = None; node = Var x}) adt.typeparams)
  in curry (Array.to_list product) output_ty

let kind_of_adt adt =
  Kind.curry (List.map ~f:(fun uvar -> uvar.kind) adt.typeparams) Kind.Mono

(** Perform the occurs check, returning true if the typevar occurs in the type.
    Adjusts the levels of unassigned typevars when necessary. *)
let rec occurs tvar ty =
  match ty.level_opt with
  | Some x when x < tvar.level -> false
  | _ ->
     ty.level_opt <- Some tvar.level;
     match ty.node with
     | App(tcon, targ) -> occurs tvar tcon || occurs tvar targ
     | Nominal _ -> false
     | Prim _ -> false
     | Var { id; _ } when id = tvar.id -> true
     | Var { ty = Some ty; _ } -> occurs tvar ty
     | Var _ -> false

let of_node node = { level_opt = None; node}

let arrow l r =
  let arrow = { level_opt = None; node = Prim Arrow } in
  let ty = { level_opt = None; node = App(arrow, l) } in
  { level_opt = None; node = App(ty, r) }
