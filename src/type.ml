open Base

type purity =
  | Pure
  | Impure
[@@deriving sexp]

type prim =
  | Arrow
  | Char
  | Float
  | Int
  | Ref
  | String
[@@deriving compare, sexp]

type levels = {
    mutable let_level : int;
    mutable lam_level : int;
  } [@@deriving sexp]

(** Type [quant] describes whether a type variable is existentially quantified
    within a scope or universally quantified. *)
type quant =
  | Exists of levels
  | Univ
[@@deriving sexp]

(** Each type is annotated with the greatest level of its children. *)
type t =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var
[@@deriving sexp]
and var =
  { id : int
  ; mutable quant : quant
  ; mutable ty : t option
  ; mutable purity : purity
  ; kind : Kind.t }
[@@deriving sexp]

(** Type [vargen] is the generator of fresh type variables. *)
type vargen = int ref

module Var = struct
  type t = var
  [@@deriving sexp]

  type gen = vargen

  let compare l r = compare l.id r.id
  let hash x = x.id
end

type adt = {
    name : string;
    adt_kind : Kind.t;
    constr_names : (string, int) Hashtbl.t;
    constrs : (string * t list * t) array
  }

type decl =
  | Abstract of Kind.t
  | Manifest of adt

let equal_prim x y = (compare_prim x y) = 0

(** [create_vargen ()] creates a fresh vargen state. *)
let create_vargen () = { contents = 0 }

let fresh_var vargen purity quant kind =
  vargen := !vargen + 1;
  { id = !vargen - 1
  ; ty = None
  ; quant
  ; purity
  ; kind = kind }

let arrow l r =
  let arrow = Prim Arrow in
  let ty = App(arrow, l) in
  App(ty, r)

(** [with_params ty \[a; b; ...; z\]] is (... ((ty a) b) ...z) *)
let with_params ty =
  List.fold ~f:(fun acc param -> App(acc, param)) ~init:ty

(** [curry \[a; b; ...; z\] ty] is a -> b -> ... z -> ty.
    [curry \[\] ty] is ty. *)
let rec curry input_tys output_ty =
  match input_tys with
  | [] -> output_ty
  | (ty::tys) ->
     let out_ty = curry tys output_ty in
     arrow ty out_ty

(** Given an ADT and one of its constructors, return the constructor's type *)
let type_of_constr adt constr =
  let _, product, output_ty = adt.constrs.(constr) in
  curry product output_ty

let kind_of_adt adt = adt.adt_kind

(** [occurs tvar ty] performs the occurs check, returning true if [tyvar] occurs
    in [ty]. It ignores universally quantified type variables and adjusts the
    levels of unassigned typevars when necessary. *)
let rec occurs tvar ty =
  match ty with
  | App(tcon, targ) ->
     occurs tvar tcon || occurs tvar targ
  | Nominal _ -> false
  | Prim _ -> false
  | Var { id; _ } when id = tvar.id -> true
  | Var { ty = Some ty; _ } -> occurs tvar ty
  | Var tvar2 ->
     begin match tvar.quant, tvar2.quant with
     | Exists levels, Exists levels2 ->
        if levels2.let_level > levels.let_level then (
          levels2.let_level <- levels.let_level
        );
        if levels2.lam_level > levels.lam_level then (
          levels2.lam_level <- levels.lam_level
        )
     | _ -> ()
     end;
     begin match tvar2.purity with
     | Pure ->
        tvar2.purity <- tvar.purity
     | _ -> ()
     end;
     false
