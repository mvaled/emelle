open Base

type prim =
  | Arrow
  | Char
  | Float
  | Int
  | String
[@@deriving compare, sexp]

(** Type [quant] describes whether a type variable is existentially quantified
    within a scope or universally quantified. *)
type quant =
  | Exists of int
  | Univ
[@@deriving sexp]

(* A universal level is greater than all existential levels *)
let compare_quant l r =
  match l, r with
  | Univ, Univ -> 0
  | Univ, Exists _ -> 1
  | Exists _, Univ -> -1
  | Exists l, Exists r -> Int.compare l r

(** The level of [Univ] is [-1]; the level of [Exists level] is [level]. *)
let level_of_quant = function
  | Univ -> -1
  | Exists level -> level

(** Returns the greater of two ints. *)
let max l r =
  if l < r then
    r
  else
    l

(** Each type is annotated with the greatest level of its children. *)
type t =
  { mutable level : int
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
  ; mutable quant : quant
  ; mutable ty : t option
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

type adt =
  { name : string
  ; typeparams: var list
  ; constr_names: (string, int) Hashtbl.t
  ; constrs: (string * t list) array }

type decl =
  | Abstract of Kind.t
  | Manifest of adt

let equal_prim x y = (compare_prim x y) = 0

(** [create_vargen ()] creates a fresh vargen state. *)
let create_vargen () = { contents = 0 }

let fresh_var vargen quant kind =
  vargen := !vargen + 1;
  { id = !vargen - 1; ty = None; quant; kind = kind }

(** [with_params ty \[a; b; ...; z\]] is (... ((ty a) b) ...z) *)
let with_params ty =
  List.fold
    ~f:(fun acc param ->
      { level = max acc.level param.level; node = App(acc, param) }
    ) ~init:ty

(** [curry \[a; b; ...; z\] ty] is a -> b -> ... z -> ty.
    [curry \[\] ty] is ty. *)
let rec curry input_tys output_ty =
  match input_tys with
  | [] -> output_ty
  | (ty::tys) ->
     let out_ty = curry tys output_ty in
     { level = max ty.level out_ty.level
     ; node = App
                ( { level = ty.level
                  ; node = App({ level = ty.level; node = Prim Arrow}, ty) }
              , out_ty) }

(** Given an ADT and one of its constructors, return the constructor's type *)
let type_of_constr ident adt constr =
  let _, product = adt.constrs.(constr) in
  let output_ty =
    with_params
      { level = -1; node = Nominal ident }
      (List.map ~f:(fun x -> { level = -1; node = Var x}) adt.typeparams)
  in curry product output_ty

let kind_of_adt adt =
  Kind.curry (List.map ~f:(fun uvar -> uvar.kind) adt.typeparams) Kind.Mono

(** [occurs tvar ty] performs the occurs check, returning true if [tyvar] occurs
    in [ty]. It ignores universally quantified type variables and adjusts the
    levels of unassigned typevars when necessary. *)
let rec occurs tvar ty =
  match tvar.quant with
  | Univ -> false
  | Exists level ->
     if ty.level < level then
       false
     else (
       ty.level <- level;
       match ty.node with
       | App(tcon, targ) -> occurs tvar tcon || occurs tvar targ
       | Nominal _ -> false
       | Prim _ -> false
       | Var { id; _ } when id = tvar.id -> true
       | Var { ty = Some ty; _ } -> occurs tvar ty
       | Var tvar2 ->
          if (level_of_quant tvar2.quant) > level then (
            tvar2.quant <- Exists level
          );
          false
     )

let of_node node =
  let level =
    match node with
    | App(f, x) -> max f.level x.level
    | Var var -> level_of_quant var.quant
    | _ -> -1
  in { level; node }

let arrow l r =
  let arrow = { level = -1; node = Prim Arrow } in
  let ty = { level = l.level; node = App(arrow, l) } in
  { level = max l.level r.level; node = App(ty, r) }
