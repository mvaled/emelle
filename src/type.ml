open Base

type prim =
  | Int
  | Float

type unassigned_var = {
    id : int;
    mutable level : int;
  }

type t =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var ref

and var =
  | Unassigned of unassigned_var
  | Assigned of t

type algebraic = (Ident.t, (t array * int)) Hashtbl.t

type def = Alias of t | Algebraic of algebraic

type error = Unification_fail of t * t

type checker = {
    mutable vargen : int
  }

let compare_prim l r =
  match l, r with
  | Int, Float -> -1
  | Float, Int -> 1
  | _ -> 0

let fresh_utvar checker level =
  let old = checker.vargen in
  checker.vargen <- old + 1;
  { id = old; level = level }

let rec occurs (uvar : unassigned_var) = function
  | App(tcon, targ) -> occurs uvar tcon && occurs uvar targ
  | Nominal _ -> false
  | Prim _ -> false
  | Var cell ->
     match !cell with
     | Assigned ty -> occurs uvar ty
     | Unassigned u ->
        if u.id = uvar.id then
          true
        else (
          (* Adjust levels if necessary *)
          if u.level > uvar.level then (
            u.level <- uvar.level
          );
          false
        )

(** Unify two types, returning the unification errors *)
let rec unify lhs rhs =
  if not (phys_equal lhs rhs) then
    Sequence.empty
  else
    match lhs, rhs with
    | App(lcon, larg), App(rcon, rarg) ->
       Sequence.append (unify lcon rcon) (unify larg rarg)
    | Nominal lstr   , Nominal rstr when (Ident.compare lstr rstr) = 0 ->
       Sequence.empty
    | Prim lprim     , Prim rprim   when (compare_prim lprim rprim) = 0 ->
       Sequence.empty
    | (Var v, ty)    | (ty, Var v) ->
       begin match !v with
       | Unassigned uvar ->
          begin match ty with
          (* A variable occurring in itself is not an error *)
          | Var {contents = Unassigned uvar2} when uvar.id = uvar2.id ->
             Sequence.empty
          | _ ->
             if occurs uvar ty then
               Sequence.return (Unification_fail(lhs, rhs))
             else
               Sequence.empty
          end
       | Assigned t -> unify t ty
       end
    | _ -> Sequence.return (Unification_fail(lhs, rhs))

(** Instantiate a type scheme by replacing type variables whose levels are
    greater than or equal to target_level with type variables of level
    new_level *)
let inst checker target_level new_level =
  let map = Hashtbl.create (module Int) in
  let rec helper = function
    | App(tcon, targ) -> App(helper tcon, helper targ)
    | Var { contents = Assigned ty } -> helper ty
    | (Var { contents = Unassigned uvar }) as var ->
       if uvar.level < target_level then
         var
       else
         begin match Hashtbl.find map uvar.id with
         | Some uvar2 -> Var (ref (Unassigned uvar2))
         | None ->
            let uvar2 = fresh_utvar checker new_level in
            Hashtbl.add_exn map ~key:uvar.id ~data:uvar2;
            Var (ref (Unassigned uvar2))
         end
    | ty -> ty
  in helper
