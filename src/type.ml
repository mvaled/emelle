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

type algebraic = (t array * int) Ident.Tbl.t

type def = Alias of t | Algebraic of algebraic

type checker = {
    mutable vargen : int
  }

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

(** Unify two types, collecting errors in the err parameter  *)
let rec unify errs lhs rhs =
  if lhs != rhs then
  match lhs, rhs with
  | App(lcon, larg), App(rcon, rarg) ->
     unify errs lcon rcon;
     unify errs larg rarg
  | Nominal lstr   , Nominal rstr when lstr = rstr -> ()
  | Prim lprim     , Prim rprim   when lprim = rprim -> ()
  | ((Var v, ty)   | (ty, Var v)) as pair ->
     begin match !v with
     | Unassigned uvar ->
        begin match ty with
        (* A variable occurring in itself is not an error *)
        | Var {contents = Unassigned uvar2} when uvar.id = uvar2.id -> ()
        | _ ->
           if occurs uvar ty then
             Queue.add pair errs
           else
             ()
        end
     | Assigned t -> unify errs t ty
     end
  | pair -> Queue.add pair errs

(** Instantiate a type scheme by replacing type variables whose levels are
    greater than or equal to target_level with type variables of level
    new_level *)
let inst checker target_level new_level =
  let map = Hashtbl.create 11 in
  let rec helper = function
    | App(tcon, targ) -> App(helper tcon, helper targ)
    | Var { contents = Assigned ty } -> helper ty
    | (Var { contents = Unassigned uvar }) as var ->
       if uvar.level < target_level then
         var
       else
         begin match Hashtbl.find_opt map uvar.id with
         | Some uvar2 -> Var (ref (Unassigned uvar2))
         | None ->
            let uvar2 = fresh_utvar checker new_level in
            Hashtbl.add map uvar.id uvar2;
            Var (ref (Unassigned uvar2))
         end
    | ty -> ty
  in helper
