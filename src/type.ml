type prim =
  | Int
  | Float

type t =
  | App of t * t
  | Nominal of Ident.t
  | Prim of prim
  | Var of var ref

and var =
  | Unassigned of int ref
  | Assigned of t

type algebraic = (t array * int) Ident.Tbl.t

type def = Alias of t | Algebraic of algebraic

let rec occurs (uvar : int ref) = function
  | App(tcon, targ) -> occurs uvar tcon && occurs uvar targ
  | Nominal _ -> false
  | Prim _ -> false
  | Var cell ->
     match !cell with
     | Assigned ty -> occurs uvar ty
     | Unassigned u ->
        if u == uvar then (* Check physical equality *)
          true
        else (
          (* Adjust levels if necessary *)
          if !u > !uvar then (
            u := !uvar
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
     | Unassigned ref ->
        begin match ty with
        (* A variable occurring in itself is not an error *)
        | Var {contents = Unassigned ref2} when ref == ref2 -> ()
        | _ ->
           if occurs ref ty then
             Queue.add pair errs
           else
             ()
        end
     | Assigned t -> unify errs t ty
     end
  | pair -> Queue.add pair errs
