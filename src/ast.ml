open Base

type path = string list * string

type monotype =
  | TApp of monotype * monotype
  | TArrow
  | TFloat
  | TInt
  | TVar of path

type polytype = Forall of string list * monotype

type 'a pattern = 'a * 'a pattern'
and 'a pattern' =
  | Con of path * string * 'a pattern list
  | Var of string
  | Wild

type 'a expr = 'a * 'a expr'
and 'a expr' =
  | App of 'a expr * 'a expr
  | Case of 'a expr * ('a pattern * 'a expr) list
  | Lam of 'a lambda_case * 'a lambda_case list
  | Let of ('a pattern * 'a expr) list * 'a expr
  | Let_rec of (string * 'a expr) list * 'a expr
  | Var of path
and 'a lambda_case = 'a pattern * 'a pattern list * 'a expr

type adt =
  { name : string
  ; typeparams : string list
  ; constrs : (string * monotype list) list }

type 'a file =
  { adts : adt list list
  ; expr : 'a expr }
