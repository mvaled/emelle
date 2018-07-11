type t =
  | Autogen of int
  | Local of string
  | Path of string list

type u = t

let compare lhs rhs =
  match lhs, rhs with
  | Autogen lhs, Autogen rhs -> compare lhs rhs
  | Local lhs, Local rhs -> compare lhs rhs
  | Path lhs, Path rhs -> compare lhs rhs
  | Autogen _, Local _ -> -1
  | Local _, Path _ -> -1
  | Autogen _, Path _ -> -1
  | lhs, rhs -> -(compare rhs lhs)

let equal lhs rhs = (compare lhs rhs) = 0

(* Rewrite this later *)
let hash ty = Hashtbl.hash ty

module Tbl = Hashtbl.Make(
  struct
    type t = u
    let equal = equal
    let hash = hash
  end
)
