open Base

type t =
  | Autogen of int
  | Local of string
  | Path of string list

let rec compare lhs rhs =
  match lhs, rhs with
  | Autogen lhs, Autogen rhs -> Int.compare lhs rhs
  | Local lhs, Local rhs -> String.compare lhs rhs
  | Path lhs, Path rhs -> List.compare String.compare lhs rhs
  | Autogen _, Local _ -> -1
  | Local _, Path _ -> -1
  | Autogen _, Path _ -> -1
  | lhs, rhs -> -(compare rhs lhs)

let equal lhs rhs = (compare lhs rhs) = 0

(* Rewrite this later *)
let hash ty = Hashtbl.hash ty

let sexp_of_t = failwith "Not supported"
