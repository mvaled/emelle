open Base

type t =
  | Local of string
  | Path of string list
[@@deriving compare, hash, sexp]

let equal x y = (compare x y) = 0
