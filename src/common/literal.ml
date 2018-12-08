open Base

type t =
  | Char of char
  | Float of float
  | Int of int
  | String of string
[@@deriving compare, hash, sexp]
