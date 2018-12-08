(** The module of fully-qualified identifers *)

open Base

module T = struct
  type t = string * string
  [@@deriving compare, hash, sexp]

  let equal x y = (compare x y) = 0
end

include T
include Comparator.Make(T)
