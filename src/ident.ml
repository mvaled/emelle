open Base

module T = struct
  type t =
    | Local of string
    | Path of t * string
  [@@deriving compare, hash, sexp]

  let equal x y = (compare x y) = 0
end

include T
include Comparator.Make(T)
