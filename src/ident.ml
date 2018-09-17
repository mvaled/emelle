open Base

module T = struct
  type t =
    | Root of string
    | Dot of t * string
  [@@deriving compare, hash, sexp]

  let equal x y = (compare x y) = 0

  let of_path (prefix, name) =
    match prefix with
    | [] -> Root name
    | root::subpath ->
       let prefix =
         List.fold ~f:(fun acc next ->
             Dot(acc, next)
           ) ~init:(Root root) subpath
       in Dot(prefix, name)

  let rec prefix pref = function
    | Root str -> Dot(pref, str)
    | Dot(left, right) -> Dot(prefix pref left, right)
end

include T
include Comparator.Make(T)
