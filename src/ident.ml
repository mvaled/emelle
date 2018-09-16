open Base

module T = struct
  type t =
    | Local of string
    | Path of t * string
  [@@deriving compare, hash, sexp]

  let equal x y = (compare x y) = 0

  let of_path (prefix, name) =
    match prefix with
    | [] -> Local name
    | root::subpath ->
       let prefix =
         List.fold ~f:(fun acc next ->
             Path(acc, next)
           ) ~init:(Local root) subpath
       in Path(prefix, name)

  let rec prefix pref = function
    | Local str -> Path(pref, str)
    | Path(left, right) -> Path(prefix pref left, right)
end

include T
include Comparator.Make(T)
