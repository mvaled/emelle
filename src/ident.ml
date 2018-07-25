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

type u = t

(** DEPRECATED compatibility module to stdlib Hashtbl module
    TODO: Switch to Jane Street's Hashtbl intf *)
module Tbl = struct
  type nonrec 'a t = (t, 'a) Hashtbl.t
  let create n =
    let module M = struct
        type t = u
        let hash = hash
        let compare = compare
        let sexp_of_t = failwith "Not supported"
      end
    in
    Hashtbl.create (module M) ~growth_allowed:true ~size:n
  let find_opt = Hashtbl.find
  let mem = Hashtbl.mem
  let add tbl key data = Hashtbl.add_exn tbl ~key:key ~data:data
  let fold f tbl init =
    Hashtbl.fold ~f:(fun ~key ~data acc -> f key data acc ) ~init:init tbl
end
