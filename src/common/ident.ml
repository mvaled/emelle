open Base

module T = struct
  type t =
    { id : int
    ; name : string option
    } [@@deriving sexp]

  let compare l r = Int.compare l.id r.id

  let hash l = l.id

  type gen = int ref

  let create_gen () = ref 0

  let fresh gen name =
    let id = !gen in
    gen := id + 1;
    { id; name }
end

include T
include Comparator.Make(T)
