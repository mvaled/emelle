open Base

type t =
  { adjacency_tbl : (int, (int, Int.comparator_witness) Set.t) Hashtbl.t }

let create () =
  { adjacency_tbl = Hashtbl.create (module Int) }

(* The register's set of interferences may include itself *)
let add_interferences graph live_regs =
  Set.iter live_regs ~f:(fun reg ->
      Hashtbl.change graph.adjacency_tbl reg ~f:(function
          | Some old_set -> Some (Set.union old_set live_regs)
          | None -> Some live_regs
        )
    );
