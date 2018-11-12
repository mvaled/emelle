open Base

type t =
  { node : pattern
  ; id : Ident.t option }
and pattern =
  | Con of Type.adt * int * t list (** Constructor pattern *)
  | Deref of t
  | Or of t * t
  | Wild (** Wildcard pattern *)

(** In the paper Compiling Pattern Matching to Good Decision Trees, an
    occurrence is either empty or an integer and an occurrence, but in
    my code, the occurrence must have an index into the pattern match
    stack at the base case. *)
type occurrence =
  | Nil of int
  | Cons of int * occurrence
  | Contents of occurrence

type occurrences = occurrence list

type decision_tree =
  | Ref of occurrence * decision_tree
  | Fail
  | Leaf of (Ident.t, occurrence, Ident.comparator_witness) Map.t * int
    (** A leaf holds a mapping from idents to pattern match occurrences. *)
  | Switch of occurrence * (int, decision_tree) Hashtbl.t * decision_tree
    (** A switch holds the scrutinee occurrence, a map from constructors to
        decision trees, and a default decision tree. *)
  | Swap of int * decision_tree

type row = {
    patterns : t list;
    bindings : (Ident.t, occurrence, Ident.comparator_witness) Map.t;
    (** [bindings] holds a map from idents to already-popped occurrences. *)
    action : int
  }

(** Contract: All rows in the matrix have the same length *)
type matrix = row list

(** Read into a row, and returns Some row where the indexed pattern has been
    moved to the front, or None if the index reads out of bounds. *)
let swap_column_of_row (idx : int) (row : row) =
  let rec f idx left = function
    | pivot::right when idx = 0 -> Some (left, pivot, right)
    | x::next -> f (idx - 1) (x::left) next
    | [] -> None
  in
  match f idx [] row.patterns with
  | Some (left, pivot, right) ->
     Some { row with patterns = pivot::(List.rev_append left right) }
  | None -> None

(** Column-swapping operation for matrices *)
let swap_column idx =
  let map = Option.map in
  let bind = Option.bind in
  List.fold ~f:(fun acc next ->
      bind acc ~f:(fun rows ->
          map ~f:(fun row -> row::rows) (swap_column_of_row idx next)
        )
    ) ~init:(Some [])

type find_adt_result =
  | All_wilds
  | Adt of Type.adt * int
  | Found_ref of int

let find_adt pats =
  let rec f i pats =
    match pats with
    | [] -> All_wilds
    | {node = Con(adt, _, _); _}::_ -> Adt(adt, i)
    | {node = Deref _; _}::_ -> Found_ref i
    | {node = Wild; _ }::xs -> f (i + 1) xs
    | {node = Or(p1, _); _}::pats -> f i (p1::pats)
  in f 0 pats

(** Specialize operation as described in Compiling Pattern Matching to Good
    Decision Trees *)
let rec specialize constr product occurrence rows =
  let open Option.Monad_infix in
  let helper row rows =
    match row.patterns with
    | [] -> None
    | first_pat::rest_pats ->
       let bindings =
         match first_pat.id with
         | None -> row.bindings
         | Some id -> Map.set row.bindings ~key:id ~data:occurrence
       in
       let rec fill acc next = function
         | [] -> acc
         | _::xs -> fill (next::acc) next xs
       in
       match first_pat.node with
       | Con(_, name, cpats) when name = constr ->
          Some ({ row with
                  patterns = cpats@rest_pats
                ; bindings }::rows)
       | Con _ -> Some rows
       | Deref _ -> None
       | Wild ->
          Some ({ row with
                  patterns =
                    fill rest_pats { node = Wild; id = None } product
                ; bindings }::rows)
       | Or(p1, p2) ->
          specialize constr product occurrence
            [{ row with
               patterns = p1::rest_pats
             ; bindings }]
          >>= fun mat1 ->
          specialize constr product occurrence
            [{ row with
               patterns = p2::rest_pats
             ; bindings }]
          >>| fun mat2 ->
          mat1@mat2@rows
  in
  List.fold_right ~f:(fun row acc ->
      acc >>= fun rows -> helper row rows
    ) ~init:(Some []) rows

(** A variation of the specialization algorithm for dereference patterns *)
let specialize_ref occurrence rows =
  let open Option.Monad_infix in
  let helper row rows =
    match row.patterns with
    | [] -> None
    | { node; id }::rest_pats ->
       let bindings =
         match id with
         | None -> row.bindings
         | Some id -> Map.set row.bindings ~key:id ~data:occurrence
       in
       match node with
       | Deref pat->
          Some ({ row with
                  patterns = pat::rest_pats
                ; bindings }::rows)
       | Wild ->
          Some ({ row with
                  patterns = { node = Wild; id = None }::rest_pats
                ; bindings }::rows)
       | _ -> None
  in
  List.fold_right ~f:(fun row acc ->
      acc >>= fun rows -> helper row rows
    ) ~init:(Some []) rows

(** Construct the default matrix *)
let rec default_matrix rows =
  let open Option.Monad_infix in
  let helper row rows =
    match row.patterns with
    | [] -> None
    | first_pat::rest_pats ->
       match first_pat.node with
       | Con _ -> Some rows
       | Deref _ -> None
       | Wild ->
          Some ({ row with patterns = rest_pats }::rows)
       | Or(p1, p2) ->
          default_matrix [{ row with patterns = p1::rest_pats }]
          >>= fun mat1 ->
          default_matrix [{ row with patterns = p2::rest_pats }]
          >>| fun mat2 ->
          mat1@mat2@rows
  in
  List.fold_right ~f:(fun row acc ->
      acc >>= fun rows -> helper row rows
    ) ~init:(Some []) rows

let map_ids_to_occs occurrences row =
  let rec helper map occurrences list =
    match occurrences, list with
    | [], [] -> Ok map
    | [], _::_ ->
       Error (Sequence.return (Message.Unreachable "Too many patterns"))
    | _::_, [] ->
       Error (Sequence.return (Message.Unreachable "Too many occurrences"))
    | occ::occs, pat::pats ->
       match pat.id with
       | None -> helper map occs pats
       | Some id -> helper (Map.set map ~key:id ~data:occ) occs pats
  in helper row.bindings occurrences row.patterns

(** Corresponds with swap_columns and swap_column_of_row (The occurrences vector
    is like another row) *)
(* Maybe make function generic instead of repeating code? TODO consider later *)
let swap_occurrences idx (occurrences : occurrence list) =
  let rec f idx left = function
    | pivot::right when idx = 0 -> Some (left, pivot, right)
    | x::next -> f (idx - 1) (x::left) next
    | [] -> None
  in
  match f idx [] occurrences with
  | Some (left, pivot, right) -> Some (pivot, List.rev_append left right)
  | None -> None

(** Compilation scheme CC *)
let rec decision_tree_of_matrix occurrences =
  let open Result.Monad_infix in
  function
  | [] -> Ok Fail (* Case 1 *)
  | (row::_) as rows ->
     match find_adt row.patterns with
     | All_wilds ->
        (* Case 2 *)
        map_ids_to_occs occurrences row >>| fun map ->
        Leaf(map, row.action)
     | Adt(alg, i) ->
        (* Case 3 *)
        let jump_tbl = Hashtbl.create (module Int) in
        begin match swap_column i rows with
        | None -> Error Sequence.empty
        | Some rows ->
           match default_matrix rows with
           | None ->
              Error (Sequence.return
                       (Message.Unreachable "No default of empty matrix"))
           | Some default ->
              match swap_occurrences i occurrences with
              | None ->
                 Error (Sequence.return (Message.Unreachable (String.concat
                   ["Pattern idx out of bounds: "; Int.to_string i]
                 )))
              | Some (first_occ, rest_occs) ->
                 Array.foldi ~f:(fun id acc (_, product, _) ->
                     acc >>= fun () ->
                     (* Just like how the matched value is popped off the stack
                        and its children pushed on the stack, pop off the
                        selected occurrence and push occurrences for its
                        subterms *)
                     let rec push_occs rest idx = function
                       | [] -> rest
                       | _::xs ->
                          (Cons(idx, first_occ))::(push_occs rest (idx + 1) xs)
                     in
                     let pushed_occs = push_occs rest_occs 0 product in
                     match
                       specialize id product first_occ rows
                     with
                     | None ->
                        Error (Sequence.return
                                 (Message.Unreachable "dec tree 1"))
                     | Some matrix ->
                        match decision_tree_of_matrix pushed_occs matrix with
                        | Ok tree ->
                           Hashtbl.add_exn ~key:id ~data:tree jump_tbl;
                           Ok ()
                        | Error e -> Error e
                   ) alg.Type.constrs ~init:(Ok ()) >>= fun () ->
                 decision_tree_of_matrix rest_occs default
                 >>| fun default_tree ->
                 let switch = Switch(first_occ, jump_tbl, default_tree) in
                 if i = 0 then switch else Swap(i, switch)
        end
     | Found_ref i ->
        match swap_occurrences i occurrences with
        | None -> Error Sequence.empty
        | Some (first_occ, rest_occs) ->
           match swap_column i rows with
           | None -> Error Sequence.empty
           | Some rows ->
              match specialize_ref first_occ rows with
              | None -> Error Sequence.empty
              | Some matrix ->
                 let occs = (Contents first_occ)::rest_occs in
                 decision_tree_of_matrix occs matrix >>| fun tree ->
                 let switch = Ref(first_occ, tree) in
                 if i = 0 then switch else Swap(i, switch)
