open Base

type t =
  { node : pattern
  ; reg : Register.t option }
and pattern =
  | Con of Type.adt * int * t list (** Constructor pattern *)
  | Or of t * t
  | Wild (** Wildcard pattern *)

(** In the paper Compiling Pattern Matching to Good Decision Trees, an
    occurrence is either empty or an integer and an occurrence, but in
    my code, the occurrence must have an index into the pattern match
    stack at the base case. *)
type occurrence =
  | Nil of int
  | Cons of int * occurrence

type occurrences = occurrence list

type 'a decision_tree =
  | Fail
  | Leaf of (Register.t, occurrence, Register.comparator_witness) Map.t * 'a
    (** A leaf holds a mapping from registers to pattern match occurrences. *)
  | Switch of occurrence * (int, 'a decision_tree) Hashtbl.t * 'a decision_tree
    (** A switch holds the scrutinee occurrence, a map from constructors to
        decision trees, and a default decision tree. *)
  | Swap of int * 'a decision_tree

type 'a row = {
    first_pattern : t;
    rest_patterns : t list;
    bindings : (Register.t, occurrence, Register.comparator_witness) Map.t;
    (** [bindings] holds a map from registers to already-popped occurrences. *)
    action : 'a
  }

(** Contract: All rows in the matrix have the same length *)
type 'a matrix = 'a row list

(** Read into a row, and returns Some row where the indexed pattern has been
    moved to the front, or None if the index reads out of bounds. *)
let swap_column_of_row (idx : int) (row : 'a row) =
  let rec f idx left = function
    | pivot::right when idx = 0 -> Some (left, pivot, right)
    | x::next -> f (idx - 1) (x::left) next
    | [] -> None
  in
  match f idx [] (row.first_pattern::row.rest_patterns) with
  | Some (left, pivot, right) ->
     Some { row with first_pattern = pivot
                   ; rest_patterns = List.rev_append left right }
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

let find_adt pats =
  let rec f i pats =
    match pats with
    | [] -> None
    | {node = Con(adt, _, _); _}::_ -> Some (adt, i)
    | {node = Wild; _ }::xs -> f (i + 1) xs
    | {node = Or(p1, p2); _}::_ ->
       match f i (p1::pats) with
       | Some x -> Some x
       | None ->
          match f i (p2::pats) with
          | Some x -> Some x
          | None -> None
  in f 0 pats

(** Specialize operation as described in Compiling Pattern Matching to Good
    Decision Trees *)
let rec specialize constr count occurrence rows =
  let helper row rows =
    let bindings =
      match row.first_pattern.reg with
      | None -> row.bindings
      | Some reg -> Map.set row.bindings ~key:reg ~data:occurrence
    in
    (* Anamorphism over lists, catamorphism over the natural numbers *)
    let rec ana coacc next = function
      | 0 -> coacc
      | n -> next::(ana coacc next (n - 1)) in
    let handle_nullary_constr rows row =
      match row.rest_patterns with
      | pat::pats ->
         { row with
           first_pattern = pat
         ; rest_patterns = pats
         ; bindings }::rows
      | [] -> rows
    in
    match row.first_pattern.node with
    | Con(_, id, cpats) when id = constr ->
       begin match cpats with
       | cpat::cpats ->
          { row with
            first_pattern = cpat
          ; rest_patterns = cpats@row.rest_patterns
          ; bindings }::rows
       | [] -> handle_nullary_constr rows row
       end
    | Con _ -> rows
    | Wild ->
       if count > 0 then
         { row with
           first_pattern = { node = Wild; reg = None }
         ; rest_patterns =
             ana row.rest_patterns { node = Wild; reg = None } (count - 1)
         ; bindings
         }::rows
       else
         handle_nullary_constr rows row
    | Or(p1, p2) ->
       let mat1 =
         specialize constr count occurrence
           [{ row with
              first_pattern = p1
            ; rest_patterns = row.rest_patterns
            ; bindings }]
       in
       let mat2 =
         specialize constr count occurrence
           [{ row with
              first_pattern = p2
            ; rest_patterns = row.rest_patterns
            ; bindings }]
       in mat1@mat2@rows
  in List.fold_right ~f:helper ~init:[] rows

(** Construct the default matrix *)
let rec default_matrix (rows : 'a row list) : 'a matrix =
  let helper row rows =
    match row.rest_patterns with
    | [] -> rows
    | second_pat::pats ->
       match row.first_pattern.node with
       | Con _ -> rows
       | Wild ->
          ({ row with first_pattern = second_pat; rest_patterns = pats }::rows)
       | Or(p1, p2) ->
          let mat1 =
            default_matrix
              [{ row with
                 first_pattern = p1
               ; rest_patterns = pats }]
          in
          let mat2 =
            default_matrix
              [{ row with
                 first_pattern = p2
               ; rest_patterns = pats }]
          in mat1@mat2@rows
  in List.fold_right ~f:helper ~init:[] rows

let map_regs_to_occs occurrences row =
  let rec helper map occurrences list =
    match occurrences, list with
    | [], [] -> Ok map
    | [], _::_ | _::_, [] -> Error Sequence.empty
    | occ::occs, pat::pats ->
       match pat.reg with
       | None -> helper map occs pats
       | Some reg -> helper (Map.set map ~key:reg ~data:occ) occs pats
  in helper row.bindings occurrences (row.first_pattern::row.rest_patterns)

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
  | (row::rows') as rows ->
     match find_adt (row.first_pattern::row.rest_patterns) with
     | None ->
        (* Case 2 *)
        map_regs_to_occs occurrences row >>| fun map ->
        Leaf(map, row.action)
     | Some(alg, i) ->
        (* Case 3 *)
        let jump_tbl = Hashtbl.create (module Int) in
        let default = default_matrix rows in
        match swap_occurrences i occurrences with
        | None -> Error Sequence.empty
        | Some (first_occ, rest_occs) ->
           let (_, product) = alg.Type.constrs.(i) in
           (* Just like how the matched value is popped off the stack and its
              children pushed on the stack, pop off the selected occurrence and
              push occurrences for its subterms *)
           let rec push_occs rest idx = function
             | [] -> rest
             | _::xs -> (Cons(idx, first_occ))::(push_occs rest (idx + 1) xs)
           in
           let pushed_occs = push_occs rest_occs 0 product in
           match swap_column i rows' with
           | None -> Error Sequence.empty
           | Some rows ->
              Array.foldi ~f:(fun id acc (_, products) ->
                  acc >>= fun () ->
                  match specialize id (List.length products) first_occ rows with
                  | [] -> Ok ()
                  | matrix ->
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
