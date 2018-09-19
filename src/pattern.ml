open Base

 (** Like a list, an occurrence is either empty or an integer followed by an
    occurence *)
type occurrence = int list
and occurrences = occurrence list
and 'a decision_tree =
  | Fail
  | Leaf of int option list * 'a
  | Switch of
      occurrence * int option * Type.adt
      * (int, 'a decision_tree) Hashtbl.t * 'a decision_tree
  | Swap of int * 'a decision_tree

type 'a row =
  { first_pattern : Term.pattern
  ; rest_patterns : Term.pattern list
  ; action : 'a }

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

type find_adt_result =
  | Some_constr of int option * Type.adt * int
  | All_wilds of int option list

let find_adt pats =
  let rec f i regs pats =
    match pats with
    | [] -> All_wilds (List.rev regs)
    | Term.{node = Con(adt, _, _); reg}::_ -> Some_constr(reg, adt, i)
    | Term.{node = Wild; reg}::xs -> f (i + 1) (reg::regs) xs
  in f 0 [] pats

(** Specialize operation as described in Compiling Pattern Matching to Good
    Decision Trees *)
let specialize
      (constr : int)
      (count  : int)
      (rows   : 'a row list)
    : 'a matrix =
  (* Anamorphism over lists, catamorphism over the natural numbers *)
  let rec ana coacc next = function
    | 0 -> coacc
    | n -> next::(ana coacc next (n - 1)) in
  let helper rows row =
    match row.first_pattern.node with
    | Term.Con(_, id, cpats) when id = constr ->
       { row with rest_patterns = cpats@row.rest_patterns }::rows
    | Term.Con _ -> rows
    | Term.Wild ->
       { row with
         rest_patterns =
           ana row.rest_patterns {node = Term.Wild; reg = None} count
       }::rows
  in List.fold ~f:helper ~init:[] rows

(** Construct the default matrix *)
let default_matrix
      (rows : 'a row list)
    : 'a matrix =
  let helper rows row =
    match row.rest_patterns with
    | [] -> rows
    | second_pat::pats ->
       match row.first_pattern.node with
       | Term.Con _ -> rows
       | Term.Wild ->
          ({ row with first_pattern = second_pat; rest_patterns = pats }::rows)
  in List.fold ~f:helper ~init:[] rows

(** Corresponds with swap_columns and swap_column_of_row (The occurrences vector
    is like another row) *)
(* Maybe make function generic instead of repeating code? TODO consider later *)
let swap_occurrences idx (occurrences : int list list) =
  let rec f idx left = function
    | pivot::right when idx = 0 -> Some (left, pivot, right)
    | x::next -> f (idx - 1) (x::left) next
    | [] -> None
  in
  match f idx [] occurrences with
  | Some (left, pivot, right) ->
     Some (pivot, List.rev_append left right)
  | None -> None

(** Compilation scheme CC *)
let rec decision_tree_of_matrix occurrences env =
  let open Result.Monad_infix in
  function
  | [] -> Ok Fail (* Case 1 *)
  | (row::rows') as rows ->
     match find_adt (row.first_pattern::row.rest_patterns) with
     | All_wilds reg_opts -> Ok (Leaf(reg_opts, row.action)) (* Case 2 *)
     | Some_constr (reg, alg, i) ->
        (* Case 3 *)
        let jump_tbl = Hashtbl.create (module Int) in
        let default = default_matrix rows in
        match swap_occurrences i occurrences with
        | None -> Error Sequence.empty
        | Some (first_occ, rest_occs) ->
           let (_, product) = alg.constrs.(i) in
           let rec f idx = function
             | [] -> []
             | _::xs -> (idx::first_occ)::(f (idx + 1) xs)
           in
           let pushed_occs = f 0 product in
           let match_occs = List.append pushed_occs rest_occs in
           match swap_column i rows' with
           | None -> Error Sequence.empty
           | Some rows ->
              Array.foldi ~f:(fun id acc (_, products) ->
                  acc >>= fun () ->
                  match specialize id (List.length products) rows with
                  | [] -> Ok ()
                  | matrix ->
                     match decision_tree_of_matrix match_occs env matrix with
                     | Ok tree ->
                        Hashtbl.add_exn ~key:id ~data:tree jump_tbl;
                        Ok ()
                     | Error e -> Error e
                ) alg.Type.constrs ~init:(Ok ()) >>= fun () ->
              decision_tree_of_matrix rest_occs env default
              >>| fun default_tree ->
              let switch =
                Switch(first_occ, reg, alg, jump_tbl, default_tree)
              in if i = 0 then switch else Swap(i, switch)
