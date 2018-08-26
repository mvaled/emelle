open Base

type t =
  | Con of Ident.t * int * t list (** Constructor pattern *)
  | Wild (** Wildcard pattern *)

type decision_tree =
  | Fail
  | Leaf of int
  | Switch of (int, decision_tree) Hashtbl.t
  | Swap of int * decision_tree

type row =
  { first_pattern : t
  ; rest_patterns : t list
  ; action : int }

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
  match f idx [] (row.first_pattern::row.rest_patterns) with
  | Some (left, pivot, right) ->
     Some {
         row with
         first_pattern = pivot;
         rest_patterns = List.rev_append left right
       }
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

let find_typename pats =
    let rec f i = function
      | [] -> None
      | Con(typename, _, _)::_ -> Some (typename, i)
      | Wild::xs -> f (i + 1) xs
    in f 0 pats

(** Specialize operation as described in Compiling Pattern Matching to Good
    Decision Trees *)
let specialize
      (constr : int)
      (count  : int)
      (rows   : row list)
    : matrix =
  (* Anamorphism over lists, catamorphism over the natural numbers *)
  let rec ana next = function
    | 0 -> []
    | n -> next::(ana next (n - 1)) in
  let helper rows row =
    match row.first_pattern with
    | Con(_, id, cpats) when id = constr ->
       { row with rest_patterns = cpats@row.rest_patterns }::rows
    | Con _ -> rows
    | Wild ->
       { row with rest_patterns = (ana Wild count)@row.rest_patterns }::rows
  in List.fold ~f:helper ~init:[] rows

(** Construct the default matrix *)
let default_matrix
      (rows : row list)
    : matrix =
  let helper rows row =
    match row.rest_patterns with
    | [] -> rows
    | second_pat::pats ->
       match row.first_pattern with
       | Con _ -> rows
       | Wild ->
          ({ row with first_pattern = second_pat; rest_patterns = pats }::rows)
  in List.fold ~f:helper ~init:[] rows

(** Compilation scheme CC *)
let rec decision_tree_of_matrix env = function
  | [] -> Some Fail (* Case 1 *)
  | (row::_) as rows ->
     match find_typename (row.first_pattern::row.rest_patterns) with
     | None -> Some (Leaf row.action) (* Case 2 *)
     | Some (typename, i) ->
        (* Case 3 *)
        begin match Env.find env typename with
        | None -> None
        | Some alg ->
           let jump_tbl = Hashtbl.create (module Int) in
           let default = default_matrix rows in
           let result =
             Array.foldi ~f:(fun id acc (_, products) ->
                 if acc then
                   let matrix =
                     match specialize id (Array.length products) rows with
                     | [] -> default
                     | matrix -> matrix
                   in
                   match decision_tree_of_matrix env matrix with
                   | Some tree ->
                      Hashtbl.add_exn ~key:id ~data:tree jump_tbl;
                      true
                   | None -> false
                 else
                   false) alg.Type.constrs ~init:true
           in
           if result then
             if i = 0 then
               Some (Switch jump_tbl)
             else
               Some (Swap (i, Switch jump_tbl))
           else
             None
        end
