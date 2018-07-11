type t =
  | Con of Ident.t * Ident.t * t list (** Constructor pattern *)
  | Wild (** Wildcard pattern *)

type decision_tree =
  | Fail
  | Leaf of int
  | Switch of decision_tree Ident.Tbl.t
  | Swap of int * decision_tree

type row = {
    first_pattern : t;
    rest_patterns : t list;
    action : int;
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
  let open Util in
  List.fold_left (fun acc next ->
      Option.bind acc (fun rows ->
          Option.map (fun row -> row::rows) (swap_column_of_row idx next)
        )
    ) (Some [])

let find_type ty =
    let rec f i = function
      | [] -> None
      | Con(typename, _, _)::_ -> Some ((Type.Nominal typename), i)
      | Wild::xs -> f (i + 1) xs
    in f 0 ty

(** Specialize operation as described in Compiling Pattern Matching to Good
    Decision Trees
 *)
let specialize
      (constr : Ident.t)
      (count  : int)
      (rows   : row list)
    : matrix =
  (* Anamorphism over lists, catamorphism over the natural numbers *)
  let rec ana next = function
    | 0 -> []
    | n -> next::(ana next (n - 1)) in
  let helper rows row =
    match row.first_pattern with
    | Con(_, id, cpats) when Ident.equal id constr ->
       { row with rest_patterns = cpats@row.rest_patterns }::rows
    | Con _ -> rows
    | Wild ->
       { row with rest_patterns = (ana Wild count)@row.rest_patterns }::rows
  in List.fold_left helper [] rows

(** Construct the default matrix *)
let default_matrix
      (constr : Ident.t)
      (rows : row list)
    : matrix =
  let helper rows row =
    match row.rest_patterns with
    | [] -> rows
    | second_pat::pats ->
       match row.first_pattern with
       | Con(_, id, _) when Ident.equal id constr -> rows
       | Con _ | Wild ->
          ({ row with first_pattern = second_pat; rest_patterns = pats }::rows)
  in List.fold_left helper [] rows

(** Compilation scheme CC *)
let rec decision_tree_of_matrix env = function
  | [] -> Some Fail (* Case 1 *)
  | (row::_) as rows ->
     match find_type (row.first_pattern::row.rest_patterns) with
     | None -> Some (Leaf row.action) (* Case 2 *)
     | Some (ty, i) ->
        (* Case 3 *)
        let rec handle_type = function
          | Type.Nominal typename ->
             begin match Env.find_type typename env with
             | None -> None
             | Some (Alias ty) -> handle_type ty
             | Some (Algebraic alg) ->
                let jump_tbl = Ident.Tbl.create 0 in
                let result =
                  Ident.Tbl.fold (fun id (prods, _) acc ->
                      if acc then
                        let matrix =
                          match specialize id (Array.length prods) rows with
                          | [] -> default_matrix id rows
                          | matrix -> matrix
                        in
                        match decision_tree_of_matrix env matrix with
                        | Some tree -> Ident.Tbl.add jump_tbl id tree; true
                        | None -> false
                      else
                        false) alg true
                in
                if result then
                  if i = 0 then
                    Some (Switch jump_tbl)
                  else
                    Some (Swap (i, Switch jump_tbl))
                else
                  None
             end
          | _ -> None
        in handle_type ty
