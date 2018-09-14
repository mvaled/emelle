open Base

(** A map with scoped name shadowing *)
type ('k, +'v, 'cmp) t =
  { curr : ('k, 'v * int, 'cmp) Map.t
  ; parents : ('k, 'v * int, 'cmp) Map.t
  ; parent : ('k, 'v, 'cmp) t option
  ; level : int }

let empty cmp =
  { curr = Map.empty cmp
  ; parents = Map.empty cmp
  ; parent = None
  ; level = 0 }

let in_scope_with f frame env =
  let combine ~key:_ x _ = x in
  let env' =
    { curr = frame
    ; parents = Map.merge_skewed env.curr env.parents ~combine:combine
    ; parent = Some env
    ; level = env.level + 1 }
  in f env'

let in_scope f env = in_scope_with f (Map.empty (Map.comparator_s env.curr)) env

let find env key =
  match Map.find env.curr key with
  | Some x -> Some x
  | None -> Map.find env.parents key

let rec find_super env idx key =
  if idx <= 0 then
    find env key
  else
    match env.parent with
    | Some parent ->
       find_super parent (idx - 1) key
    | None -> None

let add env key value =
  match Map.add env.curr ~key:key ~data:(value, env.level) with
  | `Ok x -> Some { env with curr = x }
  | `Duplicate -> None
