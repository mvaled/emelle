open Base

module Basic = struct
  (** A generic type representing a symbol table with scoped name shadowing

      This type has field tables of type 'a as opposed to field table of type
      [('a, 'b) Hashtbl.t] for some other type variable 'b so that the type can
      hold multiple tables. This is also why [find] is parameterized with a
      function from env to Hashtbl.t and [define] is parameterized with a
      [Hashtbl.t]
   *)
  type 'a t = {
      tables : 'a;
      parent : 'a t option
    }

  let create a = {
      tables = a;
      parent = None
    }

  let extend a parent = {
      tables = a;
      parent = Some parent
    }

  let tables env = env.tables

  let rec find f env id =
    match Hashtbl.find (f env) id with
    | Some def -> Some def
    | None ->
       match env.parent with
       | Some parent -> find f parent id
       | None -> None

  let define tbl id def =
    match Hashtbl.add tbl ~key:id ~data:def with
    | `Ok -> true
    | `Duplicate -> false
end

(** A hash table with scoped name shadowing *)
type ('a, 'b) t = ('a, 'b) Hashtbl.t Basic.t

let create = Basic.create

let extend = Basic.extend

let table = Basic.tables

(* The [env] parameter can't be point-free'd out because of the value
   restriction
 *)
let find env = Basic.find table env

let define env = Basic.define env.Basic.tables
