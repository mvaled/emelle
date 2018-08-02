open Base

type t = {
    type_table : (Ident.t, Type.def) Hashtbl.t;
    term_table : (int, Type.t) Hashtbl.t;
    register_table : (string, int) Hashtbl.t;
    parent : t option
  }

let type_table env = env.type_table

let term_table env = env.term_table

let reg_table env = env.register_table

let create () = {
    type_table = Hashtbl.create (module Ident);
    term_table = Hashtbl.create (module Int);
    register_table = Hashtbl.create (module String);
    parent = None
  }

let extend parent = {
    type_table = Hashtbl.create (module Ident);
    term_table = Hashtbl.create (module Int);
    register_table = Hashtbl.create (module String);
    parent = Some parent
  }

let rec find f env id =
  match Hashtbl.find (f env) id with
  | Some def -> Some def
  | None ->
     match env.parent with
     | Some parent -> find f parent id
     | None -> None

let find_type = find type_table

let find_term = find term_table

let find_reg = find reg_table

let define tbl id def =
  match Hashtbl.add tbl ~key:id ~data:def with
  | `Ok -> true
  | `Duplicate -> false

let define_type env = define env.type_table

let define_term env = define env.term_table

let define_reg env = define env.register_table
