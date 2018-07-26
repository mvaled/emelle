open Base

type t = {
    type_table : (Ident.t, Type.def) Hashtbl.t;
    term_table : (Ident.t, Type.t) Hashtbl.t;
    parent : t option
  }

let extend parent = {
    type_table = Hashtbl.create (module Ident);
    term_table = Hashtbl.create (module Ident);
    parent = Some parent
  }

let rec find_type id env =
  match Hashtbl.find env.type_table id with
  | Some def -> Some def
  | None ->
     match env.parent with
     | Some parent -> find_type id parent
     | None -> None

let rec find_term id env =
  match Hashtbl.find env.term_table id with
  | Some ty -> Some ty
  | None ->
     match env.parent with
     | Some parent -> find_term id parent
     | None -> None

let define_type env id def =
  if Hashtbl.mem env.type_table id then
    false
  else (
    Hashtbl.add_exn env.type_table ~key:id ~data:def;
    true
  )

let define_term env id def =
  if Hashtbl.mem env.term_table id then
    false
  else (
    Hashtbl.add_exn env.term_table ~key:id ~data:def;
    true
  )
