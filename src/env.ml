type t = {
    type_table : Type.def Ident.Tbl.t;
    term_table : Type.t Ident.Tbl.t;
    parent : t option
  }

let rec find_type id env =
  match Ident.Tbl.find_opt env.type_table id with
  | Some def -> Some def
  | None ->
     match env.parent with
     | Some parent -> find_type id parent
     | None -> None

let rec find_term id env =
  match Ident.Tbl.find_opt env.term_table id with
  | Some ty -> Some ty
  | None ->
     match env.parent with
     | Some parent -> find_term id parent
     | None -> None

let define_type env id def =
  if Ident.Tbl.mem env.type_table id then
    false
  else (
    Ident.Tbl.add env.type_table id def;
    true
  )

let define_term env id def =
  if Ident.Tbl.mem env.term_table id then
    false
  else (
    Ident.Tbl.add env.term_table id def;
    true
  )
