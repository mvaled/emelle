open Base

type t =
  { constrs : (string, string * int) Hashtbl.t
  ; types : (string, unit) Hashtbl.t
  ; values : (string, unit) Hashtbl.t
  ; submodules : (string, t) Hashtbl.t
  ; parent : t option
  ; prefix : Ident.t option }

let create prefix =
  { constrs = Hashtbl.create (module String)
  ; types = Hashtbl.create (module String)
  ; values = Hashtbl.create (module String)
  ; submodules = Hashtbl.create (module String)
  ; parent = None
  ; prefix }

(** [find f self name]

    Given some function [f] from [self] to a hash table, find the value of key
    [name] in the hash table, and return it paired with the fully qualified
    identifier path *)
let rec find f self name =
  match Hashtbl.find (f self) name with
  | Some data ->
     begin match self.prefix with
     | Some prefix -> Some (Ident.Path(prefix, name), data)
     | None -> Some (Ident.Local name, data)
     end
  | None ->
     match self.parent with
     | Some parent -> find f parent name
     | None -> None

let find_constr self name =
  match Hashtbl.find self.constrs name with
  | None -> None
  | Some (typename, idx) ->
     match self.prefix with
     | None -> Some (Ident.Local typename, idx)
     | Some prefix -> Some (Ident.Path(prefix, typename), idx)

let find_type self name =
  match find (fun self -> self.types) self name with
  | Some (ident, ()) -> Some ident
  | None -> None

let find_val self name =
  match find (fun self -> self.values) self name with
  | Some (ident, ()) -> Some ident
  | None -> None

let find_mod = find (fun self -> self.submodules)

let rec resolve_abs_path f self (prefix, name) =
  match prefix with
  | [] -> f self name
  | x::xs ->
     match find_mod self x with
     | None -> None
     | Some (_, submod) -> resolve_abs_path f submod (xs, name)

(** [resolve_path f strct root subpath] searches for a module of name [root]
    [root] in the scope of [strct], then calls
    [resolve_abs_path submod subpath] *)
let resolve_path f self (prefix, name) =
  match prefix with
  | [] -> f self name
  | x::xs ->
     match find_mod self x with
     | None -> None
     | Some (_, submod) -> resolve_abs_path f submod (xs, name)
