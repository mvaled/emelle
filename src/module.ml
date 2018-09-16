open Base

module Sig = struct
  type t =
    { types : (string, Type.decl) Hashtbl.t
    ; values : (string, Type.t) Hashtbl.t
    ; submodules : (string, t) Hashtbl.t }

  let find f self name = Hashtbl.find (f self) name

  let find_type = find (fun self -> self.types)
  let find_val = find (fun self -> self.values)
  let find_mod = find (fun self -> self.submodules)

  let rec resolve_path f self path name =
    match path with
    | [] -> f self name
    | root::subpath ->
       match find_mod self root with
       | Some submod -> resolve_path f submod subpath name
       | None -> None
end

module Struct = struct
  type t =
    { types : (string, Type.adt) Hashtbl.t
    ; values : (string, Type.t) Hashtbl.t
    ; submodules : (string, Sig.t) Hashtbl.t
    ; parent : t option
    ; prefix : Ident.t option }

  let create prefix =
    { types = Hashtbl.create (module String)
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

  let find_type = find (fun self -> self.types)
  let find_val = find (fun self -> self.values)
  let find_mod = find (fun self -> self.submodules)

  let to_sig self =
    { Sig.types = Hashtbl.map self.types ~f:(fun x -> Type.Adt x)
    ; Sig.values = self.values
    ; Sig.submodules = self.submodules }
end
