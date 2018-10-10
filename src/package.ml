(** The symbol table mapping:
    - Fully qualified type constructor names to type declarations (abstract
      types or ADTs)
    - Fully qualified data constructor names to ADTs and the int index
    - Fully qualified variable names to types and terms *)

open Base

type ty_state =
  | Compiled of Type.decl
  | Todo of Kind.t

type t =
  { name : string
  ; typedefs : (string, ty_state) Hashtbl.t
  ; constrs : (string, Type.adt * int) Hashtbl.t
  ; vals : (string, Type.t * Lambda.t) Hashtbl.t }

let create name =
  { name
  ; typedefs = Hashtbl.create (module String)
  ; constrs = Hashtbl.create (module String)
  ; vals = Hashtbl.create (module String) }

let find f self name = Hashtbl.find (f self) name

let find_typedef = find (fun package -> package.typedefs)

let find_adt = find (fun package -> package.constrs)

let find_val = find (fun package -> package.vals)

let kind_of_ident self name =
  match find_typedef self name with
  | Some (Compiled (Type.Manifest adt)) -> Some (Type.kind_of_adt adt)
  | Some (Compiled (Type.Abstract kind)) -> Some kind
  | Some (Todo kind) -> Some kind
  | None -> None
