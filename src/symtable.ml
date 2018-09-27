(** The symbol table of Ident.t mapping:
    - Fully qualified type constructor names to type declarations (abstract
      types or ADTs)
    - Fully qualified data constructor names to ADTs and the int index
    - Fully qualified variable names to types and terms
*)

open Base

type ty_state =
  | Compiled of Type.decl
  | Todo of Kind.t

type t =
  { typedefs : (Ident.t, ty_state) Hashtbl.t
  ; constrs : (Ident.t, Type.adt * int) Hashtbl.t
  ; vals : (Ident.t, Type.t * Lambda.t) Hashtbl.t }

let create () =
  { typedefs = Hashtbl.create (module Ident)
  ; constrs = Hashtbl.create (module Ident)
  ; vals = Hashtbl.create (module Ident) }

let find_typedef self name = Hashtbl.find self.typedefs name
let find_adt self constr = Hashtbl.find self.constrs constr
let find_val self name = Hashtbl.find self.vals name

let kind_of_ident self name =
  match find_typedef self name with
  | Some (Compiled (Type.Manifest adt)) -> Some (Type.kind_of_adt adt)
  | Some (Compiled (Type.Abstract kind)) -> Some kind
  | Some (Todo kind) -> Some kind
  | None -> None
