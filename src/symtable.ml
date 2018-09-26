(** The symbol table of Ident.t mapping:
    - Fully qualified type constructor names to type declarations (abstract
      types or ADTs)
    - Fully qualified data constructor names to ADTs and the int index
    - Fully qualified variable names to types and terms
*)

open Base

type t =
  { typedefs : (Ident.t, Type.decl) Hashtbl.t
  ; constrs : (Ident.t, Type.adt * int) Hashtbl.t
  ; vals : (Ident.t, Type.t * Lambda.t) Hashtbl.t }

let create () =
  { typedefs = Hashtbl.create (module Ident)
  ; constrs = Hashtbl.create (module Ident)
  ; vals = Hashtbl.create (module Ident) }

let find_typedef self name = Hashtbl.find self.typedefs name
let find_adt self constr = Hashtbl.find self.constrs constr
let find_val self name = Hashtbl.find self.vals name
