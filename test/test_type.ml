open Base
open Emelle

let vargen = Type.create_vargen ()

let tvar1 = Type.fresh_var vargen 0 Kind.Mono
let tvar2 = Type.fresh_var vargen 0 Kind.Mono

let () =
  assert ((Type.Var.compare tvar1 tvar2) <> 0);
  assert ((Type.Var.compare tvar1 tvar1) = 0);
  assert ((Type.Var.compare tvar2 tvar2) = 0)
