open Base
open Emelle

let a = Type.UVar.{ id = Gen 0; level = 0; name = Some "" }
let b = Type.UVar.{ id = Gen 0; level = 1; name = Some "" }
let c = Type.UVar.{ id = Gen 1; level = 0; name = None }
let d = Type.UVar.{ id = Gen 1; level = 0; name = Some "" }
let e = Type.UVar.{ id = Annotated 1; level = 0; name = None }
let f = Type.UVar.{ id = Gen 1; level = 0; name = None }

let should_equal x y =
  assert((Type.UVar.compare x y) = 0);
  assert((Type.UVar.hash x) = (Type.UVar.hash y))

let shouldn't_equal x y =
  assert((Type.UVar.compare x y) <> 0);
  assert((Type.UVar.hash x) <> (Type.UVar.hash y))

let () =
  should_equal a b;
  should_equal c d;
  shouldn't_equal e f;
  should_equal c f
