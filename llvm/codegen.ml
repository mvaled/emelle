open Base

type t = {
    id : int;
    llctx : Llvm.llcontext;
  }

let with_context ~cont =
  let ctx = Llvm.create_context () in
  try cont ctx with
  | exn ->
     Llvm.dispose_context ctx;
     raise exn

let create llctx =
  { id = 0
  ; llctx }
