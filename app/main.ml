open Base
open Stdio
open Emelle

let () =
  let open Result.Monad_infix in
  match (
    let chan = Lexing.from_channel stdin in
    let ast = Parser.expr_eof Lexer.expr chan in
    let env = Env.empty (module String) in
    let desugarer =
      Desugar.{ vargen = 0
              ; typedefs = Env.empty (module Ident) }
    in
    let result = Desugar.term_of_expr desugarer env ast in
    result >>= fun term ->
    let typechecker =
      Typecheck.{ types = Hashtbl.create (module Ident)
                ; env = Hashtbl.create (module Int)
                ; level = 0
                ; tvargen = ref 0
                ; kvargen = ref 0 }
    in Typecheck.infer typechecker term
  ) with
  | Ok ty ->
     let pprinter = Prettyprint.{ buffer = Buffer.create 12 } in
     Prettyprint.print_type pprinter (-1) ty;
     print_endline (Buffer.contents pprinter.buffer)
  | Error _ -> ()
