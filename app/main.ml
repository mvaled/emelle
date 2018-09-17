open Base
open Stdio
open Emelle

let () =
  let open Result.Monad_infix in
  match
    let chan = Lexing.from_channel stdin in
    let ast = Parser.expr_eof Lexer.expr chan in
    let env = Env.empty (module String) in
    let structure = Module.create None in
    let desugarer = Desugar.create structure in
    let result = Desugar.term_of_expr desugarer env ast in
    result >>= fun term ->
    let typechecker = Typecheck.create () in
    Typecheck.infer typechecker term
  with
  | Ok ty ->
     let pprinter = Prettyprint.create () in
     Prettyprint.print_type pprinter (-1) ty;
     print_endline (Prettyprint.to_string pprinter)
  | Error _ -> ()
