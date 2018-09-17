open Base
open Stdio
open Emelle

let () =
  let open Result.Monad_infix in
  match
    let lexbuf = Lexing.from_channel stdin in
    let ast = Parser.expr_eof Lexer.expr lexbuf in
    let symtable = Symtable.create () in
    let env = Env.empty (module String) in
    let structure = Module.create None in
    let desugarer = Desugar.create structure symtable in
    let result = Desugar.term_of_expr desugarer env ast in
    result >>= fun term ->
    let typechecker = Typecheck.create symtable in
    Typecheck.infer typechecker term
  with
  | Ok ty ->
     let pprinter = Prettyprint.create () in
     Prettyprint.print_type pprinter (-1) ty;
     print_endline (Prettyprint.to_string pprinter)
  | Error _ -> ()
