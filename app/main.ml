open Base
open Stdio
open Emelle

let () =
  let open Result.Monad_infix in
  match
    let lexbuf = Lexing.from_channel stdin in
    let ast = Parser.expr_eof Lexer.expr lexbuf in
    let package = Package.create "" in
    let env = Env.empty (module String) in
    let packages = Hashtbl.create (module String) in
    let desugarer = Desugar.create package packages in
    let result = Desugar.term_of_expr desugarer env ast in
    result >>= fun term ->
    let typechecker = Typecheck.create package packages in
    Typecheck.infer typechecker term
    >>| fun lambda ->
    Typecheck.gen typechecker lambda.Lambda.ty
  with
  | Ok ty->
     let pprinter = Prettyprint.create () in
     Prettyprint.print_type pprinter (-1) ty;
     print_endline (Prettyprint.to_string pprinter)
  | Error _ -> ()
