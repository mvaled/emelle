open Base
open Emelle

let programs = [
    "f x";
    "let x = y in x"
  ]

let _ =
  List.map ~f:(
      fun prog -> Parser.file Lexer.expr (Lexing.from_string prog)
    ) programs
