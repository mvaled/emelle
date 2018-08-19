open Base
open Emelle

let valid =
  [ "f x"
  ; "let x = y in x"
  ; "fun x y -> y"
  ; "fun (Option::Some x) -> x"
  ; "  y  x  cs w  uii8'9"
  ; "case x with | x -> x"
  ; "case x with x -> x"
  ; " case ( x  ) with x -> x | y -> z"
  ; "fun x -> x | y -> y"
  ; "  fun   |x -> x | y  -> y" ]

let invalid =
  [ "fun"
  ; "case"
  ; "fun (some x) -> x"
  ; "fun -> x" ]

let () =
  List.iter ~f:(
      fun program ->
      let _ = Parser.file Lexer.expr (Lexing.from_string program) in
      ()
    ) valid

let () =
  List.iter ~f:(
      fun program ->
      try
        let _ = Parser.file Lexer.expr (Lexing.from_string program) in
        assert false
      with
      | Parser.Error -> ()
      | exn -> raise exn
    ) invalid
