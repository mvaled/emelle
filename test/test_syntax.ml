open Base
open Emelle

let test_valid parse =
  List.iter ~f:(
      fun program ->
      let _ = parse Lexer.expr (Lexing.from_string program) in
      ()
    )

let test_invalid parse =
  List.iter ~f:(
      fun program ->
      try
        let _ = parse Lexer.expr (Lexing.from_string program) in
        assert false
      with
      | Parser.Error -> ()
      | Lexer.Error _ -> ()
      | exn -> raise exn
    )

let valid_exprs =
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

let invalid_exprs =
  [ "fun"
  ; "case"
  ; "fun (some x) -> x"
  ; "fun -> x" ]

let valid_monotypes =
  [ "a -> b"
  ; "(->) a"
  ; "(->)"
  ; "(->) a b"
  ; "a b c"
  ; "(a -> b) -> f a -> f b"
  ; "m a -> (a -> m b) -> m b"
  ; "Option a"
  ; "Either a b"
  ; "Either Foo Bar"
  ; "IO Unit"
  ; "Unit"
  ; "a' b' c'"
  ]

let invalid_monotypes =
  [ "->"
  ; "a ->"
  ; "123 a"
  ; "case"
  ; "with"
  ; "forall"
  ; "forall a . a"
  ; "fun x -> x"
  ]

let () =
  test_valid Parser.expr_eof valid_exprs;
  test_invalid Parser.expr_eof invalid_exprs;
  test_valid Parser.monotype_eof valid_monotypes;
  test_invalid Parser.monotype_eof invalid_monotypes
