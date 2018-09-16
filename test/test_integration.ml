open Base
open Emelle

type phase =
  | Syntax
  | Desugar
  | Typecheck
  | End (* Used when the test should pass all the stages *)
[@@deriving compare]

exception Fail of string * phase

let optionally f x =
  try Ok (f x) with
  | Lexer.Error str -> Error (Sequence.return (Message.Lexer_error str))
  | Parser.Error -> Error (Sequence.return Message.Parser_error)

let tests =
  [ "fun", Syntax
  ; "case", Syntax
  ; "with", Syntax
  ; "fun (some x) -> x", Syntax
  ; "fun -> x", Syntax
  ; "f", Desugar
  ; "f x", Desugar
  ; "fun x -> y", Desugar
  ; "case x with | y -> y", Desugar
  ; "let f = fun x -> f x in f", Desugar
  ; "let f = fun x -> x and g = f in g", Desugar
  ; "let g = f and f = fun x -> x in g", Desugar
  ; "case fun x -> x with | x -> x | y -> x", Desugar
  ; "fun x -> x x", Typecheck
  ; "fun f -> let g = fun x -> f (x x) in g g", Typecheck
  ; "let rec g = f and f = fun x -> x in g", End
  ; "let rec f = fun x -> x and g = f in g", End
  ; "let rec f = fun x -> f x in f", End
  ; "case fun x -> x with | x -> x | y -> y", End
  ; "fun x -> x", End
  ; "fun x -> fun y -> x", End
  ; "fun x y -> x", End
  ; "fun f x -> f x", End
  ; "fun f x y -> f y x", End
  ]

let test_phase f curr_phase input format phase =
  let result = f format in
  match result, (compare_phase phase curr_phase) = 0 with
  | Error _, true -> None
  | Error _, false -> raise (Fail(input, phase))
  | Ok _, true -> raise (Fail(input, phase))
  | Ok next, false -> Some next

let test (input, phase) =
  let open Option.Monad_infix in
  let next =
    test_phase (optionally (fun str ->
              Parser.file Lexer.expr (Lexing.from_string str)
      )) Syntax input input phase
  in
  next >>= fun next ->
  let env = Env.empty (module String) in
  let structure = Module.Struct.create None in
  let desugarer = Desugar.create structure in
  let next =
    test_phase (Desugar.term_of_expr desugarer env) Desugar input next phase
  in
  next >>= fun next ->
  let typechecker = Typecheck.create () in
  let next = test_phase (Typecheck.infer typechecker) Typecheck input next phase
  in next

let _ = List.map ~f:test tests
