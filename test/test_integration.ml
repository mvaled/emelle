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
  ; "0 0", Typecheck
  ; "let rec g = f and f = fun x -> x in g", End
  ; "let rec f = fun x -> x and g = f in g", End
  ; "let rec f = fun x -> f x in f", End
  ; "case fun x -> x with | x -> x | y -> y", End
  ; "fun x -> x", End
  ; "fun x -> fun y -> x", End
  ; "fun x y -> x", End
  ; "fun f x -> f x", End
  ; "fun f x y -> f y x", End
  ; "let id = fun x -> x in id id", End
  ; "let rec id = fun x -> x and id2 = id in id id2 (id2 id)", End
  ; "case fun x -> x with id -> id id", End
  ; "let id = fun x -> x in case id with x -> x x", End
  ; "let two = fun _ -> 2 in two 5", End
  ; "let two = fun _ -> 2.0 in two 9", End
  ; "let two = fun _ -> +2 in two 6", End
  ; "let two = fun _ -> +2.0 in two 4", End
  ; "let minus_five = fun _ -> -5 in minus_five 0", End
  ; "(fun x -> x) 0", End
  ; "\"\\\\\"", End
  ; "\"\\\"\"", End
  ; "\"\\\'\"", End
  ; "\"foobar\\\"baz\"", End
  ; "\"Hello world!\\n\"", End
  ; "\"\"", End
  ; "let f = fun x y -> x; y in f", End
  ; "let assign = fun l r -> l := r in assign", End
  ; "ref 0", End
  ; "(ref 1) := 0", End ]

let test_phase f curr_phase input format phase =
  let result = f format in
  match result, (compare_phase phase curr_phase) = 0 with
  | Error _, true -> None
  | Error _, false -> raise (Fail(input, curr_phase))
  | Ok _, true -> raise (Fail(input, curr_phase))
  | Ok next, false -> Some next

let test (input, phase) =
  let open Option.Monad_infix in
  let next =
    test_phase (optionally (fun str ->
              Parser.expr_eof Lexer.expr (Lexing.from_string str)
      )) Syntax input input phase
  in
  next >>= fun next ->
  let package = Package.create "" in
  let env = Env.empty (module String) in
  let packages = Hashtbl.create (module String) in
  let desugarer = Desugar.create package packages in
  let next =
    test_phase (Desugar.term_of_expr desugarer env) Desugar input next phase
  in
  next >>= fun next ->
  let typechecker = Typecheck.create package packages in
  let next =
    test_phase (Typecheck.infer_term typechecker (-1))
      Typecheck input next phase
  in next

let _ = List.map ~f:test tests

exception Module_fail of string

let tests =
  [ "(id) let id = fun x -> x"
  ; "() type Unit = Unit"
  ; "() type Option a = None | Some a"
  ; "(id2, id) let id = fun x -> x let id2 = id"
  ; "() type Foo = Foo type Bar = Bar Foo"
  ; "() type Bar = Bar Foo and Foo = Foo"
  ; "() type List a = Nil | Cons a (List a)"
  ; "(id, id2, id3) let rec id = fun x -> x and id2 = id let id3 = id2 id id2"
  ; "(id, id2) let id = fun x -> x let id2 = id id"
  ; "() type Unit = Unit let unit = Unit"
  ; "() type Option a = None | Some a let return = Some"
  ; "() type Option a = None | Some a let return = fun a -> Some a"
  ; "() type Either e a = Left e | Right a let return = Right"
  ; {|(map)
      type Option a = None | Some a
      let one =
        case Some 1 with
          Some x -> x
        | None -> 0

      let map = fun f opt ->
        case opt with
          Some a -> Some (f a)
        | None -> None

      let bind = fun opt f ->
        case opt with
        | Some a -> f a
        | None -> None

      let flatten = fun
        | (Some (Some a)) -> Some a
        | _ -> None
    |}
  ; {|(x)
      type Either e a = Left e | Right a
      let x =
        case Left 1 with
        | Left _ -> 0
        | Right x -> x
     |}
  ; "() type Product a b = Pair a * b let mkPair = fun x y -> Pair x y"
  ; {|(id, const, undefined)

      let id = foreign "id" forall t. t -> t

      let const = foreign "const" forall t u . t -> u -> t

      let undefined = foreign "undefined" forall t. t

      let id2 = id id id

      let id3 = const undefined id
     |}
  ; {|()
      type Option a = None | Some a

      let _ =
        let r = ref None in
        r := Some 0;
        r := Some 1

      let make_ref = fun x -> ref x

      let str_ref = make_ref ""

      let int_ref = make_ref 0
     |} ]

let _ =
  List.iter ~f:(fun test ->
      match
        Parser.file Lexer.expr (Lexing.from_string test)
        |> Pipeline.compile (Hashtbl.create (module String)) "main"
      with
      | Ok _ -> ()
      | Error e ->
         let pp = Emelle.Prettyprint.create () in
         Sequence.iter ~f:(Emelle.Prettyprint.print_error pp) e;
         Stdio.print_endline (Emelle.Prettyprint.to_string pp);
         raise (Module_fail test)
    ) tests
