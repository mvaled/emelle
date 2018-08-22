# Hacking on the Emelle compiler

The stages of the Emelle compiler are as follows:

    Lexing.lexbuf
    - Defined in the standard library for use with OCamllex
       | lexer.mll
       | - Unlike most of the codebase, uses exceptions instead of result types
       |   because the Menhir API needs the functions generated here to
       |   return tokens
       V
    Parser.token
       | parser.mly
       | - Uses Menhir
       | - Unlike most of the codebase, uses exceptions instead of result types
       |   because that's what Menhir generates
       V
    ast.ml
       | desugar.ml:
       | - Resolves names, converting them to unique integer "registers"
       | - Resolves data constructors by converting them to integers in
       |   definition order
       | - Compiles Ast.pattern to Desugar.pattern
       | - Compiles Ast.expr to Term.t
       | - Compiles Desugar.pattern to Term.t for the code for binding values to
       |   registers assuming that the pattern match is successful
       | - Compiles Desugar.pattern to Pattern.t
       | - Drives pattern.ml
       |       |
       |       V
       |   pattern.ml:
       |   - Implements the pattern match compilation algorithm as described in
       |     "Compiling Pattern Matching to Good Decision Trees" by Luc Maranget
       |     (2008)
       |   - Pattern.t -> Pattern.matrix -> Pattern.decision_tree
       |       |
       |<-------
       V
    term.ml
    - A core language based on the lambda calculus, a la GHC's CoreSyn
    - Untyped
       |   ^
       |   | typecheck.ml
       |----

You will often see the `>>=` and `>>|` operators in the code. `>>=` is monadic
bind, and `>>|` is `map` with the arguments reversed (the functor comes first
and the function comes second). These operators are used with the result type
to compose computations that may fail.
