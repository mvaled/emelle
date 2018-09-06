open Base

type error =
  | Kind_unification_fail of Kind.t * Kind.t
  | Lexer_error of string
  | Mismatched_arity
  | Parser_error
  | Redefined_id of Ident.t
  | Type_unification_fail of Type.t * Type.t
  | Unimplemented of string
  | Unknown_constr of Ident.t * string
  | Unreachable
  | Unresolved_id of Ident.t
  | Unresolved_type of Ident.t
