open Base

type error =
  | Abstract_type of Ident.t
  | Kind_unification_fail of Kind.t * Kind.t
  | Lexer_error of string
  | Mismatched_arity
  | Parser_error
  | Redefined_constr of string
  | Redefined_name of string
  | Redefined_typevar of string
  | Type_unification_fail of Type.t * Type.t
  | Unimplemented of string
  | Unknown_constr of Ident.t * string
  | Unreachable
  | Unresolved_id of Ident.t
  | Unresolved_path of Ast.qual_id
  | Unresolved_type of Ident.t
  | Unresolved_typevar of string
