open Base

type error =
  | Abstract_type of Path.t
  | Kind_unification_fail of Kind.t * Kind.t
  | Lexer_error of string
  | Mismatched_arity
  | Not_enough_fields
  | Parser_error
  | Redefined_constr of string
  | Redefined_name of string
  | Redefined_typevar of string
  | Reexported_name of string
  | Too_many_fields
  | Type_unification_fail of Type.t * Type.t
  | Unimplemented of string
  | Unknown_constr of Path.t * string
  | Unreachable of string
  | Unresolved_id of Path.t
  | Unresolved_path of Ast.qual_id
  | Unresolved_type of Path.t
  | Unresolved_typevar of string
