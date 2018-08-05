type error =
  | Redefined_id of Ident.t
  | Unification_fail of Type.t * Type.t
  | Unimplemented of string
  | Unreachable
  | Unresolved_id of Ident.t
