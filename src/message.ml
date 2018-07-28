type error =
  | Unification_fail of Type.t * Type.t
  | Unresolved_id of Ident.t * Ident.t
