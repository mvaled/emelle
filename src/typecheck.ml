open Base

type t =
  { types : (Ident.t, Type.adt) Hashtbl.t
  ; symtable : Symtable.t
  ; env : (int, Type.t) Hashtbl.t
  ; mutable level : int
  ; tvargen : Type.vargen
  ; kvargen : Kind.vargen
  ; structure : Module.t }

(** [create symtable] creates a fresh typechecker state. *)
let create symtable structure =
  { types = Hashtbl.create (module Ident)
  ; symtable
  ; env = Hashtbl.create (module Int)
  ; level = 0
  ; tvargen = Type.create_vargen ()
  ; kvargen = Kind.create_vargen ()
  ; structure }

let fresh_tvar (checker : t) =
  Type.{ level_opt = Some checker.level
       ; node =
           Type.Var (Type.fresh_var checker.tvargen checker.level Kind.Mono) }

(** [unify_kinds kind1 kind2] unifies the two kinds. *)
let rec unify_kinds l r =
  let open Result.Monad_infix in
  match l, r with
  | Kind.Mono, Kind.Mono -> Ok ()
  | Kind.Poly(a, b), Kind.Poly(c, d) ->
     unify_kinds a c >>= fun () ->
     unify_kinds b d
  | Kind.Var { id = l; _ }, Kind.Var { id = r; _ } when l = r -> Ok ()
  | Kind.Var { kind = Some k1; _ }, k2 | k2, Kind.Var { kind = Some k1; _ } ->
     unify_kinds k1 k2
  | Kind.Var kvar, kind | kind, Kind.Var kvar ->
     if Kind.occurs kvar kind then
       Error (Sequence.return (Message.Kind_unification_fail(l, r)))
     else (
       kvar.kind <- Some kind;
       Ok ()
     )
  | Kind.Mono, Kind.Poly _ | Kind.Poly _, Kind.Mono ->
     Error (Sequence.return (Message.Kind_unification_fail(l, r)))

(** [kind_of_type typechecker ty] infers the kind of [ty], returning a result
    with any errors. *)
let rec kind_of_type checker ty =
  let open Result.Monad_infix in
  match ty.Type.node with
  | Type.App(tcon, targ) ->
     kind_of_type checker targ >>= fun argkind ->
     kind_of_type checker tcon >>= fun conkind ->
     let kvar = Kind.Var (Kind.fresh_var checker.kvargen) in
     unify_kinds conkind (Kind.Poly(argkind, kvar)) >>| fun () ->
     kvar
  | Type.Nominal id ->
     begin match Hashtbl.find checker.types id with
     | Some adt -> Ok (Type.kind_of_adt adt)
     | None -> Error (Sequence.return (Message.Unresolved_type id))
     end
  | Type.Prim Type.Arrow ->
     Ok (Kind.Poly(Kind.Mono, Kind.Poly(Kind.Mono, Kind.Mono)))
  | Type.Prim Type.Float -> Ok Kind.Mono
  | Type.Prim Type.Int -> Ok Kind.Mono
  | Type.Var { ty = Some ty; _ } -> kind_of_type checker ty
  | Type.Var { ty = None; kind; _ } -> Ok kind

(** [unify_types typechecker type0 type1] unifies [type1] and [type2], returning
    a result with any unification errors. *)
let rec unify_types checker lhs rhs =
  let open Result.Monad_infix in
  if phys_equal lhs rhs then
    Ok ()
  else
    match lhs, rhs with
    | Type.{ node = Type.App(lcon, larg); _ },
      Type.{ node = Type.App(rcon, rarg); _ } ->
       begin
         match unify_types checker lcon rcon, unify_types checker larg rarg with
         | Ok (), Ok () -> Ok ()
         | Error e, Ok () | Ok (), Error e -> Error e
         | Error e1, Error e2 -> Error (Sequence.append e1 e2)
       end
    | { node = Type.Nominal lstr; _ },
      { node = Type.Nominal rstr; _ }
         when (Ident.compare lstr rstr) = 0 ->
       Ok ()
    | { node = Type.Prim lprim; _ },
      { node = Type.Prim rprim; _ }
         when Type.equal_prim lprim rprim ->
       Ok ()
    | { node = Type.Var { id = id1; _ }; _ },
      { node = Type.Var { id = id2; _ }; _ } when id1 = id2 ->
       Ok ()
    | { node = Type.Var { ty = Some ty0; _ }; _ }, ty1
    | ty0, { node = Type.Var { ty = Some ty1; _ }; _ } ->
       unify_types checker ty0 ty1
    | { node = Type.Var var; _ }, ty | ty, { node = Type.Var var; _ } ->
       if Type.occurs var ty then
         Error (Sequence.return (Message.Type_unification_fail(lhs, rhs)))
       else
         kind_of_type checker ty >>= fun kind ->
         unify_kinds kind var.kind >>| fun () ->
         var.ty <- Some ty
    | _ -> Error (Sequence.return (Message.Type_unification_fail(lhs, rhs)))

let unify_many checker ty =
  List.fold
    ~f:(fun acc next ->
      let result = unify_types checker ty next in
      match acc, result with
      | Ok (), Ok () -> Ok ()
      | Ok (), Error e | Error e, Ok () -> Error e
      | Error e1, Error e2 -> Error (Sequence.append e1 e2)
    )
    ~init:(Ok ())

(** Convert an Ast.monotype into an Type.t *)
let rec normalize checker tvars (_, node) =
  let open Result.Monad_infix in
  match node with
  | Ast.TApp(constr, arg) ->
     normalize checker tvars constr >>= fun constr ->
     normalize checker tvars arg >>| fun arg ->
     Type.of_node (Type.App(constr, arg))
  | Ast.TArrow -> Ok (Type.of_node (Type.Prim Type.Arrow))
  | Ast.TFloat -> Ok (Type.of_node (Type.Prim Type.Float))
  | Ast.TInt -> Ok (Type.of_node (Type.Prim Type.Int))
  | Ast.TNominal path ->
     begin match
       Module.resolve_path Module.find_type checker.structure path
     with
     | Some ident -> Ok (Type.of_node (Type.Nominal ident))
     | None -> Error (Sequence.return (Message.Unresolved_path path))
     end
  | Ast.TVar name ->
     match Hashtbl.find tvars name with
     | Some tvar -> Ok tvar
     | None -> Error (Sequence.return (Message.Unresolved_typevar name))

(** Convert an Ast.adt into a Type.adt *)
let type_adt_of_ast_adt checker adt =
  let open Result.Monad_infix in
  let tvar_map = Hashtbl.create (module String) in
  let constr_map = Hashtbl.create (module String) in
  List.fold_right ~f:(fun str acc ->
      acc >>= fun list ->
      let tvar =
        Type.fresh_var checker.tvargen (-1)
          (Kind.Var (Kind.fresh_var checker.kvargen))
      in
      match
        Hashtbl.add tvar_map ~key:str ~data:(Type.of_node (Type.Var tvar))
      with
      | `Duplicate -> Error (Sequence.return (Message.Redefined_typevar str))
      | `Ok -> Ok (tvar::list)
    ) ~init:(Ok []) adt.Ast.typeparams
  >>= fun tvar_list ->
  List.fold_right ~f:(fun (name, product) acc ->
      acc >>= fun (list, idx) ->
      match Hashtbl.add constr_map ~key:name ~data:idx with
      | `Duplicate -> Error (Sequence.return (Message.Redefined_constr name))
      | `Ok ->
         List.fold_right ~f:(fun ty acc ->
             acc >>= fun list ->
             normalize checker tvar_map ty >>= fun ty ->
             kind_of_type checker ty >>= fun kind ->
             unify_kinds kind Kind.Mono >>| fun () ->
             ty::list
           ) ~init:(Ok []) product
         >>| fun product ->
         ((name, product)::list, idx + 1)
    ) ~init:(Ok ([], 0)) adt.Ast.constrs
  >>| fun (constrs, _) ->
  let constrs = Array.of_list constrs in
  Type.{ name =
           begin match checker.structure.Module.prefix with
           | Some prefix -> Ident.Dot(prefix, adt.Ast.name)
           | None -> Ident.Root(adt.Ast.name)
           end
       ; typeparams = tvar_list
       ; constr_names = constr_map
       ; constrs }

let in_new_level f st =
  st.level <- st.level + 1;
  let result = f st in
  st.level <- st.level - 1;
  result

(** Instantiate a type scheme by replacing type variables whose levels are
    greater than or equal to target_level with type variables of level
    checker.level *)
let inst checker target_level =
  let map = Hashtbl.create (module Type.Var) in
  let rec helper ty =
    match ty.Type.node with
    | Type.App(tcon, targ) ->
       { Type.level_opt = Some checker.level
       ; Type.node = Type.App(helper tcon, helper targ) }
    | Type.Var { ty = Some ty; _ } -> helper ty
    | Type.Var ({ ty = None; level; _ } as var) ->
       if level < target_level then
         ty
       else
         begin match Hashtbl.find map var with
         | Some var2 -> var2
         | None ->
            let var2 =
              { Type.level_opt = Some checker.level
              ; Type.node =
                       Type.Var
                         (Type.fresh_var checker.tvargen checker.level var.kind)
              }
            in
            Hashtbl.add_exn map ~key:var ~data:var2;
            var2
         end
    | _ -> ty
  in helper

(** [inst_adt typechecker adt] returns a type of kind * representing the type
    constructor of [adt] being applied to fresh type variables of the correct
    kinds. *)
let inst_adt checker adt =
  let rec helper acc = function
    | [] -> acc
    | qvar::qvars ->
       let targ =
         Type.of_node
           (Type.Var
              (Type.fresh_var checker.tvargen checker.level qvar.Type.kind))
       in helper (Type.of_node (Type.App(acc, targ))) qvars
  in helper (Type.of_node (Type.Nominal adt.Type.name)) adt.Type.typeparams

(** [infer_pattern checker polyty pat] associates [polyty] with [pat]'s register
    if it has any while unifying any type constraints that arise from [pat]. *)
let rec infer_pattern checker polyty pat =
  let open Result.Monad_infix in
  match pat.Term.node with
  | Term.Con(adt, idx, pats) ->
     let nom_ty = inst_adt checker adt in
     (* The target level is the current checker level, as this function needs
        to receive [polyty] from itself recursively. *)
     unify_types checker (inst checker checker.level polyty) nom_ty
     >>= fun () ->
     begin match pat.reg with
     | None -> Ok ()
     | Some reg ->
        match Hashtbl.add checker.env ~key:reg ~data:polyty with
        | `Ok -> Ok ()
        | `Duplicate -> Error (Sequence.return Message.Unreachable)
     end >>= fun () ->
     let (_, products) = adt.Type.constrs.(idx) in
     let rec f pats tys =
       match pats, tys with
       | [], [] -> Ok ()
       | [], _ | _, [] -> Error Sequence.empty
       | pat::pats, ty::tys ->
          infer_pattern checker (inst checker (-1) ty) pat >>= fun () ->
          f pats tys
     in f pats products
  | Term.Wild ->
     match pat.reg with
     | None -> Ok ()
     | Some reg ->
        match Hashtbl.add checker.env ~key:reg ~data:polyty with
        | `Ok -> Ok ()
        | `Duplicate -> Error (Sequence.return Message.Unreachable)

(** [infer typechecker term] infers the type of [term], returning a result. *)
let rec infer checker =
  let open Result.Monad_infix in
  function
  | Term.Ann{term; _} -> infer checker term

  | Term.App(f, x) ->
     begin match infer checker f, infer checker x with
     | (Ok f_ty, Ok x_ty) ->
        let var = fresh_tvar checker in
        let result = unify_types checker f_ty (Type.arrow x_ty var) in
        result >>| fun () -> var
     | (Error f_err, Error x_err) -> Error (Sequence.append f_err x_err)
     | (err, Ok _) | (Ok _, err) -> err
     end

  | Term.Case(discriminant, discriminants, cases) ->
     let out_ty = fresh_tvar checker in
     List.fold_right ~f:(fun discriminant acc ->
         acc >>= fun list ->
         in_new_level (fun checker ->
             infer checker discriminant
           ) checker >>| fun ty ->
         ty::list
       ) ~init:(Ok []) (discriminant::discriminants) >>= fun discr_tys ->
     let rec f discr_tys pats =
       match discr_tys, pats with
       | [], [] -> Ok ()
       | [], _ | _, [] -> Error Sequence.empty
       | ty::tys, pat::pats ->
          infer_pattern checker ty pat >>= fun () ->
          f tys pats
     in
     List.fold ~f:(fun acc (pat, pats, consequent) ->
         acc >>= fun () ->
         in_new_level (fun _ ->
             f discr_tys (pat::pats)
           ) checker >>= fun () ->
         infer checker consequent >>= fun ty ->
         unify_types checker ty out_ty
       ) ~init:(Ok ()) cases >>| fun () -> out_ty

  | Term.Extern_var id ->
     begin match Symtable.find_val checker.symtable id with
     | Some (ty, _) -> Ok (inst checker (checker.level + 1) ty)
     | None -> Error (Sequence.return (Message.Unresolved_id id))
     end

  | Term.Lam(id, body) ->
     let var = fresh_tvar checker in
     Hashtbl.add_exn checker.env ~key:id ~data:var;
     infer checker body >>= fun body_ty ->
     Ok (Type.arrow var body_ty)

  | Term.Let(lhs, rhs, body) ->
     in_new_level (fun checker -> infer checker rhs) checker >>= fun ty ->
     Hashtbl.add_exn checker.env ~key:lhs ~data:ty;
     infer checker body

  | Term.Let_rec(bindings, body) ->
     let result =
       in_new_level (fun checker ->
           (* Associate each new binding with a fresh type variable *)
           let f (lhs, _) =
             let ty = fresh_tvar checker in
             Hashtbl.add_exn checker.env ~key:lhs ~data:ty
           in
           List.iter ~f:f bindings;
           (* Type infer the RHS of each new binding and unify the result with
              the type variable *)
           let f acc (lhs, rhs) =
             let tvar = Hashtbl.find_exn checker.env lhs in
             infer checker rhs >>= fun ty ->
             match acc, unify_types checker tvar ty with
             | Ok (), Ok () -> Ok ()
             | Ok (), Error e | Error e, Ok () -> Error e
             | Error e1, Error e2 -> Error (Sequence.append e1 e2)
           in List.fold ~f:f ~init:(Ok ()) bindings
         ) checker
     in result >>= fun () -> infer checker body

  | Term.Var reg ->
     match Hashtbl.find checker.env reg with
     | Some ty -> Ok (inst checker (checker.level + 1) ty)
     | None -> Error (Sequence.return Message.Unreachable)
