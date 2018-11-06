open Base

type t = {
    package : Package.t;
    packages : (string, Package.t) Hashtbl.t;
    env : (Register.t, Type.t) Hashtbl.t;
    let_level : int;
    lam_level : int;
    tvargen : Type.vargen;
    kvargen : Kind.vargen
  }

(** [create symtable] creates a fresh typechecker state. *)
let create package packages =
  { package
  ; packages
  ; env = Hashtbl.create (module Register)
  ; let_level = 0
  ; lam_level = 0
  ; tvargen = Type.create_vargen ()
  ; kvargen = Kind.create_vargen () }

let fresh_quant checker =
  Type.Exists
    { let_level = checker.let_level
    ; lam_level = checker.lam_level }

let fresh_tvar ?(purity = Type.Pure) (checker : t) =
  Type.Var
    (Type.fresh_var
       checker.tvargen purity (fresh_quant checker) Kind.Mono)

let find f st (pack_name, item_name) =
  match Hashtbl.find st.packages pack_name with
  | None -> None
  | Some package -> f package item_name

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
  match ty with
  | Type.App(tcon, targ) ->
     kind_of_type checker targ >>= fun argkind ->
     kind_of_type checker tcon >>= fun conkind ->
     let kvar = Kind.Var (Kind.fresh_var checker.kvargen) in
     unify_kinds conkind (Kind.Poly(argkind, kvar)) >>| fun () ->
     kvar
  | Type.Nominal id ->
     begin match find Package.kind_of_ident checker id with
     | Some kind -> Ok kind
     | None -> Error (Sequence.return (Message.Unresolved_type id))
     end
  | Type.Prim Type.Arrow ->
     Ok (Kind.Poly(Kind.Mono, Kind.Poly(Kind.Mono, Kind.Mono)))
  | Type.Prim Type.Char -> Ok Kind.Mono
  | Type.Prim Type.Float -> Ok Kind.Mono
  | Type.Prim Type.Int -> Ok Kind.Mono
  | Type.Prim Type.Ref -> Ok (Kind.Poly(Kind.Mono, Kind.Mono))
  | Type.Prim Type.String -> Ok Kind.Mono
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
    | Type.App(lcon, larg), Type.App(rcon, rarg) ->
       begin
         match unify_types checker lcon rcon, unify_types checker larg rarg with
         | Ok (), Ok () -> Ok ()
         | Error e, Ok () | Ok (), Error e -> Error e
         | Error e1, Error e2 -> Error (Sequence.append e1 e2)
       end
    | Type.Nominal lstr, Type.Nominal rstr
         when (Ident.compare lstr rstr) = 0 ->
       Ok ()
    | Type.Prim lprim, Type.Prim rprim
         when Type.equal_prim lprim rprim ->
       Ok ()
    | Type.Var { id = id1; _ }, Type.Var { id = id2; _ } when id1 = id2 ->
       Ok ()
    | Type.Var { ty = Some ty0; _ }, ty1
    | ty0, Type.Var { ty = Some ty1; _ } ->
       unify_types checker ty0 ty1
    | Type.Var var, ty | ty, Type.Var var ->
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
    ) ~init:(Ok ())

(** Convert an Ast.monotype into an Type.t *)
let rec normalize checker tvars (_, node) =
  let open Result.Monad_infix in
  match node with
  | Ast.TApp(constr, arg) ->
     normalize checker tvars constr >>= fun constr ->
     normalize checker tvars arg >>| fun arg ->
     Type.App(constr, arg)
  | Ast.TArrow -> Ok (Type.Prim Type.Arrow)
  | Ast.TFloat -> Ok (Type.Prim Type.Float)
  | Ast.TInt -> Ok (Type.Prim Type.Int)
  | Ast.TNominal path ->
     let ident =
       match path with
       | Ast.Internal str -> (checker.package.Package.name, str)
       | Ast.External(x, y) -> (x, y)
     in
     begin
       match find Package.find_typedef checker ident with
       | Some _ -> Ok (Type.Nominal ident)
       | None -> Error (Sequence.return (Message.Unresolved_path path))
     end
  | Ast.TVar name ->
     match Env.find tvars name with
     | Some tvar -> Ok tvar
     | None -> Error (Sequence.return (Message.Unresolved_typevar name))

let fresh_kinds_of_typeparams checker =
  List.map ~f:(fun _ -> (Kind.Var (Kind.fresh_var checker.kvargen)))

let tvars_of_typeparams checker tvar_map kinds names =
  let open Result.Monad_infix in
  let rec f tvar_map tvar_list kinds strs =
    match kinds, strs with
    | kind::kinds, str::strs ->
      let tvar = Type.fresh_var checker.tvargen Type.Pure Type.Univ kind in
      begin match Env.add tvar_map str (Type.Var tvar) with
      | None -> Error (Sequence.return (Message.Redefined_typevar str))
      | Some tvar_map ->
         (* Fold RIGHT, not left! *)
         f tvar_map tvar_list kinds strs >>| fun (tvar_map, tvar_list) ->
         (tvar_map, tvar::tvar_list)
      end
    | [], [] -> Ok (tvar_map, tvar_list)
    | _ -> Error Sequence.empty
  in f tvar_map [] kinds names

let type_of_ast_polytype checker (Ast.Forall(typeparams, body)) =
  let open Result.Monad_infix in
  let tvar_map = Env.empty (module String) in
  let kinds = fresh_kinds_of_typeparams checker typeparams in
  tvars_of_typeparams checker tvar_map kinds typeparams
  >>= fun (tvar_map, _) ->
  normalize checker tvar_map body

(** Convert an [Ast.adt] into a [Type.adt] *)
let type_adt_of_ast_adt checker adt =
  let open Result.Monad_infix in
  let kinds = fresh_kinds_of_typeparams checker adt.Ast.typeparams in
  let kind = Kind.curry kinds Kind.Mono in
  let constr_map = Hashtbl.create (module String) in
  List.fold_right ~f:(fun (name, product) acc ->
      acc >>= fun (constr_list, idx) ->
      match Hashtbl.add constr_map ~key:name ~data:idx with
      | `Duplicate -> Error (Sequence.return (Message.Redefined_constr name))
      | `Ok ->
         let tvar_map = Env.empty (module String) in
         tvars_of_typeparams checker tvar_map kinds adt.Ast.typeparams
         >>= fun (tvar_map, tvar_list) ->
         List.fold_right ~f:(fun ty acc ->
             acc >>= fun products ->
             normalize checker tvar_map ty >>= fun ty ->
             kind_of_type checker ty >>= fun kind ->
             unify_kinds kind Kind.Mono >>| fun () ->
             ty::products
           ) ~init:(Ok []) product
         >>| fun product ->
         let out_ty =
           Type.with_params
             (Type.Nominal (checker.package.Package.name, adt.Ast.name))
             (List.map ~f:(fun var -> Type.Var var) tvar_list)
         in
         ((name, product, out_ty)::constr_list, idx - 1)
    ) ~init:(Ok ([], List.length adt.Ast.constrs - 1)) adt.Ast.constrs
  >>| fun (constrs, _) ->
  let constrs = Array.of_list constrs in
  { Type.name = adt.Ast.name
  ; adt_kind = kind
  ; constr_names = constr_map
  ; constrs }

let in_new_let_level f self =
  f { self with let_level = self.let_level + 1 }

let in_new_lam_level f self =
  f { self with lam_level = self.lam_level + 1 }

(** [gen checker ty] generalizes a type by replacing existential type variables
    of level [checker.level] or higher with a universally quantified variable.
    Universally quantified variables really shouldn't appear in [ty], but the
    function just ignores them. *)
let gen checker =
  let map = Hashtbl.create (module Type.Var) in
  let rec helper ty =
    match ty with
    | Type.App(tcon, targ) ->
       Type.App(helper tcon, helper targ)
    | Type.Var { ty = Some ty; _ } -> helper ty
    | Type.Var ({ ty = None; quant; kind; purity; _ } as var) ->
       begin match quant with
       | Type.Exists levels ->
          let test =
            match purity with
            | Pure -> levels.let_level >= checker.let_level
            | Impure ->
               (levels.let_level >= checker.let_level) &&
                 (levels.lam_level > checker.lam_level)
          in
          if test then
            Hashtbl.find_or_add map var ~default:(fun () ->
                Type.Var
                  (Type.fresh_var checker.tvargen purity Type.Univ kind))
          else
            ty
       | _ -> ty
       end
    | ty -> ty
  in helper

(** [inst checker polyty] instantiates [polyty] by replacing universally
    quantified type variables with type variables of level [checker.level] *)
let inst checker =
  let map = Hashtbl.create (module Type.Var) in
  let rec helper ty =
    match ty with
    | Type.App(tcon, targ) ->
       Type.App(helper tcon, helper targ)
    | Type.Var { ty = Some ty; _ } -> helper ty
    | Type.Var ({ ty = None; quant; purity; kind; _ } as var) ->
       begin match quant with
       | Type.Exists _ -> ty
       | Type.Univ ->
          Hashtbl.find_or_add map var ~default:(fun () ->
              Type.Var
                (Type.fresh_var
                   checker.tvargen purity (fresh_quant checker) kind)
            )
       end
    | _ -> ty
  in helper

let make_impure checker ty =
  let tvar =
    Type.fresh_var checker.tvargen Type.Impure (fresh_quant checker) Kind.Mono
  in
  let _ = Type.occurs tvar ty in
  ()

(** [infer_pattern checker map ty pat] associates [ty] with [pat]'s register
    if it has any while unifying any type constraints that arise from [pat]. *)
let rec infer_pattern checker map ty pat =
  let open Result.Monad_infix in
  let type_binding pat =
    match pat.Pattern.reg with
    | None -> Ok map
    | Some reg ->
       (* The binding could already exist because of a prior OR pattern
          alternative *)
       match Map.find map reg with
       | Some ty2 ->
          unify_types checker ty ty2 >>| fun () -> map
       | None ->
          match Map.add map ~key:reg ~data:ty with
          | `Ok map -> Ok map
          | `Duplicate ->
             Error (Sequence.return (Message.Unreachable "infer_pattern dup"))
  in
  match pat.Pattern.node with
  | Pattern.Con(adt, idx, pats) ->
     let (_, products, adt_ty) = adt.Type.constrs.(idx) in
     let nom_ty = inst checker adt_ty in
     unify_types checker ty nom_ty >>= fun () ->
     type_binding pat >>= fun map ->
     let rec f map pats tys =
       match pats, tys with
       | [], [] -> Ok map
       | [], _ | _, [] ->
          Error (Sequence.return (Message.Unreachable "infer_pattern f"))
       | pat::pats, ty::tys ->
          infer_pattern checker map ty pat >>= fun map ->
          f map pats tys
     in f map pats products
  | Pattern.Wild -> type_binding pat
  | Pattern.Or(p1, p2) ->
     infer_pattern checker map ty p1 >>= fun map1 ->
     infer_pattern checker map ty p2 >>= fun map2 ->
     Map.fold2 map1 map2 ~init:(Ok ()) ~f:(fun ~key:_ ~data acc ->
         acc >>= fun () ->
         match data with
         | `Both(t1, t2) -> unify_types checker t1 t2
         | _ -> Error (Sequence.return (Message.Unreachable "f"))
       ) >>| fun () ->
     Map.merge_skewed map1 map ~combine:(fun ~key:_ _ v -> v)

(** [infer_expr typechecker term] infers the type of [term], returning a
    result. *)
let rec infer_term checker =
  let open Result.Monad_infix in
  function
  | Term.Ann{term; _} -> infer_term checker term

  | Term.App(f, x) ->
     begin match infer_term checker f, infer_term checker x with
     | (Ok f, Ok x) ->
        let var = fresh_tvar checker in
        let result =
          unify_types checker f.Lambda.ty (Type.arrow x.Lambda.ty var)
        in
        result >>| fun () ->
        Lambda.{ ty = var; expr = Lambda.App(f, x) }
     | (Error f_err, Error x_err) -> Error (Sequence.append f_err x_err)
     | (err, Ok _) | (Ok _, err) -> err
     end

  | Term.Assign(lval, rval) ->
     infer_term checker lval >>= fun lval ->
     infer_term checker rval >>= fun rval ->
     unify_types checker
       lval.Lambda.ty
       (Type.App(Type.Prim Type.Ref, rval.Lambda.ty)) >>| fun () ->
     make_impure checker rval.Lambda.ty;
     Lambda.{ ty = rval.Lambda.ty; expr = Lambda.Assign(lval, rval) }

  | Term.Case(scrutinees, cases) ->
     let out_ty = fresh_tvar checker in
     List.fold_right ~f:(fun scrutinee acc ->
         acc >>= fun list ->
         in_new_let_level (fun checker ->
             infer_term checker scrutinee
           ) checker >>| fun expr ->
         expr::list
       ) ~init:(Ok []) scrutinees >>= fun scruts ->
     List.fold_right ~f:(fun (pats, regs, consequent) acc ->
         acc >>= fun (idx, matrix, branches) ->
         infer_branch checker scruts pats >>= fun () ->
         infer_term checker consequent >>= fun consequent ->
         unify_types checker consequent.Lambda.ty out_ty >>| fun () ->
         ( idx - 1
         , { Pattern.patterns = pats
           ; bindings = Map.empty (module Register)
           ; action = idx }::matrix
         , (regs, consequent)::branches )
       ) ~init:(Ok (List.length cases - 1, [], [])) cases
     >>= fun (_, matrix, branches) ->
     Pattern.decision_tree_of_matrix
       (let (occurrences, _) =
          List.fold ~f:(fun (list, i) _ ->
              ((Pattern.Nil i)::list, i + 1)
            ) ~init:([], 0) scrutinees
        in occurrences)
       matrix >>| fun decision_tree ->
     { Lambda.ty = out_ty
     ; expr = Lambda.Case(scruts, decision_tree, branches) }

  | Term.Constr(adt, idx) ->
     let _, product, out_ty = adt.Type.constrs.(idx) in
     let ty = Type.curry product out_ty in
     Ok Lambda.{ ty = inst checker ty
               ; expr = Lambda.Constr(List.length product) }

  | Term.Extern_var(id, ty) ->
     Ok Lambda.{ ty = inst checker ty; expr = Lambda.Extern_var id }

  | Term.Lam(id, body) ->
     in_new_lam_level (fun checker ->
         let var = fresh_tvar checker in
         Hashtbl.add_exn checker.env ~key:id ~data:var;
         infer_term checker body >>= fun body ->
         Ok Lambda.{ ty = Type.arrow var body.Lambda.ty
                   ; expr = Lambda.Lam(id, body) }
       ) checker

  | Term.Let(lhs, rhs, body) ->
     in_new_let_level (fun checker ->
         infer_term checker rhs
       ) checker >>= fun rhs ->
     Hashtbl.add_exn checker.env ~key:lhs ~data:(gen checker rhs.Lambda.ty);
     infer_term checker body >>| fun body ->
     Lambda.{ ty = body.Lambda.ty; expr = Lambda.Let(lhs, rhs, body) }

  | Term.Let_rec(bindings, body) ->
     infer_rec_bindings checker bindings >>= fun bindings ->
     (* In the RHS of let-rec bindings, LHS names aren't quantified. Here,
        quantify them for the let-rec body. *)
     List.iter ~f:(fun (lhs, _) ->
         Hashtbl.change checker.env lhs ~f:(function
             | Some ty -> Some (gen checker ty)
             | None -> None
           )
       ) bindings;
     infer_term checker body >>| fun body ->
     Lambda.{ ty = body.Lambda.ty; expr = Lambda.Let_rec(bindings, body) }

  | Term.Lit lit ->
     Ok { Lambda.ty =
            begin match lit with
            | Literal.Char _ -> Type.Prim Type.Char
            | Literal.Float _ -> Type.Prim Type.Float
            | Literal.Int _ -> Type.Prim Type.Int
            | Literal.String _ -> Type.Prim Type.String
            end
        ; expr = Lambda.Lit lit }

  | Term.Prim(op, ty) ->
     type_of_ast_polytype checker ty >>| fun ty ->
     { Lambda.ty = inst checker ty; expr = Lambda.Prim op }

  | Term.Ref value ->
     infer_term checker value >>| fun value ->
     make_impure checker value.Lambda.ty;
     Lambda.{ ty = Type.App(Type.Prim Type.Ref, value.Lambda.ty)
            ; expr = Lambda.Ref(value) }

  | Term.Seq(s, t) ->
     infer_term checker s >>= fun s ->
     infer_term checker t >>| fun t ->
     Lambda.{ ty = t.Lambda.ty; expr = Lambda.Seq(s, t) }

  | Term.Var reg ->
     match Hashtbl.find checker.env reg with
     | Some ty ->
        Ok Lambda.{ ty = inst checker ty; expr = Lambda.Local_var reg }
     | None -> Error (Sequence.return (Message.Unreachable "Tc expr var"))

and infer_branch checker scruts pats =
  let open Result.Monad_infix in
  let rec f map scruts pats =
    match scruts, pats with
    | [], [] -> Ok map
    | [], _ | _, [] ->
       Error (Sequence.return (Message.Unreachable "infer_branch"))
    | scrut::scruts, pat::pats ->
       infer_pattern checker map scrut.Lambda.ty pat
       >>= fun map ->
       f map scruts pats
  in
  let map = Map.empty (module Register) in
  in_new_let_level (fun checker ->
      f map scruts pats >>| fun map ->
      Map.iteri ~f:(fun ~key ~data ->
          let _ = Hashtbl.add checker.env ~key ~data:(gen checker data) in
          ()
        ) map
    ) checker

and infer_rec_bindings checker bindings =
  let open Result.Monad_infix in
  in_new_let_level (fun checker ->
      (* Associate each new binding with a fresh type variable *)
      let f (lhs, _) =
        Hashtbl.add_exn checker.env ~key:lhs ~data:(fresh_tvar checker)
      in
      List.iter ~f:f bindings;
      (* Type infer the RHS of each new binding and unify the result with
         the type variable *)
      let f (lhs, rhs) acc =
        let tvar = Hashtbl.find_exn checker.env lhs in
        infer_term checker rhs >>= fun rhs ->
        match acc, unify_types checker tvar rhs.Lambda.ty with
        | Ok acc, Ok () -> Ok ((lhs, rhs)::acc)
        | Ok _, Error e | Error e, Ok () -> Error e
        | Error e1, Error e2 -> Error (Sequence.append e1 e2)
      in List.fold_right ~f:f ~init:(Ok []) bindings
    ) checker
