open Base

type t =
  { package : Package.t
  ; packages : (string, Package.t) Hashtbl.t
  ; env : (Register.t, Type.t) Hashtbl.t
  ; mutable level : int
  ; tvargen : Type.vargen
  ; kvargen : Kind.vargen }

(** [create symtable] creates a fresh typechecker state. *)
let create package packages =
  { package
  ; packages
  ; env = Hashtbl.create (module Register)
  ; level = 0
  ; tvargen = Type.create_vargen ()
  ; kvargen = Kind.create_vargen () }

let fresh_tvar (checker : t) =
  { Type.level = checker.level
  ; node =
      Type.Var
        (Type.fresh_var checker.tvargen (Type.Exists checker.level) Kind.Mono) }

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
  match ty.Type.node with
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
    ) ~init:(Ok ())

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
     let ident =
       match path with
       | Ast.Internal str -> (checker.package.Package.name, str)
       | Ast.External(x, y) -> (x, y)
     in
     begin
       match find Package.find_typedef checker ident with
       | Some _ -> Ok (Type.of_node (Type.Nominal ident))
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
        Type.fresh_var checker.tvargen Type.Univ
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
  { Type.name = adt.Ast.name
  ; typeparams = tvar_list
  ; constr_names = constr_map
  ; constrs }

let in_new_level f st =
  st.level <- st.level + 1;
  let result = f st in
  st.level <- st.level - 1;
  result

(** [gen checker ty] generalizes a type by replacing existential type variables
    of level [checker.level] or higher with a universally quantified variable.
    Universally quantified variables really shouldn't appear in [ty], but the
    function just ignores them. *)
let gen checker =
  let map = Hashtbl.create (module Type.Var) in
  let rec helper ty =
    match ty.Type.node with
    | Type.App(tcon, targ) ->
       Type.of_node (Type.App(helper tcon, helper targ))
    | Type.Var { ty = Some ty; _ } -> helper ty
    | Type.Var ({ ty = None; quant; kind; _ } as var) ->
       begin match quant with
       | Type.Exists level when level >= checker.level ->
          Hashtbl.find_or_add map var ~default:(fun () ->
              Type.of_node
                (Type.Var (Type.fresh_var checker.tvargen Type.Univ kind)))
       | _ -> ty
       end
    | _ -> ty
  in helper

(** [inst checker polyty] instantiates [polyty] by replacing universally
    quantified type variables with type variables of level [checker.level] *)
let inst checker =
  let map = Hashtbl.create (module Type.Var) in
  let rec helper ty =
    match ty.Type.node with
    | Type.App(tcon, targ) ->
       Type.of_node (Type.App(helper tcon, helper targ))
    | Type.Var { ty = Some ty; _ } -> helper ty
    | Type.Var ({ ty = None; quant; _ } as var) ->
       begin match quant with
       | Type.Exists _ -> ty
       | Type.Univ ->
          Hashtbl.find_or_add map var ~default:(fun () ->
              Type.of_node
                (Type.Var
                (Type.fresh_var
                   checker.tvargen
                   (Type.Exists checker.level)
                   var.kind)))
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
              (Type.fresh_var
                 checker.tvargen (Type.Exists checker.level) qvar.Type.kind))
       in helper (Type.of_node (Type.App(acc, targ))) qvars
  in
  helper
    (Type.of_node (Type.Nominal (checker.package.name, adt.Type.name)))
    adt.Type.typeparams

(** [compare_polytypes equalities t1 t2] where [equalities] is a map from
    universally quanitifed variables in [t1] to universally quantified variables
    in [t2] *)
let rec compare_polytys equalities t1 t2 =
  let open Result.Monad_infix in
  match t1.Type.node, t2.Type.node with
  | Type.App(tcon1, targ1), Type.App(tcon2, targ2) ->
     compare_polytys equalities tcon1 tcon2 >>= fun () ->
     compare_polytys equalities targ1 targ2
  | Type.Nominal n1, Nominal n2 when (Ident.compare n1 n2) = 0 ->
     Ok ()
  | Type.Prim p1, Type.Prim p2 when (Type.compare_prim p1 p2) = 0 -> Ok ()
  | Type.Var tvar1, Type.Var tvar2 ->
     begin match tvar1.Type.quant, tvar2.Type.quant with
     | Univ, Exists _ | Exists _, Univ -> Error Sequence.empty
     | Exists _, Exists _ ->
        if tvar1.Type.id = tvar2.Type.id then
          Ok ()
        else
          Error Sequence.empty
     | Univ, Univ ->
        let tvar3 =
          Hashtbl.find_or_add equalities tvar1 ~default:(fun () -> tvar2)
        in
        if Type.Var.compare tvar3 tvar2 = 0 then
          Ok ()
        else
          Error Sequence.empty
     end
  | _ -> Error Sequence.empty

(** [infer_pattern checker polyty pat] associates [polyty] with [pat]'s register
    if it has any while unifying any type constraints that arise from [pat]. *)
let rec infer_pattern checker polyty pat =
  let open Result.Monad_infix in
  let type_binding pat =
    match pat.Term.reg with
    | None -> Ok ()
    | Some reg ->
       (* The binding could already exist because of a prior OR pattern
          alternative *)
       let polyty2 =
         Hashtbl.find_or_add checker.env reg ~default:(fun () -> polyty)
       in
       if phys_equal polyty polyty2 then
         Ok ()
       else
         let equalities = Hashtbl.create (module Type.Var) in
         compare_polytys equalities polyty polyty2
  in
  match pat.Term.node with
  | Term.Con(adt, idx, pats) ->
     let nom_ty = inst_adt checker adt in
     unify_types checker (inst checker polyty) nom_ty >>= fun () ->
     type_binding pat >>= fun () ->
     let (_, products) = adt.Type.constrs.(idx) in
     let rec f pats tys =
       match pats, tys with
       | [], [] -> Ok ()
       | [], _ | _, [] -> Error Sequence.empty
       | pat::pats, ty::tys ->
          infer_pattern checker ty pat >>= fun () ->
          f pats tys
     in f pats products
  | Term.Wild -> type_binding pat
  | Term.Or(p1, p2) ->
     infer_pattern checker polyty p1 >>= fun () ->
     infer_pattern checker polyty p2

(** [infer typechecker term] infers the type of [term], returning a result. *)
let rec infer checker =
  let open Result.Monad_infix in
  function
  | Term.Ann{term; _} -> infer checker term

  | Term.App(f, x) ->
     begin match infer checker f, infer checker x with
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

  | Term.Case(scrutinee, scrutinees, cases) ->
     let out_ty = fresh_tvar checker in
     in_new_level (fun checker ->
         infer checker scrutinee
       ) checker >>= fun scrut ->
     List.fold_right ~f:(fun scrutinee acc ->
         acc >>= fun list ->
         in_new_level (fun checker ->
             infer checker scrutinee
           ) checker >>| fun expr ->
         expr::list
       ) ~init:(Ok []) scrutinees >>= fun scruts ->
     let rec f scruts pats =
       match scruts, pats with
       | [], [] -> Ok ()
       | [], _ | _, [] -> Error Sequence.empty
       | scrut::scruts, pat::pats ->
          infer_pattern checker (gen checker scrut.Lambda.ty) pat
          >>= fun () ->
          f scruts pats
     in
     List.fold_right ~f:(fun (pat, pats, regs, consequent) acc ->
         acc >>= fun (idx, matrix, branches) ->
         in_new_level (fun _ ->
             infer_pattern checker (gen checker scrut.Lambda.ty) pat
           ) checker >>= fun () ->
         in_new_level (fun _ ->
             f scruts pats
           ) checker >>= fun () ->
         infer checker consequent >>= fun consequent ->
         unify_types checker consequent.Lambda.ty out_ty >>| fun () ->
         ( idx - 1
         , { Pattern.first_pattern = pat
           ; Pattern.rest_patterns = pats
           ; Pattern.bindings = Map.empty (module Register)
           ; Pattern.action = idx }::matrix
         , (regs, consequent)::branches )
       ) ~init:(Ok (List.length cases - 1, [], [])) cases
     >>= fun (_, matrix, branches) ->
     Pattern.decision_tree_of_matrix
       (let (occurrences, _) =
          List.fold ~f:(fun (list, i) _ ->
              ((Pattern.Nil i)::list, i + 1)
            ) ~init:([], 0) (scrutinee::scrutinees)
        in occurrences)
       matrix >>| fun decision_tree ->
     { Lambda.ty = out_ty
     ; Lambda.expr = Lambda.Case(scrut, scruts, decision_tree, branches) }

  | Term.Extern_var(id, ty) ->
     Ok Lambda.{ ty = inst checker ty; expr = Lambda.Extern_var id }

  | Term.Lam(id, body) ->
     let var = fresh_tvar checker in
     Hashtbl.add_exn checker.env ~key:id ~data:var;
     infer checker body >>= fun body ->
     Ok Lambda.{ ty = Type.arrow var body.Lambda.ty
               ; expr = Lambda.Lam(id, body) }

  | Term.Let(lhs, rhs, body) ->
     in_new_level (fun checker -> infer checker rhs) checker >>= fun rhs ->
     Hashtbl.add_exn checker.env ~key:lhs ~data:(gen checker rhs.Lambda.ty);
     infer checker body >>| fun body ->
     Lambda.{ ty = body.Lambda.ty; expr = Lambda.Let(lhs, rhs, body) }

  | Term.Let_rec(bindings, body) ->
     in_new_level (fun checker ->
         (* Associate each new binding with a fresh type variable *)
         let f (lhs, _) =
           Hashtbl.add_exn checker.env ~key:lhs ~data:(fresh_tvar checker)
         in
         List.iter ~f:f bindings;
         (* Type infer the RHS of each new binding and unify the result with
            the type variable *)
         let f (lhs, rhs) acc =
           let tvar = Hashtbl.find_exn checker.env lhs in
           infer checker rhs >>= fun rhs ->
           match acc, unify_types checker tvar rhs.Lambda.ty with
           | Ok acc, Ok () -> Ok ((lhs, rhs)::acc)
           | Ok _, Error e | Error e, Ok () -> Error e
           | Error e1, Error e2 -> Error (Sequence.append e1 e2)
         in List.fold_right ~f:f ~init:(Ok []) bindings
       ) checker
     >>= fun bindings ->
     (* In the RHS of let-rec bindings, LHS names aren't quantified. Here,
        quantify them for the let-rec body. *)
     List.iter ~f:(fun (lhs, _) ->
         Hashtbl.change checker.env lhs ~f:(function
             | Some ty -> Some (gen checker ty)
             | None -> None
           )
       ) bindings;
     infer checker body >>| fun body ->
     Lambda.{ ty = body.Lambda.ty; expr = Lambda.Let_rec(bindings, body) }

  | Term.Var reg ->
     match Hashtbl.find checker.env reg with
     | Some ty ->
        Ok Lambda.{ ty = inst checker ty; expr = Lambda.Local_var reg }
     | None -> Error (Sequence.return (Message.Unreachable "Tc expr var"))
