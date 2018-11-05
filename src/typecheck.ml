open Base

type t = {
    package : Package.t;
    packages : (string, Package.t) Hashtbl.t;
    env : (Register.t, Type.t) Hashtbl.t;
    mutable level : int;
    tvargen : Type.vargen;
    kvargen : Kind.vargen
  }

(** [create symtable] creates a fresh typechecker state. *)
let create package packages =
  { package
  ; packages
  ; env = Hashtbl.create (module Register)
  ; level = 0
  ; tvargen = Type.create_vargen ()
  ; kvargen = Kind.create_vargen () }

let fresh_tvar (checker : t) =
  { Type.level = Type.Exists checker.level
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
  | Kind.Poly(a, g1, b), Kind.Poly(c, g2, d) ->
     unify_kinds a c >>= fun () ->
     unify_kinds b d >>| fun () ->
     begin match !g1, !g2 with
     | Kind.Mut, Kind.Const -> g2 := !g1
     | Kind.Const, Kind.Mut -> g1 := !g2
     | _ -> ()
     end
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
     unify_kinds conkind (Kind.Poly(argkind, ref Kind.Const, kvar))
     >>| fun () ->
     kvar
  | Type.Nominal id ->
     begin match find Package.kind_of_ident checker id with
     | Some kind -> Ok kind
     | None -> Error (Sequence.return (Message.Unresolved_type id))
     end
  | Type.Prim Type.Arrow ->
     Ok (Kind.Poly
           ( Kind.Mono
           , ref Kind.Const
           , Kind.Poly(Kind.Mono, ref Kind.Const, Kind.Mono)))
  | Type.Prim Type.Char -> Ok Kind.Mono
  | Type.Prim Type.Float -> Ok Kind.Mono
  | Type.Prim Type.Int -> Ok Kind.Mono
  | Type.Prim Type.Ref -> Ok (Kind.Poly(Kind.Mono, ref Kind.Mut, Kind.Mono))
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

let type_of_ast_polytype checker (Ast.Forall(typeparams, body)) =
  let open Result.Monad_infix in
  let tvar_map = Hashtbl.create (module String) in
  List.fold_right ~f:(fun str acc ->
      acc >>= fun () ->
      let tvar =
        Type.fresh_var checker.tvargen Type.Univ
          (Kind.Var (Kind.fresh_var checker.kvargen))
      in
      match
        Hashtbl.add tvar_map ~key:str ~data:(Type.of_node (Type.Var tvar))
      with
      | `Duplicate -> Error (Sequence.return (Message.Redefined_typevar str))
      | `Ok -> Ok ()
    ) ~init:(Ok ()) typeparams
  >>= fun () ->
  normalize checker tvar_map body

(** Convert an [Ast.adt] into a [Type.adt] *)
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
         ((name, product)::list, idx - 1)
    ) ~init:(Ok ([], List.length adt.Ast.constrs - 1)) adt.Ast.constrs
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
let gen checker safe_level =
  let open Result.Monad_infix in
  let map = Hashtbl.create (module Type.Var) in
  let rec helper ty =
    match ty.Type.node with
    | Type.App(tcon, targ) ->
       helper tcon >>= fun tcon ->
       let rec helper2 = function
         | Kind.Poly(kind, g, _) ->
            begin match !g with
            | Kind.Const ->
               helper targ
            | Kind.Mut ->
               let tvar =
                 Type.fresh_var checker.kvargen (Type.Exists safe_level) kind
               in
               let _ = Type.occurs tvar targ in
               Ok targ
            end >>| fun targ -> Type.of_node (Type.App(tcon, targ))
         | Kind.Var { kind = Some kind; _ } ->
            helper2 kind
         | _ ->
            Error (Sequence.return (Message.Unreachable "gen"))
       in kind_of_type checker tcon >>= helper2
    | Type.Var { ty = Some ty; _ } -> helper ty
    | Type.Var ({ ty = None; quant; kind; _ } as var) ->
       begin match quant with
       | Type.Exists level when level >= checker.level ->
          Ok (Hashtbl.find_or_add map var ~default:(fun () ->
                  Type.of_node
                    (Type.Var (Type.fresh_var checker.tvargen Type.Univ kind))))
       | _ -> Ok ty
       end
    | _ -> Ok ty
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
     let nom_ty = inst_adt checker adt in
     unify_types checker ty nom_ty >>= fun () ->
     type_binding pat >>= fun map ->
     let (_, products) = adt.Type.constrs.(idx) in
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
let rec infer_term checker safe_level =
  let open Result.Monad_infix in
  function
  | Term.Ann{term; _} -> infer_term checker safe_level term

  | Term.App(f, x) ->
     begin match
       infer_term checker safe_level f,
       infer_term checker safe_level x
     with
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
     infer_term checker safe_level lval >>= fun lval ->
     infer_term checker safe_level rval >>= fun rval ->
     unify_types checker
       lval.Lambda.ty
       (Type.of_node (Type.App( Type.of_node (Type.Prim Type.Ref)
                              , rval.Lambda.ty )
       )) >>| fun () ->
     Lambda.{ ty = rval.Lambda.ty; expr = Lambda.Assign(lval, rval) }

  | Term.Case(scrutinees, cases) ->
     let out_ty = fresh_tvar checker in
     List.fold_right ~f:(fun scrutinee acc ->
         acc >>= fun list ->
         in_new_level (fun checker ->
             infer_term checker safe_level scrutinee
           ) checker >>| fun expr ->
         expr::list
       ) ~init:(Ok []) scrutinees >>= fun scruts ->
     List.fold_right ~f:(fun (pats, regs, consequent) acc ->
         acc >>= fun (idx, matrix, branches) ->
         infer_branch checker safe_level scruts pats >>= fun () ->
         infer_term checker safe_level consequent >>= fun consequent ->
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
     let _, product = adt.Type.constrs.(idx) in
     let ty =
       Type.type_of_constr ((checker.package.name, adt.Type.name)) adt idx
     in
     Ok Lambda.{ ty = inst checker ty
               ; expr = Lambda.Constr(List.length product) }

  | Term.Extern_var(id, ty) ->
     Ok Lambda.{ ty = inst checker ty; expr = Lambda.Extern_var id }

  | Term.Lam(id, body) ->
     let var = fresh_tvar checker in
     Hashtbl.add_exn checker.env ~key:id ~data:var;
     infer_term checker checker.level body >>= fun body ->
     Ok Lambda.{ ty = Type.arrow var body.Lambda.ty
               ; expr = Lambda.Lam(id, body) }

  | Term.Let(lhs, rhs, body) ->
     in_new_level (fun checker ->
         infer_term checker safe_level rhs
       ) checker >>= fun rhs ->
     gen checker safe_level rhs.Lambda.ty >>= fun polyty ->
     Hashtbl.add_exn checker.env ~key:lhs ~data:polyty;
     infer_term checker safe_level body >>| fun body ->
     Lambda.{ ty = body.Lambda.ty; expr = Lambda.Let(lhs, rhs, body) }

  | Term.Let_rec(bindings, body) ->
     infer_rec_bindings checker safe_level bindings >>= fun bindings ->
     (* In the RHS of let-rec bindings, LHS names aren't quantified. Here,
        quantify them for the let-rec body. *)
     List.fold ~f:(fun acc (lhs, _) ->
         acc >>= fun () ->
         match Hashtbl.find checker.env lhs with
         | None -> Error Sequence.empty
         | Some ty ->
            gen checker safe_level ty >>| fun polyty ->
            Hashtbl.set checker.env ~key:lhs ~data:polyty
       ) ~init:(Ok ()) bindings
     >>= fun () ->
     infer_term checker safe_level body >>| fun body ->
     Lambda.{ ty = body.Lambda.ty; expr = Lambda.Let_rec(bindings, body) }

  | Term.Lit lit ->
     Ok { Lambda.ty =
            begin match lit with
            | Literal.Char _ -> Type.of_node (Type.Prim Type.Char)
            | Literal.Float _ -> Type.of_node (Type.Prim Type.Float)
            | Literal.Int _ -> Type.of_node (Type.Prim Type.Int)
            | Literal.String _ -> Type.of_node (Type.Prim Type.String)
            end
        ; expr = Lambda.Lit lit }

  | Term.Prim(op, ty) ->
     type_of_ast_polytype checker ty >>| fun ty ->
     { Lambda.ty = inst checker ty; expr = Lambda.Prim op }

  | Term.Ref value ->
     infer_term checker safe_level value >>| fun value ->
     Lambda.{ ty =
                Type.of_node
                  ( Type.App
                      ( Type.of_node(Type.Prim Type.Ref)
                      , value.Lambda.ty ) )
            ; expr = Lambda.Ref(value) }

  | Term.Seq(s, t) ->
     infer_term checker safe_level s >>= fun s ->
     infer_term checker safe_level t >>| fun t ->
     Lambda.{ ty = t.Lambda.ty; expr = Lambda.Seq(s, t) }

  | Term.Var reg ->
     match Hashtbl.find checker.env reg with
     | Some ty ->
        Ok Lambda.{ ty = inst checker ty; expr = Lambda.Local_var reg }
     | None -> Error (Sequence.return (Message.Unreachable "Tc expr var"))

and infer_branch checker safe_level scruts pats =
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
  in_new_level (fun _ ->
      f map scruts pats >>= fun map ->
      Map.fold ~f:(fun ~key ~data acc ->
          acc >>= fun () ->
          gen checker safe_level data >>| fun polyty ->
          let _ = Hashtbl.set checker.env ~key ~data:polyty in
          ()
        ) ~init:(Ok ()) map
    ) checker

and infer_rec_bindings checker safe_level bindings =
  let open Result.Monad_infix in
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
        infer_term checker safe_level rhs >>= fun rhs ->
        match acc, unify_types checker tvar rhs.Lambda.ty with
        | Ok acc, Ok () -> Ok ((lhs, rhs)::acc)
        | Ok _, Error e | Error e, Ok () -> Error e
        | Error e1, Error e2 -> Error (Sequence.append e1 e2)
      in List.fold_right ~f:f ~init:(Ok []) bindings
    ) checker
