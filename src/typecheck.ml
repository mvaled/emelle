open Base

type t =
  { types : (Ident.t, Type.adt) Hashtbl.t
  ; mutable env : (int, Type.t) Hashtbl.t
  ; mutable level : int
  ; tvargen : Type.vargen
  ; kvargen : Kind.vargen }

let fresh_tvar checker =
  Type.Var (Type.fresh_var checker.tvargen checker.level Kind.Mono)

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

let rec kind_of_type checker =
  let open Result.Monad_infix in
  function
  | Type.App(tcon, targ) ->
     kind_of_type checker targ >>= fun argkind ->
     kind_of_type checker tcon >>= fun conkind ->
     let kvar = Kind.Var (Kind.fresh_var checker.kvargen) in
     unify_kinds conkind (Kind.Poly(argkind, kvar)) >>= fun () ->
     Ok kvar
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

(** Unify two types, returning the unification errors *)
let rec unify_types checker lhs rhs =
  if phys_equal lhs rhs then
    Sequence.empty
  else
    match lhs, rhs with
    | Type.App(lcon, larg), Type.App(rcon, rarg) ->
       Sequence.append
         (unify_types checker lcon rcon)
         (unify_types checker larg rarg)
    | Type.Nominal lstr, Type.Nominal rstr when (Ident.compare lstr rstr) = 0 ->
       Sequence.empty
    | Type.Prim lprim, Type.Prim rprim when Type.equal_prim lprim rprim ->
       Sequence.empty
    | (Type.Var v, ty) | (ty, Type.Var v) ->
       begin match v.ty with
       | None ->
          begin match ty with
          (* A variable occurring in itself is not an error *)
          | Type.Var { ty = None; id; _ } when (compare v.id id) = 0 ->
             Sequence.empty
          | _ when Type.occurs v ty ->
             Sequence.return (Message.Type_unification_fail(lhs, rhs))
          | _ ->
             begin match kind_of_type checker ty with
             | Ok kind ->
                begin match unify_kinds kind v.kind with
                | Ok () -> Sequence.empty
                | Error e -> e
                end
             | Error e -> e
             end
          end
       | Some t -> unify_types checker t ty
       end
    | _ -> Sequence.return (Message.Type_unification_fail(lhs, rhs))

let unify_many checker ty =
  List.fold
    ~f:(fun acc next -> Sequence.append acc (unify_types checker ty next))
    ~init:Sequence.empty

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
  let rec helper = function
    | Type.App(tcon, targ) -> Type.App(helper tcon, helper targ)
    | Type.Var { ty = Some ty; _ } -> helper ty
    | Type.Var ({ ty = None; level; _ } as var) as ty ->
       if level < target_level then
         ty
       else
         begin match Hashtbl.find map var with
         | Some var2 -> var2
         | None ->
            let var2 =
              Type.Var (Type.fresh_var checker.tvargen checker.level var.kind)
            in
            Hashtbl.add_exn map ~key:var ~data:var2;
            var2
         end
    | ty -> ty
  in helper

let rec infer checker =
  let open Result.Monad_infix in
  function
  | Term.Ann{term; _} -> infer checker term

  | Term.App(f, x) ->
     begin match (infer checker f, infer checker x) with
     | (Ok f_ty, Ok x_ty) ->
        let var = fresh_tvar checker in
        let result = unify_types checker f_ty (App(App(Prim Arrow, x_ty), var))
        in
        if Sequence.is_empty result then
          Ok x_ty
        else
          Error result
     | (Error f_err, Error x_err) -> Error (Sequence.append f_err x_err)
     | (err, Ok _) | (Ok _, err) -> err
     end

  | Term.Case(_, _, cases) ->
     let var = fresh_tvar checker in
     let types =
       Array.fold
         ~f:(fun acc next ->
           acc >>= fun acc ->
           (infer checker next) >>= fun ty ->
           Ok (ty::acc)
         ) ~init:(Ok []) cases
     in
     types >>= fun types ->
     let result = unify_many checker var types in
     if Sequence.is_empty result then
       Ok var
     else
       Error result

  | Term.Lam(id, body) ->
     let var = fresh_tvar checker in
     Hashtbl.add_exn checker.env ~key:id ~data:var;
     infer checker body >>= fun body_ty ->
     Ok (Type.App(Type.App(Type.Prim Type.Arrow, var), body_ty))

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
             Sequence.append acc (
                 match infer checker rhs with
                 | Ok ty -> unify_types checker tvar ty
                 | Error e -> e
               )
           in List.fold ~f:f ~init:Sequence.empty bindings
         ) checker
     in
     if Sequence.is_empty result then (
       infer checker body
     ) else
       Error result

  | Term.Select(typename, constr, idx, data) ->
     begin match Hashtbl.find checker.types typename with
     | Some adt ->
        infer checker data >>= fun ty0 ->
        let ty1 = Type.type_of_constr typename adt constr in
        let result = unify_types checker ty0 (inst checker 0 ty1) in
        let _, tys = adt.Type.constrs.(constr) in
        if Sequence.is_empty result then
          Ok (tys.(idx))
        else
          Error result
     | None -> Error (Sequence.return (Message.Unresolved_type typename))
     end

  | Term.Var reg ->
     match Hashtbl.find checker.env reg with
     | Some ty -> Ok (inst checker (checker.level + 1) ty)
     | None -> Error (Sequence.return Message.Unreachable)
