open Base

type t =
  { types : (Ident.t, Type.adt) Hashtbl.t
  ; mutable env : (int, Type.t) Hashtbl.t
  ; mutable level : int
  ; tvargen : Type.vargen
  ; kvargen : Kind.vargen }

let create () =
  { types = Hashtbl.create (module Ident)
  ; env = Hashtbl.create (module Int)
  ; level = 0
  ; tvargen = Type.create_vargen ()
  ; kvargen = Kind.create_vargen () }

let fresh_tvar (checker : t) =
  Type.{ level_opt = Some checker.level
       ; node =
           Type.Var (Type.fresh_var checker.tvargen checker.level Kind.Mono) }

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

(** Unify two types, returning the unification errors *)
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

let rec infer checker =
  let open Result.Monad_infix in
  function
  | Term.Ann{term; _} -> infer checker term

  | Term.App(f, x) ->
     begin match infer checker f, infer checker x with
     | (Ok f_ty, Ok x_ty) ->
        let var = fresh_tvar checker in
        let result = unify_types checker f_ty (Type.arrow x_ty var) in
        result >>| fun () -> x_ty
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
     in types >>= fun types -> unify_many checker var types >>| fun () -> var

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

  | Term.Select(typename, constr, idx, data) ->
     begin match Hashtbl.find checker.types typename with
     | Some adt ->
        infer checker data >>= fun ty0 ->
        let ty1 = Type.type_of_constr typename adt constr in
        let result = unify_types checker ty0 (inst checker 0 ty1) in
        let _, tys = adt.Type.constrs.(constr) in
        result >>| fun () -> tys.(idx)
     | None -> Error (Sequence.return (Message.Unresolved_type typename))
     end

  | Term.Var reg ->
     match Hashtbl.find checker.env reg with
     | Some ty -> Ok (inst checker (checker.level + 1) ty)
     | None -> Error (Sequence.return Message.Unreachable)
