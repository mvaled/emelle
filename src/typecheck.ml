open Base

type t = {
    types : (Ident.t, Type.adt) Hashtbl.t;
    mutable env : (int, Type.t) Hashtbl.t;
    mutable level : int;
    mutable vargen : int;
  }

(** Perform the occurs check, returning true if the typevar occurs in the type.
    Adjusts the levels of unassigned typevars when necessary. *)
let rec occurs (uvar : Type.unassigned_var) = function
  | Type.App(tcon, targ) -> occurs uvar tcon && occurs uvar targ
  | Type.Nominal _ -> false
  | Type.Prim _ -> false
  | Type.Var cell ->
     match !cell with
     | Type.Assigned ty -> occurs uvar ty
     | Type.Unassigned u ->
        if u.id = uvar.id then
          true
        else (
          (* Adjust levels if necessary *)
          if u.level > uvar.level then (
            u.level <- uvar.level
          );
          false
        )

(** Unify two types, returning the unification errors *)
let rec unify lhs rhs =
  if not (phys_equal lhs rhs) then
    Sequence.empty
  else
    match lhs, rhs with
    | Type.App(lcon, larg), Type.App(rcon, rarg) ->
       Sequence.append (unify lcon rcon) (unify larg rarg)
    | Type.Nominal lstr, Type.Nominal rstr when (Ident.compare lstr rstr) = 0 ->
       Sequence.empty
    | Type.Prim lprim, Type.Prim rprim when Type.equal_prim lprim rprim ->
       Sequence.empty
    | (Type.Var v, ty) | (ty, Type.Var v) ->
       begin match !v with
       | Type.Unassigned uvar ->
          begin match ty with
          (* A variable occurring in itself is not an error *)
          | Type.Var {
              contents = Type.Unassigned uvar2
            } when uvar.id = uvar2.id ->
             Sequence.empty
          | _ when occurs uvar ty ->
             Sequence.return (Message.Unification_fail(lhs, rhs))
          | _ ->
             v := Type.Assigned ty;
             Sequence.empty
          end
       | Type.Assigned t -> unify t ty
       end
    | _ -> Sequence.return (Message.Unification_fail(lhs, rhs))

let unify_many ty =
  List.fold
    ~f:(fun acc next -> Sequence.append acc (unify ty next))
    ~init:Sequence.empty

let fresh_utvar checker =
  let old = checker.vargen in
  checker.vargen <- old + 1;
  Type.{ id = old; level = checker.level }

let in_new_level f st =
  st.level <- st.level + 1;
  let result = f st in
  st.level <- st.level - 1;
  result

(** Instantiate a type scheme by replacing type variables whose levels are
    greater than or equal to target_level with type variables of level
    checker.level *)
let inst checker target_level =
  let map = Hashtbl.create (module Int) in
  let rec helper = function
    | Type.App(tcon, targ) -> Type.App(helper tcon, helper targ)
    | Type.Var { contents = Type.Assigned ty } -> helper ty
    | (Type.Var { contents = Type.Unassigned uvar }) as var ->
       if uvar.Type.level < target_level then
         var
       else
         begin match Hashtbl.find map uvar.id with
         | Some uvar2 -> Type.Var (ref (Type.Unassigned uvar2))
         | None ->
            let uvar2 = fresh_utvar checker in
            Hashtbl.add_exn map ~key:uvar.id ~data:uvar2;
            Type.Var (ref (Type.Unassigned uvar2))
         end
    | ty -> ty
  in helper

let rec infer checker =
  let (>>=) = Result.(>>=) in
  function
  | Term.Ann{term; _} -> infer checker term

  | Term.App(f, x) ->
     begin match (infer checker f, infer checker x) with
     | (Ok f_ty, Ok x_ty) ->
        let var = Type.Var (ref (Type.Unassigned (fresh_utvar checker))) in
        let result = unify f_ty (App(App(Prim Arrow, x_ty), var)) in
        if Sequence.is_empty result then
          Ok x_ty
        else
          Error result
     | (Error f_err, Error x_err) -> Error (Sequence.append f_err x_err)
     | (err, Ok _) | (Ok _, err) -> err
     end

  | Term.Case(_, _, cases) ->
     let var = Type.Var (ref (Type.Unassigned (fresh_utvar checker))) in
     let types =
       Array.fold
         ~f:(fun acc next ->
           acc >>= fun acc ->
           (infer checker next) >>= fun ty ->
           Ok (ty::acc)
         ) ~init:(Ok []) cases
     in
     types >>= fun types ->
     let result = unify_many var types in
     if Sequence.is_empty result then
       Ok var
     else
       Error result

  | Term.Lam(id, body) ->
     let var = Type.Var (ref (Type.Unassigned (fresh_utvar checker))) in
     Hashtbl.add_exn checker.env ~key:id ~data:var;
     (infer checker body) >>= fun body_ty ->
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
             let ty = Type.Var (ref (Type.Unassigned (fresh_utvar checker))) in
             Hashtbl.add_exn checker.env ~key:lhs ~data:ty
           in
           List.iter ~f:f bindings;
           (* Type infer the RHS of each new binding and unify the result with
              the type variable *)
           let f acc (lhs, rhs) =
             let tvar = Hashtbl.find_exn checker.env lhs in
             Sequence.append acc (
                 match infer checker rhs with
                 | Ok ty -> unify tvar ty
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
        let result = unify ty0 (inst checker 0 ty1) in
        let tys = adt.Type.constr_types.(constr) in
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