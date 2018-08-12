open Base

type t = {
    types : (Ident.t, Type.adt) Hashtbl.t;
    mutable env : (int, Type.t) Hashtbl.t;
    mutable level : int;
    mutable vargen : int;
  }

let rec kind_of_type checker =
  let open Result.Monad_infix in
  function
  | Type.App(tcon, targ) ->
     kind_of_type checker targ >>= fun kind ->
     kind_of_type checker tcon >>=
       begin function
         | Type.Poly(k1, k2) ->
            if Type.equals_kind kind k1 then
              Ok k2
            else
              Error (Sequence.return Message.Kind_mismatch)
         | Type.Mono -> Error Sequence.empty
       end
  | Type.Nominal id ->
     begin match Hashtbl.find checker.types id with
     | Some adt ->
        Ok (Type.curry_kinds
              (List.map ~f:(fun uvar -> uvar.kind) adt.typeparams)
              Type.Mono)
     | None -> Error (Sequence.return (Message.Unresolved_type id))
     end
  | Type.Prim Type.Arrow -> Ok Type.Mono
  | Type.Prim Type.Float -> Ok Type.Mono
  | Type.Prim Type.Int -> Ok Type.Mono
  | Type.Var { contents = Type.Assigned ty } -> kind_of_type checker ty
  | Type.Var { contents = Type.Unassigned uvar } -> Ok uvar.kind

(** Perform the occurs check, returning true if the typevar occurs in the type.
    Adjusts the levels of unassigned typevars when necessary. *)
let rec occurs (uvar : Type.UVar.t) = function
  | Type.App(tcon, targ) -> occurs uvar tcon && occurs uvar targ
  | Type.Nominal _ -> false
  | Type.Prim _ -> false
  | Type.Var cell ->
     match !cell with
     | Type.Assigned ty -> occurs uvar ty
     | Type.Unassigned u ->
        if (Type.UVar.compare u uvar) = 0 then
          true
        else (
          (* Adjust levels if necessary *)
          if u.level > uvar.level then (
            u.level <- uvar.level
          );
          false
        )

(** Unify two types, returning the unification errors *)
let rec unify checker lhs rhs =
  if not (phys_equal lhs rhs) then
    Sequence.empty
  else
    match lhs, rhs with
    | Type.App(lcon, larg), Type.App(rcon, rarg) ->
       Sequence.append (unify checker lcon rcon) (unify checker larg rarg)
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
            } when (Type.UVar.compare uvar uvar2) = 0 ->
             Sequence.empty
          | _ when occurs uvar ty ->
             Sequence.return (Message.Unification_fail(lhs, rhs))
          | ty ->
             begin match kind_of_type checker ty with
             | Ok kind ->
                if Type.equals_kind kind uvar.kind then (
                  v := Type.Assigned ty;
                  Sequence.empty
                ) else
                  Sequence.return Message.Kind_mismatch
             | Error e -> e
             end
          end
       | Type.Assigned t -> unify checker t ty
       end
    | _ -> Sequence.return (Message.Unification_fail(lhs, rhs))

let unify_many checker ty =
  List.fold
    ~f:(fun acc next -> Sequence.append acc (unify checker ty next))
    ~init:Sequence.empty

let fresh_utvar checker kind =
  let old = checker.vargen in
  checker.vargen <- old + 1;
  Type.UVar.{ id = Type.UVar.Gen old
            ; kind = kind
            ; level = checker.level
            ; name = None }

let in_new_level f st =
  st.level <- st.level + 1;
  let result = f st in
  st.level <- st.level - 1;
  result

(** Instantiate a type scheme by replacing type variables whose levels are
    greater than or equal to target_level with type variables of level
    checker.level *)
let inst checker target_level =
  let map = Hashtbl.create (module Type.UVar) in
  let rec helper = function
    | Type.App(tcon, targ) -> Type.App(helper tcon, helper targ)
    | Type.Var { contents = Type.Assigned ty } -> helper ty
    | (Type.Var { contents = Type.Unassigned uvar }) as var ->
       if uvar.Type.UVar.level < target_level then
         var
       else
         begin match Hashtbl.find map uvar with
         | Some uvar2 -> Type.of_uvar uvar2
         | None ->
            let uvar2 = fresh_utvar checker uvar.kind in
            Hashtbl.add_exn map ~key:uvar ~data:uvar2;
            Type.of_uvar uvar2
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
        let var = Type.of_uvar (fresh_utvar checker Type.Mono) in
        let result = unify checker f_ty (App(App(Prim Arrow, x_ty), var)) in
        if Sequence.is_empty result then
          Ok x_ty
        else
          Error result
     | (Error f_err, Error x_err) -> Error (Sequence.append f_err x_err)
     | (err, Ok _) | (Ok _, err) -> err
     end

  | Term.Case(_, _, cases) ->
     let var = Type.of_uvar (fresh_utvar checker Type.Mono) in
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
     let var = Type.of_uvar (fresh_utvar checker Type.Mono) in
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
             let ty = Type.of_uvar (fresh_utvar checker Type.Mono) in
             Hashtbl.add_exn checker.env ~key:lhs ~data:ty
           in
           List.iter ~f:f bindings;
           (* Type infer the RHS of each new binding and unify the result with
              the type variable *)
           let f acc (lhs, rhs) =
             let tvar = Hashtbl.find_exn checker.env lhs in
             Sequence.append acc (
                 match infer checker rhs with
                 | Ok ty -> unify checker tvar ty
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
        let result = unify checker ty0 (inst checker 0 ty1) in
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
