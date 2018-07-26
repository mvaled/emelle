open Base

type t = {
    mutable env : Env.t;
    mutable level : int;
    mutable vargen : int;
  }

let fresh_utvar checker =
  let old = checker.vargen in
  checker.vargen <- old + 1;
  Type.{ id = old; level = checker.level }

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
        let result = Type.unify f_ty (App(App(Prim Arrow, x_ty), var)) in
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
     let result = Type.unify_many var types in
     if Sequence.is_empty result then
       Ok var
     else
       Error result
  | Term.Lam(id, body) ->
     let var = Type.Var (ref (Type.Unassigned (fresh_utvar checker))) in
     checker.env <- Env.extend checker.env;
     let _ = Env.define_term checker.env id var in
     (infer checker body) >>= fun body_ty ->
     Ok (Type.App(Type.App(Type.Prim Type.Arrow, var), body_ty))
  (* TODO *)
  | Term.Let _ -> Error Sequence.empty
  | Term.Let_rec _ -> Error Sequence.empty
  | Term.Select _ -> Error Sequence.empty
  | Term.Var _ -> Error Sequence.empty
