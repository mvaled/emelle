open Base

type kind =
  | Mono
  | Poly of kind * kind
  | KVar of kvar
and kvar =
  { k_id : int
  ; mutable k_kind : kind option }

let compare_kvar l r = compare l.k_id r.k_id

type tvar =
  { t_id : int
  ; t_kind : kind }

let compare_tvar l r = compare l.t_id r.t_id

type ty =
  | App of ty * ty
  | Nominal of Ident.t
  | Arrow
  | Int
  | Float
  | TVar of tvar

type adt =
  { typeparams : tvar list
  ; constrs : (string, int * ty list) Hashtbl.t }

let kind_of_adt adt =
  let rec f = function
    | [] -> Mono
    | x::xs -> Poly(x.t_kind, f xs)
  in f adt.typeparams

type t =
  { type_env : (Ident.t, ty) Hashtbl.t
  ; typedefs : (Ident.t, Type.adt) Hashtbl.t
  ; curr_typedefs : (Ident.t, adt) Hashtbl.t
  ; mutable kvar_gen : int
  ; mutable tvar_gen : int }

let fresh_kvar st =
  st.kvar_gen <- st.kvar_gen + 1;
  { k_id = st.kvar_gen - 1; k_kind = None }

let fresh_tvar st =
  st.tvar_gen <- st.tvar_gen + 1;
  { t_id = st.tvar_gen - 1; t_kind = KVar (fresh_kvar st) }

let rec type_of_monotype st =
  let open Result.Monad_infix in
  function
  | Ast.TApp(f, x) ->
     type_of_monotype st f >>= fun f ->
     type_of_monotype st x >>| fun x ->
     App(f, x)
  | Ast.TArrow -> Ok Arrow
  | Ast.TFloat -> Ok Float
  | Ast.TInt -> Ok Int
  | Ast.TVar id ->
     match Hashtbl.find st.type_env id with
     | Some x -> Ok x
     | None -> Error (Sequence.return (Message.Unresolved_type id))

let types_of_monotypes st types =
  let open Result.Monad_infix in
  List.fold_right
    ~f:(fun ty acc ->
      acc >>= fun list ->
      type_of_monotype st ty >>| fun ty ->
      ty::list
    ) ~init:(Ok []) types

let rec occurs kvar = function
  | Mono -> false
  | Poly(k1, k2) -> occurs kvar k1 && occurs kvar k2
  | KVar { k_kind = Some kind; _ } -> occurs kvar kind
  | KVar { k_id; _ } when k_id = kvar.k_id -> true
  | _ -> false

let rec unify l r =
  let open Result.Monad_infix in
  match l, r with
  | Mono, Mono -> Ok ()
  | Poly(a, b), Poly(c, d) ->
     unify a c >>= fun () ->
     unify b d
  | KVar { k_id = l; _ }, KVar { k_id = r; _ } when l = r -> Ok ()
  | KVar { k_kind = Some k1; _ }, k2 -> unify k1 k2
  | KVar kvar, kind ->
     if occurs kvar kind then
       Error (Sequence.return (Message.Mismatched_kinds))
     else (
       kvar.k_kind <- Some kind;
       Ok ()
     )
  | l, r -> unify r l

let rec kind_of_type_kind = function
  | Type.Mono -> Mono
  | Type.Poly(l, r) -> Poly(kind_of_type_kind l, kind_of_type_kind r)

let rec type_kind_of_kind = function
  | Mono -> Type.Mono
  | Poly(l, r) -> Type.Poly(type_kind_of_kind l, type_kind_of_kind r)
  | KVar { k_kind = Some k; _ } -> type_kind_of_kind k
  | KVar { k_kind = None; _ } -> Type.Mono

let rec kind_of_type st =
  let open Result.Monad_infix in
  function
  | App(f, x) ->
     kind_of_type st f >>= fun f ->
     kind_of_type st x >>= fun x ->
     let kvar = KVar (fresh_kvar st) in
     unify f (Poly(x, kvar)) >>| fun () ->
     kvar
  | Nominal id ->
     begin match Hashtbl.find st.typedefs id with
     | Some adt -> Ok (kind_of_type_kind (Type.kind_of_adt adt))
     | None ->
        match Hashtbl.find st.curr_typedefs id with
        | Some adt -> Ok (kind_of_adt adt)
        | None -> Error (Sequence.return (Message.Unresolved_type id))
     end
  | Arrow -> Ok (Poly(Mono, Mono))
  | Float -> Ok Mono
  | Int -> Ok Mono
  | TVar tvar -> Ok tvar.t_kind
