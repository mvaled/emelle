(** The compiler must transform statically known curried functions into
    multi-parameter functions, remap the unique registers to stack and
    environment offsets, and compile decision trees into switch statements. *)

open Base

type t = {
    ctx : (Ident.t, Anf.operand) Hashtbl.t;
    (** Map from ids to variables *)
    free_vars : Anf.operand Queue.t; (** Array of free variables *)
    pat_ctx : Pattern.context;
    parent : t option;
    mutable frame_offset : int;
  }

let create () =
  { ctx = Hashtbl.create (module Ident)
  ; free_vars = Queue.create ()
  ; pat_ctx = Pattern.create ()
  ; parent = None
  ; frame_offset = 0 }

let fresh_register self =
  let offset = self.frame_offset in
  self.frame_offset <- offset + 1;
  offset

let gen_base_occs self =
  let rec helper i = function
    | [] -> []
    | _::xs ->
       { Anf.id = Pattern.fresh_occ self.pat_ctx
       ; node = Anf.Index i
       ; parent = None
       }::(helper (i + 1) xs)
  in helper 0

let rec free_var self id =
  (* I would use Hashtbl.find_or_add here, but the callback it takes isn't
     monadic, and my code is able to fail via the result monad. *)
  Hashtbl.find_and_call self.ctx id
    ~if_found:(fun x -> Ok x)
    ~if_not_found:(fun id ->
      let open Result.Monad_infix in
      match self.parent with
      | Some parent ->
         free_var parent id >>= fun var ->
         let _ =
           Hashtbl.add
             self.ctx ~key:id ~data:(Anf.Free_var (Queue.length self.free_vars))
         in
         Queue.enqueue self.free_vars var;
         Ok (Anf.Free_var (Queue.length self.free_vars))
      | None ->
         Error (Sequence.return (Message.Unreachable "Lower free_var"))
    )

(** Combine statically known nested unary functions into multi-argument procs *)
let rec proc_of_lambda self params id body ~cont =
  let reg = fresh_register self in
  match Hashtbl.add self.ctx ~key:id ~data:(Register reg) with
  | `Duplicate ->
     Error (Sequence.return (Message.Unreachable "Lower uncurry"))
  | `Ok ->
     match body.Lambda.expr with
     | Lambda.Lam(id, body) ->
        proc_of_lambda self (reg::params) id body ~cont
     | _ ->
        instr_of_lambdacode self body ~cont:(fun opcode ->
            cont (Anf.Fun ({ env = Queue.to_array self.free_vars
                           ; params = List.rev params
                           ; body = Anf.Return opcode }))
          )

(** Combine curried one-argument applications into a function call with all the
    arguments. *)
and flatten_app self args f x ~cont =
  match f.Lambda.expr with
  | Lambda.App(f, x') ->
     operand_of_lambdacode self x' ~cont:(fun x' ->
         flatten_app self (x::args) f x' ~cont
       )
  | _ ->
     operand_of_lambdacode self f ~cont:(fun f ->
         cont (Anf.Call(f, x, Array.of_list args))
       )

(** This function implements the compilation of a case expression, as used in
    [instr_of_lambdacode]. *)
and compile_case self scruts matrix ~cont =
  let open Result.Monad_infix in
  let rec loop list = function
    | scrut::scruts ->
       operand_of_lambdacode self scrut ~cont:(fun operand ->
           loop (operand::list) scruts
         )
    | [] ->
       let scruts = List.rev list in
       Pattern.decision_tree_of_matrix
         self.pat_ctx (gen_base_occs self scruts) matrix
       >>= fun tree -> cont (scruts, tree)
  in loop [] scruts

and compile_branch self bindings ~cont =
  let open Result.Monad_infix in
  Set.fold ~f:(fun cont id () ->
      let var = fresh_register self in
      match Hashtbl.add self.ctx ~key:id ~data:(Register var) with
      | `Duplicate ->
         Error (Sequence.return
                  (Message.Unreachable "Lower compile_branch"))
      | `Ok ->
         cont () >>| fun body -> Anf.Let(var, Anf.Pop, body)
    ) ~init:cont bindings ()

(** Convert a [Lambda.t] into an [instr]. *)
and instr_of_lambdacode self lambda ~cont =
  let open Result.Monad_infix in
  match lambda.Lambda.expr with
  | Lambda.App(f, x) ->
     operand_of_lambdacode self x ~cont:(fun x ->
         flatten_app self [] f x ~cont
       )
  | Lambda.Assign(lhs, rhs) ->
     operand_of_lambdacode self lhs ~cont:(fun lhs ->
         operand_of_lambdacode self rhs ~cont:(fun rhs ->
             cont (Anf.Assign(lhs, rhs))
           )
       )
  | Lambda.Case(scruts, matrix, branches) ->
     compile_case self scruts matrix ~cont:(fun (scruts, tree) ->
         List.fold_right ~f:(fun (bindings, body) acc ->
             acc >>= fun list ->
             compile_branch self bindings ~cont:(fun () ->
                 instr_of_lambdacode self body ~cont:(fun opcode ->
                     Ok (Anf.Return opcode)
                   )
               )
             >>| fun branch -> branch::list
           ) ~init:(Ok []) branches
         >>= fun branches ->
         cont (Anf.Case(scruts, tree, Array.of_list branches))
       )
  | Lambda.Constr _ | Lambda.Extern_var _ | Lambda.Local_var _ | Lambda.Lit _ ->
     operand_of_lambdacode self lambda ~cont:(fun operand ->
         cont (Anf.Load operand)
       )
  | Lambda.Lam(reg, body) ->
     let self =
       { self with
         ctx = Hashtbl.create (module Ident)
       ; free_vars = Queue.create ()
       ; parent = Some self
       ; frame_offset = 0 }
     in proc_of_lambda self [] reg body ~cont
  | Lambda.Let(lhs, rhs, body) ->
     instr_of_lambdacode self rhs ~cont:(fun rhs ->
         let var = fresh_register self in
         match Hashtbl.add self.ctx ~key:lhs ~data:(Register var) with
         | `Duplicate ->
            Error (Sequence.return
                     (Message.Unreachable "Bytecode instr_of_lambdacode"))
         | `Ok ->
            instr_of_lambdacode self body ~cont >>| fun body ->
            Anf.Let(var, rhs, body)
       )
  | Lambda.Let_rec(bindings, body) ->
     compile_letrec self bindings ~cont:(fun bindings ->
         instr_of_lambdacode self body ~cont >>| fun body ->
         Anf.Let_rec(bindings, body)
       )
  | Lambda.Prim op -> cont (Prim op)
  | Lambda.Ref value ->
     operand_of_lambdacode self value ~cont:(fun value ->
         cont (Anf.Ref value)
       )
  | Lambda.Seq(s, t) ->
     instr_of_lambdacode self s ~cont:(fun s ->
         instr_of_lambdacode self t ~cont >>| fun t ->
         Anf.Seq(s, t)
       )

(** This function implements the compilation of a let-rec expression, as used in
    [instr_of_lambdacode]. *)
and compile_letrec self bindings ~cont =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc (lhs, rhs) ->
      acc >>= fun list ->
      let var = fresh_register self in
      match Hashtbl.add self.ctx ~key:lhs ~data:(Anf.Register var) with
      | `Duplicate ->
         Error (Sequence.return (Message.Unreachable "Bytecode comp letrec"))
      | `Ok -> Ok ((var, rhs)::list)
    ) ~init:(Ok []) bindings >>= fun list ->
  let rec f bindings = function
    | (lhs, rhs)::rest ->
       instr_of_lambdacode self rhs ~cont:(fun opcode ->
           f ((lhs, opcode)::bindings) rest
         )
    | [] -> cont bindings
  in f [] list

(** [operand_of_lambdacode self lambda cont] converts [lambda] into an
    [operand], passes it to the continuation [cont], and returns an [instr]. *)
and operand_of_lambdacode self lambda ~cont =
  let open Result.Monad_infix in
  match lambda.Lambda.expr with
  | Lambda.Constr size -> cont (Anf.Constr size)
  | Lambda.Extern_var id -> cont (Anf.Extern_var id)
  | Lambda.Lit lit -> cont (Anf.Lit lit)
  | Lambda.Local_var reg ->
     free_var self reg >>= fun var -> cont var
  | _ ->
     instr_of_lambdacode self lambda ~cont:(fun rhs ->
         let var = fresh_register self in
         cont (Anf.Register var) >>| fun body ->
         Anf.Let(var, rhs, body)
       )
