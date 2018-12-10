(** The compiler must transform statically known curried functions into
    multi-parameter functions, remap the unique registers to stack and
    environment offsets, and compile decision trees into switch statements. *)

open Base

type t = {
    ctx : (Ident.t, Anf.operand) Hashtbl.t;
    (** Map from ids to variables *)
    free_vars : Anf.operand Queue.t; (** Free variables *)
    pat_ctx : Pattern.context;
    parent : t option;
    reg_gen : int ref;
  }

let create parent =
  let reg_gen = ref 0 in
  { ctx = Hashtbl.create (module Ident)
  ; free_vars = Queue.create ()
  ; pat_ctx = Pattern.create reg_gen
  ; parent
  ; reg_gen }

let fresh_register self =
  let id = !(self.reg_gen) in
  self.reg_gen := id + 1;
  id

let gen_base_occs self =
  let rec helper i = function
    | [] -> []
    | _::xs ->
       { Anf.id = Pattern.fresh_reg self.pat_ctx
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

let make_break self instr =
  let reg = fresh_register self in
  Anf.Let(reg, instr, Anf.Break (Anf.Register reg))

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
            cont (Anf.Fun ({ env = Queue.to_list self.free_vars
                           ; params = List.rev params
                           ; body = make_break self opcode }))
          )

(** Combine curried one-argument applications into a function call with all the
    arguments. *)
and flatten_app self count args f x ~cont =
  match f.Lambda.expr with
  | Lambda.App(f, x') ->
     operand_of_lambdacode self x' ~cont:(fun x' ->
         flatten_app self (count + 1) (x::args) f x' ~cont
       )
  | Lambda.Constr(tag, fields) ->
     let args = x::args in
     cont (
         if fields = count then
           Anf.Box ((Anf.Lit (Literal.Int tag))::args)
         else
           (* Handle a partially applied data constructor by generating a
              closure *)
           let rec gen_ascending_ints list = function
             | 0 -> list
             | n -> gen_ascending_ints ((n - 1)::list) (n - 1)
           in
           let rec gen_descending_free_vars n list = function
             | [] -> list
             | _::xs ->
                gen_descending_free_vars (n + 1) ((Anf.Free_var n)::list) xs
           in
           (* Closure parameters *)
           let params = gen_ascending_ints [] (fields - count) in
           (* Operand list of the parameters *)
           let regs_of_params =
             List.map ~f:(fun reg -> Anf.Register reg) params
           in
           (* The already known arguments, accessed from within the closure and
              backwards *)
           let free_vars_rev = gen_descending_free_vars 0 [] args in
           (* The final operands of the box opcode *)
           let box_contents =
             (Anf.Lit (Literal.Int tag))::
               (List.rev_append free_vars_rev regs_of_params)
           in
           let proc =
             { Anf.env = args
             ; params
             ; body = make_break self (Anf.Box box_contents) }
           in Anf.Fun proc
       )
  | Lambda.Ref ->
     cont (Anf.Ref x)
  | _ ->
     operand_of_lambdacode self f ~cont:(fun f ->
         cont (Anf.Call(f, x, args))
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

(** Returns a list of parameters (bound variables) of the branch sorted by
    [Ident.t] *)
and compile_branch self bindings =
  let open Result.Monad_infix in
  Set.fold_right ~f:(fun id acc ->
      acc >>= fun params ->
      let param = fresh_register self in
      match Hashtbl.add self.ctx ~key:id ~data:(Register param) with
      | `Duplicate ->
         Error (Sequence.return
                  (Message.Unreachable "Lower compile_branch"))
      | `Ok -> Ok (param::params)
    ) ~init:(Ok []) bindings

(** Convert a [Lambda.t] into an [instr]. *)
and instr_of_lambdacode self lambda ~cont =
  let open Result.Monad_infix in
  match lambda.Lambda.expr with
  | Lambda.App(f, x) ->
     operand_of_lambdacode self x ~cont:(fun x ->
         flatten_app self 1 [] f x ~cont
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
             compile_branch self bindings >>= fun params ->
             instr_of_lambdacode self body ~cont:(fun opcode ->
                 Ok (make_break self opcode)
               )
             >>| fun body -> (params, body)::list
           ) ~init:(Ok []) branches
         >>= fun branches ->
         cont (Anf.Case(scruts, tree, branches))
       )
  | Lambda.Constr _ | Lambda.Extern_var _
  | Lambda.Local_var _ | Lambda.Lit _ ->
     operand_of_lambdacode self lambda ~cont:(fun operand ->
         cont (Anf.Load operand)
       )
  | Lambda.Lam(reg, body) ->
     let self = create (Some self) in
     proc_of_lambda self [] reg body ~cont
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
  | Lambda.Ref ->
     cont (Anf.Fun
             { env = []
             ; params = [0]
             ; body = make_break self (Anf.Ref (Anf.Register 0)) })
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
  | Lambda.Constr(tag, size) ->
     let rec f acc = function
       | 0 -> acc
       | n -> f ((n - 1)::acc) (n - 1)
     in
     let params = f [] size in
     let vars = List.map ~f:(fun reg -> Anf.Register reg) params in
     let proc =
       { Anf.env = []
       ; params
       ; body = make_break self (Anf.Box((Anf.Lit (Literal.Int tag))::vars)) }
     in
     let var = fresh_register self in
     cont (Anf.Register var) >>| fun body ->
     Anf.Let(var, Anf.Fun proc, body)
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
