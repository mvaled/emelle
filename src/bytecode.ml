(** The compiler must transform statically known curried functions into
    multi-parameter functions, remap the unique registers to stack and
    environment offsets, and compile decision trees into switch statements. *)

open Base

type occurrence = operand * int list

and decision_tree =
  | Fail
  | Leaf of occurrence list * int
  | Switch of occurrence * (int * decision_tree) list * decision_tree

and operand =
  | Bound_var of int (** On the stack frame *)
  | Cons of int
  | Extern_var of Ident.t
  | Free_var of int (** In the proc's environment *)
  | Lit of Literal.t

and instr =
  | Box of operand list
  | Call of operand * operand * operand array
    (** proc, first arg, rest args *)
  | Case of operand list * decision_tree * instr array
    (** discrs, decision tree, jump table *)
  | Fun of proc
  | Load of operand
  | Local of instr * instr
  | Local_rec of instr list * instr
  | Pop_match
  | Prim of string

and proc = {
    env : operand array; (** The captured variables *)
    arity : int; (** The number of parameters that the function accepts *)
    body : instr;
  }

type t = {
    ctx : (Register.t, operand) Hashtbl.t;
    (** Map from registers to variables *)
    free_vars : operand Queue.t; (** Array of free variables *)
    parent : t option;
    mutable frame_offset : int; (** Current offset from frame pointer *)
  }

let create () =
  { ctx = Hashtbl.create (module Register)
  ; free_vars = Queue.create ()
  ; parent = None
  ; frame_offset = 0 }

let fresh_bound_var self =
  let offset = self.frame_offset in
  self.frame_offset <- offset + 1;
  Bound_var offset

let rec free_var self reg =
  (* I would use Hashtbl.find_or_add here, but the callback it takes isn't
     monadic, and my code is able to fail via the result monad. *)
  Hashtbl.find_and_call self.ctx reg
    ~if_found:(fun x -> Ok x)
    ~if_not_found:(fun reg ->
      let open Result.Monad_infix in
      match self.parent with
      | Some parent ->
         free_var parent reg >>= fun var ->
         let _ =
           Hashtbl.add
             self.ctx ~key:reg ~data:(Free_var (Queue.length self.free_vars))
         in
         Queue.enqueue self.free_vars var;
         Ok (Free_var (Queue.length self.free_vars))
      | None ->
         Error (Sequence.return (Message.Unreachable "Bytecode free_var"))
    )

(** Reverse the occurrence from the pattern match compilation into a addressing
    path. *)
let convert_occurrence scruts =
  (* The structure of this function is similar to left fold. *)
  let rec helper acc = function
    | Pattern.Cons(idx, occurrence) -> helper (idx::acc) occurrence
    | Pattern.Nil idx -> (scruts.(idx), acc)
  in helper []

let rec convert_decision_tree self scruts = function
  | Pattern.Fail -> Fail
  | Pattern.Leaf(bindings, jump) ->
     let bound_occs =
       Map.fold_right ~f:(fun ~key:_ ~data:occ acc ->
           (convert_occurrence scruts occ)::acc
         ) ~init:[] bindings
     in Leaf(bound_occs, jump)
  | Pattern.Switch(occ, subtrees, default) ->
     let occ = convert_occurrence scruts occ in
     let subtrees =
       Hashtbl.fold ~f:(fun ~key:constr ~data:tree acc ->
           (constr, convert_decision_tree self scruts tree)::acc
         ) ~init:[] subtrees
     in
     let default = convert_decision_tree self scruts default in
     Switch(occ, subtrees, default)
  | Pattern.Swap(_, tree) -> convert_decision_tree self scruts tree

(** Combine statically known nested unary functions into multi-argument procs *)
let rec proc_of_lambda self reg body =
  let open Result.Monad_infix in
  match Hashtbl.add self.ctx ~key:reg ~data:(fresh_bound_var self) with
  | `Duplicate ->
     Error (Sequence.return (Message.Unreachable "Bytecode uncurry"))
  | `Ok ->
     match body.Lambda.expr with
     | Lambda.Lam(reg, body) ->
        proc_of_lambda self reg body
     | _ ->
        let arity = self.frame_offset + 1 in
        instr_of_lambdacode self body >>| fun body ->
        { env = Queue.to_array self.free_vars; arity; body }

(** Combine curried one-argument applications into a function call with all the
    arguments. *)
and flatten_app self (args : operand list) (f : Lambda.t) (x : operand) =
  match f.Lambda.expr with
  | Lambda.App(f, x') ->
     operand_of_lambdacode self x' ~cont:(fun x' ->
         flatten_app self (x::args) f x'
       )
  | _ ->
     operand_of_lambdacode self f ~cont:(fun f ->
         Ok (Call(f, x, Array.of_list args))
       )

(** This function implements the compilation of a case expression, as used in
    [instr_of_lambdacode]. It is a separate function and takes a function
    parameter because the module compilation pipeline needs to do something
    almost exactly the same and I didn't want to repeat such long code. *)
(* It has an explicit type annotation because I want it to be polymorphic
   over ['a], but it is in a let-rec that would force the ['a] to not get
   universally quantified if inferred. *)
and compile_case
    : 'a . t -> Lambda.t list -> int Pattern.decision_tree
      -> ((Register.t, Register.comparator_witness) Set.t * 'a) list
      -> ('a -> (instr, Message.error Sequence.t) Result.t)
      -> (instr, Message.error Sequence.t) Result.t
  = fun self scruts tree branches f ->
  let open Result.Monad_infix in
  let rec loop list = function
    | scrut::scruts ->
       operand_of_lambdacode self scrut ~cont:(fun operand ->
           loop (operand::list) scruts
         )
    | [] ->
       let scruts = List.rev list in
       List.fold_right ~f:(fun (regs_set, action) acc ->
           acc >>= fun list ->
           Set.fold_right ~f:(fun reg acc ->
               acc >>= fun list ->
               self.frame_offset <- self.frame_offset + 1;
               let var = Bound_var self.frame_offset in
               match Hashtbl.add self.ctx ~key:reg ~data:var with
               | `Duplicate ->
                  Error (Sequence.return
                           (Message.Unreachable "bytecode case"))
               | `Ok -> Ok (reg::list)
             ) ~init:(Ok []) regs_set
           >>= fun regs_list ->
           let rec loop = function
             | [] -> f action
             | _::regs ->
                loop regs >>| fun body -> Local(Pop_match, body)
           in
           loop regs_list
           >>| fun instr ->
           self.frame_offset <- self.frame_offset + Set.length regs_set;
           instr::list
         ) ~init:(Ok []) branches
       >>| fun branches ->
       let scruts_arr = Array.of_list scruts in
       let tree = convert_decision_tree self scruts_arr tree in
       Case(scruts, tree, Array.of_list branches)
  in loop [] scruts

(** Convert a [Lambda.t] into an [instr]. *)
and instr_of_lambdacode self lambda =
  let open Result.Monad_infix in
  match lambda.Lambda.expr with
  | Lambda.App(f, x) ->
     operand_of_lambdacode self x ~cont:(fun x -> flatten_app self [] f x)
  | Lambda.Case(scruts, tree, branches) ->
     compile_case self scruts tree branches (fun lambda ->
         instr_of_lambdacode self lambda
       )
  | Lambda.Constr _ | Lambda.Extern_var _ | Lambda.Local_var _ | Lambda.Lit _ ->
     operand_of_lambdacode self lambda ~cont:(fun operand -> Ok (Load operand))
  | Lambda.Lam(reg, body) ->
     let st =
       { ctx = Hashtbl.create (module Register)
       ; free_vars = Queue.create ()
       ; parent = Some self
       ; frame_offset = 0 }
     in proc_of_lambda st reg body >>| fun proc -> Fun proc
  | Lambda.Let(lhs, rhs, body) ->
     instr_of_lambdacode self rhs >>= fun rhs ->
     let var = fresh_bound_var self in
     begin match Hashtbl.add self.ctx ~key:lhs ~data:var with
     | `Duplicate ->
        Error (Sequence.return
                 (Message.Unreachable "Bytecode instr_of_lambdacode"))
     | `Ok ->
        instr_of_lambdacode self body >>| fun body ->
        self.frame_offset <- self.frame_offset - 1;
        Local(rhs, body)
     end
  | Lambda.Let_rec(bindings, body) ->
     compile_letrec self bindings (fun _ ->
         instr_of_lambdacode self body
       )
  | Lambda.Prim op -> Ok (Prim op)

(** This function implements the compilation of a let-rec expression, as used in
    [instr_of_lambdacode]. It is a separate function and takes a function
    parameter because the module compilation pipeline needs to do something
    almost exactly the same and I didn't want to repeat such long code. *)
and compile_letrec self bindings f =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc (lhs, _) ->
      acc >>= fun () ->
      let var = fresh_bound_var self in
      match Hashtbl.add self.ctx ~key:lhs ~data:var with
      | `Duplicate ->
         Error (Sequence.return (Message.Unreachable "Bytecode comp letrec"))
      | `Ok -> Ok()
    ) ~init:(Ok ()) bindings >>= fun () ->
  List.fold_right ~f:(fun (_, rhs) acc ->
      acc >>= fun list ->
      instr_of_lambdacode self rhs
      >>| fun instr -> instr::list
    ) ~init:(Ok []) bindings >>= fun instrs ->
  f self >>| fun body ->
  Local_rec(instrs, body)

(** [operand_of_lambdacode self lambda cont] converts [lambda] into an
    [operand], passes it to the continuation [cont], and returns an [instr]. *)
and operand_of_lambdacode self lambda ~cont =
  let open Result.Monad_infix in
  match lambda.Lambda.expr with
  | Lambda.Constr size -> cont (Cons size)
  | Lambda.Extern_var id -> cont (Extern_var id)
  | Lambda.Lit lit -> cont (Lit lit)
  | Lambda.Local_var reg ->
     free_var self reg >>= fun var -> cont var
  | _ ->
     instr_of_lambdacode self lambda >>= fun rhs ->
     let var = fresh_bound_var self in
     cont var >>| fun body ->
     self.frame_offset <- self.frame_offset - 1;
     Local(rhs, body)
