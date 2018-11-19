(** The compiler must transform statically known curried functions into
    multi-parameter functions, remap the unique registers to stack and
    environment offsets, and compile decision trees into switch statements. *)

open Base

type register = int

type occurrence' =
  | Constr of int * occurrence'
  | Contents of occurrence'
  | Nil

type occurrence = operand * occurrence'

and decision_tree =
  | Fail
  | Leaf of occurrence list * int
  | Deref of occurrence * decision_tree
  | Switch of occurrence * (int * decision_tree) list * decision_tree

and operand =
  | Cons of int
  | Extern_var of Path.t
  | Free_var of int (** In the proc's environment *)
  | Lit of Literal.t
  | Register of int

and opcode =
  | Assign of operand * operand
  | Call of operand * operand * operand array
    (** proc, first arg, rest args *)
  | Case of operand list * decision_tree * instr array
    (** discrs, decision tree, jump table *)
  | Fun of proc
  | Load of operand
  | Pop_match
  | Prim of string
  | Ref of operand

and instr =
  | Box of operand list
  | Let of register * opcode * instr
  | Let_rec of (register * opcode) list * instr
  | Return of opcode
  | Seq of opcode * instr

and proc = {
    env : operand array; (** The captured variables *)
    params : register list;
    body : instr;
  }

type t = {
    ctx : (Ident.t, operand) Hashtbl.t;
    (** Map from ids to variables *)
    free_vars : operand Queue.t; (** Array of free variables *)
    parent : t option;
    mutable frame_offset : int;
  }

let create () =
  { ctx = Hashtbl.create (module Ident)
  ; free_vars = Queue.create ()
  ; parent = None
  ; frame_offset = 0 }

let fresh_register self =
  let offset = self.frame_offset in
  self.frame_offset <- offset + 1;
  offset

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
             self.ctx ~key:id ~data:(Free_var (Queue.length self.free_vars))
         in
         Queue.enqueue self.free_vars var;
         Ok (Free_var (Queue.length self.free_vars))
      | None ->
         Error (Sequence.return (Message.Unreachable "Bytecode free_var"))
    )

(** Reverse the occurrence from the pattern match compilation into an addressing
    path. *)
let convert_occurrence scruts =
  (* The structure of this function is similar to left fold. *)
  let rec helper acc = function
    | Pattern.Cons(idx, occurrence) ->
       helper (Constr(idx, acc)) occurrence
    | Pattern.Contents occurrence ->
       helper (Contents acc) occurrence
    | Pattern.Nil idx ->
       (scruts.(idx), acc)
  in helper Nil

let rec convert_decision_tree self scruts = function
  | Pattern.Fail -> Fail
  | Pattern.Leaf(bindings, jump) ->
     let bound_occs =
       Map.fold_right ~f:(fun ~key:_ ~data:occ acc ->
           (convert_occurrence scruts occ)::acc
         ) ~init:[] bindings
     in Leaf(bound_occs, jump)
  | Pattern.Ref(occ, subtree) ->
     let occ = convert_occurrence scruts occ in
     Deref(occ, convert_decision_tree self scruts subtree)
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
let rec proc_of_lambda self params id body ~cont =
  let reg = fresh_register self in
  match Hashtbl.add self.ctx ~key:id ~data:(Register reg) with
  | `Duplicate ->
     Error (Sequence.return (Message.Unreachable "Bytecode uncurry"))
  | `Ok ->
     match body.Lambda.expr with
     | Lambda.Lam(id, body) ->
        proc_of_lambda self (reg::params) id body ~cont
     | _ ->
        instr_of_lambdacode self body ~cont:(fun opcode ->
            cont (Fun ({ env = Queue.to_array self.free_vars
                       ; params = List.rev params
                       ; body = Return opcode }))
          )

(** Combine curried one-argument applications into a function call with all the
    arguments. *)
and flatten_app self (args : operand list) (f : Lambda.t) (x : operand) ~cont =
  match f.Lambda.expr with
  | Lambda.App(f, x') ->
     operand_of_lambdacode self x' ~cont:(fun x' ->
         flatten_app self (x::args) f x' ~cont
       )
  | _ ->
     operand_of_lambdacode self f ~cont:(fun f ->
         cont (Call(f, x, Array.of_list args))
       )

(** This function implements the compilation of a case expression, as used in
    [instr_of_lambdacode]. *)
and compile_case self scruts tree ~cont =
  let rec loop list = function
    | scrut::scruts ->
       operand_of_lambdacode self scrut ~cont:(fun operand ->
           loop (operand::list) scruts
         )
    | [] ->
       let scruts = List.rev list in
       let scruts_arr = Array.of_list scruts in
       let tree = convert_decision_tree self scruts_arr tree in
       cont (scruts, tree)
  in loop [] scruts

and compile_branch self bindings ~cont =
  let open Result.Monad_infix in
  Set.fold ~f:(fun cont id () ->
      let var = fresh_register self in
      match Hashtbl.add self.ctx ~key:id ~data:(Register var) with
      | `Duplicate ->
         Error (Sequence.return
                  (Message.Unreachable "Bytecode instr_of_lambdacode"))
      | `Ok ->
         cont () >>| fun body ->
         Let(var, Pop_match, body)
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
             cont (Assign(lhs, rhs))
           )
       )
  | Lambda.Case(scruts, tree, branches) ->
     compile_case self scruts tree ~cont:(fun (scruts, tree) ->
         List.fold_right ~f:(fun (bindings, body) acc ->
             acc >>= fun list ->
             compile_branch self bindings ~cont:(fun () ->
                 instr_of_lambdacode self body ~cont:(fun opcode ->
                     Ok (Return opcode)
                   )
               )
             >>| fun branch -> branch::list
           ) ~init:(Ok []) branches
         >>= fun branches ->
         cont (Case(scruts, tree, Array.of_list branches))
       )
  | Lambda.Constr _ | Lambda.Extern_var _ | Lambda.Local_var _ | Lambda.Lit _ ->
     operand_of_lambdacode self lambda ~cont:(fun operand ->
         cont (Load operand)
       )
  | Lambda.Lam(reg, body) ->
     let self =
       { ctx = Hashtbl.create (module Ident)
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
            Let(var, rhs, body)
       )
  | Lambda.Let_rec(bindings, body) ->
     compile_letrec self bindings ~cont:(fun bindings ->
         instr_of_lambdacode self body ~cont >>| fun body ->
         Let_rec(bindings, body)
       )
  | Lambda.Prim op -> cont (Prim op)
  | Lambda.Ref value ->
     operand_of_lambdacode self value ~cont:(fun value ->
         cont (Ref value)
       )
  | Lambda.Seq(s, t) ->
     instr_of_lambdacode self s ~cont:(fun s ->
         instr_of_lambdacode self t ~cont >>| fun t ->
         Seq(s, t)
       )

(** This function implements the compilation of a let-rec expression, as used in
    [instr_of_lambdacode]. *)
and compile_letrec self bindings ~cont =
  let open Result.Monad_infix in
  List.fold ~f:(fun acc (lhs, rhs) ->
      acc >>= fun list ->
      let var = fresh_register self in
      match Hashtbl.add self.ctx ~key:lhs ~data:(Register var) with
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
  | Lambda.Constr size -> cont (Cons size)
  | Lambda.Extern_var id -> cont (Extern_var id)
  | Lambda.Lit lit -> cont (Lit lit)
  | Lambda.Local_var reg ->
     free_var self reg >>= fun var -> cont var
  | _ ->
     instr_of_lambdacode self lambda ~cont:(fun rhs ->
         let var = fresh_register self in
         cont (Register var) >>| fun body ->
         Let(var, rhs, body)
       )
