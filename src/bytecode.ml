(** The compiler must transform statically known curried functions into
    multi-parameter functions, remap the unique registers to stack and
    environment offsets, and compile decision trees into switch statements. *)

open Base

type operand =
  | Bound_var of int
  | Extern_var of Ident.t
  | Free_var of int

and instr =
  | Call of operand * operand * operand array
  | Fun of proc
  | Load of operand
  | Local of instr * instr
  | Local_rec of instr list * instr
  | Switch of operand * (int * int) list * instr array * instr

and proc = {
    env : operand array; (** The captured variables *)
    arity : int; (** The number of parameters that the function accepts *)
    body : instr;
  }

type t = {
    ctx : (int, operand) Hashtbl.t; (** Map from registers to variables *)
    free_vars : operand Queue.t; (** Array of free variables *)
    parent : t option;
    mutable frame_offset : int; (** Current offset from frame pointer *)
  }

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
        let arity = self.frame_offset in
        instr_of_lambdacode self body >>| fun body ->
        { env = Queue.to_array self.free_vars; arity; body }

and flatten_app self args f x =
  match f.Lambda.expr with
  | Lambda.App(f, x') ->
     operand_of_lambdacode self x' (fun x' -> flatten_app self (x::args) f x')
  | _ ->
     operand_of_lambdacode self f (fun f -> Ok (Call(f, x, Array.of_list args)))

and instr_of_lambdacode self lambda =
  let open Result.Monad_infix in
  match lambda.Lambda.expr with
  | Lambda.App(f, x) ->
     operand_of_lambdacode self x (fun x -> flatten_app self [] f x)
  | Lambda.Case(_, _, _, _) -> failwith ""
  | Lambda.Extern_var _ | Lambda.Local_var _ ->
     operand_of_lambdacode self lambda (fun operand -> Ok (Load operand))
  | Lambda.Lam(reg, body) ->
     let st =
       { ctx = Hashtbl.create (module Int)
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
     List.fold ~f:(fun acc (lhs, _) ->
         acc >>= fun () ->
         let var = fresh_bound_var self in
         match Hashtbl.add self.ctx ~key:lhs ~data:var with
         | `Duplicate ->
            Error (Sequence.return
                     (Message.Unreachable "Bytecode instr_of_lambdacode"))
         | `Ok ->
            Ok()
       ) ~init:(Ok ()) bindings >>= fun () ->
     List.fold_right ~f:(fun (_, rhs) acc ->
         acc >>= fun list ->
         instr_of_lambdacode self rhs >>| fun instr ->
         instr::list
       ) ~init:(Ok []) bindings >>= fun instrs ->
     instr_of_lambdacode self body >>| fun body ->
     Local_rec(instrs, body)

and operand_of_lambdacode self lambda cont =
  let open Result.Monad_infix in
  match lambda.Lambda.expr with
  | Lambda.Extern_var id -> cont (Extern_var id)
  | Lambda.Local_var reg ->
     free_var self reg >>= fun var -> cont var
  | _ ->
     instr_of_lambdacode self lambda >>= fun rhs ->
     let var = fresh_bound_var self in
     cont var >>| fun body ->
     self.frame_offset <- self.frame_offset - 1;
     Local(rhs, body)
