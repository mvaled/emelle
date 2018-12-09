(** This transformation turns ANF join points, which are local to the case expr,
    into SSA basic blocks, which are local to the function. *)

open Base

type t = {
    package : Ssa.package;
    blocks : Ssa.basic_block Queue.t;
    instrs : Ssa.instr Queue.t;
    curr_cont : Ssa.cont;
    cont : Ssa.cont;
  }

(** [fresh_block ctx ~cont] applies [cont] to a fresh [Ssa.instr] queue and the
    index of the next basic block and returns [cont]'s result  *)
let fresh_block self ~cont =
  let open Result.Monad_infix in
  let idx = Queue.length self.blocks in
  let instrs = Queue.create () in
  cont instrs idx >>| fun (ret, tail) ->
  let block = { Ssa.instrs; tail } in
  Queue.enqueue self.blocks block;
  ret

let rec compile_opcode self anf ~cont =
  let open Result.Monad_infix in
  match anf with
  | Anf.Assign(lval, rval) ->
     cont self (Ssa.Assign(lval, rval))
  | Anf.Box contents ->
     cont self (Ssa.Box contents)
  | Anf.Call(f, arg, args) ->
     cont self (Ssa.Call(f, arg, args))
  | Anf.Case(_scruts, tree, join_points) ->
     (* The basic block for the case expr continuation *)
     fresh_block self ~cont:(fun cont_instrs cont_idx ->
         List.fold_right ~f:(fun (_, instr) acc ->
             acc >>= fun list ->
             (* The basic block for the join point *)
             fresh_block self ~cont:(fun branch_instrs branch_idx ->
                 compile_instr
                   { self with
                     instrs = branch_instrs
                   ; curr_cont = Ssa.Block branch_idx
                   ; cont = Ssa.Block cont_idx }
                   instr
                 >>| fun (tail, phi_elem) ->
                 ((branch_idx, phi_elem), tail)
               ) >>| fun branch ->
             branch::list
           ) ~init:(Ok []) join_points
         >>= fun branches ->
         compile_decision_tree self cont_idx (Array.of_list branches) tree
         >>= fun cont_from_decision_tree ->
         (* Compile the rest of the ANF in the continuation block *)
         cont
           { self with
             instrs = cont_instrs
           ; curr_cont = Ssa.Block cont_idx }
           (Ssa.Phi branches)
         >>| fun (tail, result) (* Tail of continuation block *) ->
         (* Cont for origin block, cont for continuation block *)
         ((cont_from_decision_tree, result), tail)
       )
  | Anf.Fun proc ->
     let env = proc.Anf.env in
     compile_proc self proc >>= fun proc ->
     let idx = Queue.length self.package.Ssa.procs in
     Queue.enqueue self.package.Ssa.procs proc;
     cont self (Ssa.Fun(idx, env))
  | Anf.Load o -> cont self (Ssa.Load o)
  | Anf.Prim p -> cont self (Ssa.Prim p)
  | Anf.Ref x -> cont self (Ssa.Ref x)

and compile_decision_tree _self _cont_idx branches = function
  | Anf.Deref(_, _occ, _tree) ->
     failwith ""
  | Anf.Fail ->
     failwith ""
  | Anf.Leaf(_id, _occs, idx) ->
     let branch_idx, _ = branches.(idx) in
     Ok (Ssa.Block branch_idx)
  | Anf.Switch(_, _occ, _trees, _tree) ->
     Ok (Ssa.Switch)

and compile_instr self = function
  | Anf.Let(reg, op, next) ->
     compile_opcode self op ~cont:(fun self op ->
         Queue.enqueue self.instrs { Ssa.dest = Some reg; opcode = op };
         compile_instr self next
       )
  | Anf.Let_rec(bindings, next) ->
     (* Accumulator is a function *)
     List.fold_right ~f:(fun (reg, op) acc self ->
         compile_opcode self op ~cont:(fun self op ->
             Queue.enqueue self.instrs { Ssa.dest = Some reg; opcode = op };
             acc self
           )
       ) ~init:(fun self ->
         compile_instr self next
       ) bindings self
  | Anf.Seq(op, next) ->
     compile_opcode self op ~cont:(fun self opcode ->
         Queue.enqueue self.instrs { Ssa.dest = None; opcode = opcode };
         compile_instr self next
       )
  | Anf.Break operand ->
     Ok (self.cont, operand)

and compile_proc self proc =
  let open Result.Monad_infix in
  let blocks = Queue.create () in
  let instrs = Queue.create () in
  let state =
    { package = self.package
    ; blocks
    ; instrs
    ; curr_cont = Ssa.Entry
    ; cont = Ssa.Return }
  in
  compile_instr state proc.Anf.body >>| fun (tail, return) ->
  { Ssa.blocks
  ; entry = { instrs; tail }
  ; return = return }
