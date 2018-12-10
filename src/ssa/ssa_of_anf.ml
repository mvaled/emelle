(** This transformation turns ANF join points, which are local to the case expr,
    into SSA basic blocks, which are local to the function. *)

open Base

type t = {
    package : Ssa.package ref;
    mutable blocks : (int, Ssa.basic_block, Int.comparator_witness) Map.t;
    label_gen : int ref;
    proc_gen : int ref;
    instrs : Ssa.instr Queue.t;
    curr_cont : Ssa.cont;
    cont : Ssa.cont;
  }

(** [fresh_block ctx ~cont] applies [cont] to a fresh [Ssa.instr] queue and the
    index of the next basic block and returns [cont]'s result *)
let fresh_block ctx ~cont =
  let open Result.Monad_infix in
  let idx = !(ctx.label_gen) in
  ctx.label_gen := idx + 1;
  let instrs = Queue.create () in
  cont instrs idx >>| fun (ret, tail) ->
  let block = { Ssa.instrs; tail } in
  ctx.blocks <- Map.set ctx.blocks ~key:idx ~data:block;
  ret

let rec compile_opcode ctx anf ~cont =
  let open Result.Monad_infix in
  match anf with
  | Anf.Assign(lval, rval) ->
     cont ctx (Ssa.Assign(lval, rval))
  | Anf.Box contents ->
     cont ctx (Ssa.Box contents)
  | Anf.Call(f, arg, args) ->
     cont ctx (Ssa.Call(f, arg, args))
  | Anf.Case(_scruts, tree, join_points) ->
     (* The basic block for the case expr continuation *)
     fresh_block ctx ~cont:(fun cont_instrs cont_idx ->
         List.fold_right ~f:(fun (_, instr) acc ->
             acc >>= fun list ->
             (* The basic block for the join point *)
             fresh_block ctx ~cont:(fun branch_instrs branch_idx ->
                 compile_instr
                   { ctx with
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
         compile_decision_tree ctx cont_idx (Array.of_list branches) tree
         >>= fun cont_from_decision_tree ->
         (* Compile the rest of the ANF in the continuation block *)
         cont
           { ctx with
             instrs = cont_instrs
           ; curr_cont = Ssa.Block cont_idx }
           (Ssa.Phi branches)
         >>| fun (tail, result) (* Tail of continuation block *) ->
         (* Cont for origin block, cont for continuation block *)
         ((cont_from_decision_tree, result), tail)
       )
  | Anf.Fun proc ->
     let env = proc.Anf.env in
     compile_proc ctx proc >>= fun proc ->
     let idx = !(ctx.proc_gen) in
     ctx.proc_gen := idx + 1;
     let procs = Map.set !(ctx.package).Ssa.procs ~key:idx ~data:proc in
     ctx.package := { procs };
     cont ctx (Ssa.Fun(idx, env))
  | Anf.Load o -> cont ctx (Ssa.Load o)
  | Anf.Prim p -> cont ctx (Ssa.Prim p)
  | Anf.Ref x -> cont ctx (Ssa.Ref x)

and compile_decision_tree _ctx _cont_idx branches = function
  | Anf.Deref(_occ, _tree) ->
     failwith ""
  | Anf.Fail ->
     failwith ""
  | Anf.Leaf(_occs, idx) ->
     let branch_idx, _ = branches.(idx) in
     Ok (Ssa.Block branch_idx)
  | Anf.Switch(_occ, _trees, _tree) ->
     Ok (Ssa.Switch)

and compile_instr ctx = function
  | Anf.Let(reg, op, next) ->
     compile_opcode ctx op ~cont:(fun ctx op ->
         Queue.enqueue ctx.instrs { Ssa.dest = Some reg; opcode = op };
         compile_instr ctx next
       )
  | Anf.Let_rec(bindings, next) ->
     (* Accumulator is a function *)
     List.fold_right ~f:(fun (reg, op) acc ctx ->
         compile_opcode ctx op ~cont:(fun ctx op ->
             Queue.enqueue ctx.instrs { Ssa.dest = Some reg; opcode = op };
             acc ctx
           )
       ) ~init:(fun ctx ->
         compile_instr ctx next
       ) bindings ctx
  | Anf.Seq(op, next) ->
     compile_opcode ctx op ~cont:(fun ctx opcode ->
         Queue.enqueue ctx.instrs { Ssa.dest = None; opcode = opcode };
         compile_instr ctx next
       )
  | Anf.Break operand ->
     Ok (ctx.cont, operand)

and compile_proc ctx proc =
  let open Result.Monad_infix in
  let blocks = Map.empty (module Int) in
  let instrs = Queue.create () in
  let state =
    { ctx with
      blocks
    ; instrs
    ; label_gen = ref 0
    ; curr_cont = Ssa.Entry
    ; cont = Ssa.Return }
  in
  compile_instr state proc.Anf.body >>| fun (tail, return) ->
  { Ssa.blocks
  ; entry = { instrs; tail }
  ; return = return }
