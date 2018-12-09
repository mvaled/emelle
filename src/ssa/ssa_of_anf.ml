(** This transformation turns ANF join points, which are local to the case expr,
    into SSA basic blocks, which are local to the function. *)

open Base

type t = {
    package : Ssa.package;
    blocks : (int, Ssa.basic_block, Int.comparator_witness) Map.t;
    next_label : int;
    next_proc : int;
    instrs : Ssa.instr Queue.t;
    curr_cont : Ssa.cont;
    cont : Ssa.cont;
  }

(** [fresh_block ctx ~cont] applies [cont] to a fresh [Ssa.instr] queue and the
    index of the next basic block and returns [cont]'s result *)
let fresh_block ctx ~cont =
  let open Result.Monad_infix in
  let idx = ctx.next_label in
  let instrs = Queue.create () in
  cont { ctx with next_label = idx + 1 } instrs idx >>| fun (ctx, ret, tail) ->
  let block = { Ssa.instrs; tail } in
  let blocks = Map.set ctx.blocks ~key:idx ~data:block in
  ({ ctx with blocks }, ret)

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
     fresh_block ctx ~cont:(fun ctx cont_instrs cont_idx ->
         List.fold_right ~f:(fun (_, instr) acc ->
             acc >>= fun (ctx, list) ->
             (* The basic block for the join point *)
             fresh_block ctx ~cont:(fun ctx branch_instrs branch_idx ->
                 compile_instr
                   { ctx with
                     instrs = branch_instrs
                   ; curr_cont = Ssa.Block branch_idx
                   ; cont = Ssa.Block cont_idx }
                   instr
                 >>| fun (ctx, tail, phi_elem) ->
                 (ctx, (branch_idx, phi_elem), tail)
               ) >>| fun (ctx, branch) ->
             (ctx, branch::list)
           ) ~init:(Ok (ctx, [])) join_points
         >>= fun (ctx, branches) ->
         compile_decision_tree ctx cont_idx (Array.of_list branches) tree
         >>= fun (ctx, cont_from_decision_tree) ->
         (* Compile the rest of the ANF in the continuation block *)
         cont
           { ctx with
             instrs = cont_instrs
           ; curr_cont = Ssa.Block cont_idx }
           (Ssa.Phi branches)
         >>| fun (ctx, tail, result) (* Tail of continuation block *) ->
         (* Cont for origin block, cont for continuation block *)
         (ctx, (cont_from_decision_tree, result), tail)
       ) >>| fun (ctx, (tail, result)) ->
     (ctx, tail, result)
  | Anf.Fun proc ->
     let env = proc.Anf.env in
     compile_proc ctx proc >>= fun (ctx, proc) ->
     let idx = ctx.next_proc in
     let procs = Map.set ctx.package.Ssa.procs ~key:idx ~data:proc in
     cont
       { ctx with
         next_proc = idx + 1
       ; package = { procs } }
       (Ssa.Fun(idx, env))
  | Anf.Load o -> cont ctx (Ssa.Load o)
  | Anf.Prim p -> cont ctx (Ssa.Prim p)
  | Anf.Ref x -> cont ctx (Ssa.Ref x)

and compile_decision_tree ctx _cont_idx branches = function
  | Anf.Deref(_, _occ, _tree) ->
     failwith ""
  | Anf.Fail ->
     failwith ""
  | Anf.Leaf(_id, _occs, idx) ->
     let branch_idx, _ = branches.(idx) in
     Ok (ctx, Ssa.Block branch_idx)
  | Anf.Switch(_, _occ, _trees, _tree) ->
     Ok (ctx, Ssa.Switch)

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
     Ok (ctx, ctx.cont, operand)

and compile_proc ctx proc =
  let open Result.Monad_infix in
  let blocks = Map.empty (module Int) in
  let instrs = Queue.create () in
  let state =
    { ctx with
      blocks
    ; instrs
    ; next_label = 0
    ; curr_cont = Ssa.Entry
    ; cont = Ssa.Return }
  in
  compile_instr state proc.Anf.body >>| fun (state, tail, return) ->
  ( { ctx with
      package = state.package
    ; next_proc = state.next_proc }
  , { Ssa.blocks
    ; entry = { instrs; tail }
    ; return = return } )
