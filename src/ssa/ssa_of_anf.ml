(** This transformation turns ANF join points, which are local to the case expr,
    into SSA basic blocks, which are local to the function. Here, the compiler
    compiles decision trees into switches, jumps, and phi nodes. *)

open Base

type t = {
    procs : (int, Ssa.proc, Int.comparator_witness) Map.t ref;
    blocks : (int, Ssa.basic_block, Int.comparator_witness) Map.t ref;
    label_gen : int ref;
    proc_gen : int ref;
    instrs : Ssa.instr Queue.t;
    curr_block : Ssa.Label.t;
    cont : Ssa.cont;
  }

(** [fresh_block ctx ~cont] applies [cont] the index of the next basic block,
    [cont] returns a tuple consisting of a result, the block predecessors, the
    instruction queue, and the block successor. The entire function returns
    [cont]'s result *)
let fresh_block ctx ~cont =
  let open Result.Monad_infix in
  let idx = !(ctx.label_gen) in
  ctx.label_gen := idx + 1;
  cont idx >>| fun (ret, preds, instrs, tail) ->
  let block = { Ssa.instrs; preds; tail } in
  ctx.blocks := Map.set !(ctx.blocks) ~key:idx ~data:block;
  (ret, block)

let rec compile_opcode ctx anf ~cont =
  let open Result.Monad_infix in
  match anf with
  | Anf.Assign(lval, rval) -> cont ctx (Ssa.Assign(lval, rval))
  | Anf.Box contents -> cont ctx (Ssa.Box contents)
  | Anf.Call(f, arg, args) -> cont ctx (Ssa.Call(f, arg, args))
  | Anf.Case(tree, join_points) ->
     (* The basic block for the case expr continuation *)
     fresh_block ctx ~cont:(fun cont_idx ->
         let cont_instrs = Queue.create () in
         List.fold_right ~f:(fun (reg_args, instr) acc ->
             acc >>= fun list ->
             (* The basic block for the join point *)
             fresh_block ctx ~cont:(fun branch_idx ->
                 let branch_instrs = Queue.create () in
                 List.iteri ~f:(fun i reg_arg ->
                     Queue.enqueue branch_instrs
                       { Ssa.dest = Some reg_arg
                       ; opcode = Phi i };
                   ) reg_args;
                 compile_instr
                   { ctx with
                     instrs = branch_instrs
                   ; curr_block = Ssa.Label.Block branch_idx
                   ; cont = Ssa.Break (Ssa.Label.Block cont_idx) }
                   instr
                 >>| fun (tail, exit_phi_elem) ->
                 ( (branch_idx, exit_phi_elem)
                 , Map.empty (module Ssa.Label)
                 , branch_instrs
                 , tail )
               ) >>| fun ((branch_idx, exit_phi_elem), block) ->
             (branch_idx, exit_phi_elem, block)::list
           ) ~init:(Ok []) join_points
         >>= fun branches ->
         compile_decision_tree ctx ctx.instrs ctx.curr_block cont_idx
           (Array.of_list branches) tree
         >>= fun cont_from_decision_tree ->
         let preds =
           List.fold ~f:(fun acc (idx, exit_phi_elem, _) ->
               Map.set acc ~key:(Ssa.Label.Block idx) ~data:[exit_phi_elem]
             ) ~init:(Map.empty (module Ssa.Label)) branches;
         in
         (* Compile the rest of the ANF in the continuation block *)
         cont
           { ctx with
             instrs = cont_instrs
           ; curr_block = Ssa.Label.Block cont_idx }
           (Ssa.Phi 0)
         >>| fun (tail, result) (* Tail of continuation block *) ->
         (* Cont for origin block, cont for continuation block *)
         ( (cont_from_decision_tree, result)
         , preds
         , cont_instrs
         , tail )
       ) >>| fun (result, _) -> result
  | Anf.Fun proc ->
     let env = proc.Anf.env in
     compile_proc ctx proc >>= fun proc ->
     let idx = !(ctx.proc_gen) in
     ctx.proc_gen := idx + 1;
     let procs = Map.set !(ctx.procs) ~key:idx ~data:proc in
     ctx.procs := procs;
     cont ctx (Ssa.Fun(idx, env))
  | Anf.Load o -> cont ctx (Ssa.Load o)
  | Anf.Prim p -> cont ctx (Ssa.Prim p)
  | Anf.Ref x -> cont ctx (Ssa.Ref x)

and compile_decision_tree ctx instrs origin_label cont_idx branches =
  let open Result.Monad_infix in
  function
  | Anf.Deref(occ, dest, tree) ->
     Queue.enqueue instrs { Ssa.dest = Some dest; opcode = Deref occ };
     compile_decision_tree ctx instrs origin_label cont_idx branches tree
  | Anf.Fail -> Ok Ssa.Fail
  | Anf.Leaf(operands, idx) ->
     let branch_idx, _, block = branches.(idx) in
     block.Ssa.preds <-
       Map.set block.Ssa.preds ~key:(Ssa.Label.Block cont_idx) ~data:operands;
     Ok (Ssa.Break (Ssa.Label.Block branch_idx))
  | Anf.Switch(tag_reg, occ, trees, else_tree) ->
     Queue.enqueue instrs { Ssa.dest = Some tag_reg; opcode = Get(occ, 0) };
     Map.fold ~f:(fun ~key:case ~data:(regs, tree) acc ->
         acc >>= fun list ->
         fresh_block ctx ~cont:(fun jump_idx ->
             let jump_instrs = Queue.create () in
             List.iteri ~f:(fun idx reg ->
                 Queue.enqueue jump_instrs
                   { Ssa.dest = Some reg; opcode = Get(occ, idx + 1) }
               ) regs;
             compile_decision_tree ctx jump_instrs
               (Ssa.Label.Block jump_idx) jump_idx branches tree
             >>| fun cont ->
             ( (case, Ssa.Label.Block jump_idx)::list
             , Map.singleton (module Ssa.Label) origin_label []
             , jump_instrs
             , cont )
           ) >>| fun (result, _) -> result
       ) ~init:(Ok []) trees
     >>= fun cases ->
     fresh_block ctx ~cont:(fun else_idx ->
         let else_instrs = Queue.create () in
         compile_decision_tree ctx else_instrs
           (Ssa.Label.Block else_idx) else_idx branches else_tree
         >>| fun cont ->
         ( else_idx
         , Map.singleton (module Ssa.Label) origin_label []
         , else_instrs
         , cont )
       )
     >>| fun (else_block_idx, _) ->
     Ssa.Switch(Anf.Register tag_reg, cases, Ssa.Label.Block else_block_idx)

and compile_instr ctx anf =
  let open Result.Monad_infix in
  match anf.Anf.instr with
  | Anf.Let(reg, op, next) ->
     compile_opcode ctx op ~cont:(fun ctx op ->
         Queue.enqueue ctx.instrs { Ssa.dest = Some reg; opcode = op };
         compile_instr ctx next
       )
  | Anf.Let_rec(bindings, next) ->
     (* Initialize registers with dummy allocations *)
     List.fold_left ~f:(fun acc (reg, _, def) ->
         acc >>= fun () ->
         begin match def with
         | Anf.Box list -> Ok (List.length list)
         | Anf.Fun proc -> Ok (List.length proc.Anf.env + 1)
         | _ -> Error (Sequence.return Message.Unsafe_let_rec)
         end >>| fun size ->
         Queue.enqueue ctx.instrs
           { Ssa.dest = Some reg; opcode = Ssa.Box_dummy size }
       ) ~init:(Ok ()) bindings
     >>= fun () ->
     (* Accumulator is a function *)
     List.fold_right ~f:(fun (reg, temp, op) acc ctx ->
         compile_opcode ctx op ~cont:(fun ctx op ->
             (* Evaluate the let-rec binding RHS *)
             Queue.enqueue ctx.instrs { Ssa.dest = Some temp; opcode = op };
             (* Mutate the memory that the register points to *)
             Queue.enqueue ctx.instrs
               { Ssa.dest = None
               ; opcode = Ssa.Memcopy(Anf.Register reg, Anf.Register temp) };
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
  | Anf.Break operand -> Ok (ctx.cont, operand)

and compile_proc ctx proc =
  let open Result.Monad_infix in
  let blocks = ref (Map.empty (module Int)) in
  let instrs = Queue.create () in
  let state =
    { ctx with
      blocks
    ; instrs
    ; label_gen = ref 0
    ; curr_block = Ssa.Label.Entry
    ; cont = Ssa.Return }
  in
  compile_instr state proc.Anf.body >>| fun (tail, return) ->
  { Ssa.params = proc.Anf.params
  ; blocks = !blocks
  ; entry = { preds = Map.empty (module Ssa.Label); instrs; tail }
  ; return }

let compile_module anf =
  let open Result.Monad_infix in
  let ctx =
    { procs = ref (Map.empty (module Int))
    ; blocks = ref (Map.empty (module Int))
    ; instrs = Queue.create ()
    ; proc_gen = ref 0
    ; label_gen = ref 0
    ; curr_block = Ssa.Label.Entry
    ; cont = Ssa.Return }
  in
  compile_instr ctx anf >>| fun (tail, return) ->
  let main_proc =
    { Ssa.params = []
    ; blocks = !(ctx.blocks)
    ; entry =
        { preds = Map.empty (module Ssa.Label)
        ; instrs = ctx.instrs
        ; tail }
    ; return }
  in
  { Ssa.procs = !(ctx.procs)
  ; main = main_proc }
