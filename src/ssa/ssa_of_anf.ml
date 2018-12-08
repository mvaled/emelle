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
  cont instrs idx >>| fun (a, tail) ->
  let block = { Ssa.instrs; tail } in
  Queue.enqueue self.blocks block;
  a

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
     List.fold_right ~f:(fun (_, instr) acc ->
         acc >>= fun list ->
         fresh_block self ~cont:(fun instrs idx ->
             compile_instr
               { self with
                 instrs
               ; curr_cont = Ssa.Block idx
               ; cont = self.curr_cont }
               instr
             >>| fun tail ->
             (idx, tail)
           ) >>| fun idx ->
         idx::list
       ) ~init:(Ok []) join_points
     >>= fun branches ->
     fresh_block self ~cont:(fun instrs idx ->
         compile_decision_tree self branches idx tree >>= fun phis ->
         cont
           { self with
             instrs
           ; curr_cont = Ssa.Block idx
           ; cont = self.curr_cont }
           phis
         >>| fun tail ->
         (tail, tail)
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

and compile_decision_tree _self _cont_idx _branches = function
  | Anf.Deref(_, _occ, _tree) -> failwith ""
  | Anf.Fail -> failwith ""
  | Anf.Leaf(_id, _occs, _idx) -> failwith ""
  | Anf.Switch(_, _occ, _trees, _tree) -> failwith ""

and compile_instr self = function
  | Anf.Let(reg, op, next) ->
     compile_opcode self op ~cont:(fun self op ->
         Queue.enqueue self.instrs { Ssa.dest = Some reg; opcode = op };
         compile_instr self next
       )
  | Anf.Let_rec(bindings, next) ->
     (* Accumulator is a function *)
     List.fold ~f:(fun acc (reg, op) self ->
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
  | Anf.Break _ ->
     Ok self.cont

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
  compile_instr state proc.Anf.body >>| fun tail ->
  { Ssa.blocks; entry = { instrs; tail } }
