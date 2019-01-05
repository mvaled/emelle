open Base

type t =
  { live_regs : (int, Int.comparator_witness) Set.t
  ; graph : Interf.t
  ; visited_blocks : (Ssa.Label.t, Ssa.Label.comparator_witness) Set.t }

let operands_of_opcode = function
  | Ssa.Assign(lval, rval) -> [lval; rval]
  | Ssa.Box list -> list
  | Ssa.Box_dummy _ -> []
  | Ssa.Call(f, arg, args) -> f::arg::args
  | Ssa.Deref op -> [op]
  | Ssa.Fun(_, captures) -> captures
  | Ssa.Get(op, _) -> [op]
  | Ssa.Load op -> [op]
  | Ssa.Memcopy(dest, src) -> [dest; src]
  | Ssa.Phi _ -> []
  | Ssa.Prim _ -> []
  | Ssa.Ref op -> [op]

let operand_of_jump = function
  | Ssa.Switch(scrut, _, _) -> Some scrut
  | _ -> None

let regs_of_opcode opcode =
  let operands = operands_of_opcode opcode in
  List.fold operands ~init:[] ~f:(fun acc ->
      function
      | Anf.Register reg -> reg::acc
      | _ -> acc
    )

let reg_of_jump jump =
  let open Option.Monad_infix in
  operand_of_jump jump >>= function
  | Anf.Register reg -> Some reg
  | _ -> None

let handle_instr ctx { Ssa.dest; opcode } =
  let regs = regs_of_opcode opcode in
  let regs = Set.of_list (module Int) regs in
  let live_regs = Set.union ctx.live_regs regs in
  let live_regs =
    match dest with
    | Some reg -> Set.remove live_regs reg
    | None -> live_regs
  in
  Interf.add_interferences ctx.graph live_regs;
  { ctx with live_regs }

let handle_instrs ctx instrs =
  let rec f ctx = function
    | 0 -> ctx
    | i ->
       let ctx = handle_instr ctx (Queue.get instrs (i - 1)) in
       f ctx (i - 1)
  in f ctx (Queue.length instrs)

let handle_proc
      { Ssa.blocks
      ; entry
      ; before_return
      ; return
      ; interf_graph; _ } =
  let open Result.Monad_infix in
  let live_regs =
    match return with
    | Anf.Register reg -> Set.singleton (module Int) reg
    | _ -> Set.empty (module Int)
  in
  Interf.add_interferences interf_graph live_regs;
  let ctx =
    { graph = interf_graph
    ; live_regs
    ; visited_blocks = Set.empty (module Ssa.Label) } in
  let rec handle_block ctx label =
    if Set.mem ctx.visited_blocks label then
      Ok ()
    else
      match
        match label with
        | Ssa.Label.Entry -> Some entry
        | Ssa.Label.Block idx -> Map.find blocks idx
      with
      | Some { Ssa.preds; instrs; _ } ->
         let ctx = handle_instrs ctx instrs in
         let ctx =
           { ctx with visited_blocks = Set.add ctx.visited_blocks label }
         in
         Map.fold preds ~init:(Ok ()) ~f:(fun ~key:label ~data:_ acc ->
             acc >>= fun () ->
             handle_block ctx label
           )
      | None -> Message.unreachable "Unknown label"
  in handle_block ctx before_return >>| fun _ -> ()

let handle_package { Ssa.procs; main } =
  let open Result.Monad_infix in
  Map.fold procs ~init:(Ok ()) ~f:(fun ~key:_ ~data:proc acc ->
      acc >>= fun () ->
      handle_proc proc
    ) >>= fun () ->
  handle_proc main;
