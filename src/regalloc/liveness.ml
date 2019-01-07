open Base

type color = int

type t = {
    live_regs : (int, Int.comparator_witness) Set.t;
  }

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

let handle_regs ctx regs =
  let regs = Set.of_list (module Int) regs in
  let new_regs = Set.diff regs ctx.live_regs in
  (Set.union ctx.live_regs regs, new_regs)

let handle_instr ctx instr =
  let (live_regs, ending_regs) =
    handle_regs ctx (regs_of_opcode instr.Ssa.opcode) in
  let live_regs =
    match instr.Ssa.dest with
    | None -> live_regs
    | Some reg -> Set.remove live_regs reg in
  ( { Post_ssa.dest = instr.Ssa.dest
    ; opcode = instr.Ssa.opcode
    ; ending_regs }
  , { live_regs } )

(** [handle_instrs ctx instrs] iterates over [instrs] backwards and calls
    [handle_instr ctx instr] for each instruction. *)
let handle_instrs ctx instrs =
  let rec go ctx list = function
    | 0 -> list, ctx
    | i ->
       let instr, ctx = handle_instr ctx (Queue.get instrs (i - 1)) in
       go ctx (instr::list) (i - 1)
  in go ctx [] (Queue.length instrs)

let handle_phi_elems ctx elems =
  let regs =
    Array.fold elems ~init:[] ~f:(fun acc operand ->
        match operand with
        | Anf.Register reg -> reg::acc
        | _ -> acc
      )
  in handle_regs ctx regs

let find_block proc idx = Map.find proc.Ssa.blocks idx

let rec handle_block ctx blocks proc label =
  let open Result.Let_syntax in
  match find_block proc label with
  | Some block ->
     if block.Ssa.visited then Message.unreachable ""
     else (
       block.Ssa.visited <- true;
       let instrs, ctx = handle_instrs ctx block.Ssa.instrs in
       let block' = { Post_ssa.instrs; jump = block.Ssa.jump } in
       let blocks = Map.set blocks ~key:label ~data:block' in
       Map.fold block.Ssa.preds ~init:(Ok blocks)
         ~f:(fun ~key:label ~data:elems acc ->
           let%bind blocks = acc in
           let live_regs, _ = handle_phi_elems ctx elems in
           let ctx = { live_regs } in
           let%bind block =
             match Map.find proc.Ssa.blocks label with
             | None -> Message.unreachable "Unknown block"
             | Some block -> Ok block in
           let succs = Ssa.successors block.Ssa.jump in
           let%bind visited_all_succs =
             List.fold succs ~init:(Ok true) ~f:(fun acc label ->
                 acc >>= fun visited_all_succs ->
                 if visited_all_succs then
                   match find_block proc label with
                   | Some { Ssa.visited; _ } -> Ok visited
                   | None -> Message.unreachable "Unknown block"
                 else Ok false
               ) in
           (* Only visit predecessor block if all of its successors have been
              visited *)
           if visited_all_succs then
             handle_block ctx blocks proc label
           else Ok blocks
         )
     )
  | None -> Message.unreachable "Unknown label"

let handle_proc proc =
  let open Result.Monad_infix in
  let live_regs =
    match proc.Ssa.return with
    | Anf.Register reg ->
       Set.singleton (module Int) reg
    | _ -> Set.empty (module Int) in
  let ctx = { live_regs } in
  let map = Map.empty (module Int) in
  handle_block ctx map proc proc.Ssa.before_return
  >>| fun blocks ->
  { Post_ssa.params = proc.Ssa.params
  ; entry = proc.Ssa.entry
  ; blocks = blocks
  ; before_return = proc.Ssa.before_return
  ; return = proc.Ssa.return }

let handle_package { Ssa.procs; main } =
  let open Result.Monad_infix in
  Map.fold procs ~init:(Ok (Map.empty (module Int)))
    ~f:(fun ~key:id ~data:proc acc ->
      acc >>= fun map ->
      handle_proc proc >>| fun proc ->
      Map.set map ~key:id ~data:proc
    ) >>= fun procs ->
  handle_proc main >>| fun main ->
  { Post_ssa.procs; main }
