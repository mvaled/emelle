open Base

type t = {
    color_gen : int ref;
      (* Is a reference so that multiple states can share it *)
    coloring : (int, int) Hashtbl.t;
    mutable free_colors : int list;
    live_regs : (int, int) Hashtbl.t;
    visited_blocks :
      (Ssa.Label.t, (int, int) Hashtbl.t) Hashtbl.t;
  }

let fresh_color ctx =
  match ctx.free_colors with
  | [] ->
     let c = !(ctx.color_gen) in
     ctx.color_gen := c + 1;
     c
  | color::colors ->
     ctx.free_colors <- colors;
     color

let recycle_color ctx color =
  ctx.free_colors <- color::ctx.free_colors

let alloc_reg ctx reg =
  let color = fresh_color ctx in
  Hashtbl.set ctx.coloring ~key:reg ~data:color;
  Hashtbl.set ctx.live_regs ~key:reg ~data:color

let handle_instr ctx instr =
  let open Result.Monad_infix in
  Set.fold instr.Post_ssa.ending_regs ~init:(Ok ()) ~f:(fun acc reg ->
      acc >>= fun () ->
      match Hashtbl.find_and_remove ctx.live_regs reg with
      | None ->
         Message.unreachable ("Color unknown register " ^ (Int.to_string reg))
      | Some color -> Ok (recycle_color ctx color)
    ) >>| fun () ->
  match instr.Post_ssa.dest with
  | None -> ()
  | Some reg -> alloc_reg ctx reg

let handle_instrs ctx =
  let open Result.Monad_infix in
  List.fold ~init:(Ok ()) ~f:(fun acc instr ->
      acc >>= fun () ->
      handle_instr ctx instr
    )

let rec handle_block ctx proc label =
  let open Result.Monad_infix in
  match Map.find proc.Post_ssa.blocks label with
  | None -> Message.unreachable "Unknown block"
  | Some block ->
     match Hashtbl.add ctx.visited_blocks ~key:label ~data:ctx.live_regs with
     | `Duplicate -> Ok ()
     | `Ok ->
        let visited_all_preds =
          Map.fold block.Post_ssa.preds ~init:true
            ~f:(fun ~key:label ~data:_ acc ->
              acc && (
                  match Hashtbl.find ctx.visited_blocks label with
                  | None -> false
                  | Some tbl ->
                     let f ~key:_ a _ = Hashtbl.Set_to a in
                     Hashtbl.merge_into ~src:tbl ~dst:ctx.live_regs ~f;
                     true
                )
            ) in
        if visited_all_preds then
          (* free_colors is a mutable field; here, we make it get mutated
             separately for each successor block *)
          handle_instrs ctx block.Post_ssa.instrs
          >>= fun () ->
          let succs = Ssa.successors block.Post_ssa.jump in
          List.fold succs ~init:(Ok ()) ~f:(fun acc label ->
              let live_regs = Hashtbl.create (module Int) in
              let ctx' = { ctx with free_colors = ctx.free_colors; live_regs }
              in
              acc >>= fun () ->
              handle_block ctx' proc label
            )
        else Ok ()

let handle_proc proc =
  let open Result.Monad_infix in
  let ctx =
    { color_gen = ref 0
    ; coloring = Hashtbl.create (module Int)
    ; free_colors = []
    ; live_regs = Hashtbl.create (module Int)
    ; visited_blocks = Hashtbl.create (module Int) } in
  List.iter proc.Post_ssa.params ~f:(fun reg -> alloc_reg ctx reg);
  handle_block ctx proc proc.Post_ssa.entry >>| fun () ->
  ctx.coloring

let handle_package package =
  let open Result.Monad_infix in
  Map.fold package.Post_ssa.procs ~init:(Ok (Map.empty (module Int)))
    ~f:(fun ~key ~data acc ->
      acc >>= fun map ->
      handle_proc data >>| fun coloring ->
      Map.set map ~key ~data:coloring
    ) >>= fun map ->
  handle_proc package.Post_ssa.main
  >>| fun main's_coloring ->
  (map, main's_coloring)
