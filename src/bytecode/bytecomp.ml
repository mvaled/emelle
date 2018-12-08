open Base

type t = {
    colors : (Anf.register, int) Hashtbl.t;
    package : Bytecode.package;
  }

let rec compile_operand self =
  let open Result.Monad_infix in
  function
  | Anf.Extern_var path -> Ok (Bytecode.Extern_var path)
  | Anf.Free_var idx -> Ok (Bytecode.Free_var idx)
  | Anf.Fun proc ->
     compile_proc self proc >>| fun proc ->
     let idx = Queue.length self.package.Bytecode.procs in
     Queue.enqueue self.package.Bytecode.procs proc;
     Bytecode.Fun idx
  | Anf.Lit lit -> Ok (Bytecode.Lit lit)
  | Anf.Register reg ->
     match Hashtbl.find self.colors reg with
     | Some idx -> Ok (Bytecode.Stack_var idx)
     | None -> Error Sequence.empty

and compile_opcode self =
  let open Result.Monad_infix in
  function
  | Anf.Assign(lval, rval) ->
     compile_operand self lval >>= fun lval ->
     compile_operand self rval >>| fun rval ->
     Bytecode.Assign(lval, rval)
  | Anf.Box contents ->
     List.fold_right ~f:(fun next acc ->
         acc >>= fun list ->
         compile_operand self next >>| fun next ->
         next::list
       ) ~init:(Ok []) contents
     >>| fun contents ->
     Bytecode.Box contents
  | Anf.Call(f, arg, args) ->
     compile_operand self f >>= fun f ->
     compile_operand self arg >>= fun arg ->
     List.fold_right ~f:(fun next acc ->
         acc >>= fun list ->
         compile_operand self next >>| fun next ->
         next::list
       ) ~init:(Ok []) args
     >>| fun args ->
     Bytecode.Call(f, arg, args)
  | Anf.Case _ -> failwith ""
  | Anf.Load o ->
     compile_operand self o >>| fun o -> Bytecode.Load o
  | Anf.Prim p -> Ok (Bytecode.Prim p)
  | Anf.Ref x ->
     compile_operand self x >>| fun x -> Bytecode.Ref x

and compile_instr self instrs =
  let open Result.Monad_infix in
  function
  | Anf.Let(reg, op, next) ->
     begin match Hashtbl.find self.colors reg with
     | None -> Error Sequence.empty
     | Some idx ->
        compile_opcode self op >>= fun opcode ->
        Queue.enqueue instrs { Bytecode.dest = Some idx; opcode = opcode };
        compile_instr self instrs next
     end
  | Anf.Let_rec(bindings, next) ->
     List.fold_right ~f:(fun (reg, op) acc ->
         acc >>= fun list ->
         match Hashtbl.find self.colors reg with
         | None -> Error Sequence.empty
         | Some idx ->
            Queue.enqueue instrs { Bytecode.dest = Some idx; opcode = Init };
            Ok ((idx, op)::list)
       ) ~init:(Ok []) bindings
     >>= fun bindings ->
     List.fold_right ~f:(fun (idx, op) acc ->
         acc >>= fun () ->
         compile_opcode self op >>| fun op ->
         Queue.enqueue instrs { Bytecode.dest = Some idx; opcode = op }
       ) ~init:(Ok ()) bindings
     >>= fun () ->
     compile_instr self instrs next
  | Anf.Seq(op, next) ->
     compile_opcode self op >>= fun opcode ->
     Queue.enqueue instrs { Bytecode.dest = None; opcode = opcode };
     compile_instr self instrs next
  | Anf.Break _ -> failwith ""

and compile_proc self proc =
  let open Result.Monad_infix in
  let instrs = Queue.create () in
  List.fold_right ~f:(fun reg acc ->
      acc >>= fun list ->
      match Hashtbl.find self.colors reg with
      | None -> Error Sequence.empty
      | Some idx ->
         Ok (idx::list)
    ) ~init:(Ok []) proc.Anf.params
  >>= fun _ ->
  compile_instr self instrs proc.Anf.body >>| fun () ->
  { Bytecode.instrs = instrs }
