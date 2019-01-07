open Base

type instr = {
    dest : int option;
    opcode : Ssa.opcode;
    ending_regs : (int, Int.comparator_witness) Set.t;
  }

type basic_block = {
    instrs : instr list;
    jump : Ssa.jump;
  }

type proc = {
    params : Anf.register list;
    entry : Ssa.Label.t;
    blocks : (int, basic_block, Int.comparator_witness) Map.t;
    before_return : Ssa.Label.t;
    return : Anf.operand;
  }

type package = {
    procs : (int, proc, Int.comparator_witness) Map.t;
    main : proc
  }
