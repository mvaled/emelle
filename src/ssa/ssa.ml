open Base

type cont =
  | Block of int (** A basic block other than the entry *)
  | Entry (** The entry basic block *)
  | Return (** Return from the function *)
  | Switch (** The continuation is dynamic *)

type operand = Anf.operand

type opcode =
  | Assign of operand * operand
  | Box of operand list
  | Break of cont
  | Call of operand * operand * operand list
  | Contents of operand
  | Fun of int * operand list
  | Index of operand * int
  | Load of operand
  | Phi of (int * operand) list
  | Prim of string
  | Ref of operand

type instr = {
    dest : int option;
    opcode : opcode;
  }

type basic_block = {
    instrs : instr Queue.t;
    tail : cont;
  }

type proc = {
    entry : basic_block;
    blocks : (int, basic_block, Int.comparator_witness) Map.t;
    return : Anf.operand;
  }

type package = {
    procs : (int, proc, Int.comparator_witness) Map.t;
  }
