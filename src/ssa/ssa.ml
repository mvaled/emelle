open Base

type label = int

type operand = Anf.operand

type cont =
  | Block of label (** A basic block other than the entry *)
  | Entry (** The entry basic block *)
  | Fail (** Pattern match failure *)
  | Halt
  | Return (** Return from the function *)
  | Switch of operand * (int * label) list * int
      (** The continuation is dynamic *)

type opcode =
  | Assign of operand * operand
  | Box of operand list
  | Break of cont
  | Call of operand * operand * operand list
  | Contents of operand
  | Deref of operand
  | Fun of int * operand list
  | Get of operand * int
  | Index of operand * int
  | Load of operand
  | Phi of (label * operand) Queue.t
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
    blocks : (label, basic_block, Int.comparator_witness) Map.t;
    return : Anf.operand;
  }

type package = {
    procs : (int, proc, Int.comparator_witness) Map.t;
  }
