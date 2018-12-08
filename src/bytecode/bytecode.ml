open Base

type operand =
  | Extern_var of Path.t
  | Free_var of int
  | Lit of Literal.t
  | Fun of int
  | Stack_var of int

type opcode =
  | Assign of operand * operand
  | Box of operand list
  | Break of int
  | Call of operand * operand * operand list
  | Contents of operand
  | Index of operand * int
  | Init
  | Load of operand
  | Prim of string
  | Ref of operand
  | Switch of operand * int list * int

type instr = {
    dest : int option; (** Stack offset to store result *)
    opcode : opcode;
  }

type proc = {
    instrs : instr Queue.t;
  }

type package = {
    procs : proc Queue.t;
  }
