open Base

module Label = struct
  module T = struct
    type t =
      | Entry
      | Block of int
    [@@deriving compare, sexp]
  end
  include T
  include Comparator.Make(T)
end

type operand = Anf.operand

type jump =
  | Break of Label.t (** Break to a basic block *)
  | Fail (** Pattern match failure *)
  | Return (** Return from the function *)
  | Switch of operand * (int * Label.t) list * Label.t
      (** The jump is dynamic *)

type opcode =
  | Assign of operand * operand
  | Box of operand list
  | Box_dummy of int
  | Call of operand * operand * operand list
  | Deref of operand
  | Fun of int * operand list
  | Get of operand * int
  | Load of operand
  | Memcopy of operand * operand
  | Phi of int
  | Prim of string
  | Ref of operand

type instr = {
    dest : int option;
    opcode : opcode;
  }

type basic_block = {
    mutable preds : (Label.t, operand array, Label.comparator_witness) Map.t;
    instrs : instr Queue.t;
    jump : jump;
  }

type proc = {
    params : Anf.register list;
    entry : basic_block;
    blocks : (int, basic_block, Int.comparator_witness) Map.t;
    before_return : Label.t;
    return : Anf.operand;
    interf_graph : Interf.t;
  }

type package = {
    procs : (int, proc, Int.comparator_witness) Map.t;
    main : proc
  }
