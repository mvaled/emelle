open Base

type register = int

and operand =
  | Extern_var of Path.t
  | Free_var of int (** In the proc's environment *)
  | Lit of Literal.t
  | Register of int

and opcode =
  | Assign of operand * operand
  | Box of operand list
  | Call of operand * operand * operand list
    (** proc, first arg, rest args *)
  | Case of operand list * decision_tree * join_point list
    (** discrs, decision tree, jump table *)
  | Fun of proc
  | Load of operand
  | Prim of string
  | Ref of operand

and instr =
  | Break of operand
  | Let of register * opcode * instr
  | Let_rec of (register * opcode) list * instr
  | Seq of opcode * instr

and proc = {
    env : operand list; (** The captured variables *)
    params : register list;
    body : instr;
  }

and decision_tree =
  | Deref of operand * register * decision_tree
  | Fail
  | Leaf of jump
    (** A leaf holds a mapping from idents to pattern match occurrences. *)
  | Switch of
      register * operand * (int, register list * decision_tree) Hashtbl.t
      * decision_tree
    (** A switch holds the scrutinee occurrence and a map from constructors to
        decision trees, and a default decision tree. *)

(** A join point is like a basic block with parameters *)
and join_point = register list * instr

(** A jump is a branch instruction to a join point with the given arguments *)
and jump = operand list * int
