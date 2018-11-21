open Base

type register = int

and operand =
  | Constr of int
  | Extern_var of Path.t
  | Free_var of int (** In the proc's environment *)
  | Lit of Literal.t
  | Register of int

and opcode =
  | Assign of operand * operand
  | Box of operand list
  | Call of operand * operand * operand array
    (** proc, first arg, rest args *)
  | Case of operand list * decision_tree * instr array
    (** discrs, decision tree, jump table *)
  | Fun of proc
  | Load of operand
  | Pop
  | Prim of string
  | Ref of operand

and instr =
  | Let of register * opcode * instr
  | Let_rec of (register * opcode) list * instr
  | Return of opcode
  | Seq of opcode * instr

and proc = {
    env : operand array; (** The captured variables *)
    params : register list;
    body : instr;
  }

and occurrence = {
    id : int;
    node : occurrence';
    parent : occurrence option;
  }

and occurrence' =
  | Index of int
  | Contents

and occurrences = occurrence list

and leaf_id = int

and decision_tree =
  | Deref of int * occurrence * decision_tree
  | Fail
  | Leaf of leaf_id * (Ident.t * occurrence) list * int
    (** A leaf holds a mapping from idents to pattern match occurrences. *)
  | Switch of int * occurrence * (int, decision_tree) Hashtbl.t * decision_tree
    (** A switch holds the swap index, the scrutinee occurrence, a map from
        constructors to decision trees, and a default decision tree. *)
