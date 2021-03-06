open Base

type ('ann, 'fix) term =
  | App of 'fix * 'fix
  | Assign of 'fix * 'fix
  | Case of 'fix list * ('ann, 'fix) branch list
  | Constr of Type.adt * int
  | Extern_var of Path.t * Type.t
  | Lam of Ident.t * 'fix
  | Let of Ident.t * 'fix * 'fix
  | Let_rec of 'fix bind_group * 'fix
  | Lit of Literal.t
  | Prim of string * 'ann Ast.polytype
  | Ref
  | Seq of 'fix * 'fix
  | Var of Ident.t

and 'a bind_group = (Ident.t * 'a) list

and id_set = (Ident.t, Ident.comparator_witness) Set.t

and ('ann, 'term) branch = 'ann Pattern.t list * id_set * 'term

type 'ann t = {
    term : ('ann, 'ann t) term;
    ann : 'ann;
  }

type 'a item =
  | Top_let of
      'a t list * (Ident.t, Ident.comparator_witness) Set.t * 'a Pattern.t list
  | Top_let_rec of 'a t bind_group

type 'a file = {
    top_ann : 'a;
    env : (string, Ident.t, String.comparator_witness) Env.t;
    items : 'a item list;
  }
