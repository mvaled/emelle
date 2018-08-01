open Base

type t = {
    mutable vargen : int;
    registers : (string, int) Hashtbl.t;
  }

let fresh_register st =
  st.vargen <- st.vargen + 1;
  st.vargen - 1

let rec pattern_of_ast_pattern (_, node) =
  match node with
  | Ast.Con(typename, con, pats) ->
     Pattern.Con(typename, con, List.map ~f:pattern_of_ast_pattern pats)
  | Ast.Var _ -> Pattern.Wild
  | Ast.Wild -> Pattern.Wild

let rec term_of_ast_pattern st def cont (ann, node) =
  let term =
    match node with
    | Ast.Con(typename, constr, args) ->
       let rec helper idx arg_regs = function
         | [] ->
            let rec helper = function
              | [] -> cont
              | ((arg, reg)::xs) ->
                 term_of_ast_pattern st (Term.Var reg) (helper xs) arg
            in helper arg_regs
         | (arg::args) ->
            let reg = fresh_register st in
            let def = Term.Select(typename, constr, idx, def) in
            let body = helper (idx + 1) ((arg, reg)::arg_regs) args in
            Term.Let([reg, def], body)
       in helper 0 [] args
    | Ast.Var id ->
       let reg = fresh_register st in
       (* Map the identifier to its register *)
       let _ = Hashtbl.add st.registers ~key:id ~data:reg in
       Term.Let([(reg, def)], cont)
    | Ast.Wild ->
       let reg = fresh_register st in
       Term.Let([reg, def], cont)
  in Term.Ann { ann = ann; term = term }
