open Base

type t =
  { buffer : Buffer.t }

let create () = { buffer = Buffer.create 12 }

let to_string pp = Buffer.contents pp.buffer

let print_ident pp (package, name) =
     Buffer.add_string pp.buffer package;
     Buffer.add_string pp.buffer ".";
     Buffer.add_string pp.buffer name

let print_path pp = function
  | Ast.Internal str ->
     Buffer.add_string pp.buffer str
  | Ast.External(l, r) ->
     Buffer.add_string pp.buffer l;
     Buffer.add_string pp.buffer ".";
     Buffer.add_string pp.buffer r

let with_necessary_parens f pp parent_prec prec =
  if parent_prec >= prec then (
    Buffer.add_char pp.buffer '(';
    f pp;
    Buffer.add_char pp.buffer ')';
  ) else
    f pp

let rec print_type pp parent_prec ty =
  match ty.Type.node with
  | Type.App(f, x) ->
     let prec = 1 in
     with_necessary_parens (fun pp ->
         print_type pp (prec - 1) f;
         Buffer.add_char pp.buffer ' ';
         print_type pp prec x
       ) pp parent_prec prec
  | Type.Nominal id ->
     print_ident pp id
  | Type.Prim Type.Arrow ->
     Buffer.add_string pp.buffer "(->)"
  | Type.Prim Type.Char ->
     Buffer.add_string pp.buffer "Char"
  | Type.Prim Type.Int ->
     Buffer.add_string pp.buffer "Int"
  | Type.Prim Type.Float ->
     Buffer.add_string pp.buffer "Float"
  | Type.Prim Type.Ref ->
     Buffer.add_string pp.buffer "Ref";
  | Type.Prim Type.String ->
     Buffer.add_string pp.buffer "String"
  | Type.Var { ty = Some ty; _ } ->
     print_type pp parent_prec ty
  | Type.Var { id; quant; _ } ->
     begin match quant with
     | Type.Exists _ ->
        Buffer.add_char pp.buffer '_';
     | _ -> ()
     end;
     Buffer.add_char pp.buffer 't';
     Buffer.add_string pp.buffer (Int.to_string id)

let print_error pp e =
  begin match e with
  | Message.Abstract_type id ->
     Buffer.add_string pp.buffer "Abstract type ";
     print_ident pp id
  | Message.Type_unification_fail(t1, t2) ->
     Buffer.add_string pp.buffer "Type unification fail: ";
     print_type pp (-1) t1;
     Buffer.add_string pp.buffer " and ";
     print_type pp (-1) t2
  | Message.Unreachable str ->
     Buffer.add_string pp.buffer "Unreachable ";
     Buffer.add_string pp.buffer str
  | Message.Unresolved_id id ->
     Buffer.add_string pp.buffer "Unresolved id ";
     print_ident pp id
  | Message.Unresolved_path path ->
     Buffer.add_string pp.buffer "Unresolved_path ";
     print_path pp path
  | _ ->
     Buffer.add_string pp.buffer "other"
  end;
  Buffer.add_char pp.buffer '\n'
