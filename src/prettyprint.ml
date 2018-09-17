open Base

type t =
  { buffer : Buffer.t }

let create () = { buffer = Buffer.create 12 }

let to_string pp = Buffer.contents pp.buffer

let rec print_ident pp = function
  | Ident.Root str ->
     Buffer.add_string pp.buffer str
  | Ident.Dot(id, str) ->
     print_ident pp id;
     Buffer.add_string pp.buffer "::";
     Buffer.add_string pp.buffer str

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
  | Type.Prim Type.Int ->
     Buffer.add_string pp.buffer "Int"
  | Type.Prim Type.Float ->
     Buffer.add_string pp.buffer "Float"
  | Type.Var { ty = Some ty; _ } ->
     print_type pp parent_prec ty
  | Type.Var { id; _ } ->
     Buffer.add_char pp.buffer 't';
     Buffer.add_string pp.buffer (Int.to_string id)
