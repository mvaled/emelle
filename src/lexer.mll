{
  open Base
  open Parser

  exception Error of string

  let keywords =
    Hashtbl.of_alist_exn
      (module String)
      [ "and", AND
      ; "case", CASE
      ; "else", ELSE
      ; "forall", FORALL
      ; "fun", FUN
      ; "if", IF
      ; "in", IN
      ; "let", LET
      ; "rec", REC
      ; "self", SELF
      ; "then", THEN
      ; "type", TYPE
      ; "with", WITH ]
}

let whitespace = [' ' '\t']
let digit = ['0'-'9']
let upper = ['A'-'Z']
let lower = ['a'-'z']
let alphanum = upper | lower | digit
let uident = upper (alphanum | '_' | '\'')*
let lident = lower (alphanum | '_' | '\'')*

rule expr = parse
  | whitespace { expr lexbuf }
  | '\n' { Lexing.new_line lexbuf; expr lexbuf }
  | '(' { LPARENS }
  | ')' { RPARENS }
  | "->" { ARROW }
  | '|' { BAR }
  | ':' { COLON }
  | "::" { COLONCOLON }
  | ',' { COMMA }
  | '.' { DOT }
  | '=' { EQUALS }
  | '*' { STAR }
  | '_' { UNDERSCORE }
  | uident as str { UIDENT str }
  | lident as str {
      match Hashtbl.find keywords str with
      | Some keyword -> keyword
      | None -> LIDENT str
    }
  | eof { EOF }
  | _ { raise (Error (Lexing.lexeme lexbuf)) }

{
}
