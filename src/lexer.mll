{
  open Base
  open Parser

  exception Lexer_error of string

  let keywords =
    Hashtbl.of_alist_exn (module String) [
        ("and", AND);
        ("case", CASE);
        ("else", ELSE);
        ("fun", FUN);
        ("if", IF);
        ("in", IN);
        ("let", LET);
        ("rec", REC);
        ("then", THEN);
        ("type", TYPE);
        ("with", WITH)
      ]
}

let whitespace = [' ' '\t' '\n']
let digit = ['0'-'9']
let upper = ['A'-'Z']
let lower = ['a'-'z']
let alphanum = upper | lower | digit
let ident = (upper | lower) (alphanum | '_' | '\'')*

rule expr = parse
  | whitespace { expr lexbuf }
  | '(' { LPARENS }
  | ')' { RPARENS }
  | "->" { ARROW }
  | '|' { BAR }
  | ':' { COLON }
  | "::" { COLONCOLON }
  | ',' { COMMA }
  | '=' { EQUALS }
  | '_' { UNDERSCORE }
  | ident as str {
      match Hashtbl.find keywords str with
      | Some keyword -> keyword
      | None -> IDENT str
    }
  | eof { EOF }
  | _ { raise (Lexer_error (Lexing.lexeme lexbuf)) }

{
}
