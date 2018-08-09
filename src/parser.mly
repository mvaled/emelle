%{
%}

%token AND
%token CASE
%token ELSE
%token FUN
%token IF
%token IN
%token LET
%token REC
%token THEN
%token TYPE
%token WITH

%token LPARENS
%token RPARENS
%token ARROW
%token BAR
%token COLON
%token COLONCOLON
%token COMMA
%token EQUALS
%token UNDERSCORE

%token <string> IDENT

%token EOF

%start <(Lexing.position * Lexing.position) Ast.expr> file

%%

file: expr EOF { $1 };

expr:
  | expr_kw { $1 }
  ;

expr_kw:
  | CASE test = expr WITH option(BAR) cases = separated_list(BAR, case) {
        (($symbolstartpos, $endpos), Ast.Case(test, cases))
      }
  | FUN pattern ARROW expr {
        (($symbolstartpos, $endpos), Ast.Lam($2, $4))
      }
  | LET bindings = separated_list(AND, binding) IN body = expr {
        (($symbolstartpos, $endpos), Ast.Let(bindings, body))
      }
  | LET REC bindings = separated_list(AND, rec_binding) IN body = expr {
        (($symbolstartpos, $endpos), Ast.Let_rec(bindings, body))
      }
  | expr_app { $1 }
  ;

case:
  | pattern ARROW expr { ($1, $3) }
  ;

binding:
  | pattern EQUALS expr { ($1, $3) }
  ;

rec_binding:
  | IDENT EQUALS expr { ($1, $3) }
  ;

expr_app:
  | expr_app expr_atom { (($symbolstartpos, $endpos), Ast.App($1, $2)) }
  | expr_atom { $1 }
  ;

expr_atom:
  | IDENT { (($symbolstartpos, $endpos), Ast.Var (Ident.Local $1)) }
  | LPARENS expr RPARENS { $2 }
  ;

pattern:
  | typename = IDENT COLONCOLON con = IDENT args = list(pattern) {
         (($symbolstartpos, $endpos), Ast.Con(Ident.Local typename, con, args))
      }
  | IDENT { (($symbolstartpos, $endpos), Ast.Var $1) }
  | UNDERSCORE { (($symbolstartpos, $endpos), Ast.Wild) }
  | LPARENS pattern RPARENS { $2 }
  ;
