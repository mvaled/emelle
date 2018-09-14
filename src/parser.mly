%{
%}

%token AND
%token CASE
%token ELSE
%token FORALL
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
%token DOT
%token EQUALS
%token UNDERSCORE

%token <string> IDENT

%token EOF

%start <(Lexing.position * Lexing.position) Ast.expr> file
%start <(Lexing.position * Lexing.position) Ast.expr> expr_eof
%start <Ast.monotype> monotype_eof
%start <Ast.adt> adt_eof

%%

file: expr EOF { $1 };
expr_eof: expr EOF { $1 };
monotype_eof: monotype EOF { $1 };
adt_eof: adt EOF { $1 }

adt:
  | IDENT list(IDENT) EQUALS option(BAR) separated_list(BAR, constr) {
      Ast.{ name = $1; typeparams = $2; constrs = $5 }
    }
  ;

constr: IDENT list(monotype) { ($1, $2) };

polytype: FORALL list(IDENT) DOT monotype { Ast.Forall($2, $4) };

monotype:
  | monotype_app ARROW monotype { Ast.TApp(Ast.TApp(Ast.TArrow, $1), $3) }
  | monotype_app { $1 }
  ;

monotype_app:
  | monotype_app monotype_atom { Ast.TApp($1, $2) }
  | monotype_atom { $1 }
  ;

monotype_atom:
  | IDENT { Ast.TVar (Ident.Local $1) }
  | LPARENS ARROW RPARENS { Ast.TArrow }
  | LPARENS monotype RPARENS { $2 }
  ;

expr:
  | expr_kw { $1 }
  ;

expr_kw:
  | CASE test = expr WITH option(BAR) cases = separated_list(BAR, case) {
        (($symbolstartpos, $endpos), Ast.Case(test, cases))
      }
  | FUN option(BAR) lambda_case list(BAR lambda_case { $2 }) {
        (($symbolstartpos, $endpos), Ast.Lam($3, $4))
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

lambda_case:
  | pattern list(pattern) ARROW expr { ($1, $2, $4) }
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
  | typename = IDENT COLONCOLON con = IDENT {
        (($symbolstartpos, $endpos), Ast.Con(Ident.Local typename, con, []))
      }
  | LPARENS
      typename = IDENT COLONCOLON con = IDENT arg = pattern args = list(pattern)
    RPARENS {
        (($symbolstartpos, $endpos)
        , Ast.Con(Ident.Local typename, con, arg::args))
      }
  | IDENT { (($symbolstartpos, $endpos), Ast.Var $1) }
  | UNDERSCORE { (($symbolstartpos, $endpos), Ast.Wild) }
  | LPARENS pattern RPARENS { $2 }
  ;
