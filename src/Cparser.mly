%{
  open Implicit
  exception Error
%}

%token <int> INT
%token COLON EQUAL OK ERR COMMA
%token VAR LAM APP
%token TVAR TARR TFOR
%token KSTAR KONE KPROD
%token LPAREN RPAREN

%start <(Implicit.term * Implicit.typ) option> main

%%

main:
| EQUAL OK LPAREN a = term COMMA t = typ RPAREN COLON
    { Some (a, t) }
| EQUAL ERR
    { None }

term:
| VAR i = INT
    { Var i }
| LAM a = termatom
    { Lam a }
| APP a = termatom b = termatom
    { App (a, b) }
| a = termatom
    { a }

termatom:
| LPAREN a = term RPAREN
    { a }

typ:
| TVAR i = INT
    { TVar i }
| TARR t = typatom s = typatom
    { TArr (t, s) }
| TFOR k = kindatom t = typatom
    { TFor (k, t) }
| t = typatom
    { t }

typatom:
| LPAREN t = typ RPAREN
    { t }

kind:
| KPROD k1 = kindatom k2 = kindatom
    { KProd (k1, k2) }
| k = kindatom
    { k }

kindatom:
| KSTAR
    { KStar }
| KONE
    { KOne }
| LPAREN k = kind RPAREN
    { k }
