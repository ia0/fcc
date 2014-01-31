%{
  open Explicit
  exception Error
%}

%token <string> IDENT
%token <int> INT
%token FUN COLON COMMA FST SND BANG FOLD UNFOLD EQUAL
%token STAR ARROW FORALL PLUS PI MU TOP BOT INL INR
%token TRUE EXISTS AMP FIX BAR SEMICOLON GEN DOT
%token LPAREN RPAREN LCURLY RCURLY LSQUARE RSQUARE LANGLE RANGLE
%token EOF

%start <(string, string) Explicit.term> main

%%

main:
| a = term EOF
    { a }

typ:
| t = typneq COLON k = kind
    { Teq (t, k) }
| t = typneq
    { t }

typneq:
| FORALL LPAREN a = IDENT COLON k = kind RPAREN t = typneq
    { TFor (a, k, t) }
| PI LPAREN a = IDENT COLON k = kind RPAREN t = typneq
    { TPi (a, k, t) }
| MU a = IDENT t = typneq
    { TMu (a, t) }
| t = typinfix
    { t }

typinfix:
| t = typapp ARROW s = typinfix
    { TArr (t, s) }
| t = typapp STAR s = typinfix
    { TProd (t, s) }
| t = typapp PLUS s = typinfix
    { TSum (t, s) }
| t = typapp COMMA s = typinfix
    { TPair (t, s) }
| t = typapp
    { t }

typapp:
| t = typatom
    { t }

typatom:
| a = IDENT
    { TVar a }
| BOT
    { TBot }
| TOP
    { TTop }
| LPAREN RPAREN
    { TUnit }
| LCURLY a = IDENT EQUAL t = typ BAR pf = proofneq COLON pp = prop RCURLY
    { TPack (a, t, pf, pp) }
| FST t = typatom
    { TFst t }
| SND t = typatom
    { TSnd t }
| BANG t = typatom
    { TUnpack t }
| LPAREN t = typ RPAREN
    { t }

proof:
| pf = proofneq COLON pp = prop
    { Peq (pf, pp) }
| p = proofneq
    { p }

proofneq:
| EXISTS t = typneq
    { PExi t }
| FUN LPAREN a = IDENT COLON k = kind RPAREN p = proofneq
    { PLam (a, k, p) }
| FIX LPAREN c = IDENT COLON pp = prop RPAREN pf = proofneq
    { PFix (c, pp, pf) }
| p = proofinfix
    { p }

proofinfix:
| p1 = proofatom COMMA p2 = proofinfix
    { PPair (p1, p2) }
| p = proofapp
    { p }

proofapp:
| p = proofapp t = typatom
    { PApp (p, t) }
| p = proofatom
    { p }

proofatom:
| c = IDENT
    { PVar c }
| LPAREN RPAREN
    { PTrue }
| AMP t = typatom
    { PRes t }
| FST p = proofatom
    { PFst p }
| SND p = proofatom
    { PSnd p }
| g = coeratom LSQUARE t = typ RSQUARE
    { PCoer (g, t) }
| LPAREN p = proof RPAREN
    { p }

coer:
| g = coerinfix
    { g }

coerinfix:
| g1 = coeratom SEMICOLON g2 = coerinfix
    { GTrans (g1, g2) }
| g1 = coeratom STAR g2 = coerinfix
    { GProd (g1, g2) }
| g1 = coeratom PLUS g2 = coerinfix
    { GSum (g1, g2) }
| g = coeratom
    { g }

coeratom:
| LANGLE RANGLE
    { GRefl }
| BANG g = coeratom
    { GWeak g }
| LPAREN g1 = coeratom COLON t = typatom RPAREN ARROW g2 = coeratom
    { GArr (g1, t, g2) }
| GEN LPAREN a = IDENT LSQUARE p = proof RSQUARE COLON k = kind RPAREN
    { GGen (a, (Kexi (p, k))) }
| LSQUARE t = typ RSQUARE
    { GInst t }
| UNFOLD
    { GUnfold }
| FOLD a = IDENT t = typatom
    { GFold (a, t) }
| TOP
    { GTop }
| BOT t = typatom
    { GBot t }
| LPAREN g = coer RPAREN
    { g }

cotenv:
| h = cotenv COMMA LPAREN a = IDENT LSQUARE p = proof RSQUARE COLON k = kind RPAREN
    { HCons (h, a, (Kexi (p, k))) }
| DOT
    { HNil }

kind:
| k1 = kindatom STAR k2 = kind
    { WKProd (k1, k2) }
| k = kindatom
    { k }

kindatom:
| STAR
    { WKStar }
| i = INT
    { if i = 1 then WKOne else raise Error }
| LCURLY a = IDENT COLON k = kind BAR p = prop RCURLY
    { WKRes (a, k, p) }
| LPAREN k = kind RPAREN
    { k }

prop:
| EXISTS k = kind
    { WPExi k }
| FORALL LPAREN a = IDENT COLON k = kind RPAREN p = propinfix
    { WPFor (a, k, p) }
| p = propinfix
    { p }

propinfix:
| p1 = propatom COMMA p2 = propinfix
    { WPAnd (p1, p2) }
| t = typinfix LANGLE s = typ
    { WPCoer (HNil, t, s) }
| h = cotenv BAR t = typ LANGLE s = typ
    { WPCoer (h, t, s) }
| p = propatom
    { p }

propatom:
| TRUE
    { WPTrue }
| LPAREN p = prop RPAREN
    { p }

term:
| FUN LPAREN x = IDENT COLON t = typ RPAREN a = term
    { ELam (x, t, a) }
| g = coer a = term
    { ECoer (g, a) }
| a = termapp
    { a }

termapp:
| a = termapp b = termatom
    { EApp (a, b) }
| a = termatom
    { a }

termatom:
| x = IDENT
    { EVar x }
| INL a = termatom t = typatom
    { EInl (a, t) }
| INR t = typatom a = termatom
    { EInr (t, a) }
| LPAREN a = term RPAREN
    { a }

