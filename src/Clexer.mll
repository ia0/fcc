{
  open Cparser
  exception Error of string
}

rule token = parse
| [' ' '\t' '\n'] { token lexbuf }
| ['0'-'9']+ as i { INT (int_of_string i) }
| "OK" { OK }
| "Err" { ERR }
| "=" { EQUAL }
| ":" { COLON }
| "," { COMMA }
| "Var" { VAR }
| "Lam" { LAM }
| "App" { APP }
| "TVar" { TVAR }
| "TArr" { TARR }
| "TFor" { TFOR }
| "KStar" { KSTAR }
| "KOne" { KONE }
| "KProd" { KPROD }
| '(' { LPAREN }
| ')' { RPAREN }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }

