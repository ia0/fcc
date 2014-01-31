{
  open Lparser
  exception Error of string
}

rule token = parse
| [' ' '\t' '\n'] { token lexbuf }
| ['0'-'9']+ as i { INT (int_of_string i) }
| "fun" { FUN }
| "gen" { GEN }
| "forall" { FORALL }
| "exists" { EXISTS }
| "pi" { PI }
| "mu" { MU }
| "fix" { FIX }
| "fst" { FST }
| "snd" { SND }
| "inl" { INL }
| "inr" { INR }
| "fold" { FOLD }
| "unfold" { UNFOLD }
| "Top" { TOP }
| "Bot" { BOT }
| "True" { TRUE }
| '=' { EQUAL }
| '.' { DOT }
| ':' { COLON }
| ';' { SEMICOLON }
| ',' { COMMA }
| '*' { STAR }
| '+' { PLUS }
| "->" { ARROW }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LCURLY }
| '}' { RCURLY }
| '[' { LSQUARE }
| ']' { RSQUARE }
| '<' { LANGLE }
| '>' { RANGLE }
| '|' { BAR }
| '!' { BANG }
| '&' { AMP }
| ['A'-'Z' 'a'-'z']+ as id { IDENT id }
| eof { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }

