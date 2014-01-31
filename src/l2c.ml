open Explicit

let () =
  let buffer = Lexing.from_channel stdin in
  try
    let a = Lparser.main Llexer.token buffer in
    print_endline (print_term (resolve_term [] [] a))
  with
  | Llexer.Error msg -> Printf.fprintf stderr "%s%!\n" msg; exit 1
  | Lparser.Error -> Printf.fprintf stderr
    "At offset %d: syntax error.\n%!" (Lexing.lexeme_start buffer); exit 1

