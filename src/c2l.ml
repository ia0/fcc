open Implicit

let () =
  if Array.length Sys.argv < 3
  then (Printf.eprintf "Usage: %s <term> <type>" Sys.argv.(0); exit 1)
  else
  let buffer = Lexing.from_channel stdin in
  try
    let r = Cparser.main Clexer.token buffer in
    match r with
    | Some (a, t) ->
      let fa = open_out Sys.argv.(1) in
      Printf.fprintf fa "%s\n" (print_term a);
      close_out fa;
      let fi = open_out Sys.argv.(2) in
      Printf.fprintf fi "%s\n" (print_typ t);
      close_out fi
    | None -> exit 1
  with
  | Clexer.Error msg -> Printf.fprintf stderr "%s%!\n" msg; exit 1
  | Cparser.Error -> Printf.fprintf stderr
    "At offset %d: syntax error.\n%!" (Lexing.lexeme_start buffer); exit 1

