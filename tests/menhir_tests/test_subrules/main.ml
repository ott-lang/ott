open Test_subrules_ast

module Lexer = Test_subrules_lexer
module Parser = Test_subrules_parser
module PP = Test_subrules_parser_pp

let process (line : string) =
  let linebuf = Lexing.from_string line in
  try
    (* Run the parser on this line of input. *)
    let t = (Parser.expr_start Lexer.token linebuf) in
    Printf.printf "   "; PPrint.ToChannel.compact stdout (PP.pp_raw_expr t); Printf.printf "\n";
    Printf.printf "   "; PPrint.ToChannel.compact stdout (PP.pp_expr t); Printf.printf "\n"
  with
  | Lexer.Error msg ->
      Printf.fprintf stdout "%s" msg
  | Parser.Error ->
      Printf.fprintf stdout "%s^\nAt offset %d: syntax error.\n" (String.make (Lexing.lexeme_start linebuf) ' ') (Lexing.lexeme_start linebuf)

let () = Printf.printf "Enter a Test_subrules expression:\n"

let rec run () =
  let s = read_line () in
  process s; flush stdout;
  run ()

let () = run ()
