open Test10menhir_with_aux_ast

module Lexer = Test10menhir_with_aux_lexer
module Parser = Test10menhir_with_aux_parser
module PP = Test10menhir_with_aux_parser_pp


(*
let rec pp_term t : string = 
  match t with
  | T_var x -> Printf.sprintf "%s" x
  | T_lam (x,t) -> Printf.sprintf "\\%s. %s" x (pp_term t)
  | T_app (t,t') -> Printf.sprintf "(%s %s)" (pp_term t) (pp_term t')
  | T_paren t -> Printf.sprintf "(%s)" (pp_term t) 
*)

let () = Printf.printf "enter lambda calculus terms, in the grammar t ::= x | t t | \\x.t | (t)\n"

let process (line : string) =
  let linebuf = Lexing.from_string line in
  try
    (* Run the parser on this line of input. *)
    let t = (Parser.term_start Lexer.token linebuf) in
    Printf.printf "   "; PPrint.ToChannel.compact stdout (PP.pp_raw_term t); Printf.printf "\n";
    Printf.printf "   "; PPrint.ToChannel.compact stdout (PP.pp_term t); Printf.printf "\n"
  with
  | Lexer.Error msg ->
      Printf.fprintf stdout "%s" msg
  | Parser.Error ->
      Printf.fprintf stdout "%s^\nAt offset %d: syntax error.\n" (String.make (Lexing.lexeme_start linebuf) ' ') (Lexing.lexeme_start linebuf)

(*
let process (optional_line : string option) =
  match optional_line with
  | None ->
      ()
  | Some line ->
      process line

let rec repeat channel =
  (* Attempt to read one line. *)
  let optional_line, continue = Lexer.line channel in
  process optional_line;
  if continue then
    repeat channel

let () = 
  repeat (Lexing.from_channel stdin)
  *)

let rec foo () =
  let s = read_line () in
  process s; flush stdout;
  foo ()

let () = foo ()


