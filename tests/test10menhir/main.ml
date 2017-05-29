open Test10menhir_ast

module Parser = Test10menhir_parser

module Lexer = Test10menhir_lexer

let rec pp_term t : string = 
  match t with
  | T_var x -> Printf.sprintf "%s" x
  | T_lam (x,t) -> Printf.sprintf "\\%s. %s" x (pp_term t)
  | T_app (t,t') -> Printf.sprintf "(%s %s)" (pp_term t) (pp_term t')
  | T_paren t -> Printf.sprintf "(%s)" (pp_term t) 

let process (line : string) =
  let linebuf = Lexing.from_string line in
  try
    (* Run the parser on this line of input. *)
    let t = (Parser.term_start Lexer.token linebuf) in
    Printf.printf "   %s\n" (pp_term t)
  with
  | Lexer.Error msg ->
      Printf.fprintf stderr "%s" msg
  | Parser.Error ->
      Printf.fprintf stderr "At offset %d: syntax error.\n" (Lexing.lexeme_start linebuf)

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
  process s;
  foo ()

let () = foo ()


