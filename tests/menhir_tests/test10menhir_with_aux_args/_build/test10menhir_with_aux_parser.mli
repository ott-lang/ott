
(* The type of tokens. *)

type token = 
  | VAR of (string)
  | RPAREN
  | LPAREN
  | FOO
  | EOF
  | DOT
  | BACKSLASH

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val term_start: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Test10menhir_with_aux_ast.term)
