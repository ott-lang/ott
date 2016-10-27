(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2008                                                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

type parser_transform
val defn_transform : Types.prodname -> parser_transform

exception Parse_error of Types.loc * string
val ident_string : string
val parse_lu_lowerbound : (char, Types.suffixnum) Types.parser
val parse_lu_upperbound :
  string list -> (char, Types.suffix_item) Types.parser
val one_parse :
  (('a list -> 'b -> unit) -> char list -> 'c) ->
  string -> 'b Types.optionprime
val make_ident_lexer :
  Types.metavarroot list ->
  Types.metavarroot list ->
  Types.nontermroot list ->
  string -> Lexing.position -> Types.mytoken Types.optionprime
val make_ident_lexer_of_syntaxdefn :
  Types.syntaxdefn ->
  string -> Lexing.position -> Types.mytoken Types.optionprime
val cd_env_of_syntaxdefn : Types.syntaxdefn -> Types.cd_env
val strip_trailing_whitespace : string -> string
val make_parser : Types.syntaxdefn -> Types.made_parser

val parse_complete : 
  Types.made_parser -> Types.nontermroot -> bool -> string -> Types.symterm list

val just_one_parse :
  ?transform: parser_transform ->
  Types.syntaxdefn ->
  Types.made_parser ->
  Types.nontermroot -> bool -> Types.loc -> string -> Types.symterm

val test_parse :
  Types.pp_mode -> Types.syntaxdefn -> Types.nontermroot -> bool -> string -> unit
