(**************************************************************************)
(*                    ocamllex/menhir partial backend                     *)
(*                                                                        *)
(*                     Peter Sewell, University of Cambridge              *)
(*                                                                        *)
(*  Copyright 2017                                                        *)
(**************************************************************************)

(**************************************************************************)
(*                    ocamllex/ocamlyacc backend                          *)
(*                                                                        *)
(*                     Viktor Vafeiadis, MPI-SWS                          *)
(*                                                                        *)
(*  Copyright 2011                                                        *)
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

(*

This is a partial Ott backend to produce, given an Ott input file,
sketch source files for the menhir/ocamllex parser and lexer generators.

In general this is impossible: 
- fundamentally, because an Ott grammar can be an arbitrary
   context-free grammar, whereas menhir supports LR grammars; and
- practically, because one may also want to hand-tune the grammar or
   lexer, e.g. for decent parse error messages/recovery

Hence the idea is, given a relatively stable Ott source, to produce
menhir/ocamllex source files that can be hand-edited, to take some of
the tedious work out of producing a parser and lexer. This contrasts
with normal Ott usage, where we have aimed to produce files that do
not need hand-editing, so that the Ott source remains the principal
source.

(One can imagine fancy mechanisms for maintaining both a context-free
and LR grammar in sync, eg by writing an LR Ott grammar but including
annotations saying that some rules should be inlined in the
context-free grammar, or with ad hoc transformations for standard
language idioms.  But none of those are here.)

Moreover, the implementation is also partial.  Currently it:
- does not handle synthesised aux rules, or recording of source location info
- does not handle ott lists
- does not support subrules properly 
   (it should only take the maximal elements from the subrule order)
- does not support syntactic sugar productions properly

There is a minimal working example in tests/test10menhir. In the Ott source:
- metavar definitions should have ocaml and ocamllex homs, to specify
   their OCaml type and the ocamllex regexps.
- grammar rules that are start symbols should have "menhir_start" homs

Command-line usage should specify single .ml, .mll, and .mly output
files, in a single run of Ott (as the files have to refer to each
other).

There was a previous attempt at an ocamllex/ocamlyacc backend, by
Viktor Vafeiadis in 2011, but that code seemed to be very partial.
This implementation reuses a little of that infrastructure. 

*)


open Types;;

(* which rules and productions to include *)
let suppress_prod yo p = 
  let suppressed_category = 
    StringSet.exists (fun x -> List.mem x yo.ppm_suppressed_categories)
      p.prod_categories in
  suppressed_category || (not(yo.ppm_show_meta) && p.prod_meta && not(p.prod_sugar))

let suppress_rule yo r = 
  let suppressed_ntr = 
    List.mem r.rule_ntr_name yo.ppm_suppressed_ntrs
  in
  suppressed_ntr || (not(yo.ppm_show_meta) && r.rule_semi_meta)


(* tokens arise from terminals and metavardefns *)
type token_kind = 
  | TK_terminal 
  | TK_metavar of string (* ocamllex hom *) * string (* ocaml hom, for type*)

type token_data = 
    (string(*synthesised token name*) * string(*terminal or metavarroot*) * token_kind) list


(* find the token associated with a terminal or metavarroot *) 
let token_of_terminal ts t0 = 
  try let (tn,_,_) = List.find (function td -> match td with (tn,t,TK_terminal) when t=t0 -> true | _ -> false) ts in tn 
  with Not_found -> raise (Failure "token_of_terminal not found")

let token_of_metavarroot ts mvr = 
  try let (tn,_,_) = List.find (function td -> match td with (tn,t,TK_metavar _) when t=mvr -> true | _ -> false) ts in tn 
  with Not_found -> raise (Failure "token_of_metavarroot not found")


(* pull out all terminals actually used in (non-suppressed) productions *)
let rec get_terminals_of_element e = 
  match e with
  | Lang_terminal t -> [t]
  | Lang_list elb -> 
      let ts = List.flatten (List.map get_terminals_of_element elb.elb_es) in
      (match elb.elb_tmo with
      | None -> ts
      | Some t -> t::ts)
  | _ -> []

let get_terminals_of_prod yo p = 
  if suppress_prod yo p then 
    [] 
  else
    List.flatten (List.map get_terminals_of_element p.prod_es)

let get_terminals_of_syntaxdefn yo xd =
  let ts = 
    List.flatten 
      (List.map 
         (fun r -> 
           if suppress_rule yo r then
             []
           else List.flatten (List.map (get_terminals_of_prod yo) r.rule_ps))
         xd.xd_rs) in
  Auxl.remove_duplicates ts


(* make ocamllex token names by uniformly replacing non-alphabetic
characters and smashing to uppercase, then uniqueify (tokens from
terminals and from metavars) afterwards by appending a number if
necessary, keeping the result in a lookup table *)

(* token name munging *)
let token_escape_map = 
  [
   ('!', "BANG");
   ('\"', "QUOTE");
    ('#', "HASH");
    ('$', "DOLLAR");
    ('%', "PERCENT");
    ('&', "AMPERSAND");
    ('\'', "APOSTROPHE");
    ('(', "LPAREN");
    (')', "RPAREN");
    ('*', "STAR");
    ('+', "PLUS");
    (',', "COMMA");
    ('-', "MINUS");
    ('.', "DOT");
    ('/', "SLASH");
    ('0', "ZERO");
    ('1', "ONE");
    ('2', "TWO");
    ('3', "THREE");
    ('4', "FOUR");
    ('5', "FIVE");
    ('6', "SIX");
    ('7', "SEVEN");
    ('8', "EIGHT");
    ('9', "NINE");
    (':', "COLON");
    (';', "SEMICOLON");
    ('<', "LT");
    ('=', "EQ");
    ('>', "GT");
    ('?', "QUESTIONMARK");
    ('@', "AT");
    ('[', "LBRACK");
    ('\\', "BACKSLASH");
    (']', "RBRACK");
    ('^', "CARET");
    ('_', "UNDERSCORE");
    ('`', "BACKTICK");
    ('{', "LBRACE");
    ('|', "BAR");
    ('}', "RBRACE");
    ('~', "TILDE")
  ]

let token_name_char (c:char) : (string * bool (*symbolic?*)) =
  if c >='A' && c <= 'Z' then (String.make 1 c, false)
  else if c >='a' && c <= 'z' then (String.make 1 (Char.chr (Char.code c - 32)), false)
  else 
    try (List.assoc c token_escape_map, true) with
    | Not_found -> raise (Failure "token_of_terminal given non-ASCII character")

let rec token_name_char_list (cs:char list) : (string * bool (*front is symbolic*)) =
  match cs with
  | [c] -> token_name_char c
  | c::cs -> 
      (match (token_name_char c, token_name_char_list cs) with
      | ((s,false), (s',false)) -> (s ^ s',      false)
      | ((s,false), (s',true )) -> (s ^ "_" ^ s',false)
      | ((s,true),  (s',false)) -> (s ^ "_" ^ s', true)
      | ((s,true),  (s',true )) -> (s ^ "_" ^ s', true))
  | [] -> raise (Failure "token_escape_char_list given empty list")

let token_name_of t = 
  let cs = Auxl.char_list_of_string t in
  let (s, _) = token_name_char_list cs in
  s

(* collect terminals and metavardefns and construct unique token names *)
let token_names_of_syntaxdefn yo xd : token_data = 
  let m = Menhir yo in
  let ts_terminals = get_terminals_of_syntaxdefn yo xd in
  let ts_terminals' = List.map (function t -> ((token_name_of t), t, TK_terminal)) ts_terminals in

  let ts_metavars = Auxl.option_map
      (function mvd -> match mvd.mvd_phantom with
      | true -> None
      | false -> 
          (* following Grammar_pp.pp_metavarrep *)
          let ocaml_type = 
            (try
	      let hs = List.assoc "ocaml" mvd.mvd_rep in
	      Grammar_pp.pp_hom_spec m xd hs
            with Not_found -> Auxl.error ("ocamllex output: undefined ocaml hom for "^mvd.mvd_name^"\n")) in
          let ocamllex_hom = 
            (try
	      let hs = List.assoc "ocamllex" mvd.mvd_rep in
	      Grammar_pp.pp_hom_spec m xd hs
            with Not_found -> Auxl.error ("ocamllex output: undefined ocamllex hom for "^mvd.mvd_name^"\n")) in
          Some (token_name_of mvd.mvd_name, mvd.mvd_name, TK_metavar(ocaml_type, ocamllex_hom)))
      xd.xd_mds in

  let ts' = ts_terminals' @ ts_metavars in 

  let ts'' = List.sort compare ts' in 

  let rec uniqueify (acc: token_data) (ts:token_data) = 
    match ts with
    | [] -> acc
    | (tname,t,tk)::ts' -> 
        let rec find_same_tname_prefix acc ts'' = 
          match ts'' with
          | [] -> (acc,[])
          | (tname',t',tk')::ts''' -> if tname'=tname then find_same_tname_prefix ((tname',t',tk')::acc) ts''' else (acc,ts'') in
        let (same_tname_prefix,ts2) = find_same_tname_prefix [] ts' in
        if same_tname_prefix = [] then
          uniqueify ((tname,t,tk)::acc) ts'
        else
          let same_tname = (tname,t,tk)::List.rev same_tname_prefix in
          let acc' = List.rev (List.mapi (function i -> function (tname'',t'',tk'') -> (tname'' ^ string_of_int (i+1), t'',tk'')) same_tname) @ acc in
          uniqueify acc' ts2 in
  List.rev (uniqueify [] ts'')
    

(* output an ocamllex lexing rule for a token *)
let lex_token_argument_variable_of_mvr  mvr = mvr 

let pp_lex_token fd (tname, t, tk) =
  match tk with
  | TK_terminal -> 
      Printf.fprintf fd "| \"%s\"\n    { %s }\n" (String.escaped t) tname
  | TK_metavar(ocaml_type, ocamllex_hom) ->
      let tv = lex_token_argument_variable_of_mvr t in
      Printf.fprintf fd "| %s as %s\n    { %s (%s) }\n" ocamllex_hom tv tname tv

(* output an ocamllex source file *)
let pp_lex_systemdefn m sd oi =
  let yo = match m with Lex yo -> yo | _ -> raise (Failure "pp_menhir_systemdefn called with bad ppmode") in 
  match oi with
  | (o,is)::[] ->
      let _ = Auxl.filename_check m o in
      let fd = open_out o in
(*      let tl = get_terminals sd.syntax in*)
      let ts = token_names_of_syntaxdefn yo sd.syntax in
      Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
      output_string fd ("{\n" ^ "open " ^ yo.ppm_caml_parser_module ^ "\n" ^ "exception Error of string\n" ^ "}\n\n");
      output_string fd "rule token = parse\n";
      output_string fd 
"| [' ' '\\t']
    { token lexbuf }
";
      output_string fd 
"| eof
    { EOF }
";
      List.iter (pp_lex_token fd) ts;
      output_string fd 
"| _
    { raise (Error (Printf.sprintf \"At offset %d: unexpected character.\\n\" (Lexing.lexeme_start lexbuf))) }
"
;
      output_string fd "\n\n{\n}\n\n";
      close_out fd
  | _ -> Auxl.error "must specify only one output file in the lex backend.\n"


(* output a menhir token definition *)
let pp_menhir_token fd (tname, t, tk) =
  match tk with
  | TK_terminal -> 
      Printf.fprintf fd "%%token %s  (* %s *)\n" tname t
  | TK_metavar(ocaml_type, ocamllex_hom) ->
      Printf.fprintf fd "%%token <%s> %s  (* metavarroot %s *)\n" ocaml_type tname t

(* construct the ids used in menhir semantic actions to refer to values of production elements *)
let menhir_nonterminal_id_of_ntr ntr = ntr
(* Manhir docs say the following, which we do not currently ensure:
(It is recommended that the name of a nonterminal symbol begin with a
lowercase letter, so it falls in the category lid. This is in fact
mandatory for the start symbols.) *)

(* menhir nonterminal for synthesised start rules, which have an EOF added *)
let menhir_start ntr = ntr ^ "_start"

let menhir_semantic_value_id_of_ntmv ((ntmvr,suffix) as ntmv) = 
  let escape s =
    String.concat "" 
      (List.map 
         (fun c -> match c with
         | '\'' ->"_prime"             (* ignoring possibility of collision*)
         | _ -> String.make 1 c) 
         (Auxl.char_list_of_string s)) in
  let string_of_suffix_item si = match si with
  | Si_num s -> s
  | Si_punct s -> s
  | Si_var (sv,i) -> "Si_var_UNIMPLEMENTED"
  | Si_index i -> "Si_index_UNIMPLEMENTED" in
  escape (ntmvr ^ String.concat "" (List.map string_of_suffix_item suffix))

(* construct a menhir production *)
let rec pp_menhir_element ts e = 
  match e with
  | Lang_terminal t -> token_of_terminal ts t
  | Lang_nonterm (ntr,nt) ->
      Printf.sprintf "%s=%s" (menhir_semantic_value_id_of_ntmv nt) (menhir_nonterminal_id_of_ntr ntr)
  | Lang_metavar (mvr,mv) ->
      Printf.sprintf "%s=%s" (menhir_semantic_value_id_of_ntmv mv) (token_of_metavarroot ts mvr)
  | Lang_list elb -> "list_UNIMPLEMENTED"
(*      let ts = List.flatten (List.map get_terminals_of_element elb.elb_es) in
      (match elb.elb_tmo with
      | None -> ts
      | Some t -> t::ts)
*)
  | Lang_option _ -> raise (Failure "Lang_option not implemented")
  | Lang_sugaroption _ -> raise (Failure "Lang_option not implemented")

let rec pp_menhir_element_action ts e = 
  match e with
  | Lang_terminal t -> None
  | Lang_nonterm (ntr,nt) ->
      Some (menhir_semantic_value_id_of_ntmv nt)
  | Lang_metavar (mvr,mv) ->
      Some (menhir_semantic_value_id_of_ntmv mv)
  | Lang_list elb -> Some "list_UNIMPLEMENTED"
(*      let ts = List.flatten (List.map get_terminals_of_element elb.elb_es) in
      (match elb.elb_tmo with
      | None -> ts
      | Some t -> t::ts)
*)
  | Lang_option _ -> raise (Failure "Lang_option not implemented")
  | Lang_sugaroption _ -> raise (Failure "Lang_option not implemented")

let pp_menhir_prod yo xd ts p = 
  if suppress_prod yo p then 
    ""
  else
    let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in
    "| " ^ String.concat " " (List.map (pp_menhir_element ts) p.prod_es) ^ "\n"
    ^ "    { " ^ String.capitalize p.prod_name ^ "("^ String.concat "," (Auxl.option_map (pp_menhir_element_action ts) es') ^ ") }\n"

(* construct a menhir rule *)
let pp_menhir_rule yo xd ts r = 
  if suppress_rule yo r then 
    ""
  else 
    menhir_nonterminal_id_of_ntr r.rule_ntr_name ^ ":\n" 
    ^  String.concat "" (List.map (pp_menhir_prod yo xd ts) r.rule_ps)
    ^ "\n"

let is_start_rule yo r = 
  not(suppress_rule yo r) && (try ignore(List.assoc "menhir_start" r.rule_homs); true with Not_found -> false)

(* construct a menhir rule for a start symbol, sticking an EOF on *)
let pp_menhir_start_rule yo xd ts r = 
  if not(is_start_rule yo r) then 
    ""
  else 
    let ntr = r.rule_ntr_name in
    let nt = (ntr,[]) in
    menhir_start (menhir_nonterminal_id_of_ntr ntr) ^ ":\n" 
    ^ "| " ^ (pp_menhir_element ts (Lang_nonterm (ntr, nt))) ^ " EOF" ^ "\n"
    ^ "    { " ^ (menhir_semantic_value_id_of_ntmv nt) ^ " }\n"

let pp_menhir_start_rules yo xd ts = 
  String.concat "" 
    (List.map (pp_menhir_start_rule yo xd ts)  xd.xd_rs)
                                                                
(* construct menhir start symbol declarations *)
let pp_menhir_start_symbols yo xd = 
  String.concat "" 
    (List.map 
       (function r -> 
         if not(is_start_rule yo r) then 
           ""
         else
           "%start <" 
           ^ yo.ppm_caml_ast_module 
           ^ "."  
           ^ Grammar_pp.strip_surrounding_parens 
               (Grammar_pp.pp_nontermroot_ty (Caml yo.ppm_caml_opts) xd r.rule_ntr_name) 
           ^ "> " 
           ^ menhir_start (menhir_nonterminal_id_of_ntr r.rule_ntr_name) 
           ^ "\n")
       xd.xd_rs)


(* old code to pull out precedence/assoc info*)
(*
let pp_menhir_precedences fd ts =
  let go_fun (_, (t, s, hs)) = 
    if t = "" then None else
    try match List.assoc "prec" hs with
      | [Hom_string x] ->
           Some (s, int_of_string x,
                 List.exists (fun (x,_) -> x="leftassoc") hs,
                 List.exists (fun (x,_) -> x="rightassoc") hs)
      | _ -> None
    with _ -> None
  in
  let rec group xs = match xs with
    | [] -> []
    | (s,c,l,r)::xs -> group1 [s] c l r xs
  and group1 b c l r xs = match xs with
   | (s',c',l',r')::xs when c'=c -> group1 (s'::b) c (l||l') (r||r') xs
   | _ -> (b,l,r) :: group xs in
  let ts = Auxl.option_map go_fun ts in
  let ts = List.sort (fun (_,c1,_,_) (_,c2,_,_) -> c1-c2) ts in
  let gs = group ts in
  List.iter (fun (b,l,r) -> 
    if l then output_string fd "\n%left"
    else if r then output_string fd "\n%right"
    else output_string fd "\n%nonassoc";
    List.iter (fun s -> output_char fd ' '; output_string fd s) b) gs
*)

(* output a menhir source file *)
let pp_menhir_systemdefn m sd oi =
  let yo = match m with Menhir yo -> yo | _ -> raise (Failure "pp_menhir_systemdefn called with bad ppmode") in 
  match oi with
  | (o,is)::[] ->
      let _ = Auxl.filename_check m o in
      let fd = open_out o in
      let ts = token_names_of_syntaxdefn yo sd.syntax in
      Printf.fprintf fd "/* generated by Ott %s from: %s */\n" Version.n sd.sources;
      output_string fd ("%{\n" ^ "open " ^ yo.ppm_caml_ast_module ^ "\n" ^ "%}\n\n");
      List.iter (pp_menhir_token fd) ts;
      Printf.fprintf fd "%%token EOF  (* added by Ott *)\n";
(*
      let tl = get_terminals sd.syntax in
      pp_menhir_precedences fd tl;
      output_string fd "\n%%\n";
*)
      output_string fd "\n";
      output_string fd (pp_menhir_start_symbols yo sd.syntax);
      output_string fd "\n\n%%\n\n";

      output_string fd (pp_menhir_start_rules yo sd.syntax ts);
      List.iter (function r -> output_string fd (pp_menhir_rule yo sd.syntax ts r)) sd.syntax.xd_rs;
      close_out fd
  | _ -> Auxl.error "must specify only one output file in the menhir backend.\n"

