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

(* which metavars, rules and productions to include *)
let suppress_metavar yo mvd =
  mvd.mvd_indexvar  (* mvd.mvd_phantom *)

let contains_list p = 
  List.exists (function e -> match e with Lang_list _ -> true | _ -> false  )  p.prod_es

let suppress_prod yo p = 
  let suppressed_category = 
    StringSet.exists (fun x -> List.mem x yo.ppm_suppressed_categories)
      p.prod_categories in


 (* contains_list p (* just for now... *)
   ||*) suppressed_category || (not(yo.ppm_show_meta) && p.prod_meta && not(p.prod_sugar))

let suppress_rule yo r = 
  let suppressed_ntr = 
    List.mem r.rule_ntr_name yo.ppm_suppressed_ntrs
  in
  [] = r.rule_ps (*List.filter (function p -> not (contains_list p)) r.rule_ps *)
|| suppressed_ntr || (not(yo.ppm_show_meta) && r.rule_semi_meta)


(* tokens arise from terminals and metavardefns *)
type token_kind = 
  | TK_terminal 
  | TK_metavar of string (* ocamllex hom *) * string (* ocaml hom, for type*)

type token_data = 
    (string(*synthesised token name*) * string(*terminal or metavarroot*) * token_kind) list


(* find the token associated with a terminal or metavarroot *) 
let token_of_terminal ts t0 = 
  try let (tn,_,_) = List.find (function td -> match td with (tn,t,TK_terminal) when t=t0 -> true | _ -> false) ts in tn 
  with Not_found -> raise (Failure ("token_of_terminal \""^t0^"\" not found"))

let token_of_metavarroot ts mvr = 
  try let (tn,_,_) = List.find (function td -> match td with (tn,t,TK_metavar _) when t=mvr -> true | _ -> false) ts in tn 
  with Not_found -> raise (Failure ("token_of_metavarroot \""^mvr^"\" not found"))


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
      (function mvd -> match suppress_metavar yo mvd with
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
    

(** ******************************************************************** *)
(** ocamllex                                                             *)
(** ******************************************************************** *)

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


(** ******************************************************************** *)
(** menhir                                                               *)
(** ******************************************************************** *)


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
  | Si_index i -> string_of_int i in (* ignoring possible name clashes...*)
  escape (ntmvr ^ String.concat "" (List.map string_of_suffix_item suffix))

(* construct a menhir production *)
let rec pp_menhir_element ts e = 
  match e with
  | Lang_terminal t -> token_of_terminal ts t
  | Lang_nonterm (ntr,nt) ->
      Printf.sprintf "%s=%s" (menhir_semantic_value_id_of_ntmv nt) (menhir_nonterminal_id_of_ntr ntr)
  | Lang_metavar (mvr,mv) ->
      Printf.sprintf "%s=%s" (menhir_semantic_value_id_of_ntmv mv) (token_of_metavarroot ts mvr)
  | Lang_list elb ->
      let f lhs rhs = 
        let terminal_option = 
          match elb.elb_tmo with
          | None -> None
          | Some t -> Some (token_of_terminal ts t) in
        let non_empty = 
          match elb.elb_boundo with
          | Some (Bound_dotform bd)   -> bd.bd_length 
          | Some (Bound_comp bc)      -> 0
          | Some (Bound_comp_u bcu)   -> 0
          | Some (Bound_comp_lu bclu) -> bclu.bclu_length 
          | None                      -> 0 in
        let rhs' = 
          (* this isn't enforcing the length >=2 constraints from the Ott source *)
          match (non_empty, terminal_option) with
          | (0,Some t) -> "separated_list(" ^ t ^ "," ^ rhs ^ ")"
          | (0,None)   -> "list(" ^ rhs ^ ")" 
          | (_,Some t) -> "separated_nonempty_list(" ^ t ^ "," ^ rhs ^ ")"
          | (_,None)   -> "nonempty_list(" ^ rhs ^ ")"
(*
          | (2,Some t) -> "separated_nonempty2_list(" ^ t ^ "," ^ rhs ^ ")"
          | (2,None)   -> "nonempty2_list(" ^ rhs ^ ")"
          | (_,_)      -> Auxl.error ("unexpected length in pp_menhir_element") 
*)
        in
        Printf.sprintf "%s=%s" lhs rhs'  in
      (match elb.elb_es with
      | [Lang_nonterm (ntr,nt)] -> 
          let lhs = menhir_semantic_value_id_of_ntmv nt in
          let rhs = menhir_nonterminal_id_of_ntr ntr in
          f lhs rhs 
      | [Lang_metavar (mvr,mv)] ->
          let lhs = menhir_semantic_value_id_of_ntmv mv in
          let rhs = token_of_metavarroot ts mvr in
          f lhs rhs 
      | _ -> "(*LISTS THAT ARE NOT SINGLETON NONTERMS OR METAARS ARE UNIMPLEMENTED*)"
            (* we should be able to use the menhir anonymous rules to implement non-singleton Ott lists *)
      )
  | Lang_option _ -> raise (Failure "Lang_option not implemented")
  | Lang_sugaroption _ -> raise (Failure "Lang_option not implemented")

let rec pp_menhir_element_action ts e = 
  match e with
  | Lang_terminal t -> None
  | Lang_nonterm (ntr,nt) ->
      Some (menhir_semantic_value_id_of_ntmv nt)
  | Lang_metavar (mvr,mv) ->
      Some (menhir_semantic_value_id_of_ntmv mv)
  | Lang_list elb -> 

      (match elb.elb_es with
      | [Lang_nonterm (ntr,nt)] -> 
          let lhs = menhir_semantic_value_id_of_ntmv nt in
          Some lhs
      | [Lang_metavar (mvr,mv)] ->
          let lhs = menhir_semantic_value_id_of_ntmv mv in
          Some lhs
      | _ -> Some "(*LISTS THAT ARE NOT SINGLETON NONTERMS OR METAARS ARE UNIMPLEMENTED*)"
      )

  | Lang_option _ -> raise (Failure "Lang_option not implemented")
  | Lang_sugaroption _ -> raise (Failure "Lang_option not implemented")

(* build an OCaml application of a production's constructor to
identifiers for its arguments, to use as the action of a menhir
production *)

let pp_menhir_prod_rhs p ts es' = 
  String.capitalize p.prod_name 
  ^ 
    (let args = Auxl.option_map (pp_menhir_element_action ts) es' in
    match args with
    | [] -> ""
    | _ -> "("^ String.concat "," args ^ ")" )

(* build a menhir production *)
let pp_menhir_prod yo xd ts r p = 
  if suppress_prod yo p then 
    ""
  else
    let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in
    "| " ^ String.concat " " (List.map (pp_menhir_element ts) p.prod_es) ^ "\n"
    ^ 
      if not(r.rule_phantom) then 
        "    { " ^ pp_menhir_prod_rhs p ts es' ^ " }\n"
      else (* use the ocaml hom *)
        "    { " ^ (match Auxl.hom_spec_for_hom_name "ocaml" p.prod_homs with Some hom -> Grammar_pp.pp_hom_spec (Menhir yo) xd hom | None -> ignore(Auxl.error ("no ocaml hom for production "^p.prod_name));"") ^ " }\n"

(* build a menhir rule *)
let pp_menhir_rule yo xd ts r = 
  if suppress_rule yo r then 
    ""
  else 
    menhir_nonterminal_id_of_ntr r.rule_ntr_name ^ ":\n" 
    ^  String.concat "" (List.map (pp_menhir_prod yo xd ts r) r.rule_ps)
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
           let ty0 = 
             Grammar_pp.strip_surrounding_parens 
               (Grammar_pp.pp_nontermroot_ty (Caml yo.ppm_caml_opts) xd r.rule_ntr_name) in
           let (ty1, ty_arg) = 
           if String.length ty0 >= 3 && String.sub ty0 0 3 = "'a " then 
             (String.sub ty0 3 (String.length ty0 - 3), "unit ")
           else
             (ty0, "") in
           "%start <" 
           ^ ty_arg 
           ^ yo.ppm_caml_ast_module 
           ^ "."  
           ^ ty1
           ^ "> " 
           ^ menhir_start (menhir_nonterminal_id_of_ntr r.rule_ntr_name) 
           ^ "\n")
       xd.xd_rs)

(** ******************************************************************** *)
(** raw pp                                                               *)
(** ******************************************************************** *)

(* all this should really use a more efficient representation than string *)

let pp_pp_raw_name ntmvr =
  "pp_raw_" ^ ntmvr

let rec pp_pp_raw_prod_rhs_element ts e = 
  match e with
  | Lang_terminal t -> None
  | Lang_nonterm (ntr,nt) ->
      Some (pp_pp_raw_name ntr ^ " " ^ menhir_semantic_value_id_of_ntmv nt)
  | Lang_metavar (mvr,mv) ->
      Some (menhir_semantic_value_id_of_ntmv mv)  (* assuming all metavars map onto string-containing tokens *)
(*      Some (pp_pp_raw_name mvr ^ " " ^ menhir_semantic_value_id_of_ntmv mv)*)
  | Lang_list elb -> 
      (match elb.elb_es with
      | [Lang_nonterm (ntr,nt)] -> 
          Some ("String.concat \",\" (List.map " ^ pp_pp_raw_name ntr ^ " " ^ menhir_semantic_value_id_of_ntmv nt ^ ")")
      | [Lang_metavar (mvr,mv)] ->
          Some ("String.concat \",\" ((*List.map " ^ pp_pp_raw_name mvr ^ "*) " ^ menhir_semantic_value_id_of_ntmv mv ^ ")")
      | _ -> Some "(*LISTS THAT ARE NOT SINGLETON NONTERMS OR METAARS ARE UNIMPLEMENTED*)"
      )
  | Lang_option _ -> raise (Failure "Lang_option not implemented")
  | Lang_sugaroption _ -> raise (Failure "Lang_option not implemented")


let pp_pp_raw_prod_rhs p ts es' = 
  "\"" ^ String.capitalize p.prod_name ^ "\"" 
  ^ 
    (let args = Auxl.option_map (pp_pp_raw_prod_rhs_element ts) es' in
    match args with
    | [] -> ""
    | _ -> " ^ \"(\" ^ "^ String.concat " ^ \",\" ^ " args ^ " ^ \")\"" )


let pp_pp_raw_prod yo xd ts r p = 
  if suppress_prod yo p then 
    ""
  else
    let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in
    "| " ^ pp_menhir_prod_rhs p ts es' ^ " -> " 
    ^ pp_pp_raw_prod_rhs p ts es'
    ^ "\n"


let pp_pp_raw_rule yo xd ts r = 
  if suppress_rule yo r then 
    None
  else 
    Some (pp_pp_raw_name r.rule_ntr_name ^ " x = match x with\n" 
    ^  String.concat "" (List.map (pp_pp_raw_prod yo xd ts r) r.rule_ps)
    ^ "\n")

let pp_pp_raw_rules yo xd ts rs = 
  "let rec " ^ String.concat "and " (Auxl.option_map (pp_pp_raw_rule yo xd ts) rs)


(** ******************************************************************** *)
(** raw pp                                                               *)
(** ******************************************************************** *)

(* all this should really use a more efficient representation than string *)

let pp_pp_name ntmvr =
  "pp_" ^ ntmvr

let rec pp_pp_prod_rhs_element ts e = 
  match e with
  | Lang_terminal t -> Some ("\"" ^ t ^ "\"")
  | Lang_nonterm (ntr,nt) ->
      Some (pp_pp_name ntr ^ " " ^ menhir_semantic_value_id_of_ntmv nt)
  | Lang_metavar (mvr,mv) ->
      Some (menhir_semantic_value_id_of_ntmv mv)  (* assuming all metavars map onto string-containing tokens *)
(*      Some (pp_pp_name mvr ^ " " ^ menhir_semantic_value_id_of_ntmv mv)*)
  | Lang_list elb -> 
      let sep = match elb.elb_tmo with Some t -> t | None -> " " in
      (match elb.elb_es with
      | [Lang_nonterm (ntr,nt)] -> 
          Some ("String.concat \"" ^ sep ^ "\" (List.map " ^ pp_pp_name ntr ^ " " ^ menhir_semantic_value_id_of_ntmv nt ^ ")")
      | [Lang_metavar (mvr,mv)] ->
          Some ("String.concat \"" ^ sep ^ "\" ((*List.map " ^ pp_pp_name mvr ^ "*) " ^ menhir_semantic_value_id_of_ntmv mv ^ ")")
      | _ -> Some "(*LISTS THAT ARE NOT SINGLETON NONTERMS OR METAARS ARE UNIMPLEMENTED*)"
      )
  | Lang_option _ -> raise (Failure "Lang_option not implemented")
  | Lang_sugaroption _ -> raise (Failure "Lang_option not implemented")


let pp_pp_prod_rhs p ts es' = 
  let args = Auxl.option_map (pp_pp_prod_rhs_element ts) es' in
  String.concat " ^ \" \" ^ " args 

let pp_pp_prod yo xd ts r p = 
  if suppress_prod yo p then 
    ""
  else
    let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in
    "| " ^ pp_menhir_prod_rhs p ts es' ^ " -> " 
    ^ pp_pp_prod_rhs p ts es'
    ^ "\n"

let pp_pp_rule yo xd ts r = 
  if suppress_rule yo r then 
    None
  else 
    Some (pp_pp_name r.rule_ntr_name ^ " x = match x with\n" 
    ^  String.concat "" (List.map (pp_pp_prod yo xd ts r) r.rule_ps)
    ^ "\n")

let pp_pp_rules yo xd ts rs = 
  "let rec " ^ String.concat "and " (Auxl.option_map (pp_pp_rule yo xd ts) rs)



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
let pp_menhir_systemdefn m sd lookup oi =
  let yo = match m with Menhir yo -> yo | _ -> raise (Failure "pp_menhir_systemdefn called with bad ppmode") in 
  match oi with
  | (o,is)::[] ->
      let _ = Auxl.filename_check m o in
      let xd = sd.syntax in 
      let fd = open_out o in
      let ts = token_names_of_syntaxdefn yo xd in
      Printf.fprintf fd "/* generated by Ott %s from: %s */\n" Version.n sd.sources;
      output_string fd ("%{\n" ^ "open " ^ yo.ppm_caml_ast_module ^ "\n" 
                        ^ "%}\n\n");
      List.iter (pp_menhir_token fd) ts;
      Printf.fprintf fd "%%token EOF  (* added by Ott *)\n";
(*
      let tl = get_terminals xd in
      pp_menhir_precedences fd tl;
      output_string fd "\n%%\n";
*)
      output_string fd "\n";
      Embed_pp.pp_embeds fd m xd lookup xd.xd_embed;

      output_string fd (pp_menhir_start_symbols yo xd);
      output_string fd "\n\n%%\n\n";

      output_string fd (pp_menhir_start_rules yo xd ts);
      List.iter (function r -> output_string fd (pp_menhir_rule yo xd ts r)) xd.xd_rs;
      close_out fd;

      (* horrid hack to make filename for pp code by removing .mly *)
      let o_pp = String.sub o 0 (String.length o - 4)  ^ "_pp.ml" in

      let fd = open_out o_pp in
      Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
      output_string fd ("open " ^ yo.ppm_caml_ast_module ^ "\n\n" 
                        ^ pp_pp_raw_rules yo xd ts xd.xd_rs
                        ^ "\n"
                        ^ pp_pp_rules yo xd ts xd.xd_rs
                        );
      close_out fd;



  | _ -> Auxl.error "must specify only one output file in the menhir backend.\n"

