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
basic source files for the menhir/ocamllex parser and lexer generators,
and for ocaml pretty printers of raw and source terms. 

In general this is impossible: 
- fundamentally, because an Ott grammar can be an arbitrary
   context-free grammar, whereas menhir supports LR grammars; and
- practically, because one may also want to hand-tune the grammar or
   lexer, e.g. for decent parse error messages/recovery

The normal goal for Ott development has been to produce files that do
not need hand-editing, so that the Ott source remains the principal
source.  Here we may not be able to achieve that: we might aim instead
to produce menhir/ocamllex source files that can be hand-edited, to
take some of the tedious work out of producing a parser and lexer;
we'll see.

Along with this, Ott now supports maintaining both a context-free and LR
grammar in sync, by writing an LR Ott grammar but including
annotations saying that some rules should be quotiented together in
the context-free grammar.

The implementation is partial in several respects.  Currently it:
- does not support subrules
   (it should only take the maximal elements from the subrule order)
- does not support {{ order }} homs
- does not support ocaml type or variable name homs
- does not check or enforce ocaml naming conventions, eg capitalisation
- requires an explicit hom for syntactic sugar productions

There are some minimal working examples in tests/menhir_tests. In the Ott source:
- metavar definitions should have ocaml and ocamllex homs, to specify
   their OCaml type and the ocamllex regexps.
- grammar rules that are start symbols should have "menhir-start" homs

Command-line usage should specify single .ml, .mll, and .mly output
files, in a single run of Ott (as the files have to refer to each
other).  The output also generates a simple pretty printer for the ast. 

There was a previous attempt at an ocamllex/ocamlyacc backend, by
Viktor Vafeiadis in 2011, but that code seemed to be very partial.
This implementation repurposes a little of that infrastructure. 

*)


(* for the generated lexer, metavar definitions should either have an ocamllex hom (specifying how they should be lexed) or an ocamllex-remove hom (specifying that a constructor of the token type should be generated, but without a lexer rule). *)


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
   ||*) suppressed_category || ((*not(yo.ppm_show_meta) &&*) p.prod_meta && not(p.prod_sugar))

(* identify which nonterminal-root rules should be suppressed in the generated menhir rule set *)
let suppress_rule yo r = 
  let suppressed_ntr = 
    List.mem r.rule_ntr_name yo.ppm_suppressed_ntrs
  in
  [] = r.rule_ps (*List.filter (function p -> not (contains_list p)) r.rule_ps *)
(*|| suppressed_ntr || (not(yo.ppm_show_meta) && r.rule_semi_meta) || r.rule_meta*)
  || suppressed_ntr || r.rule_semi_meta


(* tokens arise from terminals and metavardefns *)
type token_kind = 
  | TK_terminal 
  | TK_metavar of string (* ocamllex hom *) * string option (* ocaml hom, for type*) * string option (* ocamllex_of_string hom, for function to convert from string to ocaml type*)
(* or other way round?*)

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
            with Not_found -> Auxl.error (Some mvd.mvd_loc) ("ocamllex output: undefined ocaml hom for "^mvd.mvd_name^"\n")) in
          let ocamllex_hom_opt = 
            (try
	      let hs = List.assoc "ocamllex" mvd.mvd_rep in
	      Some (Grammar_pp.pp_hom_spec m xd hs)
            with Not_found -> None) in
          let ocamllex_of_string_hom_opt = 
            (try
	      let hs = List.assoc "ocamllex-of-string" mvd.mvd_rep in
	      Some (Grammar_pp.pp_hom_spec m xd hs)
            with Not_found -> None) in
          let ocamllex_remove_hom = 
            (try
	      let hs = List.assoc "ocamllex-remove" mvd.mvd_rep in
	      true
            with Not_found -> false) in
          (match ocamllex_hom_opt, ocamllex_remove_hom with
          | Some ocamllex_hom, false -> 
              Some (token_name_of mvd.mvd_name, mvd.mvd_name, TK_metavar(ocaml_type, Some ocamllex_hom, ocamllex_of_string_hom_opt))
          | None, false -> 
(* hack: default to ocamllex-remove *)
(*              Auxl.error (Some mvd.mvd_loc) ("ocamllex output: no ocamllex or ocamllex-remove hom for "^mvd.mvd_name^"\n")*)
              Some (token_name_of mvd.mvd_name, mvd.mvd_name, TK_metavar(ocaml_type, None, ocamllex_of_string_hom_opt))
          | Some ocamllex_hom, false -> 
              Auxl.error (Some mvd.mvd_loc) ("ocamllex output: both ocamllex and ocamllex-remove hom for "^mvd.mvd_name^"\n")
          | None, true -> 
              Some (token_name_of mvd.mvd_name, mvd.mvd_name, TK_metavar(ocaml_type, None, ocamllex_of_string_hom_opt))
          )
      )
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
  List.stable_sort (fun (tn1,_,tk1) (tn2,_,tk2) -> match (tk1, tk2) with
      | TK_terminal, TK_metavar _ -> -1
      | TK_metavar _, TK_terminal -> 1
      | _, _ -> compare (String.length tn2) (String.length tn1)) (List.rev (uniqueify [] ts''))
    

(** ******************************************************************** *)
(** ocamllex                                                             *)
(** ******************************************************************** *)

(* output an ocamllex lexing rule for a token *)
let lex_token_argument_variable_of_mvr  mvr = mvr 

let pp_lex_token fd (tname, t, tk) =
  match tk with
  | TK_terminal -> 
      Printf.fprintf fd "| \"%s\"\n    { %s }\n" (String.escaped t) tname
  | TK_metavar(ocaml_type, Some ocamllex_hom, ocamllex_of_string_hom_opt) ->
      let tv = lex_token_argument_variable_of_mvr t in
      Printf.fprintf fd "| %s as %s\n    { %s (%s) }\n" ocamllex_hom tv tname
        (
         (match ocamllex_of_string_hom_opt with
         | None -> 
             (match ocaml_type with
             | "string" -> ""
             | "int" -> "int_of_string"
             | "float" -> "float_of_string"
             | "bool" -> "bool_of_string")
         | Some f -> f)
         ^ " " ^ tv)
(*         | _ -> tv)*)
  | TK_metavar(ocaml_type, None, _) ->
      Printf.fprintf fd "(* lexer rule for %s suppressed by ocamllex-remove *)\n" tname

let rec list_find_map f l =
  match l with
  | [] -> None
  | h :: t -> match f h with
    | Some v -> Some v
    | None -> list_find_map f t

let get_comment_start xd =
  xd.xd_rs |>
  list_find_map
    (fun rule ->
       match Auxl.hom_spec_for_hom_name "lex-comment" rule.rule_homs with
       | Some hs ->
         hs |> list_find_map
           (function
             | Hom_string s -> Some s
             | _ -> raise (Failure "lex-comment hom must be a string")
           )
       | None -> None)


(* output an ocamllex source file *)
let pp_lex_systemdefn m sd oi =
  let yo = match m with Lex yo -> yo | _ -> raise (Failure "pp_menhir_systemdefn called with bad ppmode") in 
  match oi with
  | (o,is)::[] ->
      let _ = Auxl.filename_check m o in
      let fd = open_out o in
(*      let tl = get_terminals sd.syntax in*)
      let comment_start =
        match get_comment_start sd.syntax with
        | Some v -> v
        | None -> "//"
      in
      let ts = token_names_of_syntaxdefn yo sd.syntax in
      Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sd.sources;
      output_string fd ("{\n" ^ "open " ^ yo.ppm_caml_parser_module ^ "\n" ^ "exception Error of string\n" ^ "}\n\n");
      output_string fd "rule token = parse\n";
      output_string fd 
"| [' ' '\\t']
    { token lexbuf }
";
      output_string fd
"| '\n'
   { Lexing.new_line lexbuf; token lexbuf }
";
      output_string fd
("| \"" ^ comment_start ^ "\" [^'\\n']* '\\n'
    { Lexing.new_line lexbuf; token lexbuf }
");
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
  | _ -> Auxl.error None "must specify only one output file in the lex backend.\n"


(** ******************************************************************** *)
(** menhir                                                               *)
(** ******************************************************************** *)


(* output a menhir token definition *)
let pp_menhir_token fd (tname, t, tk) =
  match tk with
  | TK_terminal -> 
      Printf.fprintf fd "%%token %s  (* %s *)\n" tname (if t <> (String.escaped t) then tname else t)
  | TK_metavar(ocaml_type, ocamllex_hom_opt, ocamllex_of_string_opt) ->
      Printf.fprintf fd "%%token <%s> %s  (* metavarroot %s *)\n" ocaml_type tname t

(* construct the ids used in menhir semantic actions to refer to values of production elements *)
let menhir_nonterminal_id_of_ntr ntr = ntr
(* Menhir docs say the following, which we do not currently ensure:
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

let menhir_semantic_value_id_of_list es = 
  let f e = match e with
  | Lang_terminal t -> None
  | Lang_nonterm (ntr,nt) ->
      Some (menhir_semantic_value_id_of_ntmv nt)
  | Lang_metavar (mvr,mv) ->
      Some (menhir_semantic_value_id_of_ntmv mv)
  | Lang_list elb -> 
      raise (Failure "unexpected nested Lang_list")
  | _ ->
      raise (Failure "unexpected other Lang_ form") in
  let ss = Auxl.option_map f es in
  match ss with
  | [] -> raise (Failure "List form consisting only of terminals not supported")
  | _ -> String.concat "_" ss


(* ocaml pp function names *)

let pp_pp_raw_name ntmvr =
  "pp_raw_" ^ ntmvr

let pp_pp_json_name ntmvr =
  "pp_json_" ^ ntmvr

let pp_pp_name ntmvr =
  "pp_" ^ ntmvr

let string_of_hom_spec_el hse =
  match hse with
  | Hom_string s -> s
  | Hom_index i -> raise (Failure "string_of_hom_spec")
  | Hom_terminal t -> t
  | Hom_ln_free_index _ -> raise (Failure "string_of_hom_spec")

let string_of_hom_spec hs =
  String.concat "" (List.map string_of_hom_spec_el hs)

                                              
let pp_params r =
  match Auxl.hom_spec_for_hom_name "pp-params" r.rule_homs with 
  | Some hs -> 
      " " ^ string_of_hom_spec hs
  | None ->
      ""
      

            
(* construct all the data we need, for parsing and pretty printing,
from an element of an ott production *)

type element_data = {
    semantic_value_id : string option; (* None for terminals, Some ntmv for nonterms and metavars, Some compound_id for lists *)
    grammar_body : string;
    semantic_action : string option;  (* None for terminals *)
    pp_raw_rhs : string option;       (* None for terminals *)
    pp_pretty_rhs : string option;
    pp_json_rhs : string option;  (* None for terminals *)
  }

let pp_json_key s = "\\\"" ^ s ^ "\\\""
                  
let rec element_data_of_element xd ts (allow_lists:bool) (indent_nonterms:bool) (no_json_key : bool) e : element_data = 
(*string option(*semantic_value_id*) * string(*grammar body*) * string option (*semantic action*) =*)
  match e with
  | Lang_terminal t -> 
      { semantic_value_id = None;
        grammar_body      = token_of_terminal ts t;
        semantic_action   = None;
        pp_raw_rhs        = None;
        pp_json_rhs       = None;
        pp_pretty_rhs     = Some ("string \"" ^ String.escaped t ^ "\""); }

  | Lang_nonterm (ntr,nt) ->
      let svi = menhir_semantic_value_id_of_ntmv nt in 
      { semantic_value_id = Some svi;
        grammar_body      = menhir_nonterminal_id_of_ntr ntr;
        semantic_action   = Some svi;
        pp_raw_rhs        = Some (pp_pp_raw_name ntr ^ pp_params (Auxl.rule_of_ntr_nonprimary xd ntr) ^ " " ^ svi);
        pp_json_rhs       = Some (
                                (if no_json_key then
                                  ""
                                else
                                  "string \"" ^ pp_json_key (Grammar_pp.pp_plain_nonterm nt)  ^ ":\" ^^ ")
                                ^ pp_pp_json_name ntr ^ pp_params (Auxl.rule_of_ntr_nonprimary xd ntr) ^ " " ^ svi);
        pp_pretty_rhs     
          = match Auxl.hom_spec_for_hom_name "pp-suppress" (Auxl.rule_of_ntr_nonprimary xd ntr).rule_homs with 
          | Some hs ->
              None
          | None -> 
              if indent_nonterms then
                Some ("nest 2 (" ^ pp_pp_name ntr ^ pp_params (Auxl.rule_of_ntr_nonprimary xd ntr) ^ " " ^ svi ^")")
              else
                Some ("" ^ pp_pp_name ntr ^ pp_params (Auxl.rule_of_ntr_nonprimary xd ntr) ^ " " ^ svi ^"";) }

  | Lang_metavar (mvr,mv) -> (* assuming all metavars map onto string-containing tokens *)
      let svi = menhir_semantic_value_id_of_ntmv mv in 
      { semantic_value_id = Some svi;
        grammar_body      = token_of_metavarroot ts mvr;
        semantic_action   = Some svi;
        pp_raw_rhs        = Some (pp_pp_raw_name mvr ^ " " ^ svi);
        pp_json_rhs       = Some ( "string \"" ^ pp_json_key (Grammar_pp.pp_plain_metavar mv) ^ " : \" ^^ " ^ pp_pp_json_name mvr ^ " " ^ svi);
        pp_pretty_rhs     
          = match Auxl.hom_spec_for_hom_name "pp-suppress" (Auxl.mvd_of_mvr_nonprimary xd mvr).mvd_rep with 
          | Some hs ->
              None
          | None -> 
              Some (pp_pp_name mvr ^ " " ^ svi); }
(*        pp_raw_rhs        = Some (" string \"\\\"\" ^^ string " ^ svi ^ " ^^ string \"\\\"\"");
        pp_pretty_rhs     = "string "^ svi ; }
 *)
      
  | Lang_list elb -> 
      if not allow_lists then raise (Failure "unexpected list form");
      let element_data = List.map (element_data_of_element xd ts false true indent_nonterms ) elb.elb_es in 
      
      let svi = menhir_semantic_value_id_of_list elb.elb_es in      

      let body = 
        let list_grammar_constructor body = 
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
          match (non_empty, terminal_option) with
          | (0,Some t) -> "separated_list(" ^ t ^ "," ^ body ^ ")"
          | (0,None)   -> "list(" ^ body ^ ")" 
          | (1,Some t) -> "separated_nonempty_list(" ^ t ^ "," ^ body ^ ")"
          | (1,None)   -> "nonempty_list(" ^ body ^ ")"
          | (2,Some t) -> "separated_nonempty2_list(" ^ t ^ "," ^ body ^ ")"
          | (2,None)   -> "nonempty2_list(" ^ body ^ ")"
          | (_,_)      -> Auxl.error None ("unexpected length in pp_menhir_element") 
        in
        let body0 = 
          (match element_data with
          | [] -> raise (Failure "unexpected empty list form")
          | [x] -> x.grammar_body;
          | _ -> 
              Printf.sprintf "tuple%d(%s)" (List.length element_data) (String.concat "," (List.map (function x->x.grammar_body) element_data))) in
        list_grammar_constructor body0 in

      let action = 
        (* if need be (but not otherwise) project out unit elements from terminals within list *)
        if List.exists (function x-> x.semantic_value_id = None)  element_data  then 
          let pat = String.concat "," (List.map (function x -> match x.semantic_value_id with Some svi->svi | None->"()") element_data) in
          let rhs = String.concat "," (Auxl.option_map (function x -> x.semantic_value_id) element_data) in
          "List.map (function ("^pat^") -> ("^rhs^")) "^svi
        else 
          svi  in
      
      let pat = "(" ^ String.concat "," (Auxl.option_map (function x -> x.semantic_value_id) element_data) ^")" in

      let pp_raw_rhs = 
        let rhs_data = Auxl.option_map (function x-> x.pp_raw_rhs) element_data in
        let rhs =  "string \"(\" ^^ " ^ String.concat  " ^^ string \",\" ^^ " rhs_data ^ " ^^ string \")\"" in
        let f = "(function "^pat^" -> "^rhs^")" in
        let pper = "string \"[\" ^^ separate  (string \";\") (List.map " ^ f ^ " " ^ svi ^")" ^" ^^ string \"]\"" in
        pper in

      let pp_json_rhs = 
        let rhs_data = Auxl.option_map (function x-> x.pp_json_rhs) element_data in
        let rhs =  "string \"\" ^^ " ^ String.concat  " ^^ string \",\" ^^ " rhs_data ^ " ^^ string \"\"" in
        let f = "(function "^pat^" -> "^rhs^")" in
        let pper = "string \"\\\"list\\\" : [\" ^^ separate  (string \",\") (List.map " ^ f ^ " " ^ svi ^")" ^" ^^ string \"]\"" in
        pper in

      
      let pp_pretty_rhs = 
        let rhs_data = Auxl.option_map (function x-> x.pp_pretty_rhs) element_data in
        let rhs =  String.concat  " ^^ string \" \" ^^ " rhs_data in
        let f = "(function "^pat^" -> "^rhs^")" in
        let sep = match elb.elb_tmo with Some t -> "(string \""^String.escaped t^"\")" | None -> "(break 1)" in
        let pper = "group(separate " ^  sep ^ " (List.map " ^ f ^ " " ^ svi ^ "))" in
        pper in

      { semantic_value_id = Some svi;
        grammar_body      = body;
        semantic_action   = Some action;
        pp_raw_rhs        = Some pp_raw_rhs;
        pp_json_rhs       = Some pp_json_rhs;
        pp_pretty_rhs     = Some pp_pretty_rhs ; }
        
  | _ -> raise (Failure "unexpected Lang_ form")
        

let element_data_of_prod xd ts p =
  (* try indenting nonterms iff this production has a top-level terminal *)
  let indent_nonterms = List.exists (function | Lang_terminal _ -> true | _ -> false) p.prod_es in 
  List.map (element_data_of_element xd ts true indent_nonterms false) p.prod_es


let pp_menhir_prod_grammar element_data = 
  String.concat "  " 
    (List.map 
       (function x -> 
         match x.semantic_value_id with 
         | Some svi -> Printf.sprintf "%s = %s" svi (x.grammar_body) 
         | None -> x.grammar_body) 
       element_data)

let pp_menhir_prod_action p element_data = 
  String.capitalize_ascii p.prod_name 
  ^ 
    (let args = Auxl.option_map (function x-> x.semantic_action) element_data in
    match args with
    | [] -> ""
    | _ -> "("^ String.concat "," args ^ ")" )

let has_hom hn hs = match Auxl.hom_spec_for_hom_name hn hs with Some _ -> true | None -> false

(* aux rule stuff *)
(* ...for rules *)
let generate_aux_info_for_rule generate_aux_info r = 
  generate_aux_info &&
  (match Auxl.hom_spec_for_hom_name "aux" r.rule_homs with 
  | Some hs -> true
  | None -> false)

let aux_constructor generate_aux_info_here r p : string option = 
  if generate_aux_info_here && not(has_hom "ocaml" p.prod_homs) && !Global_option.aux_style_rules then
    let aux_prod_name = (if r.rule_pn_wrapper<>"" then r.rule_pn_wrapper else String.capitalize_ascii r.rule_ntr_name ^"_") ^ "aux" in
    Some aux_prod_name
  else
    None
(* ...for constructors *)

let ott_menhir_loc = "ott_menhir_loc" (* ocaml variable to use for locations *)

let aux_constructor_element : element_data = 
  { semantic_value_id = Some ott_menhir_loc;
    grammar_body = "DUMMY";
    semantic_action = Some "Range($symbolstartpos,$endpos)";
    pp_raw_rhs = None;
    pp_json_rhs = None;
    pp_pretty_rhs = None (* effectively pp-suppress for this element *); }

let generate_aux_info_for_prod generate_aux_info r p = 
  generate_aux_info && not(!Global_option.aux_style_rules) && 
  (match Auxl.hom_spec_for_hom_name "aux" r.rule_homs with 
  | Some hs -> true
  | None -> false)


let pp_pattern_prod r p generate_aux_info_here element_data = 
  let element_data' = element_data @ if generate_aux_info_for_prod generate_aux_info_here r p then [aux_constructor_element] else [] in
  let inner_pattern = 
    String.capitalize_ascii p.prod_name 
    ^ 
      (let args = Auxl.option_map (function x-> x.semantic_value_id) element_data' in
      match args with
      | [] -> ""
      | _ -> "("^ String.concat "," args ^ ")" )
  in
  match aux_constructor generate_aux_info_here r p with
  | Some aux_con -> aux_con ^ "(" ^ inner_pattern ^ "," ^ ott_menhir_loc^")"
  | None -> inner_pattern



let menhir_prec_spec homs = 
  match Auxl.hom_spec_for_hom_name "menhir-prec" homs with 
  | None -> ""
  | Some hs -> 
      let pp_hse hse = 
        match hse with
        | Hom_string s ->  s
        | Hom_index i -> raise (Failure ("pp_menhir_prec_spec Hom_index"))
        | Hom_terminal s -> s
        | Hom_ln_free_index (mvs,s) -> raise (Failure "pp_menhir_prec_spec Hom_ln_free_index")  in
      "%prec " ^ String.concat "" (List.map pp_hse hs) ^ "\n"





(* build a menhir production *)
let pp_menhir_prod yo generate_aux_info_here xd ts r p = 
  if suppress_prod yo p then 
    ""
  else

    (* pp the production source, to use in comment *)
    let m_ascii = Ascii { ppa_colour = false; 
		          ppa_lift_cons_prefixes = false; 
		          ppa_ugly= false; 
		          ppa_show_deps = false; 
		          ppa_show_defns = false } in
    let ppd_prod =
      let stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in
      let st = St_node(dummy_loc,stnb) in
      Grammar_pp.pp_symterm m_ascii xd [] de_empty st in
    let ppd_comment = "(* "^ppd_prod ^ " :: " ^ p.prod_name^" *)" in

    (* now the real work *)
    let element_data = element_data_of_prod xd ts p in 
    let element_data' = element_data @ if generate_aux_info_for_prod generate_aux_info_here r p then [aux_constructor_element] else [] in
    let ppd_action = 
      let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in
      if p.prod_sugar || (has_hom "quotient-remove" p.prod_homs && has_hom "ocaml" p.prod_homs) || r.rule_phantom then 
        (* ocaml hom case *)
        (* to do the proper escaping of nonterms within the hom, we need to pp here, not reuse the standard machinery *)
"(*Case 1*) " ^ 
        let hs = (match Auxl.hom_spec_for_hom_name "ocaml" p.prod_homs with Some hs -> hs | None -> raise (Failure ("no ocaml hom for "^p.prod_name))) in
        let es'' =  (* remove terminals from es to get Hom_index indexing right *)
      	(List.filter
           (function 
             | (Lang_nonterm (_,_)|Lang_metavar (_,_)|Lang_list _) -> true
             | Lang_terminal _ -> false
             | (Lang_option _|Lang_sugaroption _) -> 
               raise (Invalid_argument "com for prods with option or sugaroptions not implemented"))
           es') in
        let pp_menhir_hse hse = 
          match hse with
          | Hom_string s ->  s
          (* TODO, arbitrary failure? *)
          | Hom_index i -> let e = List.nth es'' (*or es? *) i  in let d=element_data_of_element xd ts true false false e in (match d.semantic_action with Some s -> s | None -> raise (Failure ("pp_menhir_hse Hom_index " ^ string_of_int i ^ " at " ^ Location.pp_loc p.prod_loc)))
          | Hom_terminal s -> s
          | Hom_ln_free_index (mvs,s) -> raise (Failure "Hom_ln_free_index not implemented")  in
        String.concat "" (List.map pp_menhir_hse hs)

       (*  let m' = Caml { Types.ppo_include_terminals=false; Types.caml_library = ref ("",[]) } in *)
       (*  let pp_prod m'= *)
       (*    let stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in *)
       (*    let st = St_node(dummy_loc,stnb) in *)
       (*    Grammar_pp.pp_symterm m' xd [] de_empty st  *)
       (*  in  *)
       (* (\* (match Grammar_pp.pp_elements m xd [] (Grammar_pp.apply_hom_order m xd p) (\*p.prod_es*\) false false true false with Some s -> s | None -> "None")*\) *)
       (*  pp_prod m' *)
      else if not(r.rule_phantom) then 
"(*Case 2*) " ^         pp_menhir_prod_action p element_data'
      else (* use the ocaml hom - is this code now defunct? *)
"(*Case 3*) " ^         
        (match Auxl.hom_spec_for_hom_name "ocaml" p.prod_homs with 
        | Some hom -> 

            let m_hol = Hol { Types.hol_library = ref ("",[]) } in
            let m_ocaml = Caml { Types.ppo_include_terminals=false; Types.caml_library = ref ("",[]) } in
            let m_ascii = Types.error_opts in 
           Grammar_pp.pp_hom_spec m_hol (*m_ocaml*) (*(Menhir yo)*) xd hom
       (*  let pp_prod m'= *)
       (*    let stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in *)
       (*    let st = St_node(dummy_loc,stnb) in *)
       (*    Grammar_pp.pp_symterm m' xd [] de_empty st *)
       (*  in *)
       (* (\* (match Grammar_pp.pp_elements m xd [] (Grammar_pp.apply_hom_order m xd p) (\*p.prod_es*\) false false true false with Some s -> s | None -> "None")*\) *)
       (*  pp_prod (\*m_ocaml*\) m_ascii *)



        | None -> ignore(Auxl.error (Some (r.rule_loc)) ("no ocaml hom for production "^p.prod_name));"")
    in

    let aux_wrapper_l, aux_wrapper_r = 
      (match aux_constructor generate_aux_info_here r p with 
      | Some aux_con -> 
          (aux_con ^ "(",
       ",Range($symbolstartpos,$endpos) )")
      | None -> 
          ("", "")) in

    "| " ^ pp_menhir_prod_grammar element_data ^ "    " ^ ppd_comment ^ "\n"
    ^ 
      "    { " ^ aux_wrapper_l ^ ppd_action ^ aux_wrapper_r ^ " }\n"
    ^ 
      menhir_prec_spec p.prod_homs



(* build a menhir rule *)
let pp_menhir_rule yo generate_aux_info xd ts r = 
  if suppress_rule yo r then 
    ""
  else 
    (* ignore the body of the aux hom - assume it is {{ aux _ l }} *)
    let generate_aux_info_here = generate_aux_info_for_rule generate_aux_info r in 
     menhir_nonterminal_id_of_ntr r.rule_ntr_name ^ ":\n" 
    ^  String.concat "" (List.map (pp_menhir_prod yo generate_aux_info_here xd ts r) r.rule_ps)
    ^ "\n"

let is_start_rule yo r = 
  not(suppress_rule yo r) && (has_hom "menhir-start" r.rule_homs) && not (has_hom "quotient-with" r.rule_homs)

(* construct a menhir rule for a start symbol, sticking an EOF on *)
let pp_menhir_start_rule yo xd ts r = 
  if not(is_start_rule yo r) then 
    ""
  else 
    let ntr = r.rule_ntr_name in
    let nt = (ntr,[]) in
    let id,body = menhir_semantic_value_id_of_ntmv nt, menhir_nonterminal_id_of_ntr ntr in 
    menhir_start id ^ ":\n" 
    ^ "| " ^ Printf.sprintf "%s = %s" id body ^ " EOF" ^ "\n"
    ^ "    { " ^ id ^ " }\n\n"

let pp_menhir_start_rules yo xd ts = 
  String.concat "" 
    (List.map (pp_menhir_start_rule yo xd ts)  xd.xd_rs)
                                                                
(* construct menhir start symbol declarations *)
  let pp_menhir_start_symbols yo generate_aux_info xd = 
    String.concat "" 
      (List.map 
         (function r -> 
           if not(is_start_rule yo r) then 
             ""
           else
             let ty0 = 
               Grammar_pp.strip_surrounding_parens 
                 (Grammar_pp.pp_nontermroot_ty (Caml yo.ppm_caml_opts) xd r.rule_ntr_name) in
             let ty =
               match Auxl.hom_spec_for_hom_name "menhir-start-type" r.rule_homs with 
               | Some hs ->
                   let pp_hse hse = 
                     match hse with
                     | Hom_string s ->  s
                     | Hom_index i -> raise (Failure ("menhir-start-type Hom_index"))
                     | Hom_terminal s -> s
                     | Hom_ln_free_index (mvs,s) -> raise (Failure "menhir-start-type Hom_ln_free_index")  in
                   String.concat "" (List.map pp_hse hs)
               | None ->
                   let (ty1, ty_arg) = 
                     if String.length ty0 >= 3 && String.sub ty0 0 3 = "'a " then 
                       (String.sub ty0 3 (String.length ty0 - 3), "unit ")
                     else
                       (ty0, "") in
                   ty_arg 
                   ^ yo.ppm_caml_ast_module 
                   ^ "."  
                   ^ ty1
             in
             (*let generate_aux_info_here = generate_aux_info &&
               (match Auxl.hom_spec_for_hom_name "aux" r.rule_homs with 
               | Some hs -> true
               | None -> false) in
               let ty1 = if generate_aux_info_here then ty1 ^ "_aux" else ty1 in*)
             "%start <" 
             ^ ty
             ^ "> " 
             ^ menhir_start (menhir_nonterminal_id_of_ntr r.rule_ntr_name) 
             ^ "\n")
         xd.xd_rs)

(** ******************************************************************** *)
(** raw pp                                                               *)
(** ******************************************************************** *)

      
(* all this should really use a more efficient representation than string *)


(*        pp_raw_rhs        = Some (" string \"\\\"\" ^^ string " ^ svi ^ " ^^ string \"\\\"\"");
        pp_pretty_rhs     = "string "^ svi ; }
 *)
let pp_pp_raw_metavar_defn yo generate_aux_info xd ts md = 
  if suppress_metavar yo md then 
    None
  else 
    (match Auxl.hom_spec_for_hom_name "pp-raw" md.mvd_rep with 
    | Some hs -> 
        Some (pp_pp_raw_name md.mvd_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n\n")
    | None ->
       (*       let svi = menhir_semantic_value_id_of_ntmv (md.mvd_name,[])  in *)
       let svi = "x" in
       (match Auxl.hom_spec_for_hom_name "ocaml" md.mvd_rep with 
        | Some [Hom_string s] when s="string" -> 
           Some (pp_pp_raw_name md.mvd_name ^ " "^svi^" = " ^ " string \"\\\"\" ^^ string " ^ svi ^ " ^^ string \"\\\"\"\n\n")
        | Some [Hom_string s] when s="int" -> 
           Some (pp_pp_raw_name md.mvd_name ^ " "^svi^" = " ^ " string_of_int " ^ svi ^ "\n\n")
        | Some [Hom_string s] when s="big_int" -> 
           Some (pp_pp_raw_name md.mvd_name ^ " "^svi^" = " ^ " Big_int.string_of_big_int " ^ svi ^ "\n\n")
        | Some [Hom_string s]  -> 
           Some (pp_pp_raw_name md.mvd_name ^ " "^svi^" = " ^ " string_of_" ^ s ^ " " ^ svi ^ "\n\n")
        | Some hs -> Some ("no default for "^md.mvd_name^" ocaml homspec="^Grammar_pp.pp_plain_hom_spec hs ^ "\n\n")
        | None -> Some ("no pp-raw or ocaml hom for "^md.mvd_name^ "\n\n")
       )
    )


let pp_pp_metavar_defn yo generate_aux_info xd ts md = 
  if false && suppress_metavar yo md then 
    None
  else 
    (match Auxl.hom_spec_for_hom_name "pp" md.mvd_rep with 
    | Some hs -> 
        Some (pp_pp_name md.mvd_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n\n")
    | None ->
       (*       let svi = menhir_semantic_value_id_of_ntmv (md.mvd_name,[])  in *)
       let svi = "x" in
       (match Auxl.hom_spec_for_hom_name "ocaml" md.mvd_rep with 
        | Some [Hom_string s] when s="string" -> 
           Some (pp_pp_name md.mvd_name ^ " "^svi^" = " ^ "string " ^ svi ^ " ^^ string \"\"\n\n")
        | Some [Hom_string s] when s="int" -> 
           Some (pp_pp_name md.mvd_name ^ " "^svi^" = " ^ "string_of_int " ^ svi ^ "\n\n")
        | Some [Hom_string s] when s="big_int" -> 
           Some (pp_pp_name md.mvd_name ^ " "^svi^" = " ^ " Big_int.string_of_big_int " ^ svi ^ "\n\n")
        | Some [Hom_string s]  -> 
           Some (pp_pp_name md.mvd_name ^ " "^svi^" = " ^ " string_of_" ^ s ^ " " ^ svi ^ "\n\n")
        | Some hs -> Some ("no pp default for "^md.mvd_name^" ocaml homspec="^Grammar_pp.pp_plain_hom_spec hs ^ "\n\n")
        | None -> Some ("no pp or ocaml hom for "^md.mvd_name^ "\n\n")
       )
    )


  
       (*
       if r.rule_phantom then
       (*(Auxl.error (Some r.rule_loc) ("no pp-raw hom for phantom production "^r.rule_ntr_name));*)
         Some (pp_pp_raw_name r.rule_ntr_name ^ "_default " (*^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs*) ^"\n\n")
       else 
 *)

(*
       
         Some (pp_pp_raw_name mvd.mvd_name ^ " x = match x with\n" 
               ^  String.concat "" (List.map (pp_pp_raw_prod yo generate_aux_info_here xd ts r) r.rule_ps)
               ^ "\n")
    )
 *)
  
  
let pp_pp_raw_prod yo generate_aux_info_here xd ts r p = 
  if suppress_prod yo p || p.prod_sugar then 
    ""
  else
    match Auxl.hom_spec_for_hom_name "pp-raw" p.prod_homs with 
    | Some hs -> 
       "| " ^ String.capitalize_ascii p.prod_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n"
    | None ->
       (*let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in*)
       let element_data = element_data_of_prod xd ts p in 
       
       let ppd_rhs = 
         (match aux_constructor generate_aux_info_here r p with
          | Some _ -> " string \"[\" ^^ string (pp_raw_l "^ott_menhir_loc^") ^^ string \"]\" ^^ "
          | None -> "") 
         ^
           "string \"" ^ String.capitalize_ascii p.prod_name ^ "\"" 
         ^ 
           let args = Auxl.option_map (function x->x.pp_raw_rhs) element_data in
           match args with
           | [] -> ""
           | _ -> " ^^ string \"(\" ^^ "^ String.concat " ^^ string \",\" ^^ " args ^ " ^^ string \")\"" 
       in                                                                   
       "| " ^ pp_pattern_prod r p generate_aux_info_here element_data ^ " -> " 
       ^ ppd_rhs
       ^ "\n"
       

let pp_pp_raw_rule yo generate_aux_info xd ts r = 
  if suppress_rule yo r then 
    None
  else 
    (match Auxl.hom_spec_for_hom_name "pp-raw" r.rule_homs with 
    | Some hs -> 
        Some (pp_pp_raw_name r.rule_ntr_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n\n")
    | None ->
       if r.rule_phantom then
       (*(Auxl.error (Some r.rule_loc) ("no pp-raw hom for phantom production "^r.rule_ntr_name));*)
         Some (pp_pp_raw_name r.rule_ntr_name ^ "_default " (*^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs*) ^"\n\n")
       else 
         let generate_aux_info_here = generate_aux_info_for_rule generate_aux_info r in 
    
         Some (pp_pp_raw_name r.rule_ntr_name ^ pp_params r ^ " x = match x with\n" 
               ^  String.concat "" (List.map (pp_pp_raw_prod yo generate_aux_info_here xd ts r) r.rule_ps)
               ^ "\n")
    )

let pp_pp_raw_metavar_defns_and_rules yo generate_aux_info xd ts mds rs = 
  "let rec "
  ^ String.concat "and "
      ((Auxl.option_map (pp_pp_raw_metavar_defn yo generate_aux_info xd ts) mds)
       @ (Auxl.option_map (pp_pp_raw_rule yo generate_aux_info xd ts) rs))


(** ******************************************************************** *)
(**  pp                                                                  *)
(** ******************************************************************** *)
      
let pp_pp_prod yo generate_aux_info_here prettier xd ts r p = 
  if suppress_prod yo p || p.prod_sugar then 
    ""
  else
    match Auxl.hom_spec_for_hom_name "pp" p.prod_homs with 
    | Some hs -> 
       "| " ^ String.capitalize_ascii p.prod_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n"
    | None ->
       (*let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in*)
       let element_data = element_data_of_prod xd ts p in 
       let ppd_rhs = 
         let args = Auxl.option_map (function x -> x.pp_pretty_rhs) element_data in
         match args with
         | [] -> "string \"\""
         | [arg] -> arg
         | _ ->
            if prettier then 
              "group(string \"\" ^^ " ^ String.concat " ^^ break 1 ^^ " args  ^ " ^^ string \"\")" (* no extra parens - even when required*)
                                                                                   (*              "group(string \"(\" ^^ " ^ String.concat " ^^ break 1 ^^ " args  ^ " ^^ string \")\")" (* full parens*)*)
            else                                                                              "string \"(\" ^^ " ^ String.concat " ^^ string \" \" ^^ " args  ^ " ^^ string \")\"" (* full parens*)
                                                                                    (*  | _ -> String.concat " ^ \" \" ^ " args *)
       in
       "| " ^ pp_pattern_prod r p generate_aux_info_here element_data ^ " -> " 
       ^ ppd_rhs
       ^ "\n"

let pp_pp_rule yo generate_aux_info prettier  xd ts r = 
  if suppress_rule yo r || has_hom "pp-suppress" r.rule_homs then 
    None
  else 
    (match Auxl.hom_spec_for_hom_name "pp" r.rule_homs with 
    | Some hs -> 
        Some (pp_pp_name r.rule_ntr_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n\n")
    | None ->
       if r.rule_phantom then
         (* hack: default pp hom if missing *)
         let () = Auxl.warning (Some r.rule_loc) ("no pp hom for phantom production "^r.rule_ntr_name) in
         Some (pp_pp_name r.rule_ntr_name ^ "_default " (*^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs *)^"\n\n")
       else
         let generate_aux_info_here = generate_aux_info_for_rule generate_aux_info r in 
         Some (pp_pp_name r.rule_ntr_name ^ pp_params r ^ " x = match x with\n" 
               ^  String.concat "" (List.map (pp_pp_prod yo generate_aux_info_here prettier xd ts r) r.rule_ps)
               ^ "\n")
    )


let pp_pp_metavar_defns_and_rules yo generate_aux_info xd ts mds rs = 
  let prettier = true in
  "let rec "
  ^ String.concat "and "
      ((Auxl.option_map (pp_pp_metavar_defn yo generate_aux_info xd ts) mds)
      @ (Auxl.option_map (pp_pp_rule yo generate_aux_info prettier xd ts) rs))

(** ******************************************************************** *)
(** json pp                                                               *)
(** ******************************************************************** *)

      
let pp_pp_json_metavar_defn yo generate_aux_info xd ts md = 
  if suppress_metavar yo md then 
    None
  else 
    (match Auxl.hom_spec_for_hom_name "pp-json" md.mvd_rep with 
    | Some hs -> 
        Some (pp_pp_json_name md.mvd_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n\n")
    | None ->
       (*       let svi = menhir_semantic_value_id_of_ntmv (md.mvd_name,[])  in *)
       let svi = "x" in
       (match Auxl.hom_spec_for_hom_name "ocaml" md.mvd_rep with 
        | Some [Hom_string s] when s="string" -> 
           Some (pp_pp_json_name md.mvd_name ^ " "^svi^" = " ^ " string \"\\\"\" ^^ string " ^ svi ^ " ^^ string \"\\\"\"\n\n")
        | Some [Hom_string s] when s="int" -> 
           Some (pp_pp_json_name md.mvd_name ^ " "^svi^" = " ^ " string_of_int " ^ svi ^ "\n\n")
        | Some [Hom_string s] when s="big_int" -> 
           Some (pp_pp_json_name md.mvd_name ^ " "^svi^" = " ^ " Big_int.string_of_big_int " ^ svi ^ "\n\n")
        | Some [Hom_string s]  -> 
           Some (pp_pp_json_name md.mvd_name ^ " "^svi^" = " ^ " string_of_" ^ s ^ " " ^ svi ^ "\n\n")
        | Some hs -> Some ("no default for "^md.mvd_name^" ocaml homspec="^Grammar_pp.pp_plain_hom_spec hs ^ "\n\n")
        | None -> Some ("no pp-json or ocaml hom for "^md.mvd_name^ "\n\n")
       )
    )

  
let pp_pp_json_prod yo generate_aux_info_here xd ts r p = 
  if suppress_prod yo p || p.prod_sugar then 
    ""
  else
    match Auxl.hom_spec_for_hom_name "pp-json" p.prod_homs with 
    | Some hs -> 
       "| " ^ String.capitalize_ascii p.prod_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n"
    | None ->
       (*let es' = Grammar_pp.apply_hom_order (Menhir yo) xd p in*)
       let element_data = element_data_of_prod xd ts p in 
       
       let ppd_rhs = 
         (match aux_constructor generate_aux_info_here r p with
          | Some _ -> " string \"[\" ^^ string (pp_json_l "^ott_menhir_loc^") ^^ string \"]\" ^^ "
          | None -> "") 
         ^
           "string \"{ \\\"tag\\\" : \\\"" ^ String.capitalize_ascii p.prod_name ^ "\\\"\"" 
         ^ 
           let args = Auxl.option_map (function x->x.pp_json_rhs) element_data in
           match args with
           | [] -> " ^^ string \"}\""
           | _ -> " ^^ string \", \" ^^ "^ String.concat " ^^ string \",\" ^^ " args ^ " ^^ string \"}\"" 
       in                                                                   
       "| " ^ pp_pattern_prod r p generate_aux_info_here element_data ^ " -> " 
       ^ ppd_rhs
       ^ "\n"
       

let pp_pp_json_rule yo generate_aux_info xd ts r = 
  if suppress_rule yo r then 
    None
  else 
    (match Auxl.hom_spec_for_hom_name "pp-json" r.rule_homs with 
    | Some hs -> 
        Some (pp_pp_json_name r.rule_ntr_name ^ " " ^ Grammar_pp.pp_hom_spec (Menhir yo) xd hs ^"\n\n")
    | None ->
       if r.rule_phantom then
         Auxl.error (Some r.rule_loc) ("no pp-json hom for phantom production "^r.rule_ntr_name)
       else 
         let generate_aux_info_here = generate_aux_info_for_rule generate_aux_info r in 
    
         Some (pp_pp_json_name r.rule_ntr_name ^ pp_params r ^ " x = match x with\n" 
               ^  String.concat "" (List.map (pp_pp_json_prod yo generate_aux_info_here xd ts r) r.rule_ps)
               ^ "\n")
    )

let pp_pp_json_metavar_defns_and_rules yo generate_aux_info xd ts mds rs = 
  "let rec "
  ^ String.concat "and "
      ((Auxl.option_map (pp_pp_json_metavar_defn yo generate_aux_info xd ts) mds)
       @ (Auxl.option_map (pp_pp_json_rule yo generate_aux_info xd ts) rs))



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
let pp_menhir_syntaxdefn m sources _(*xd_quotiented*) xd_unquotiented lookup generate_aux_info oi = let yo = match m with Menhir yo -> yo | _ -> raise (Failure "pp_menhir_systemdefn called with bad ppmode") in 
  match oi with
  | (o,is)::[] ->
      let _ = Auxl.filename_check m o in
      let fd = open_out o in
      let ts = token_names_of_syntaxdefn yo xd_unquotiented in
      Printf.fprintf fd "/* generated by Ott %s from: %s */\n" Version.n sources;
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
      Embed_pp.pp_embeds fd m xd_unquotiented lookup xd_unquotiented.xd_embed;

      output_string fd (pp_menhir_start_symbols yo generate_aux_info xd_unquotiented);
      output_string fd "\n\n%%\n\n";

      output_string fd (pp_menhir_start_rules yo xd_unquotiented ts);
      List.iter (function r -> output_string fd (pp_menhir_rule yo generate_aux_info xd_unquotiented ts r)) xd_unquotiented.xd_rs;
      close_out fd

  | _ -> Auxl.error None "must specify only one output file in the menhir backend.\n"

(* output pp source file (should be called with quotiented syntaxdefn file) *)
let pp_pp_syntaxdefn m sources xd_quotiented xd_unquotiented xd_quotiented_unaux generate_aux_info hack_filename oi filename =
  let yo = match m with Menhir yo -> yo | _ -> raise (Failure "pp_pp_systemdefn called with bad ppmode") in 


  let filename =
    if hack_filename then    
      match oi with
      | (o,is)::[] ->
          
          (* horrid hack to make filename for pp code by removing .mly *)
          let o_pp =
            String.sub o 0 (String.length o - 4)  ^ "_pp.ml" in
          o_pp
      | _ -> Auxl.error None "must specify only one output file in the menhir backend.\n"
            
    else
       filename 
  in

  let ts = token_names_of_syntaxdefn yo xd_unquotiented in (* from non-quotiented, to match parser *)

  (* for aux_style_rules true, should we generate recursive functions for the ntr and ntr_aux rules, or just for the ntr rules but with an extra Ntr_aux constructor on the lhs? *)
  let xd = xd_quotiented_unaux (*if !Global_option.aux_style_rules then xd_quotiented else xd_quotiented_unaux in*) in
(*
  let m_ascii = Ascii { ppa_colour = false; 
		      ppa_lift_cons_prefixes = false; 
		      ppa_ugly= false; 
		      ppa_show_deps = false; 
		      ppa_show_defns = false } in
  Printf.printf "%s\n" (Grammar_pp.pp_syntaxdefn m_ascii xd);
 *)
  let fd = open_out filename in
  Printf.fprintf fd "(* generated by Ott %s from: %s *)\n" Version.n sources;
  output_string fd "open PPrint\n";
  output_string fd ("open " ^ (match !Global_option.caml_pp_ast_module with None -> yo.ppm_caml_ast_module | Some s -> s)  ^ "\n\n" 
                    ^ pp_pp_raw_metavar_defns_and_rules yo generate_aux_info xd ts xd.xd_mds xd.xd_rs
                    ^ "\n"
                    ^ pp_pp_metavar_defns_and_rules yo generate_aux_info xd ts xd.xd_mds xd.xd_rs);
  if !Global_option.caml_pp_json then
    output_string fd ("\n"
                      ^ pp_pp_json_metavar_defns_and_rules yo generate_aux_info xd ts xd.xd_mds xd.xd_rs
                   );
  close_out fd;


