(**************************************************************************)
(*                          new_term_parser                               *)
(*                                                                        *)
(*        Scott Owens, Computer Laboratory, University of Cambridge       *)
(*                                                                        *)
(*  Copyright 2007                                                       *)
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

(* Build a parser for Ott symterms and concrete terms using glr.ml *)

(* Not yet implemented:
 * Better performance
 * Fix weird ambiguity with ":concrete"
 *)

let fast_parse = ref false 
  (* true: do not add pseudoterminals :rulename: and :concrete: to grammar *)

open Types;;

exception Parse_error of loc * string;;

let error_string s0 s c = 
  s0
  ^
  let c=c+0 in
    if c > String.length s then "(internal overflow in building error string)"
    else
      let s1 = String.sub s 0 c in
      let s2 = String.sub s c (String.length s - c) in
        " (char "^string_of_int c^"): "^s1^"***"^s2^" ";;
                                                   
let no_parses_error_string s l = 
  error_string "no parses" s l;;

let parse_error2 loc s msg =
  raise (Parse_error (loc, msg));;

module type NTsig =
sig
  type t
  type nt = 
      Orig_nt of string * bool
    | Term_nt of string
    | Metavar_nt of string * bool
    | Builtin_nt of string
    | Gen_nt of t
  val compare : t -> t -> int
  val to_string : t -> string
  val make_build : unit -> nt -> t
  val whitespace : nt
  val fail : nt
  val suffix : nt
  val suffix_item : nt
  val digit : nt
  val digit_plus : nt
  val digit_plus2 : nt
  val dots : nt
  val alphanum0 : nt
  val alphanum : nt
  val cap_alphanum : nt
  val cap_az : nt
  val az : nt
  val alpha_follow : nt
  val indexvar : nt
  val indexvar_fancy_suffix : nt
  val number : nt
  val nt_or_mv : nt
end;;


module Gtp = 
struct
  module Terminal =
  struct
    type t = char
    let compare = Char.compare
    let eof =  '\xFF'
    let is_eof c = c == eof
    let to_string c = "'" ^ Char.escaped c ^ "'"
    let to_int = Char.code
  end;;

  module Nonterminal : NTsig =
  struct
    type nt =
        Orig_nt of string * bool
      | Term_nt of string
      | Metavar_nt of string * bool
      | Builtin_nt of string
      | Gen_nt of t
    and t = int * nt;;
    let compare_nt nt1 nt2 = match nt1 with
      | Orig_nt (s1, b1) ->
          (match nt2 with 
          | Orig_nt (s2, b2) ->
            let n = String.compare s1 s2 in
            if n = 0 then Obj.magic b1 - Obj.magic b2 else n
          | _ -> -1)
      | Term_nt s1 ->
          (match nt2 with 
          | Orig_nt _ -> 1
          | Term_nt s2 -> String.compare s1 s2
          | _ -> -1)
      | Metavar_nt (s1, b1) ->
          (match nt2 with 
          | Orig_nt _ | Term_nt _ -> 1
          | Metavar_nt (s2, b2) ->
            let n = String.compare s1 s2 in
            if n = 0 then Obj.magic b1 - Obj.magic b2 else n
          | _ -> -1)
      | Builtin_nt s1 ->
          (match nt2 with 
          | Orig_nt _ | Term_nt _ | Metavar_nt _ -> 1
          | Builtin_nt s2 -> String.compare s1 s2
          | _ -> -1)
      | Gen_nt (i1,t1) ->
          (match nt2 with Gen_nt (i2,t2) -> i1 - i2 | _ -> 1)

    module Ntmap = Map.Make (struct type t = nt;; let compare x y = compare_nt x y;; end);;
    let compare (i1, _) (i2, _) = i1 - i2;;

    let encode_string_chars s =
      let open Str in
        global_substitute (regexp "[][!\"#$%&()*+,./:;<=>?@\\^`{}|~-]")
          (function 
             | "[" -> "lbrac"
             | "]" -> "rbrac"
             | "!" -> "excl"
             | "\"" -> "doublequote"
             | "#" -> "hash"
             | "$" -> "dollar"
             | "(" -> "lparen"
             | ")" -> "rparen"
             | "*" -> "times"
             | "+" -> "plus"
             | "," -> "comma"
             | "/" -> "slash"
             | ":" -> "colon"
             | ";" -> "semi"
             | "<" -> "lt"
             | "=" -> "eq"
             | ">" -> "gt"
             | "?" -> "question"
             | "@" -> "at"
             | "\\" -> "backslash"
             | "^" -> "caret"
             | "`" -> "singlequote"
             | "{" -> "lcurly"
             | "}" -> "rcurly"
             | "|" -> "bar"
             | "~" -> "tilde"
             | "-" -> "minus")
          s

    let rec to_string (i, nt) =
      match nt with
        Orig_nt (s, con) -> (if con then "concrete_" else "") ^ s
      | Term_nt s -> "terminal_" ^ s
      | Metavar_nt (s, con) -> (if con then "concrete_" else "") ^ s
      | Builtin_nt s -> s
      | Gen_nt t -> to_string t ^ string_of_int i

    let make_build () =
      let c = ref 0 in
      let m = ref Ntmap.empty in
        function
           Gen_nt s ->
             let res = (!c, Gen_nt s) in
               incr c;
               res
          | nt ->
              try
                Ntmap.find nt !m
              with Not_found ->
                let res = (!c, nt) in
                  m := Ntmap.add nt res !m;
                  incr c;
                  res;;

    let whitespace = Builtin_nt "whitespace";;
    let fail = Builtin_nt "fail";;
    let suffix = Builtin_nt "suffix";;
    let suffix_item = Builtin_nt "suffix_item";;
    let digit = Builtin_nt "digit";;
    let digit_plus = Builtin_nt "digit_plus";;
    let digit_plus2 = Builtin_nt "digit_plus2";;
    let dots = Builtin_nt "dots";;
    let alphanum0 = Builtin_nt "alphanum0";;
    let alphanum = Builtin_nt "alphanum";;
    let cap_alphanum = Builtin_nt "Alphanum";;
    let cap_az = Builtin_nt "cap_az";;
    let az = Builtin_nt "az";;
    let alpha_follow = Builtin_nt "alpha_follow";;
    let indexvar = Builtin_nt "indexvar";;
    let indexvar_fancy_suffix = Builtin_nt "indexvar_fancy_suffix";;
    let number = Builtin_nt "number";;
    let nt_or_mv = Builtin_nt "nt_or_mv";;
  end;;

  type result =
      Res_st of symterm
    | Res_ste of symterm_element
    | Res_stli of symterm_list_item
    | Res_stlil of symterm_list_item list
    | Res_ignore
    | Res_char of char
    | Res_charl of char list
    | Res_string of string
    | Res_int of int
    | Res_si of suffix_item
    | Res_sil of suffix_item list
    | Res_none;;

  exception BadInputGrammar of string;;
  let signal_error s = raise (BadInputGrammar s);;
end;;

open Gtp;;
module Nt = Nonterminal;;
module GramTypes = Parse_table.MakeTypes (Gtp);;
open GramTypes;;

exception Reject_parse
exception Reject_all_parses

let rec split l n = 
  if n = 0 then
    ([], l)
  else
    match l with
        [] -> raise (Invalid_argument "List too short")
      | x::y ->
          let (f, r) = split y (n - 1) in
            (x::f, r);;

let split_last l n = 
  let (f, r) = split (List.rev l) n in
      (List.rev r, List.rev f);;

let string_to_terms s = 
  let res = ref [] in
    for i = String.length s - 1 downto 0 do
      res := T (String.get s i) :: !res
    done;
    !res;;

let lex_regexp_of_mvd : metavardefn -> string option (*Str.regexp*) = 
  function mvd -> 
    try 
      match List.assoc "lex" mvd.mvd_rep with
        | Hom_string s::[] -> Some s 
        | _ -> failwith "malformed lex specification" 
    with Not_found -> None;;

let concrete_parsers = 
  [ "alphanum0", Nt.alphanum0;
    "alphanum", Nt.alphanum;
    "Alphanum", Nt.cap_alphanum;
    "numeral", Nt.digit_plus2
  ] 

let res_ignore _ = Res_ignore;;

let res_charl [Res_char c; Res_charl l] =
  Res_charl (c::l);;

let res_cons_string [Res_char c; Res_charl l] =
  Res_string (Auxl.string_of_char_list (c::l));;

let res_stlil [Res_stli a; Res_stlil b] = Res_stlil (a::b);;

let build_grammar (xd : syntaxdefn) 
      : (grammar * (Nonterminal.t * follow) list * priority list * Nt.t list *
         (Nt.nt -> Nt.t)) =

  let ntr_synonyms = Auxl.ntr_synonyms xd in

  let index_count = ref 0 in
  let (prods : production list ref) = ref [] in
  let add_prod_idx_reject t r x y z =
    prods := {prod_left=x; prod_right=y; prod_action=z; reject=r;
              transparent=t; index=(!index_count)} :: !prods;
    incr index_count;
    !index_count - 1 
  in
  let add_prod_idx x y z = add_prod_idx_reject false false x y z in
  let add_prod_reject x y z = ignore(add_prod_idx_reject false true x y z); () in 
  let add_prod x y z = ignore(add_prod_idx x y z); () in
  let add_prod_transp x y z = add_prod_idx_reject true false x y z in

  let prodname_to_index1 = Hashtbl.create 101 in
  let prodname_to_index2 = Hashtbl.create 101 in

  let ((mknt : Nt.nt -> Nt.t), (mkNT : Nt.nt -> grammar_symbol)) =
    let f = Nt.make_build () in
      (f, fun x -> NT (f x))
  in


  (* The string is just for printing out the grammar *)
  let (follows : (Nonterminal.t * follow * string) list ref) = ref [] in
  let add_alphanum_restr x =
    follows := (x, Single Auxl.isalphanum, "[a-zA-Z0-9]") :: !follows
  in
  let add_num_restr x =
    follows := (x, Single (fun c -> c >= '0' && c <= '9'), "[0-9]") :: !follows
  in

  let (priorities : priority list ref) = ref [] in
  let add_right_assoc (i1 : int) (i2 : int) = 
    priorities := Right (i1, i2)::!priorities
  in
  let add_greater_prior (i1 : int) (i2 : int) =
    priorities := Greater (i1, i2)::!priorities
  in

  let rec process_prod_res : result list -> symterm_element list = function
      [] -> []
    | Res_ignore::rl -> process_prod_res rl
    | Res_ste ste::rl -> ste::process_prod_res rl
    | Res_st st::rl -> Ste_st (dummy_loc, st)::process_prod_res rl
  in

  let enforce_length_constraint elb =
    let (length_constraint : int option) = 
      (match elb.elb_boundo with
         | Some(Bound_dotform bd) -> Some bd.bd_length
         | Some(Bound_comp_lu bclu) -> Some bclu.bclu_length
         | _ -> None)
    in
      fun stlis ->
        if 
          (match length_constraint with
             | Some lc -> 
                 Auxl.min_length_of_stlis stlis >= lc
             | None -> true )
        then
          Res_ste (Ste_list (dummy_loc, stlis))
        else
          raise Reject_parse
  in
  let rec process_element (concrete : bool) (nt : Nonterminal.t) (pn : prodname)
        : element -> grammar_symbol = 
    function
        Lang_terminal t' -> mkNT (Nt.Term_nt t')
      | Lang_nonterm (ntrp, nt) -> mkNT (Nt.Orig_nt (ntrp, concrete))
      | Lang_metavar (mvrp, mv) ->
          let mvd = Auxl.mvd_of_mvr xd mvrp in
            mkNT (Nt.Metavar_nt (mvd.mvd_name, concrete))
      | Lang_list elb -> 
          let elc = enforce_length_constraint elb in
          let list_nt = mknt (Nt.Gen_nt nt) in
            (* list_nt : Res_ste *)
            (* list_help_nt : Res_stlil *)
            add_prod list_nt [] (fun _ -> elc []);
            add_prod list_nt [NT (process_list_form concrete nt pn elb)]
              (fun [Res_stlil x] -> elc x);
            NT list_nt
      | (Lang_option _ | Lang_sugaroption _) -> mkNT Nt.fail
  and process_elements (concrete: bool) (nt : Nonterminal.t) (pn : prodname) 
             (es : element list) 
             : grammar_symbol list =
    List.map (process_element concrete nt pn) es
  and process_list_form (concrete : bool) (nt : Nonterminal.t) (pn : prodname) 
      (elb : element_list_body) : Nonterminal.t =
    let list_help_nt = mknt (Nt.Gen_nt nt) in
    let concrete_list_entry_nt = mknt (Nt.Gen_nt nt) in

      (* concrete_list_entry_nt : Res_stli *)
      add_prod 
        concrete_list_entry_nt 
        (process_elements concrete nt pn elb.elb_es)
        (fun rl ->
           Res_stli (Stli_single (dummy_loc, process_prod_res rl)));
      add_prod list_help_nt [NT concrete_list_entry_nt]
        (fun [Res_stli x]-> Res_stlil [x]);
      let idx = 
        match elb.elb_tmo with
            None -> 
              add_prod_reject list_help_nt [] (fun _ -> assert false);
              add_prod_transp
                list_help_nt 
                [NT concrete_list_entry_nt; NT list_help_nt]
                res_stlil
          | Some t -> 
              add_prod_transp
                list_help_nt 
                ([NT concrete_list_entry_nt; mkNT Nt.whitespace] @
                 string_to_terms t @
                 [NT list_help_nt])
                (fun [x; _; y] -> res_stlil [x; y])
        in
          add_right_assoc idx idx;


          if not concrete then
            begin
              let list_form_nt = mknt (Nt.Gen_nt nt) in
              let make_listform_token (t : string) : grammar_symbol list = 
                mkNT Nt.whitespace :: string_to_terms t
              in
              let wsidxvar_nt = [mkNT Nt.whitespace; mkNT Nt.indexvar] in
              let list_form_prefix =
                make_listform_token Grammar_pp.pp_COMP_LEFT @
                [NT concrete_list_entry_nt] @
                make_listform_token Grammar_pp.pp_COMP_MIDDLE @
                wsidxvar_nt
              in
              (* list_form_nt : Res_stli *)
              let process_dot_listform_res es1 n' es2 =
                try let (bo'', es'') =
                  Merge.merge_symterm_element_list 0 (es1,es2) in
                  match bo'' with
                    | None ->
                        (* no index changed - so ill-formed *)
                        raise Reject_parse
                    | Some (si1,si2) ->
                        let b = Bound_dotform {bd_lower = si1;
                                               bd_upper = si2;
                                               bd_length = n'} in
                        let stlb = {stl_bound = b;
                                    stl_elements = es'';
                                    stl_loc = dummy_loc} in
                          Res_stli (Stli_listform stlb)
                with
                    Merge.Merge s -> 
                      raise Reject_parse
              in
                begin
                  match elb.elb_tmo with
                      None ->
                        add_prod 
                          list_form_nt 
                          [NT concrete_list_entry_nt;
                           mkNT Nt.whitespace;
                           mkNT Nt.dots;
                           NT concrete_list_entry_nt]
                          (fun [Res_stli (Stli_single (_, es1)); 
                                _; 
                                Res_int n';
                                Res_stli (Stli_single (_, es2))] ->
                             process_dot_listform_res es1 n' es2) 
                    | Some t -> 
                        add_prod 
                          list_form_nt 
                          ([NT concrete_list_entry_nt; mkNT Nt.whitespace] @
                           string_to_terms t @
                           [mkNT Nt.whitespace; mkNT Nt.dots; mkNT Nt.whitespace] @
                           string_to_terms t @
                           [NT concrete_list_entry_nt])
                          (fun [Res_stli (Stli_single (_, es1)); 
                                _; 
                                _;
                                Res_int n';
                                _;
                                Res_stli (Stli_single (_, es2))] ->
                             process_dot_listform_res es1 n' es2)
                end;
                add_prod
                  list_form_nt
                  (list_form_prefix @ 
                   make_listform_token Grammar_pp.pp_COMP_RIGHT)
                  (fun [_; Res_stli (Stli_single (_, es)); _; _; Res_string ivr;
                        _] ->
                     let es'' = 
                       List.map 
                         (Merge.abstract_indexvar_symterm_element ivr 0) 
                         es
                     in
                     let b = Bound_comp {bc_variable=ivr} in
                     let stlb = {stl_bound = b;
                                 stl_elements = es'';
                                 stl_loc = dummy_loc}
                     in
                       Res_stli (Stli_listform stlb));

                add_prod
                  list_form_nt
                  (list_form_prefix @
                   make_listform_token Grammar_pp.pp_COMP_IN @
                   wsidxvar_nt @
                   make_listform_token Grammar_pp.pp_COMP_RIGHT)
                  (fun [_; Res_stli (Stli_single (_, es)); _; _; Res_string ivr;
                        _;
                        _; Res_string ivr';
                        _] ->
                     let es'' = 
                       List.map 
                         (Merge.abstract_indexvar_symterm_element ivr 0)
                         es
                     in
                     let b = 
                       Bound_comp_u {bcu_variable=ivr;bcu_upper=Si_var (ivr',0)}
                     in
                     let stlb = {stl_bound = b;
                                 stl_elements = es'';
                                 stl_loc = dummy_loc} in
                       Res_stli (Stli_listform stlb));

                add_prod
                  list_form_nt
                  (list_form_prefix @
                   make_listform_token Grammar_pp.pp_COMP_IN @
                   [mkNT Nt.whitespace;
                    mkNT Nt.number;
                    mkNT Nt.whitespace; 
                    mkNT Nt.dots;
                    mkNT Nt.whitespace;
                    mkNT Nt.indexvar_fancy_suffix] @
                   make_listform_token Grammar_pp.pp_COMP_RIGHT)
                  (fun [_; Res_stli (Stli_single (_, es)); _; _; Res_string ivr;
                        _;
                        _;
                        Res_string lower;
                        _;
                        Res_int dotlength;
                        _;
                        Res_si si';
                        _] ->
                     let es'' =
                       List.map 
                         (Merge.abstract_indexvar_symterm_element ivr 0) 
                         es
                     in
                     let b = Bound_comp_lu {bclu_variable=ivr;
                                            bclu_lower=Si_num lower;
                                            bclu_upper=si';
                                            bclu_length=dotlength} in
                     let stlb = {stl_bound = b;
                                 stl_elements = es'';
                                 stl_loc = dummy_loc} in
                       Res_stli (Stli_listform stlb));

                ignore(add_prod_idx list_help_nt [NT list_form_nt]
                  (fun [Res_stli x] -> Res_stlil [x]));
                match elb.elb_tmo with
                    None -> 
                      ignore(add_prod_transp
                        list_help_nt 
                        [NT list_form_nt; NT list_help_nt]
                        res_stlil);
                      ()
                  | Some t -> 
                      ignore(add_prod_transp
                        list_help_nt 
                        ([NT list_form_nt; mkNT Nt.whitespace] @
                         string_to_terms t @
                         [NT list_help_nt])
                        (fun [x; _; y] -> res_stlil [x; y]));
                      ()
            end;
          list_help_nt
  in

  let process_prod (concrete : bool) (nt : Nonterminal.t) (ntr : nontermroot) 
        (p : prod)
        : unit =
    let build_res rl =
      Res_st
        (St_node (dummy_loc, {st_rule_ntr_name = ntr;
                              st_prod_name = p.prod_name;
                              st_es = process_prod_res rl;
                              st_loc = dummy_loc}))
    in
    let rhs = process_elements concrete nt p.prod_name p.prod_es in
    let index = add_prod_idx nt rhs build_res in
    if concrete then 
      Hashtbl.add prodname_to_index1 p.prod_name index
    else match p.prod_disambiguate with
      | None ->
         if !fast_parse then
           Hashtbl.add prodname_to_index1 p.prod_name index
         else 
           let index2 =
             add_prod_idx nt 
               (mkNT Nt.whitespace ::
                (string_to_terms (Auxl.psuedo_terminal_of_prod_name p.prod_name) @ rhs))
               (fun (_::rl) -> build_res rl) in
           Hashtbl.add prodname_to_index2 p.prod_name (index, index2)
      | Some (s1, s2) ->
           let index2 =
             add_prod_idx nt 
               (mkNT Nt.whitespace :: string_to_terms s1 @ (rhs @ string_to_terms s2))
               (fun (_::rl) -> build_res rl) in
           Hashtbl.add prodname_to_index2 p.prod_name (index, index2)
  in

  (* Orig_nt : Res_st *)
  let process_rule (r : rule) : unit =
    let ntr = r.rule_ntr_name in
    let nt = mknt (Nt.Orig_nt (r.rule_ntr_name, false)) in
      if not r.rule_meta && not !fast_parse then
        begin
          let concrete_prods = 
            List.filter (fun p -> not p.prod_meta || p.prod_sugar) r.rule_ps 
          in
          let nt_c = mknt (Nt.Orig_nt (r.rule_ntr_name, true)) in
          List.iter (process_prod true nt_c ntr) concrete_prods;
          add_prod nt
            (mkNT Nt.whitespace::
             string_to_terms Auxl.parse_as_concrete@
             [NT nt_c])
            (fun [_; x] -> x)
        end;
      (* the productions from the Ott grammar *)
      List.iter (process_prod false nt ntr) r.rule_ps;
      (* productions for mentioning the nonterminal name *)
      List.iter 
        (fun nt' -> 
           add_prod
             nt
             (mkNT Nt.whitespace::string_to_terms nt' @ [mkNT Nt.suffix])
             (fun [_; Res_sil l] ->
                Res_st (St_nonterm (dummy_loc, ntr, (nt', l)))))
        (ntr_synonyms r.rule_ntr_name);
      (* productions for mentioning the nonterminal name of subrules *)
      List.iter 
        (fun ntl -> 
           List.iter 
             (fun nt' ->
                add_prod 
                  nt
                  (mkNT Nt.whitespace::string_to_terms nt' @ [mkNT Nt.suffix])
                  (fun [_; Res_sil l] ->
                     Res_st (St_nontermsub (dummy_loc, 
                                            ntl, 
                                            Auxl.promote_ntr xd ntr, 
                                            (nt', l)))))
             (ntr_synonyms ntl))
        (Auxl.ntr_proper_subs xd r.rule_ntr_name);
      if not r.rule_meta then
        begin

        end
  in

  let add_mvr_idx nt name mvr =
    add_prod nt (mkNT Nt.whitespace::string_to_terms mvr @ [mkNT Nt.suffix])
      (fun [_; Res_sil x] ->
         Res_ste (Ste_metavar (dummy_loc, name, (mvr, x))))
  in
 
  let add_mvr_nonidx nt name mvr =
    add_prod nt (mkNT Nt.whitespace :: string_to_terms mvr)
      (fun _ -> Res_ste (Ste_metavar (dummy_loc, name, (mvr, []))));
      add_alphanum_restr nt
  in

  let terminals = Auxl.terminals_of_syntaxdefn xd in

  let is_tm s = List.mem s terminals in

  (* Metavar_nt : Res_ste *)
  let process_metavar (mvd : metavardefn) : unit =
    let nt = mknt (Nt.Metavar_nt (mvd.mvd_name, false)) in
    List.iter 
      (fun (mvr, _) ->
         if mvd.mvd_indexvar then
           add_mvr_nonidx nt mvd.mvd_name mvr
         else
           add_mvr_idx nt mvd.mvd_name mvr;
         )
      mvd.mvd_names;
    match lex_regexp_of_mvd mvd with
        None -> ()
      | Some r -> 
          begin try 
            add_prod nt (mkNT Nt.whitespace :: T ':' :: string_to_terms mvd.mvd_name
                         @ [T ':'; mkNT (List.assoc r concrete_parsers)])
              (fun (_::Res_string s::_) -> Res_ste (Ste_metavar (dummy_loc, mvd.mvd_name, (s, []))))
          with Not_found -> () end;
          let nt_aux = mknt (Nt.Gen_nt nt) in
          let nt_c = mknt (Nt.Metavar_nt (mvd.mvd_name, true)) in
          if not !fast_parse then
            try 
              add_prod nt_c [mkNT Nt.whitespace; 
                             mkNT (List.assoc r concrete_parsers)]
                (fun [_; Res_string s] -> 
                   if is_tm s then
                     raise Reject_parse
                   else
                     Res_ste (Ste_var (dummy_loc, mvd.mvd_name, s)));
              add_prod nt_aux [mkNT Nt.whitespace; 
                               mkNT (List.assoc r concrete_parsers)]
                (fun [_; Res_string s] -> 
                   Res_ste (Ste_var (dummy_loc, mvd.mvd_name, s)));
              add_prod_reject nt_aux [mkNT Nt.nt_or_mv]
                (fun _ -> assert false);
              add_prod nt [NT nt_aux] 
                (fun [((Res_ste (Ste_var (_, _, s))) as x)] -> 
                   if is_tm s then 
                     raise Reject_parse
                   else
                     x)
            with Not_found -> ()

  in

    (* whitespace = (' '|'\010'|'\009'|'\013'|'\012')* *)
    (* Nt.whitespace : Res_ignore *)
    add_prod (mknt Nt.whitespace) [] res_ignore;
    List.iter 
      (fun t -> add_prod (mknt Nt.whitespace)
                  [mkNT Nt.whitespace; t] res_ignore) 
      (string_to_terms " \n\t\013\012");

    (* digit = [0-9] *)
    (* Nt.digit : Res_char *)
    Auxl.string_iter 
      (let n = mknt Nt.digit in 
       fun c -> add_prod n [T c] (fun _ -> Res_char c)) 
      "0123456789";

    (* digit_plus = [0-9]+ *)
    (* Nt.digit_plus : Res_charl *)
    add_prod (mknt Nt.digit_plus) [mkNT Nt.digit] 
      (fun [Res_char c] -> Res_charl [c]);
    add_prod (mknt Nt.digit_plus) [mkNT Nt.digit; mkNT Nt.digit_plus] res_charl;
    add_num_restr (mknt Nt.digit_plus);

    (* digit_plus2 : Res_string *)
    add_prod (mknt Nt.digit_plus2) [mkNT Nt.digit_plus]
      (fun [Res_charl s] -> Res_string (Auxl.string_of_char_list s));
    add_alphanum_restr (mknt Nt.digit_plus2);

    (* dots = ..|...|.... *)
    (* Nt.dots : Res_int *)
    add_prod (mknt Nt.dots) (string_to_terms "..") (fun _ -> Res_int 0); 
    add_prod (mknt Nt.dots) (string_to_terms "...") (fun _ -> Res_int 1); 
    add_prod (mknt Nt.dots) (string_to_terms "....") (fun _ -> Res_int 2); 

    (* suffix = suffix_item* *)
    (* Nt.suffix : Res_sil *)
    add_prod (mknt Nt.suffix) [] (fun _ -> Res_sil []);
    add_prod (mknt Nt.suffix) [mkNT Nt.suffix_item; mkNT Nt.suffix]
      (fun [Res_si s; Res_sil sl] -> Res_sil (s::sl));
    add_alphanum_restr (mknt Nt.suffix);

    (* suffix_item = [0-9]+|_|'|indexvar_fancy_suffix *)
    (* Nt.suffix_item : Res_si *)
    add_prod (mknt Nt.suffix_item) [mkNT Nt.digit_plus] 
      (fun [Res_charl l] -> Res_si (Si_num (Auxl.string_of_char_list l)));
    add_prod (mknt Nt.suffix_item) [T '_'] (fun _ -> Res_si (Si_punct "_"));
    add_prod (mknt Nt.suffix_item) [T '\''] (fun _ -> Res_si (Si_punct "'"));
    add_prod (mknt Nt.suffix_item) [mkNT Nt.indexvar_fancy_suffix]
      (fun [rsi] -> rsi);

    (* cap_az = [A-Z] *)
    (* Nt.cap_az : Res_char *)
    Auxl.string_iter 
      (let n = mknt Nt.cap_az in 
       fun c -> add_prod n [T c] (fun _ -> Res_char c)) 
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ";

    (* az = [a-z] *)
    (* Nt.az : Res_char *)
    Auxl.string_iter 
      (let n = mknt Nt.az in 
       fun c -> add_prod n [T c] (fun _ -> Res_char c)) 
      "abcdefghijklmnopqrstuvwxyz";

    (* alpha_follow = ([A-Z]|[a-z]|[0-9]|['_])* *)
    (* Nt.alpha_follow : Res_charl *)
    add_prod (mknt Nt.alpha_follow) [] (fun _ -> Res_charl []);
    add_prod (mknt Nt.alpha_follow) [mkNT Nt.az; mkNT Nt.alpha_follow] res_charl;
    add_prod (mknt Nt.alpha_follow) [mkNT Nt.cap_az; mkNT Nt.alpha_follow] res_charl;
    add_prod (mknt Nt.alpha_follow) [mkNT Nt.digit; mkNT Nt.alpha_follow] res_charl;
    add_prod (mknt Nt.alpha_follow) [T '_'; mkNT Nt.alpha_follow]
      (fun [Res_charl c] -> Res_charl ('_'::c));
    add_prod (mknt Nt.alpha_follow) [T '\''; mkNT Nt.alpha_follow]
      (fun [Res_charl c] -> Res_charl ('\''::c));

    (* alphanum0 = [a-z]alpha_follow *)
    (* alphanum0 : Res_string *)
    add_prod (mknt Nt.alphanum0) [mkNT Nt.az; mkNT Nt.alpha_follow] res_cons_string;
    add_alphanum_restr (mknt Nt.alphanum0);

    (* alphanum = [a-z][A-Z]alpha_follow*)
    (* alphanum : Res_string *)
    add_prod (mknt Nt.alphanum) [mkNT Nt.az; mkNT Nt.alpha_follow] res_cons_string;
    add_prod (mknt Nt.alphanum) [mkNT Nt.cap_az; mkNT Nt.alpha_follow] res_cons_string;
    add_alphanum_restr (mknt Nt.alphanum);

    (* cap_alphanum = [A-Z]alpha_follow *)
    (* cap_alphanum : Res_string *)
    add_prod (mknt Nt.cap_alphanum) [mkNT Nt.cap_az; mkNT Nt.alpha_follow] res_cons_string;
    add_alphanum_restr (mknt Nt.cap_alphanum);

    (* number = 0|1 *)
    (* Nt.number : Res_string *)
    add_prod (mknt Nt.number) [T '0'] (fun _ -> Res_string "0");
    add_prod (mknt Nt.number) [T '1'] (fun _ -> Res_string "1");
    add_alphanum_restr (mknt Nt.number);

    (* Nt.indexvar : Res_string *)
    List.iter 
      (fun iv -> 
         add_prod (mknt Nt.indexvar) (string_to_terms iv)
           (fun _ -> Res_string iv))
      (Auxl.all_indexvar_synonyms xd);

    (* indexvar_fancy_suffix = indexvar | indexvar-1 *)
    (* Nt.indexvar_fancy_suffix : Res_si *)
    add_prod (mknt Nt.indexvar_fancy_suffix)
      [mkNT Nt.indexvar]
      (fun [Res_string s] -> Res_si (Si_var (s, 0)));

    add_prod (mknt Nt.indexvar_fancy_suffix)
      (mkNT Nt.indexvar :: string_to_terms "-1")
      (fun [Res_string s] -> Res_si (Si_var (s, -1)));

    if not !fast_parse then begin
      List.iter (add_mvr_nonidx (mknt Nt.nt_or_mv) "")
        (Auxl.all_index_mvrs_defined_by_syntaxdefn xd);
      List.iter (add_mvr_idx (mknt Nt.nt_or_mv) "")
        (Auxl.all_nonindex_mvrs_defined_by_syntaxdefn xd);
      List.iter 
        (fun nt ->
           add_prod (mknt Nt.nt_or_mv) 
             (mkNT Nt.whitespace::string_to_terms nt @ [mkNT Nt.suffix])
             (fun [_; Res_sil x] ->
                Res_st (St_nonterm (dummy_loc, "", (nt, x)))))
        (Auxl.all_ntrs_defined_by_syntaxdefn xd);
    end;

    List.iter process_metavar xd.xd_mds;
    List.iter process_rule xd.xd_rs;

    List.iter
      (fun term ->
         let term_nt = mknt (Nt.Term_nt term) in
           add_prod term_nt (mkNT Nt.whitespace::string_to_terms term)
             (fun [x] -> x);
           if Auxl.last_char_isalphanum term then
             add_alphanum_restr term_nt)
      (Auxl.terminals_of_syntaxdefn xd);

    if !Global_option.do_pp_grammar then begin
      print_string "\n----------------- Grammar -----------------\n";
      List.iter
        (fun p -> 
           print_string (Nonterminal.to_string p.prod_left);
           print_string " ::= ";
           List.iter
             (function 
                  (T t) -> print_string (Terminal.to_string t ^ " ")
                | (NT nt) -> print_string (Nonterminal.to_string nt ^ " "))
             p.prod_right;
           print_string "(** #";
           print_string (string_of_int p.index);
           print_string (if p.reject then "reject" else " ");
           print_string (if p.transparent then "transparent" else " ");
           print_string "**) ";

             print_string "\n")
        !prods;
      print_string "\n----------------- Follow restrictions -----------------\n";
      print_string "nonterminal cannot be followed by character set\n\n";
      List.iter
        (function
           | (nt,Single follow, s) ->
               print_string (Nonterminal.to_string nt ^ " cannot be followed by " ^ s ^ "\n")
           | (nt, Multi _, s) -> 
               print_string (Nonterminal.to_string nt ^ " unsupported multi-term follow restriction\n"))
        !follows;
      print_string "\n----------------- Priorities -----------------\n";
      List.iter
        (function 
           | Right(x,y) -> Format.printf "Right #%d #%d\n" x y
           | Left(x,y) -> Format.printf "Left #%d #%d\n" x y
           | Greater(x,y) -> Format.printf "Greater #%d #%d\n" x y
           | Nonassoc(x,y) -> Format.printf "Nonassoc #%d #%d\n" x y)
        !priorities;


    end; 

    List.iter
      (fun (pn1, annot, pn2) ->
         let (i1, i1') = Hashtbl.find prodname_to_index2 pn1 in
         let (i2, i2') = Hashtbl.find prodname_to_index2 pn2 in
         let entry = 
           match annot with
               Types.LTEQ -> [Greater (i2, i1); Greater (i2', i1)]
             | Types.Left -> [Left (i1, i2); Left (i1', i2)]
             | Types.Right -> [Right (i1, i2); Right (i1', i2)]
             | Types.Non -> [Nonassoc (i1, i2); Nonassoc (i1', i2)]
         in
         let entry = 
           try
             let c1 = Hashtbl.find prodname_to_index1 pn1 in
             let c2 = Hashtbl.find prodname_to_index1 pn2 in
               match annot with
                   Types.LTEQ -> [Greater (c2, c1)]@entry
                 | Types.Left -> [Left (c1, c2)]@entry
                 | Types.Right -> [Right (c1, c2)]@entry
                 | Types.Non -> [Nonassoc (c1, c2)]@entry
           with Not_found -> entry
         in
           priorities := entry @ !priorities)
      xd.xd_pas.pa_data;

    let inits =
      List.fold_right
        (fun r acc -> 
           let s1 = mknt (Nt.Orig_nt (r.rule_ntr_name, false)) in
           if r.rule_meta || !fast_parse then
             s1 :: acc
           else
             s1 :: mknt (Nt.Orig_nt (r.rule_ntr_name, true)) :: acc)
        xd.xd_rs [] in

    if !Global_option.do_pp_grammar then begin
      print_string "\n----------------- Initial non-terminals -----------------\n";
      print_string "The non-terminals that we want parsers for\n";
      List.iter
        (fun init -> print_string (Nonterminal.to_string init ^ "\n"))
        inits
    end;

    (!prods, (List.map (fun (a,b,c) -> (a,b)) !follows), !priorities, inits, mknt);;
