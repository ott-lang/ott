(**************************************************************************)
(*                                   Ott                                  *)
(*                                                                        *)
(*        Peter Sewell, Computer Laboratory, University of Cambridge      *)
(*      Francesco Zappa Nardelli, Moscova project, INRIA Rocquencourt     *)
(*                                                                        *)
(*  Copyright 2005-2010                                                   *)
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

open Types

(* exceptions ************************************************************ *)

exception ThisCannotHappen

(* debug, warning and error report *************************************** *)

let mode_name m = match m with
  | Ascii _ -> "Ascii" 
  | Tex _ -> "Tex"
  | Isa _ -> "Isabelle"
  | Hol _ -> "HOL"
  | Lem _ -> "Lem"
  | Coq _ -> "Coq"
  | Twf _ -> "Twelf"
  | Caml _ -> "OCaml"
  | Lex _ -> "Lex"
  | Yacc _ -> "Yacc"

let debug_on = false

let debug s = if debug_on then begin print_string s; flush stdout end

let warning s = print_endline ("warning: " ^ s); flush stdout

let error s = print_endline ("error: " ^ s); flush stdout; exit 2

let int_error s = print_endline("internal: " ^ s); flush stdout; exit 2

let errorm m s = print_endline ("internal (" ^ mode_name m ^ "): " ^ s); flush stdout; exit 2


(* ***************** *)
(* naming convention *)
(* ***************** *)

(* let var_name m xd ntrp = ntrp *)

(* turned off version *)
(* let hide_isa_trailing_underscore m s = *)
(*   s *)

(* turned on version *)
let hide_isa_trailing_underscore m s =
  let debug = false in
  if debug then
    match m with
    | Isa _ ->
	if s="" then "E"  (* empty *)
	else if s.[String.length s - 1] = '_' then s^"U"   (* underscore *)
	else s^"N"  (* no underscore *)
    | _ -> s
  else
    match m with
    | Isa _ ->
	if s="" then ""  (* empty *)
	else if s.[String.length s - 1] = '_' then s^"XXX"   (* underscore *)
	else s  (* no underscore *)
    | _ -> s


let psuedo_terminal_of_prod_name pn = ":" ^ pn ^ ":"

let fake_concrete_ntr_of_ntr ntr = "concrete_"^ntr

let parse_as_concrete = ":concrete:"

let subst_name : string -> nontermroot -> string =
  fun s ntr -> s^"_"^ntr

let auxfn_name : auxfn -> nontermroot -> nontermroot -> string =
  fun s ntr typ -> 
(*    print_string ("==="^s^"=="^ntr^"=="^typ^"===\n");flush stdout; *)
(*     if ntr="av" then failwith "auxfn_name called with ntr=av";*)
    "aux_"^s^"_"^ntr^"_of_"^typ 

let fv_name : string -> nontermroot -> string =
  fun s ntr -> s^"_"^ntr

let context_name =
  fun ntr hole -> "appctx_"^ntr^"_"^hole

(* generate a predicate name for a sub-ntr *)
let pp_is : nontermroot -> string -> string = fun ntr typ -> "is_"^ntr^"_of_"^typ
let pp_is_list : nontermroot -> string -> string = fun ntr typ -> (pp_is ntr typ)^"_list"


(* **************************** *)
(* lexical character categories *)
(* **************************** *)
let isalphanum c = (c>='A' && c<= 'Z') || (c>='a' && c<= 'z') || (c>='0' && c<= '9')

let iswhitespace c = c=' ' || c = '\010' || c='\009' || c='\013' || c='\012'

let issuffixpunct c = c='\'' || c='_' (* || c='^' *)



(* simple auto-insert parentheses *)
let paren s =
  if String.contains s ' '
  then "("^s^")"
  else s

(* equality testing up-to location data ********************************** *)

let rec eq_raw_element (red,red') = 
  match red,red' with
  | Raw_ident (_,(_,ri)), Raw_ident (_,(_,ri')) -> 
      (* (List.for_all (fun (a,b) -> a = b) (List.combine rv rv')) && FZ *) (ri = ri')
  | Raw_option (_,res), Raw_option (_,res') -> eq_raw_elements res res'
  | Raw_list (_,res), Raw_list (_,res') -> eq_raw_elements res res'
  | Raw_nelist (_,res), Raw_nelist (_,res') ->  eq_raw_elements res res'
  | Raw_sugaroption (_,res), Raw_sugaroption (_,res') -> 
      eq_raw_element (res,res')
  | Raw_dots (_,n), Raw_dots (_,n') -> n=n'
  | _,_ -> false

and eq_raw_elements res res' = 
  try List.for_all eq_raw_element (List.combine res res') 
  with Invalid_argument _ -> false 

(* utilities *********************************************************** *)

exception TheOfNone

let the x =
  match x with
  | Some x -> x
  | None -> raise TheOfNone

let rec option_map f xs = 
  match xs with 
  | [] -> [] 
  | x::xs -> 
      ( match f x with 
      | None -> option_map f xs 
      | Some x -> x :: (option_map f xs) ) 

let rec list_concat (xs_sep : 'a list) (xss : 'a list list) : 'a list =
  match xss with 
  | [] -> []
  | [xs1]  -> xs1
  | xs1::xs2::xss' -> xs1 @ xs_sep @ list_concat xs_sep (xs2::xss')

let fold_left1 f lst = match lst with 
  | [] -> raise ThisCannotHappen
  | x::xs -> List.fold_left f x xs

let string_iter f s = 
  for i = 0 to String.length s - 1 do f (String.get s i) done

(* we use char lists a lot *)

let char_list_of_string s = 
  let n = String.length s in
  let rec f i = if i=n then [] else String.get s i :: f (i+1) in
  f 0

let string_of_char_list ts =
  let n = List.length ts in
  let s = String.create n in
  let rec f i ts = 
    match ts with 
    | [] -> ()
    | t::ts -> String.set s i t; f (i+1) ts
  in 
  f 0 ts; 
  s

(* tests to identify strings *)

exception Not_alpha

let is_char_alpha c =
  ((c >= 'A' && c <= 'Z')
 || (c >= '\192' && c <= '\214')
 || (c >= '\216' && c <= '\222')
 || (c >= 'a' && c <= 'z')
 || (c >= '\224' && c <= '\246')
 || (c >= '\248' && c <= '\254'))

let is_alpha s =  (* FZ this should work for iso-8859-1 *)
  try
    String.iter (fun c ->
      if not ((c >= 'A' && c <= 'Z')
	    || (c >= '\192' && c <= '\214')
	    || (c >= '\216' && c <= '\222')
	    || (c >= 'a' && c <= 'z')
	    || (c >= '\224' && c <= '\246')
	    || (c >= '\248' && c <= '\254')) then raise Not_alpha else ()) s;
    true
  with Not_alpha -> false

(* pretty-printing library definitions/lemmas ********************** *)

let add_to_lib r name def =
  let (s, l) = !r in
  if not (List.mem name l) then r := (s ^ def, name :: l)

(* manipulation of a syntaxdefn ************************************ *)

(* Similar function already in Grammar_pp
let pp_type_name m xd (s: string) = 
  let homname = match m with
    | Coq _ -> "coq"
    | Hol _ -> "hol"
    | Isa _ -> "isa"
    | Twf _ -> "twf"
    | Caml _ | Lex _ -> "ocaml"
    | Ascii _ | Tex _ -> errorm m "pp_type_name" in
  let rec search_hom homs = match homs with
    | [] -> None (* should never happen in type-checked specs *)
    | (hn,hs)::_ when hn = homname ->
        Some (String.concat " " (option_map (function Hom_string s -> Some s | _ -> None) hs))
    | _::homs -> search_hom homs in
  let rec search_ntr rs = match rs with
    | [] -> None 
    | r::rs when r.rule_ntr_name = s || List.exists (fun (s',_) -> s'=s) r.rule_ntr_names ->
      if r.rule_phantom then search_hom r.rule_homs
      else Some s 
    | _::rs -> search_ntr rs in
  let rec search_mvr mds = match mds with
    | [] -> None 
    | mvd::_ when mvd.mvd_name = s || List.exists (fun (s',_) -> s'=s) mvd.mvd_names ->
      if mvd.mvd_phantom then search_hom mvd.mvd_rep
      else Some s 
    | _::rs -> search_mvr rs in
  match search_mvr xd.xd_mds with Some s -> s | None -> 
  match search_ntr xd.xd_rs with Some s -> s | None ->
  s (* should never happen in type-checked specs *)
*)

let rec has_assoc (s:string) l = match l with
  | [] -> false
  | (t,_)::l -> s = t || has_assoc s l

let mvd_of_mvr (xd:syntaxdefn) (mvr:metavarroot) : metavardefn =
  List.find (fun mvd -> mvd.mvd_name = mvr) xd.xd_mds

let mvd_of_mvr_nonprimary (xd:syntaxdefn) (mvr:metavarroot) : metavardefn =
  List.find (fun mvd -> has_assoc mvr mvd.mvd_names) xd.xd_mds

let rule_of_ntr (xd:syntaxdefn) (ntr:nontermroot) : rule = 
  let rec search_ntr ntr rs = match rs with
    | [] -> raise Not_found
    | r::_ when r.rule_ntr_name = ntr -> r
    | _::rs -> search_ntr ntr rs in
  search_ntr ntr xd.xd_rs 

let rule_of_ntr_nonprimary (xd:syntaxdefn) (ntr:nontermroot) : rule = 
  let rec search_ntr2 ntr rs = match rs with
    | [] -> raise Not_found
    | r::_ when has_assoc ntr r.rule_ntr_names -> r
    | _::rs -> search_ntr2 ntr rs in
  search_ntr2 ntr xd.xd_rs 

let prod_of_prodname ?(warn=true) (xd:syntaxdefn) (pn:prodname) : prod = 
  let r = 
    try
      List.find 
	(fun r -> List.exists (fun p -> p.prod_name=pn) r.rule_ps)
	xd.xd_rs
    with Not_found -> if warn then warning ("internal: prod_of_prodname: searching pn = "^pn^"\n"); raise Not_found in
  List.find (fun p -> p.prod_name=pn) r.rule_ps
(*        let prod_of_prod_name : prodname -> prod  *)
(*            = fun prod_name' ->  *)
(*              let rec q prods =  *)
(*                match prods with *)
(*                  [] -> raise Not_found *)
(*                | prod::prods' ->  *)
(*                    if prod.prod_name=prod_name' then prod else q prods' in *)
(*              let rec p rules =  *)
(*                match rules with  *)
(*                  [] -> raise Not_found *)
(*                | r::rules' ->  *)
(*                    try q (r.rule_ps) with Not_found -> p rules' in *)
(*              p (List.concat l.rs) in *)


(* auxiliary to promote a primary ntr to its super-ntr, if any *)
let promote_ntr xd ntrp = 
  (* prerr_string (""^ntrp^"\n");flush stderr; *)
  let d = List.map (function sr -> sr.sr_lower,sr.sr_top) xd.xd_srs in
  try
    List.assoc ntrp d 
  with Not_found ->
    ntrp

let promote_ntr' xd ntrp = 
  (* prerr_string (""^ntrp^"\n");flush stderr; *)
  let d = List.map (function sr -> sr.sr_lower,(sr.sr_upper,sr.sr_top)) xd.xd_srs in
    List.assoc ntrp d 

let promote_ntmvr xd ntmvr = 
  match ntmvr with
  | Ntr ntrp -> (* print_endline ("promoting: " ^ ntrp); *) 
      Ntr (promote_ntr xd ntrp)
  | Mvr mvr -> Mvr mvr

(* extract the set of nonterminalroots defined by a syntax (including synonyms)
   reverse-sorted *)
let all_ntrs_defined_by_syntaxdefn xd = 
  List.sort 
    (function a -> function b -> compare b a) 
    (List.concat (List.map (function r -> List.map fst r.rule_ntr_names) xd.xd_rs )) 

(* extract the set of metavarroots defined by a syntax (including synonms), 
   reverse-sorted *)
let all_mvrs_defined_by_syntaxdefn xd =  
  List.sort 
    (function a -> function b -> compare b a) 
    (List.concat (List.map (function mvd -> List.map fst mvd.mvd_names) xd.xd_mds ))
let all_nonindex_mvrs_defined_by_syntaxdefn xd =  
  List.sort 
    (function a -> function b -> compare b a) 
    (List.concat 
       (List.map (function mvd -> List.map fst mvd.mvd_names) 
          (List.filter (function md->not md.mvd_indexvar) xd.xd_mds )))
let all_index_mvrs_defined_by_syntaxdefn xd =  
  List.sort 
    (function a -> function b -> compare b a) 
    (List.concat 
       (List.map (function mvd -> List.map fst mvd.mvd_names) 
          (List.filter (function md-> md.mvd_indexvar) xd.xd_mds )))

(* extract the set of prodnames defined by a syntax *)
let all_prodnames_defined_by_syntaxdefn xd = 
  List.sort 
    (function a -> function b -> compare b a) 
    (List.concat (List.map (function r -> List.map (function p->p.prod_name) r.rule_ps) xd.xd_rs ))
  

(* auxiliary to find the primary ntrs used in an element, prod, and rule *)
let rec primary_ntrs_used_in_element xd promote e = 
  match e with
  | Lang_nonterm (ntr_primary,nt_as_written) -> 
      NtrSet.singleton 
        (if promote 
        then promote_ntr xd ntr_primary
        else ntr_primary)
  | Lang_metavar _ -> NtrSet.empty
  | Lang_terminal _ -> NtrSet.empty
  | Lang_option es -> ntrlistunion (List.map (primary_ntrs_used_in_element xd promote) es)
  | Lang_sugaroption  es -> NtrSet.empty
  | Lang_list elb -> ntrlistunion(List.map (primary_ntrs_used_in_element xd promote) elb.elb_es)

let primary_ntrs_used_in_hom xd m promote homs =
  try
    let hom = List.assoc m homs in 
    let defined_ntrs = all_ntrs_defined_by_syntaxdefn xd in
    ntrsetoflist
      (List.concat
	 (List.map 
	    (fun hse ->
	      ( match hse with
	      | Hom_index _ | Hom_terminal _ -> []
	      | Hom_string s -> 
		  let strs = Str.split (Str.regexp "[ \t]+") s in
		  let ntrs_hom = List.filter (fun st -> List.mem st defined_ntrs) strs in
		  if promote 
		  then List.map (promote_ntr xd) ntrs_hom
		  else ntrs_hom ))
	    hom ))
  with Not_found -> NtrSet.empty

let primary_ntrs_used_in_prod xd promote p = 
  ntrlistunion (List.map (primary_ntrs_used_in_element xd promote) p.prod_es) 
  
let primary_ntrs_used_in_rule xd scan_meta scan_homs promote r = 
  let prods = 
    if scan_meta 
    then r.rule_ps
    else List.filter (fun p -> not p.prod_meta) r.rule_ps in
  let in_rule = ntrlistunion (List.map (primary_ntrs_used_in_prod xd promote) prods) in
  match scan_homs with
  | None -> in_rule
  | Some m -> NtrSet.union in_rule (primary_ntrs_used_in_hom xd m promote r.rule_homs)

  

(* auxiliary to find the nts used in an element, prod, and rule *)
let rec nts_used_in_element pe e = match e with
| Lang_nonterm (ntr_primary,nt_as_written) -> 
    [(ntr_primary,nt_as_written,pe)]
| Lang_metavar _ -> []
| Lang_terminal _ -> []
| Lang_option es -> List.flatten (List.map (nts_used_in_element pe) es)
| Lang_sugaroption  es -> []
| Lang_list elb -> List.flatten (List.map (nts_used_in_element (elb.elb_boundo::pe)) elb.elb_es) 

let nts_list_used_in_es es = List.flatten (List.map (nts_used_in_element []) es) 

let nts_set_used_in_es es = ntsetoflist (nts_list_used_in_es es)

let nts_used_in_prod p = nts_set_used_in_es p.prod_es

let nts_used_in_rule r = ntlistunion (List.map nts_used_in_prod r.rule_ps) 

(* auxiliary to find the primary mvrs used in an element, prod, and rule *)
let rec primary_mvrs_used_in_element e = match e with
| Lang_nonterm _ -> MvrSet.empty
| Lang_metavar (mvr_primary,mv_as_written) -> 
    MvrSet.singleton mvr_primary
| Lang_terminal _ -> MvrSet.empty
| Lang_option es -> mvrlistunion (List.map primary_mvrs_used_in_element es)
| Lang_sugaroption  es -> MvrSet.empty
| Lang_list elb -> mvrlistunion (List.map primary_mvrs_used_in_element elb.elb_es) 

let primary_mvrs_used_in_hom xd m homs =
  try
    let hom = List.assoc m homs in 
    let defined_mvrs = all_mvrs_defined_by_syntaxdefn xd in
    mvrsetoflist
      (List.concat
	 (List.map 
	    (fun hse ->
	      ( match hse with
	      | Hom_index _ | Hom_terminal _ -> []
	      | Hom_string s -> 
		  let strs = Str.split (Str.regexp "[ \t]+") s in
		  List.filter (fun st -> List.mem st defined_mvrs) strs ))
	    hom ))
  with Not_found -> MvrSet.empty

let primary_mvrs_used_in_prod p = 
  mvrlistunion (List.map primary_mvrs_used_in_element p.prod_es) 

let primary_mvrs_used_in_rule xd scan_meta scan_homs r = 
  let rules = 
    if scan_meta 
    then r.rule_ps
    else List.filter (fun p -> not p.prod_meta) r.rule_ps in
  let in_rule = mvrlistunion (List.map primary_mvrs_used_in_prod rules) in
  match scan_homs with
  | None -> in_rule
  | Some m -> MvrSet.union in_rule (primary_mvrs_used_in_hom xd m r.rule_homs)
  
(* auxiliary to find the mvs used in an element, prod, and rule *)
let rec mvs_used_in_element pe e = match e with
| Lang_nonterm _ -> []
| Lang_metavar (mvr_primary,mv_as_written) -> 
    [(mvr_primary,mv_as_written,pe)]
| Lang_terminal _ -> []
| Lang_option es -> List.flatten (List.map (mvs_used_in_element pe) es)
| Lang_sugaroption  es -> []
| Lang_list elb -> List.flatten (List.map (mvs_used_in_element (elb.elb_boundo::pe)) elb.elb_es) 

let mvs_list_used_in_es es = List.flatten (List.map (mvs_used_in_element []) es) 

let mvs_set_used_in_es es = mvsetoflist (mvs_list_used_in_es es)

let mvs_used_in_prod p = mvs_set_used_in_es p.prod_es

let mvs_used_in_rule r = mvlistunion (List.map mvs_used_in_prod r.rule_ps) 

(* auxiliary to find the terminals used in a systemdefn, reverse-sorted *)
(* including pseudo-terminals :Expr_tuple: made up from production names *)
(* Expr_tuple *)
let rec terminals_of_element e = match e with
  Lang_nonterm (_,_) -> TerminalSet.empty
| Lang_metavar (_,_) -> TerminalSet.empty
| Lang_terminal tm -> TerminalSet.singleton tm
| Lang_option es -> terminallistunion (List.map terminals_of_element es)
| Lang_sugaroption tm -> TerminalSet.singleton tm
| Lang_list elb -> 
    terminallistunion 
      ((match elb.elb_tmo with 
      | None -> TerminalSet.empty 
      | Some tm -> TerminalSet.singleton tm)
       ::(List.map terminals_of_element elb.elb_es) )
let terminals_of_prod p = 
  let ts = List.map terminals_of_element p.prod_es in
  (*let ts = TerminalSet.singleton(psuedo_terminal_of_prod_name p.prod_name) :: ts in*)
  terminallistunion ts
let terminals_of_rule r = terminallistunion 
    (List.map terminals_of_prod r.rule_ps) 
let terminals_of_syntaxdefn0 xd =  (* as a set *)
  terminallistunion 
    (* ((terminalsetoflist extra_pseudo_terminals)  *)
      (* ::*)  (List.map terminals_of_rule xd.xd_rs)
let terminals_of_syntaxdefn xd =  (* as a reverse-ordered list *)
  List.rev_append (TerminalSet.elements (terminals_of_syntaxdefn0 xd)) []
let terminals_of_systemdefn sd = terminals_of_syntaxdefn sd.syntax

let last_char_isalphanum s = s="" || (isalphanum s.[String.length s -1])

let terminals_of_syntaxdefn_alpha xd = 
  List.filter last_char_isalphanum (terminals_of_syntaxdefn xd)

let terminals_of_syntaxdefn_nonalpha xd = 
  List.filter (function c -> not (last_char_isalphanum c)) (terminals_of_syntaxdefn xd)

    
(* auxiliaries to find the synonyms of a primary mvr or ntr *)
let mvr_synonyms : syntaxdefn -> metavarroot -> metavarroot list = 
  function xd -> 
    let assoc = List.map (function mvd -> (mvd.mvd_name, List.map fst mvd.mvd_names)) xd.xd_mds in
    function mvrp -> List.assoc mvrp assoc 

let ntr_synonyms : syntaxdefn -> nontermroot -> nontermroot list = 
  function xd -> 
    let assoc = List.map (function r -> (r.rule_ntr_name, List.map fst r.rule_ntr_names)) xd.xd_rs in
    function ntrp -> List.assoc ntrp assoc 

let all_indexvar_synonyms : syntaxdefn -> metavarroot list = 
  function xd -> 
    List.flatten (option_map (function mvd -> if mvd.mvd_indexvar then Some(List.map fst mvd.mvd_names) else None) xd.xd_mds)

(* auxiliaries to take an ntr or mvr and find its primary one *)
let primary_ntr_of_ntr : syntaxdefn -> nontermroot -> nontermroot =
  function xd ->
    let assoc = List.map (function r -> (r.rule_ntr_name, List.map fst r.rule_ntr_names)) xd.xd_rs in
    (* and one in the other direction *)
    let assoc_op : (nontermroot * nontermroot) list 
        = List.concat 
        (List.map 
           (function (ntrp,ntrs)->List.map (function ntr'->(ntr',ntrp)) ntrs) 
           assoc) in
    function ntr -> List.assoc ntr assoc_op 

let primary_mvr_of_mvr : syntaxdefn -> metavarroot -> metavarroot =
  function xd ->
    let assoc = List.map (function mvd -> (mvd.mvd_name, List.map fst mvd.mvd_names)) xd.xd_mds in
    (* and one in the other direction *)
    let assoc_op : (metavarroot * metavarroot) list
        = List.concat
        (List.map
           (function (mvrp,mvrs)->List.map (function mvr'->(mvr',mvrp)) mvrs)
           assoc) in
    function mvr -> List.assoc mvr assoc_op

let primary_nt_or_mv_of_nt_or_mv : syntaxdefn -> nt_or_mv_root -> nt_or_mv_root =
  fun xd ntmvr ->
    match ntmvr with
    | Ntr ntr -> Ntr (primary_ntr_of_ntr xd ntr)
    | Mvr mvr -> Mvr (primary_mvr_of_mvr xd mvr)
      
(* auxiliary to take a primary ntr and give all its proper sub- (primary) ntrs *)
(* TODO WHAT EXACTLY IS THIS SUPPOSED TO DO??? *)
let ntr_proper_subs : syntaxdefn -> nontermroot -> nontermroot list = 
  fun xd ntrp -> 
    try List.assoc ntrp (xd.xd_srd.srd_proper_subntr_data) with Not_found -> []
(*     let x1 = List.map (function r -> r.rule_ntr_name) xd.xd_rs in *)
(*     let x2 = List.map (function sr -> (sr.sr_upper,sr.sr_lower)) xd.xd_srs in *)
(*     let x3 = List.map (function ntr -> try (ntr,[List.assoc ntr x2]) with Not_found -> (ntr,[])) x1 in *)
(*     function ntrp -> List.assoc ntrp x3  *)

let hom_name_for_pp_mode m 
    = match m with
    | Ascii _ -> "ascii" 
    | Tex _ -> "tex"
    | Isa _ -> "isa"
    | Hol _ -> "hol"
    | Lem _ -> "lem"
    | Coq _ -> "coq"
    | Twf _ -> "twf"
    | Caml _ -> "ocaml"
    | Lex _ -> "lex"
    | Yacc _ -> "yacc"

(* select dependencies *)

let select_dep_ts m xddep =
  try ( List.assoc (hom_name_for_pp_mode m) xddep ).xd_dep_ts
  with Not_found -> int_error "cannot select dependencies\n"

let select_dep_graph m xddep =
  try ( List.assoc (hom_name_for_pp_mode m) xddep ).xd_dep_graph
  with Not_found -> int_error "cannot select dependencies\n"

let select_dep_graph_nontran m xddep =
  try ( List.assoc (hom_name_for_pp_mode m) xddep ).xd_dep_graph_nontran
  with Not_found -> int_error "cannot select dependencies\n"

let hom_spec_for_hom_name hn homs = 
  try Some (List.assoc hn homs)
  with Not_found -> None

let hom_spec_for_pp_mode m homs = 
  hom_spec_for_hom_name (hom_name_for_pp_mode m) homs

let loc_of_raw_element e = 
  match e with
  | Raw_ident (l,_) 
  | Raw_option (l,_) 
  | Raw_list (l,_) 
  | Raw_nelist (l,_) 
  | Raw_sugaroption (l,_) 
  | Raw_dots (l,_) 
  | Raw_comp (l,_,_,_)
    -> l

let loc_of_raw_mse raw_mse = 
  match raw_mse with
  | Raw_MVorNTExp (l,_)
  | Raw_MVorNTListExp_dotform (l,_,_,_)
  | Raw_MVorNTListExp_comp (l,_,_)
  | Raw_Aux (l,_,_)
  | Raw_AuxList_dotform (l,_,_,_,_)
  | Raw_AuxList_comp (l,_,_,_)
  | Raw_Union (l,_,_)
  | Raw_Empty (l)
    -> l

let loc_of_raw_bindspec bs = 
  match bs with
  | Raw_Bind (l,_,_)
  | Raw_AuxFnDef(l,_,_)
  | Raw_NamesEqual(l,_,_)
  | Raw_NamesDistinct(l,_,_)
  | Raw_AllNamesDistinct(l,_)
    -> l

let loc_of_raw_subrule sr =
  sr.raw_sr_loc

let loc_of_raw_contextrule cr =
  cr.raw_cr_loc

let loc_of_raw_subst sb =
  sb.raw_sb_loc

let loc_of_raw_freevar fv =
  fv.raw_fv_loc

let loc_of_raw_parsing_annotation pa =
  pa.raw_pa_loc

let loc_of_mytoken t = 
  match t with
  | Tok_nonterm(l,_)
  | Tok_metavar(l,_)
(*   | Tok_terminal(l,_) *)
(*   | Tok_dots(l,_) *)
(*   | Tok_otherident(l,_) *)
(*   | Tok_listform(l,_) *)
    -> l

(* *) 
let rec remove_duplicates l =
  match l with
  | x::xs -> 
      if (List.mem x xs) then remove_duplicates xs else x::(remove_duplicates xs)
  | [] -> []

let rec remove_duplicates2 f l =
  match l with
  | x::xs -> 
      if (List.exists (f x) xs) then remove_duplicates xs else x::(remove_duplicates xs)
  | [] -> []
(* PS: the above looks suspicious - should the recursive calls be to remove_duplicates2 f ?*)

let rec find_first_duplicate l =
  match l with
  | x::xs -> 
      if (List.mem x xs) then Some x else find_first_duplicate xs
  | [] -> None

let rec find_first_duplicate2 f l =
  match l with
  | x::xs -> 
      if (List.exists (f x) xs) then Some x else find_first_duplicate xs
  | [] -> None

let rec setlist_union xs ys = 
  ( match xs with
  | [] -> ys
  | x::xs -> 
      if List.mem x ys then setlist_union xs ys 
      else x::setlist_union xs ys ) 
    
let rec setlist_list_union xss = 
  ( match xss with
  | [] -> []
  | xs::xss -> setlist_union xs (setlist_list_union xss) ) 



let result_type_of_mse xd mse : nt_or_mv_root = 
  let rec f mse = match mse with
  | MetaVarExp (mv)  | MetaVarListExp (mv,_) ->
      Some(Mvr(primary_mvr_of_mvr xd (fst mv)))
  | NonTermExp (nt) | NonTermListExp (nt,_) ->
      Some(Ntr(primary_ntr_of_ntr xd (fst nt)))
  | Aux (f,(ntr',suffix)) | AuxList (f,(ntr',suffix),_) ->
      Some(snd (List.assoc f xd.xd_axs))
  | Union(mse,mse') -> (match f mse, f mse' with
    | Some ntmv, None | None,Some ntmv -> Some ntmv
    | Some ntmv, Some ntmv' when ntmv=ntmv' -> Some ntmv
    | None, None -> None
    | _ -> failwith "result_type_of_mse applied to an mse with inconsistent type constraints")
  | Empty -> None in
  match f mse with
  | Some ntmv -> ntmv
  | None -> failwith "result_type_of_mse applied to an mse with unconstained type"

let min_length_of_stli stli = match stli with
  | Stli_single (_,_) -> 1
  | Stli_listform stlb -> match stlb.stl_bound with
    | Bound_dotform bd -> 2 (* bd.bd_length  *)
    | Bound_comp _ -> 2 (* 0 *)
    | Bound_comp_u _ -> 2 (* 0 *)
    | Bound_comp_lu bclu -> 2 (* bclu.bclu_length *)

let min_length_of_stlis stlis
    = List.fold_left (+) 0 (List.map min_length_of_stli stlis)


let string_remove_suffix s s' =
  let l = String.length s in
  let l' = String.length s' in
  if l<(String.length s') then None
  else
    let s1=String.sub s 0 (l-l') in
    let s2=String.sub s (l-l') l' in
    if s2<>s' then 
      None 
    else
      Some s1

let string_is_prefix s s' =
  let l = String.length s in
  let l' = String.length s' in
  if l'<l then false
  else
    (s = String.sub s' 0 l)



(* list functions *)

let rec transpose (m: 'a list list) : 'a list list =
  match m with
  | [] -> []
  | fst::_ ->  
      List.fold_left
	(fun r xs -> List.map2 (fun x r -> x::r) xs r)
	(List.map (fun _ -> []) fst)
	(List.rev m)

let split3 (l : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list =
  let rec internal l ba bb bc =
    match l with
    | [] -> (List.rev ba, List.rev bb, List.rev bc)
    | (a,b,c)::tl -> internal tl (a::ba) (b::bb) (c::bc)
  in internal l [] [] []

let big_line_comment m s = 
  match m with
  | Coq _ | Hol _ | Lem _ | Isa _ | Caml _ -> "(** "^s^" *)\n"
  | Twf _ -> "%%% "^s^" %%%\n\n"
  | Tex _ -> "% "^s^"\n"
  | Yacc _ | Lex _ | Ascii _ -> errorm m "big_line_comment"

(* print only if not empty *)

let rec print_with_comment m s0 c s =
  match s with
  | "" -> ""
  | _ -> s0 ^ big_line_comment m c ^ s




(* extract nonterms from a symterm - used when building types in coq list treatment *)

(* let rec extract_nonterms s = *)
(*   match s with  *)
(*   | [] -> [] *)
(*   | (Ste_st (_,St_nonterm (_,nt,_)))::t -> nt :: (extract_nonterms t) *)
(*   | h::t ->  *)
(*       warning  *)
(*         ("internal: extract_nonterms case failure\n " *)
(*          ^ (Grammar_pp.pp_plain_symterm_element h) ^ "***\n\n"); [] *)



(* collect all the nonterms/metavars in a symterm *)
let rec nts_of_symterm st 
: nonterm list = 
  match st with
  | St_node (_,stnb) -> nts_of_symterm_node_body stnb
  | St_nonterm (_,_,nt) -> [ nt ]
  | St_nontermsub (_,ntrl,ntrt,nt) -> [nt]
  | St_uninterpreted (_,_)-> []
and nts_of_symterm_element ste =
  match ste with
  | Ste_st (_,st) -> nts_of_symterm st
  | Ste_metavar (_,_,mv) -> [ ]
  | Ste_var _ -> []
  | Ste_list (_,stlis)  -> 
      List.concat (List.map nts_of_symterm_list_item stlis)
and nts_of_symterm_list_item stli = 
  match stli with
  | Stli_single(_,stes) ->
      List.concat (List.map nts_of_symterm_element stes)
  | Stli_listform stlb -> 
      nts_of_symterm_list_body stlb
and nts_of_symterm_node_body stnb = 
  List.concat (List.map nts_of_symterm_element stnb.st_es)
and nts_of_symterm_list_body stlb =    
  List.concat (List.map nts_of_symterm_element stlb.stl_elements)
and nts_of_symterms sts =
  List.concat (List.map nts_of_symterm sts)

let rec mvs_of_symterm st 
: metavar list = 
  match st with
  | St_node (_,stnb) -> mvs_of_symterm_node_body stnb
  | St_nonterm (_,_,nt) -> [ ]
  | St_nontermsub (_,ntrl,ntrt,nt) -> []
  | St_uninterpreted (_,_)-> []
and mvs_of_symterm_element ste =
  match ste with
  | Ste_st (_,st) -> mvs_of_symterm st
  | Ste_metavar (_,_,mv) -> [ mv ]
  | Ste_var _ -> []
  | Ste_list (_,stlis)  -> 
      List.concat (List.map mvs_of_symterm_list_item stlis)
and mvs_of_symterm_list_item stli = 
  match stli with
  | Stli_single(_,stes) ->
      List.concat (List.map mvs_of_symterm_element stes)
  | Stli_listform stlb -> 
      mvs_of_symterm_list_body stlb
and mvs_of_symterm_node_body stnb = 
  List.concat (List.map mvs_of_symterm_element stnb.st_es)
and mvs_of_symterm_list_body stlb =    
  List.concat (List.map mvs_of_symterm_element stlb.stl_elements)
and mvs_of_symterms sts =
  List.concat (List.map mvs_of_symterm sts)

let rec ntmvr_of_symterm st 
: nt_or_mv_root list = 
  match st with
  | St_node (_,stnb) -> ntmvr_of_symterm_node_body stnb
  | St_nonterm (_,_,(ntr,_)) -> [ Ntr ntr ]
  | St_nontermsub (_,ntrl,ntrt,(ntr,_)) -> [Ntr ntr]
  | St_uninterpreted (_,_)-> []
and ntmvr_of_symterm_element ste =
  match ste with
  | Ste_st (_,st) -> ntmvr_of_symterm st
  | Ste_metavar (_,_,(mvr,_)) -> [ Mvr mvr ]
  | Ste_var _ -> []
  | Ste_list (_,stlis)  -> 
      List.concat (List.map ntmvr_of_symterm_list_item stlis)
and ntmvr_of_symterm_list_item stli = 
  match stli with
  | Stli_single(_,stes) ->
      List.concat (List.map ntmvr_of_symterm_element stes)
  | Stli_listform stlb -> 
      ntmvr_of_symterm_list_body stlb
and ntmvr_of_symterm_node_body stnb = 
  List.concat (List.map ntmvr_of_symterm_element stnb.st_es)
and ntmvr_of_symterm_list_body stlb =    
  List.concat (List.map ntmvr_of_symterm_element stlb.stl_elements)
and ntmvr_of_symterms sts =
  List.concat (List.map ntmvr_of_symterm sts)

(** ******************************** *)
(** ******************************** *)
(** freshening                       *)
(** ******************************** *)
(** ******************************** *)

let fresh_suffix : suffix list -> suffix -> suffix = 
  fun suffs suff0 ->
    let suffix_nums suffs = 
      option_map 
        (function suffi -> 
          match suffi with 
            Si_num n -> Some(int_of_string n) 
          | _ -> None) 
        (List.concat suffs) in
    let rec next ns n = if not (List.mem n ns) then n else next ns (n+1) in
    (* TODO: do something better than this to avoid the less-trivial clashes *)
    let index_suffis suff = List.filter (function suffi -> match suffi with Si_index _ -> true | _ -> false) suff in
    let max_non_primes_suffix_length suffs = 
      List.fold_left max 0 (List.map (function suff -> if List.exists
          (fun suffi -> match suffi with Si_punct "'" -> true | _ -> false) suff then 0 else List.length suff) suffs) in
    let rec initial_underscores n = if n=0 then [] else (Si_punct "_")::initial_underscores (n-1) in
    initial_underscores (max_non_primes_suffix_length suffs) 
    @ [Si_num (string_of_int (next (suffix_nums suffs) 5 (* 0 *)))] @ index_suffis suff0



(* find a suffix for a nontermroot that is distinct from all the
suffixes for that root that occur in an NtSet, and similarly for a
metavarroot *)

(* let fresh_ntr_suffix : NtSet.t -> nontermroot -> suffix = *)
(*   fun nts ntr0 ->  *)
(*     let suffs : suffix list =  *)
(*       NtSet.fold  *)
(*         (function (ntrp,(ntr,suff),pe) ->  *)
(*           function suffs' ->  *)
(*             if ntr=ntr0 then suff::suffs' else suffs')  *)
(*         nts  *)
(*         [] in *)
(*     fresh_suffix suffs  *)

(* let fresh_mvr_suffix : MvSet.t -> metavarroot -> suffix = *)
(*   fun mvs mvr0 ->  *)
(*     let suffs : suffix list =  *)
(*       MvSet.fold  *)
(*         (function (mvrp,(mvr,suff),pe) ->  *)
(*           function suffs' ->  *)
(*             if mvr=mvr0 then suff::suffs' else suffs')  *)
(*         mvs *)
(*         [] in *)
(*     fresh_suffix suffs  *)

let fresh_nt : nonterm list -> nonterm -> nonterm =
  fun nts (ntr0,suff0) -> 
    let suffs : suffix list = 
      List.fold_right
        (function (ntr,suff) -> 
          function suffs' -> 
            if ntr=ntr0 then suff::suffs' else suffs') 
        nts 
        [] in
    let fresh_suff = fresh_suffix suffs suff0 in
    (ntr0,fresh_suff)

let fresh_mv : metavar list -> metavar -> metavar =
  fun mvs (mvr0,suff0) -> 
    let suffs : suffix list = 
      List.fold_right
        (function (mvr,suff) -> 
          function suffs' -> 
            if mvr=mvr0 then suff::suffs' else suffs') 
        mvs
        [] in
    let fresh_suff = fresh_suffix suffs suff0 in
    (mvr0,fresh_suff)


(** ******************************** *)
(** ******************************** *)
(** nt and mv renaming               *)
(** ******************************** *)
(** ******************************** *)

(* to apply a simultaneous renaming to the nonterms (and roots), metavars (and roots) and prodnames of a system *)
(* NB: the renaming should be consistent in many ways... *)

let rename_metavarroot (map_mvr,map_mv,map_ntr,map_nt,map_pn) mvr = 
  try List.assoc mvr map_mvr with Not_found -> mvr
let rename_metavar (map_mvr,map_mv,map_ntr,map_nt,map_pn) (mvr,suff) =
  let mv = (mvr,suff) in
  match map_mv with
  | Some map_mv -> (try List.assoc mv map_mv with Not_found -> mv)
  | None -> (try (List.assoc mvr map_mvr, suff) with Not_found -> mv)
let rename_nontermroot (map_mvr,map_mv,map_ntr,map_nt,map_pn) ntr = 
  try List.assoc ntr map_ntr with Not_found -> ntr
let rename_nonterm (map_mvr,map_mv,map_ntr,map_nt,map_pn) (ntr,suff) = 
  let nt = (ntr,suff) in
  match map_nt with
  | Some map_nt -> (try List.assoc nt map_nt with Not_found -> nt)
  | None -> (try (List.assoc ntr map_ntr, suff) with Not_found -> nt)
let rename_prodname (map_mvr,map_mv,map_ntr,map_nt,map_pn) pn = 
  try List.assoc pn map_pn with Not_found -> pn

let rec rename_nt_or_mv_root map ntmvr = match ntmvr with
| Mvr mvr -> Mvr (rename_metavarroot map mvr)
| Ntr ntr -> Ntr (rename_nontermroot map ntr)

and rename_nt_or_mv map (ntmv,suff) = 
  (rename_nt_or_mv_root map ntmv,suff)

and rename_metavardefn map mvd =
  { mvd_name = rename_metavarroot map mvd.mvd_name;
    mvd_names = List.map (function mvr,homs -> rename_metavarroot map mvr,homs) mvd.mvd_names;
    mvd_rep = mvd.mvd_rep;
    mvd_indexvar = mvd.mvd_indexvar;
    mvd_locally_nameless = mvd.mvd_locally_nameless;
    mvd_phantom = mvd.mvd_phantom;
    mvd_loc = mvd.mvd_loc }

and rename_suffix map suff = List.map (rename_suffix_item map) suff

and rename_suffix_item map suffi = match suffi with
| Si_var (suffv,n) -> Si_var(rename_metavarroot map suffv,n)
| _ -> suffi
    
and rename_bound map b = match b with
| Bound_dotform bd -> Bound_dotform { bd with
                        bd_lower = rename_suffix_item map bd.bd_lower;
                        bd_upper = rename_suffix_item map bd.bd_upper }
| Bound_comp bc -> Bound_comp { (* bc with *)
                     bc_variable = rename_metavarroot map bc.bc_variable}
| Bound_comp_u bcu -> Bound_comp_u { (* bcu with *)
                        bcu_variable = rename_metavarroot map bcu.bcu_variable;
                        bcu_upper = rename_suffix_item map bcu.bcu_upper }
| Bound_comp_lu bclu -> Bound_comp_lu { bclu with
                          bclu_variable = rename_metavarroot map bclu.bclu_variable;
                          bclu_lower = rename_suffix_item map bclu.bclu_lower;
                          bclu_upper = rename_suffix_item map bclu.bclu_upper }
                        
and rename_bindspec map bs = match bs with
| Bind(mse,nt)->Bind(rename_mse map mse,rename_nonterm map nt)
| AuxFnDef(auxfn,mse)->AuxFnDef(auxfn, rename_mse map mse)
| NamesEqual(mse,mse')->NamesEqual(rename_mse map mse,rename_mse map mse')
| NamesDistinct(mse,mse')->NamesDistinct(rename_mse map mse,rename_mse map mse')
| AllNamesDistinct(mse)->AllNamesDistinct(rename_mse map mse)

and rename_mse map mse = match mse with
| MetaVarExp(mv)->MetaVarExp(rename_metavar map mv)
| NonTermExp(nt)->NonTermExp(rename_nonterm map nt)
| MetaVarListExp(mv,b)->MetaVarListExp(rename_metavar map mv,rename_bound map b)
| NonTermListExp(nt,b)->NonTermListExp(rename_nonterm map nt,rename_bound map b)
| Aux(f,nt)->Aux(f,rename_nonterm map nt)
| AuxList(f,nt,b)->AuxList(f,rename_nonterm map nt,rename_bound map b)
| Union(mse,mse')->Union(rename_mse map mse,rename_mse map mse')
| Empty->Empty
      
and rename_auxfn_type map (ntrs,ntmvr) = List.map (rename_nontermroot map) ntrs,rename_nt_or_mv_root map ntmvr

and rename_element map e = match e with
| Lang_nonterm(ntr,nt)->Lang_nonterm(rename_nontermroot map ntr,rename_nonterm map nt)
| Lang_metavar(mvr,mv)->Lang_metavar(rename_metavarroot map mvr,rename_metavar map mv)
| Lang_terminal(tm)->Lang_terminal(tm)
| Lang_option(es)->Lang_option(List.map (rename_element map) es)
| Lang_sugaroption(tm)->Lang_sugaroption(tm)
| Lang_list(elb)->Lang_list(rename_element_list_body map elb)

and rename_element_list_body map elb =
  { elb_boundo = (match elb.elb_boundo with None->None | Some b -> Some (rename_bound map b));
    elb_tmo = elb.elb_tmo;
    elb_es = List.map (rename_element map) elb.elb_es }

and rename_prod map p = 
  { p with
    prod_name = rename_prodname map p.prod_name;
    prod_es = List.map (rename_element map) p.prod_es;
    prod_bs = List.map (rename_bindspec map) p.prod_bs; }

and rename_rule map r = 
  { r with
    rule_ntr_name = rename_nontermroot map r.rule_ntr_name;
    rule_ntr_names = List.map (function ntr,homs -> rename_nontermroot map ntr,homs) r.rule_ntr_names;
    rule_ps = List.map (rename_prod map) r.rule_ps }

and rename_subrule map sr = 
  { sr with
    sr_lower = rename_nontermroot map sr.sr_lower;
    sr_upper = rename_nontermroot map sr.sr_upper;
    sr_top = rename_nontermroot map sr.sr_top }

and rename_proper_subntr_data map psd =
  List.map (function ntr,ntrs -> (rename_nontermroot map ntr,List.map (rename_nontermroot map) ntrs)) psd

and rename_subrule_graph map sg =
  List.map (function ntr,ntr' -> (rename_nontermroot map ntr,rename_nontermroot map ntr')) sg

and rename_subrule_pn_promotion map spp =
  List.map (function ntr,(ntr',pps) -> (rename_nontermroot map ntr,(rename_nontermroot map ntr',List.map (function pn,pn'->rename_prodname map pn,rename_prodname map pn') pps))) spp

and rename_subrule_data map srd =
  {srd_proper_subntr_data = rename_proper_subntr_data map srd.srd_proper_subntr_data;
   srd_subrule_graph = rename_subrule_graph map srd.srd_subrule_graph;
   srd_subrule_pn_promotion = rename_subrule_pn_promotion map srd.srd_subrule_pn_promotion }

and rename_contextrule map cr = 
  { cr with
    cr_ntr = rename_nontermroot map cr.cr_ntr;
    cr_target = rename_nontermroot map cr.cr_target;
    cr_hole = rename_nontermroot map cr.cr_hole }

and rename_subst map subst = 
  { subst with
    sb_this = rename_nontermroot map subst.sb_this;
    sb_that = rename_nt_or_mv_root map subst.sb_that; }

and rename_freevar map fv =
  { fv with
    fv_that = rename_nt_or_mv_root map fv.fv_that; }

and rename_parsing_annotations map pas =
  { pa_data = List.map (fun (ntr1,pa_type,ntr2)-> 
      (rename_nontermroot map ntr1,pa_type,rename_nontermroot map ntr2)) pas.pa_data }

and rename_dependencies map xddep =
  { xd_dep_ts = List.map (List.map (rename_nt_or_mv_root map)) xddep.xd_dep_ts;
    xd_dep_graph = List.map (function ntmvr,ntmvrs -> rename_nt_or_mv_root map ntmvr, List.map (rename_nt_or_mv_root map) ntmvrs) xddep.xd_dep_graph;
    xd_dep_graph_nontran = List.map (function ntmvr,ntmvrs -> rename_nt_or_mv_root map ntmvr, List.map (rename_nt_or_mv_root map) ntmvrs) xddep.xd_dep_graph; }

and rename_syntaxdefn map xd =
    { xd_mds = List.map (rename_metavardefn map) xd.xd_mds;
      xd_rs  = List.map (rename_rule map) xd.xd_rs;
      xd_dep = List.map (function be,xddep -> (be, rename_dependencies map xddep)) xd.xd_dep;
      xd_srs = List.map (rename_subrule map) xd.xd_srs;
      xd_srd = rename_subrule_data map xd.xd_srd;
      xd_crs = List.map (rename_contextrule map) xd.xd_crs;
      xd_axs = List.map (function f,ftype -> (f,rename_auxfn_type map ftype)) xd.xd_axs;
      xd_sbs = List.map (rename_subst map) xd.xd_sbs;
      xd_fvs = List.map (rename_freevar map) xd.xd_fvs;
      xd_embed_preamble = xd.xd_embed_preamble;
      (* xd_embed_postamble = xd.xd_embed_postamble; *)
      xd_embed = xd.xd_embed;
      xd_isa_imports = xd.xd_isa_imports;
      xd_pas = rename_parsing_annotations map xd.xd_pas;
}

and rename_defnclass map dc =
  { dc with dc_defns = List.map (rename_defn map) dc.dc_defns }

and rename_defn map d =
  { d with 
(* TODO: do we need to rename d_names?    d_name = rename_nontermroot d.d_name *)
    d_rules = List.map (rename_processed_semiraw_rule map) d.d_rules }

and rename_drule map dr = 
  { dr with 
    drule_premises = List.map (fun (hn,st) -> (hn,rename_symterm map st)) dr.drule_premises;
    drule_conclusion = rename_symterm map dr.drule_conclusion; }

and rename_processed_semiraw_rule map psr = 
  match psr with
  | PSR_Rule dr -> PSR_Rule (rename_drule map dr)
  | PSR_Defncom es -> psr

and rename_funclause map fc = 
  { fc with
    fc_lhs = rename_symterm map fc.fc_lhs;
    fc_rhs = rename_symterm map fc.fc_rhs; }

and rename_fundefn map fd = 
  { fd with
    fd_clauses = List.map (rename_funclause map) fd.fd_clauses }

and rename_fundefnclass map fdc =
  { fdc with
    fdc_fundefns = List.map (rename_fundefn map) fdc.fdc_fundefns }

and rename_fun_or_reln_defnclass map frdc =
  match frdc with
  | FDC fdc -> FDC (rename_fundefnclass map fdc)
  | RDC dc -> RDC (rename_defnclass map dc)
    
and rename_relationsdefn map rd =
  List.map (rename_fun_or_reln_defnclass map) rd

and rename_structure_entry map stre =
  match stre with
  | Struct_md mvr -> Struct_md (rename_metavarroot map mvr)
  | Struct_rs ntrs -> Struct_rs (List.map (rename_nontermroot map) ntrs)
  | Struct_srs xs ->
      Struct_srs (List.map
		    (fun (ntr1,ntr2) -> 
		      (rename_nontermroot map ntr1, 
		       rename_nontermroot map ntr2)) xs)
  | Struct_crs xs -> 
      Struct_crs (List.map
		    (fun (ntr1,ntr2,ntr3) -> 
		      (rename_nontermroot map ntr1, 
		       rename_nontermroot map ntr2, 
		       rename_nontermroot map ntr3)) xs)
  | Struct_axs f -> Struct_axs f
  | Struct_sbs xs -> Struct_sbs xs 
  | Struct_fvs xs -> Struct_fvs xs 
  | Struct_embed embeds -> Struct_embed embeds 
  | Struct_fun_or_defnclass dcns -> Struct_fun_or_defnclass dcns

and rename_structure map str =
  List.map (fun (fn,stre) -> (fn, rename_structure_entry map stre)) str

and rename_systemdefn map sd =
  { syntax = rename_syntaxdefn map sd.syntax;
    relations = rename_relationsdefn map sd.relations;
    structure = rename_structure map sd.structure;
    sources = sd.sources }

and rename_symterm map st = 
  match st with
  | St_node(l,stnb)->St_node(l,rename_symterm_node_body map stnb)
  | St_nonterm(l,ntrp,nt) -> St_nonterm(l,rename_nontermroot map ntrp,rename_nonterm map nt)
  | St_nontermsub(l,ntrpl,ntrpt,nt) -> St_nontermsub(l,rename_nontermroot map ntrpl,rename_nontermroot map ntrpt,rename_nonterm map nt)
  | St_uninterpreted(l,s) -> st

and rename_symterm_node_body map stnb =
  { stnb with st_es = List.map (rename_symterm_element map) stnb.st_es }

and rename_symterm_element map ste =  
  match ste with
  | Ste_st(l,st) -> Ste_st(l,rename_symterm map st)
  | Ste_metavar(l,mvrp,mv) -> Ste_metavar(l,rename_metavarroot map mvrp,rename_metavar map mv)
  | Ste_var(l,mvr,var) -> Ste_var(l,rename_metavarroot map mvr,var)
  | Ste_list(l,stlis) -> Ste_list(l,List.map (rename_symterm_list_item map) stlis)

and rename_symterm_list_item map stli = 
  match stli with
  | Stli_single(l,stes) -> Stli_single(l,List.map (rename_symterm_element map) stes)
  | Stli_listform(stlb) -> Stli_listform(rename_symterm_list_body map stlb)

and rename_symterm_list_body map stlb =
  { stlb with 
    stl_bound = rename_bound map stlb.stl_bound;
    stl_elements = List.map (rename_symterm_element map) stlb.stl_elements }


(** ******************************** *)
(** ******************************** *)
(** avoidance of primary ntrs etc    *)
(** ******************************** *)
(** ******************************** *)

(* build renamings for metavars and nonterms, to avoid non-suffixed primary ones, *)
(* report an error if there is a primary indexvar *)

let avoid xd mvs0 nts0 = 

  (* first for metavariables *)

  (* remove duplicates, as we didn't bother before *)
  let mvs1 = remove_duplicates mvs0 in

  (* consider only mvs with primary mvrs, and raise an error *)
  (* if there is one with a primary indexvar, as they cannot be freshened *)
  let mvs2 = option_map
      (function ((mvr,suff) as mv) -> 
        let mvd = mvd_of_mvr_nonprimary xd mvr in
        match mvd.mvd_indexvar with
        | true ->
            if mvr=mvd.mvd_name then 
              warning ("warning: indexvar \""^mvr^"\" is primary so may give a name-clash\n") ;
            None
        | false ->
            if mvr=mvd.mvd_name then Some mv else None
      ) mvs1 in
            
  (* for each such, if there is one with an empty suffix, generate a new suffix that is *)
  (* fresh amongst all the suffixes of mvs with the same root *)
  let mv_map = option_map
      (function ((mvr,suff) as mv) -> 
        match suff with
        | [] -> 
            let suffs = 
              option_map 
                (function (mvr',suff') -> if mvr'=mvr then Some suff' else None) 
                mvs2 in
            let suff'' = fresh_suffix suffs suff in
            let mv'' = (mvr,suff'') in
            Some (mv,mv'')
        | _ -> None)
      mvs2 in

  (* and now for nonterminals *)
  (* remove duplicates, as we didn't bother before *)
  let nts1 = remove_duplicates nts0 in

  (* consider only nts with primary ntrs *)
  let primary_ntrs = List.map (function r -> r.rule_ntr_name) xd.xd_rs in
  let nts2 = List.filter 
      (function (ntr,suff) -> List.mem ntr primary_ntrs) nts1 in
            
  (* for each such, if there is one with an empty suffix, generate a new suffix that is *)
  (* fresh amongst all the suffixes of nts with the same root *)
  let nt_map = option_map
      (function ((ntr,suff) as nt) -> 
        match suff with
        | [] -> 
            let suffs = option_map (function (ntr',suff') -> if ntr'=ntr then Some suff' else None) nts2 in
            let suff'' = fresh_suffix suffs suff in
            let nt'' = (ntr,suff'') in
            Some (nt,nt'')
        | _ -> None)
      nts2 in

  ([],Some mv_map,[],Some nt_map,[]) 

(* alternatively...*)
(* build renamings for metavars and nonterms, to rename them all *)
(* (except indexvars) to freshly-renamed secondary ones. *)
(* report an error if there is a primary indexvar *)
(* report an error if there is a (non-index) metavar or nonterm without a secondary name *)

let secondary_mvr xd mvr =
  let mvd = mvd_of_mvr_nonprimary xd mvr in
  (match mvd.mvd_names with
  | [] -> int_error "secondary_mvr, empty list of rule names"
  | [_] ->mvr
  | mvrp::mvrq::_ -> fst mvrq)

let secondary_ntr xd ntr =
  let r = rule_of_ntr_nonprimary xd ntr in
  (match r.rule_ntr_names with
  | [] -> int_error "secondary_ntr, empty list of rule names"
  | [_] ->ntr
  | ntrp::ntrq::_ -> fst ntrq)

let secondary_ntmvr xd ntmvr = 
  match ntmvr with
  | Ntr ntr -> Ntr (secondary_ntr xd ntr)
  | Mvr mvr -> Mvr (secondary_mvr xd mvr)

let secondaryify xd mvs0 nts0 = 

  (* first for metavariables *)
  (* remove duplicates, as we didn't bother before *)
  let mvs1 = remove_duplicates mvs0 in

  (* consider only nonindex mvs, and raise an error *)
  (* if there is one with a primary indexvar, as they cannot be freshened *)
  let mvs2 = option_map
      (function ((mvr,suff) as mv) -> 
        let mvd = mvd_of_mvr_nonprimary xd mvr in
        match mvd.mvd_indexvar with
        | true ->
            if mvr=mvd.mvd_name then 
              warning ("indexvar \""^mvr^"\" is primary so may give a name-clash\n") ;
            Some mv
        | false ->
            Some mv
      ) mvs1 in
            
  let rec mv_map acc mvs = match mvs with
  | [] -> acc
  | ((mvr,suff) as mv)::mvs' ->
      let mvr' = secondary_mvr xd mvr in 
      (*if mvr'=mvr then error ("no secondary metavar root defined for \""^mvr^"\"");*)
      let suffs = option_map (function (_,(mvr'',suff'')) -> if mvr''=mvr' then Some suff'' else None) acc in
      let suff'' = fresh_suffix suffs suff in
      let mv'' = (mvr',suff'') in
      mv_map ((mv,mv'')::acc) mvs' in

  (* and now for nonterminals *)
  let nts2 = remove_duplicates nts0 in

  let rec nt_map acc nts = match nts with
  | [] -> acc
  | ((ntr,suff) as nt)::nts' ->
      let ntr' = secondary_ntr xd ntr in 
      (*if ntr'=ntr then error ("no secondary nonterminal root defined for \""^ntr^"\"");*)
      let suffs = option_map (function (_,(ntr'',suff'')) -> if ntr''=ntr' then Some suff'' else None) acc in
      let suff'' = fresh_suffix suffs suff in
      let nt'' = (ntr',suff'') in
      nt_map ((nt,nt'')::acc) nts' in

  (  [], Some(mv_map [] mvs2),  [], Some(nt_map [] nts2), [] )

(* apply suitable renamings across a systemdefn *)  

(* this renames the syntaxdefn and the relations.  Such renaming *)
(* should have no effect on the parsing of symterms, so it doesn't *)
(* matter whether we parse (in embed sections) with respect to a *)
(* renamed or original syntaxdefn. *)

(* We don't rename any embedded symterms within embed sections.  Should we? Perhaps not.*)
  
(* let avoid = secondaryify *)
  
let rec avoid_primaries_prod xd s p = 
  let mvs =
    List.map (function(mvrp,mv,pe)->mv) (mvs_list_used_in_es p.prod_es) in
  let nts = 
    List.map (function(ntrp,nt,pe)->nt) (nts_list_used_in_es p.prod_es) in
  let map = if s then secondaryify xd mvs nts else avoid xd mvs nts in
  { p with 
    prod_es = List.map (rename_element map) p.prod_es;
    prod_bs = List.map (rename_bindspec map) p.prod_bs; }

and avoid_primaries_rule xd s r = 
  { r with
    rule_ps = List.map (avoid_primaries_prod xd s) r.rule_ps }

and avoid_primaries_syntaxdefn xd s xd =
  { xd with
    xd_rs = List.map (avoid_primaries_rule xd s) xd.xd_rs; } 

and avoid_primaries_defnclass xd s dc =
  { dc with dc_defns = List.map (avoid_primaries_defn xd s) dc.dc_defns }

and avoid_primaries_defn xd s d =
  {d with d_rules = List.map (avoid_primaries_processed_semiraw_rule xd s) d.d_rules }

and avoid_primaries_drule xd s dr = 
  let sts = dr.drule_conclusion :: (List.map snd dr.drule_premises) in
  let nts = nts_of_symterms sts in
  let mvs = mvs_of_symterms sts in
  let map = if s then secondaryify xd mvs nts else avoid xd mvs nts in
  {dr with 
   drule_premises = List.map (fun (hn,st) -> (hn,rename_symterm map st)) dr.drule_premises;
   drule_conclusion = rename_symterm map dr.drule_conclusion;}

and avoid_primaries_processed_semiraw_rule xd s psr = 
 match psr with
 | PSR_Rule dr -> PSR_Rule (avoid_primaries_drule xd s dr)
 | PSR_Defncom es -> psr

and avoid_primaries_funclause xd s fc = 
  let sts = [fc.fc_lhs;fc.fc_rhs] in
  let nts = nts_of_symterms sts in
  let mvs = mvs_of_symterms sts in
  let map = if s then secondaryify xd mvs nts else avoid xd mvs nts in
  { fc with
    fc_lhs = rename_symterm map fc.fc_lhs;
    fc_rhs = rename_symterm map fc.fc_rhs; }

and avoid_primaries_fundefn xd s fd =
  { fd with fd_clauses = List.map (avoid_primaries_funclause xd s) fd.fd_clauses }

and avoid_primaries_fundefnclass xd s fdc =
   { fdc with 
     fdc_fundefns = List.map (avoid_primaries_fundefn xd s) fdc.fdc_fundefns }

and avoid_primaries_fun_or_reln_defnclass xd s fdrc =
  match fdrc with
  | FDC fdc -> FDC (avoid_primaries_fundefnclass xd s fdc)
  | RDC dc -> RDC (avoid_primaries_defnclass xd s dc)

and avoid_primaries_relationsdefn xd s rd =
  List.map (avoid_primaries_fun_or_reln_defnclass xd s) rd

and avoid_structure_entry xd s stre =
  stre  (* FZ BROKEN BROKEN BROKEN *)
  
and avoid_primaries_structure xd s str =
  List.map (avoid_structure_entry xd s) str

and avoid_primaries_systemdefn s sd =
  { syntax = avoid_primaries_syntaxdefn sd.syntax s sd.syntax;
    relations = avoid_primaries_relationsdefn sd.syntax s sd.relations;
    structure = avoid_primaries_structure sd.syntax s sd.structure;
    sources = sd.sources }


(** ******************************** *)
(** ******************************** *)
(** caml renaming                    *)
(** ******************************** *)
(** ******************************** *)

(* build renamings for metavars and nonterms, to map nonterminals and
metavariables (and their roots) to lowercase, and production names to
uppercase *)

let rec detect_conflicts l =
  match l with
  | [] -> (false,"")
  | (_,x)::tl -> 
      if List.mem x (List.map (fun x -> snd x) tl)
      then (true,x)
      else detect_conflicts tl

let capitalize_prodnames sd =
  let rule_list = sd.syntax.xd_rs in
  let prod_list = List.flatten (List.map (fun r -> r.rule_ps) rule_list) in
  let prod_name_list = List.map (fun p -> p.prod_name) prod_list in
  let map_prod_names = List.map (fun pn -> (pn,String.capitalize pn)) prod_name_list in
  let (conflict,err_msg) = detect_conflicts map_prod_names in
  if conflict
  then error ("Renaming of production name \""^err_msg^"\" generates a conflict\n")
  else map_prod_names

let uncapitalize_prodnames sd =
  let rule_list = sd.syntax.xd_rs in
  let prod_list = List.flatten (List.map (fun r -> r.rule_ps) rule_list) in
  let prod_name_list = List.map (fun p -> p.prod_name) prod_list in
  let map_prod_names = List.map (fun pn -> (pn,String.uncapitalize pn)) prod_name_list in
  let (conflict,err_msg) = detect_conflicts map_prod_names in
  if conflict
  then error ("Renaming of production name \""^err_msg^"\" generates a conflict\n")
  else map_prod_names

let uncapitalize_primary_nontermroots sd = 
  let rule_list = sd.syntax.xd_rs in
  let nontermroots_list = List.map (fun r -> r.rule_ntr_name) rule_list in
  let map_nontermroots = List.map (fun ntr -> (ntr,String.uncapitalize ntr)) nontermroots_list in
  let (conflict,err_msg) = detect_conflicts map_nontermroots in
  if conflict
  then error ("Renaming of primary nontermroot \""^err_msg^"\" generates a conflict\n")
  else map_nontermroots

let uncapitalize_primary_metavarroots sd =
  let metavardefn_list = sd.syntax.xd_mds in
  let metavarroots_list = List.map (fun mvd -> mvd.mvd_name) metavardefn_list in
  let map_metavarroots = List.map (fun mvr -> (mvr,String.uncapitalize mvr)) metavarroots_list in
  let (conflict,err_msg) = detect_conflicts map_metavarroots in
  if conflict
  then error ("Renaming of primary metavar \""^err_msg^"\" generates a conflict\n")
  else map_metavarroots 

let caml_rename sd =
  let map_prod_names = capitalize_prodnames sd in
  let map_nontermroots = uncapitalize_primary_nontermroots sd in
  let map_metavarroots = uncapitalize_primary_metavarroots sd in
  rename_systemdefn (map_metavarroots,None,map_nontermroots,None,map_prod_names) sd

let twelf_rename sd =
  let map_prod_names = uncapitalize_prodnames sd in
  let map_nontermroots = uncapitalize_primary_nontermroots sd in
  let map_metavarroots = uncapitalize_primary_metavarroots sd in
  rename_systemdefn (map_metavarroots,None,map_nontermroots,None,map_prod_names) sd

let rec capitalize_prodnames_in_symterm st =
  match st with
  | St_node (l,stnb) -> St_node (l,capitalize_prodnames_in_symterm_node_body stnb)
  | _ -> st
and capitalize_prodnames_in_symterm_node_body stnb =
  { st_rule_ntr_name = stnb.st_rule_ntr_name;
    st_prod_name = String.capitalize stnb.st_prod_name;
    st_es = List.map capitalize_prodnames_in_symterm_element stnb.st_es;
    st_loc = stnb.st_loc }
and capitalize_prodnames_in_symterm_element ste =
  match ste with
  | Ste_st (l,st) -> Ste_st (l,capitalize_prodnames_in_symterm st)
  | Ste_list (l,stlis) -> Ste_list (l,List.map capitalize_prodnames_in_symterm_list_item stlis)
  | _ -> ste
and capitalize_prodnames_in_symterm_list_item stli =
  match stli with
  | Stli_single (l,stes) -> Stli_single (l,List.map capitalize_prodnames_in_symterm_element stes)
  | Stli_listform stlb -> Stli_listform (capitalize_prodnames_in_symterm_list_body stlb)
and capitalize_prodnames_in_symterm_list_body stlb =
  { stl_bound = stlb.stl_bound ; 
    stl_elements = List.map capitalize_prodnames_in_symterm_element stlb.stl_elements;
    stl_loc = stlb.stl_loc } 

(** ******************************** *)
(** ******************************** *)
(** ******************************** *)
(** ******************************** *)

(* some useful conversions *)

let pp_true m in_prop =
  match m with 
  | Isa _ -> "True" 
  | Coq co ->
      if co.coq_expand_lists || in_prop  
      then "True"     
      else "true"
  | Hol _ -> "T" 
  | Caml _ -> "true" 
  | Lem _ -> "true" 
  | Ascii _ | Tex _ | Twf _ | Lex _ | Yacc _ -> errorm m "pp_true"

let pp_false m in_prop =
  match m with 
  | Isa _ -> "False" 
  | Coq co ->
      if co.coq_expand_lists || in_prop 
      then "False"     
      else "false"
  | Hol _ -> "F" 
  | Caml _ -> "false"
  | Lem _ -> "false"
  | Ascii _ | Tex _ | Twf _ | Lex _ | Yacc _ -> errorm m "pp_false"

let pp_and m in_prop =
  match m with
  | Isa _ -> " & " 
  | Caml _ -> " && " 
  | Lem _ -> " && " 
  | Coq co ->
      if co.coq_expand_lists || in_prop
      then " /\\ "     
      else " && "
  | Hol _ -> " /\\ "
  | Ascii _ | Tex _ | Twf _ | Lex _ | Yacc _ -> errorm m "pp_and"

let pp_or m in_prop =
  match m with 
  | Isa _ -> " | " 
  | Coq co ->
      if co.coq_expand_lists || in_prop 
      then " \\/ "     
      else " || "
  | Hol _ -> " \\/ " 
  | Caml _ -> " || "
  | Lem _ -> " || "
  | Ascii _ | Tex _ | Twf _ | Lex _ | Yacc _ -> errorm m "pp_or"

(* coq/twelf support *)
let fresh_nl =
  let counter = ref 0 in
  fun () -> counter := !counter+1; "NL"^(string_of_int !counter)

let insert_append m l =
  match m with
  | Coq _ ->
      ( match l with
      | [] -> "nil"
      | x::[] -> "("^x^")"
      | _ ->
	  let rec last l = 
            ( match l with
            | [] -> errorm m "never happen in insert_append"
            | x::[] -> errorm m "never happen in insert_append"
            | x::y::[] -> ([x],y)
            | h::t -> let (x,y) = last t in (h::x,y) ) in
	  let els,el_last = last l in
	  List.fold_right (fun x s -> "(app "^x^" "^s^")") els el_last )
  | Twf _ -> 
      ( match l with
      | [] -> "natlist/nil"
      | x::[] -> x
      | _ ->
	  let result_nl = List.map (fun x -> fresh_nl()) (List.tl l) in
	  let list_nl = List.map (fun x -> fresh_nl()) l in
	  let final_append = 
	    let rec internal current_result result_nl list_nl =
	      ( match result_nl with 
	      | [] -> " <- append/natlist " ^ String.concat " " list_nl ^ " " ^ current_result
	      | r::rt -> 
		  " <- append/natlist " ^ (List.hd list_nl) ^ " " ^ current_result ^ " " ^ (List.hd result_nl) 
		  ^ (internal (List.hd result_nl) (List.tl result_nl) (List.tl list_nl)) ) 
		  
	    in internal (List.hd result_nl) (List.tl result_nl) list_nl in

	  List.hd (List.rev result_nl) ^ " <- "
	  ^ ( String.concat " <- " 
	      (List.map2 (fun s nl -> s ^ " " ^ nl) l list_nl) )
	  ^ final_append )
  | Caml _ | Tex _ | Ascii _ | Hol _ | Lem _ | Isa _ | Lex _ | Yacc _ -> raise ThisCannotHappen

(* skip a nonterm or a metavar in a list of elements *)
let rec skip_nt_mv (es:element list) =
  match es with
  | [] -> []
  | (Lang_nonterm (_,_))::tl | (Lang_metavar (_,_))::tl -> tl
  | _::tl -> skip_nt_mv tl

let rec head_nt_mv (es:element list) =
  match es with
  | [] -> raise Not_found
  | (Lang_nonterm (ntr,nt))::tl -> Lang_nonterm (ntr,nt)
  | (Lang_metavar (mvr,mv))::tl -> Lang_metavar (mvr,mv)
  | _::tl -> head_nt_mv tl

(* analyze the productions and decide if it relies on polymorphic lists or not - isa output *)
let compute_isa_list_name_flag r =
  let prods = List.filter (fun p -> not (p.prod_meta)) r.rule_ps in
  let ess = List.concat (List.map (fun p -> p.prod_es) prods) in
  let rec scan ess =
    match ess with
    | [] -> false
    | x::xs -> 
	( match x with
	| Lang_list elb -> (scan_int elb.elb_es xs) || (scan xs) 
	| _ -> scan xs )
  and scan_int x xs = 
    match xs with
    | [] -> false
    | (Lang_list elb)::ys -> 
	if x = elb.elb_es then true
	else scan_int x ys
    | _::ys -> scan_int x ys
  in
  scan ess 

let collapse_embed_spec_el_list es = 

  let rec collapse_embed_spec_el_list1 acc es 
      = match es with
      | (Embed_string(l,s))::es' -> collapse_embed_spec_el_list2 acc (l,s) es'
      | (Embed_inner(_,_) as ese)::es' -> collapse_embed_spec_el_list1 (ese::acc) es'
      | [] -> acc
  and collapse_embed_spec_el_list2 acc (l0,s0) es 
      = match es with
      | (Embed_string(l,s))::es' -> collapse_embed_spec_el_list2 acc (dummy_loc,s0^s) es'
      | (Embed_inner(_,_) as ese)::es' -> collapse_embed_spec_el_list1 (ese::Embed_string(l0,s0)::acc) es'
      | [] -> Embed_string(l0,s0)::acc
  in
  List.rev (collapse_embed_spec_el_list1 [] es) 

let collapse_embed (l,hn,es) = (l,hn,collapse_embed_spec_el_list es)

let rec pp_tex_escape s = 
  String.concat "" 
    (List.map 
       (fun c -> 
         if c='_' then "\\_" else 
         if c='%' then "\\%" else 
         if c='$' then "\\$" else 
         if c='#' then "\\#" else 
         if c='?' then "\\mbox{?}" else 
         if c='^' then "\\mbox{$\\uparrow$}" else 
         if c='{' then "\\{" else 
         if c='}' then "\\}" else 
         if c='&' then "\\&" else 
         if c='\\' then "\\mbox{$\\backslash{}$}" else 
         if c='|' then "\\mbox{$\\mid$}" else 
         String.make 1 c) 
       (char_list_of_string s))

let rec pp_tex_escape_alltt s = 
  String.concat "" 
    (List.map 
       (fun c -> 
(*         if c='_' then "\\_" else  *)
         if c='{' then "\\mylb{}" else 
         if c='}' then "\\myrb{}" else 
         if c='\\' then "\\mybackslash{}" else 
         String.make 1 c)
       (char_list_of_string s))

(* file name manipulation *)

let isa_filename_check s =
  match string_remove_suffix s ".thy" with
  | None -> error ("Isabelle filenames must end with .thy\n")
  | Some s1 -> s1

let hol_filename_check s =
  match string_remove_suffix s "Script.sml" with
  | None -> failwith ("HOL filenames must end with Script.sml\n")
  | Some s1 -> s1

let filename_check m s =
  match m with
  | Hol _ -> hol_filename_check s
  | Isa _ -> isa_filename_check s
  | _ -> s

(* locally nameless *)

let is_lngen m =
  let co = match m with Coq co -> co 
  | _ -> errorm m "ln_transform_syntaxdefn of non-coq target" in
  co.coq_lngen

let require_locally_nameless xd =
  List.exists 
    ( fun mvd -> 
      try let _ = List.assoc "repr-locally-nameless" mvd.mvd_rep in true 
      with Not_found -> false )
    xd.xd_mds

(* nominal *)

let is_nominal_atom m xd mvd =
  List.exists 
    (fun (hn,_) -> String.compare hn "repr-nominal" = 0) 
    mvd.mvd_rep

let prod_require_nominal m xd p =
  (* true if p contains binders with nominal repr *)
  List.exists
    ( fun bs -> 
      match bs with
      | Bind (MetaVarExp (mvr,_), nt) -> 
	  is_nominal_atom m xd (mvd_of_mvr xd (primary_mvr_of_mvr xd mvr) )
      | _ -> false )
    p.prod_bs

let rule_require_nominal m xd r =
  List.exists (prod_require_nominal m xd) r.rule_ps
  
let rules_require_nominal m xd rs =
  List.exists (rule_require_nominal m xd) rs

let require_nominal xd =
  List.exists 
    ( fun mvd -> 
      try let _ = List.assoc "repr-nominal" mvd.mvd_rep in true 
      with Not_found -> false )
    xd.xd_mds

(* debug code for the structure data type *)

let dump_structure_entry (l,stre) = 
  ( match l with
  | [] -> ""
  | h::_ -> (Location.pp_t h)^" : " ) 
  ^ 
    ( match stre with 
    | Struct_md mvr ->  "metavar def: "^mvr
    | Struct_rs ntrs -> "rule def: "^(String.concat " " ntrs)
    | Struct_srs xs -> "subrule def: "^
	(String.concat " " 
	   (List.map (fun (ntr1,ntr2) -> "("^ntr1^","^ntr2^")") xs))
    | Struct_fvs xs -> "freevar def: "^
	(String.concat " " 
	   (List.map (fun (name,ntr1,ntmvr2) -> "("^name^","^ntr1^","^(match ntmvr2 with Ntr s | Mvr s -> s)^")") xs))
    | Struct_sbs xs -> "substs def: "^
	(String.concat " " 
	   (List.map (fun (name,ntr1,ntmvr2) -> "("^name^","^ntr1^","^(match ntmvr2 with Ntr s | Mvr s -> s)^")") xs))
    | Struct_axs xs -> "aux def: "^
        (String.concat " " xs)
    | Struct_fun_or_defnclass s -> "fundefn_class def: "^s
    | Struct_embed (_,h,_) -> "embed: "^h)

let dump_structure str = 
  "*** dump structure ***\n"^
  (String.concat "\n" (List.map dump_structure_entry str))

let dump_structure_fn str = 
  "*** dump structure ***\n"^
  (String.concat "\n" (List.map (fun (fn,s) -> fn ^" : "^ (dump_structure_entry (dummy_loc,s))) str))


(* reading a whole file in as a string *)
 
let string_of_filename filename =
  let ic = open_in filename in
  let _ = set_binary_mode_in ic true in
  let len = in_channel_length ic in
  let buff = String.create len  in
  let _ = really_input ic buff 0 len in
  buff
