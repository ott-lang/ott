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

let debug = Auxl.debug

module G = Graph.Pack.Digraph

(* FZ need more reasonable exceptions *)
exception ThisCannotHappen;;
exception ThisCannotHappenB;;
exception ThisCannotHappenC;;

(* We take care to report errors in a reasonable way *)

exception Typecheck_error of string*string;;

let ty_error s1 s2 = raise (Typecheck_error(s1,s2))
let ty_error2 l s1 s2 = raise (Typecheck_error(s1^" at "^Location.pp_loc l,s2))

let rec firstdup xs = match xs with 
  [] -> None 
| x::xs -> if (List.mem x xs) then Some x else firstdup xs 


(* synthesising a raw aux-annotated rule *)

(* 
We permit an aux hom on grammar rules. For any rule with such a hom,
we transform that rule by appending an "_aux" to its primary nonterminal
root name. We then add a synthesised rule with the original nonterminal
root name and a single production, with a shape described by the body of 
the aux hom, which must be of the form  

  {{ aux  foo1 foo2 _ bar1 bar2 bar3 }}

with a single _ and any number of strings fooi and barj before and
after, and no Raw_hom_ident's.  The _ is replaced by the original
nonterminal root name.  

For example, given a grammar or metavariable l of source locations, one
might say 

ntr :: 'NTR_'  ::=  {{ aux _ l }}
 | ...

to synthesise grammars ntr_aux and ntr of unannotated and location-annotated 
terms, the first with all the original productions and the second with a 
single production 
 | ntr l :: :: NTR_aux. 

If the rule has an empty production name wrapper (eg with '' in place
of 'NTR_') then the production name is based on the original
nonterminal root, capitalised and with _aux appended (eg Ntr_aux), to
avoid spurious conflicts.

Generation of aux rules is controlled by a command-line option
-generate_aux_rules {true | false}, which one might (eg) set to false
for latex output and true for OCaml output.

*)

let ty_error_string_aux_hom = "illegal aux hom: an aux hom must be of the form {{ aux  foo1 foo2 _ bar1 bar2 bar3 }}"
let rec cd_raw_aux_hom_before l (acc_before :string list) (rhs :raw_hom_spec_el list) =
match rhs with
| [] -> ty_error2 l ty_error_string_aux_hom ""
| Raw_hom_string "_"::rhs' -> cd_raw_aux_hom_after l acc_before [] rhs'
| Raw_hom_string s::rhs' -> cd_raw_aux_hom_before l (acc_before@[s]) rhs'
| Raw_hom_blanks s::rhs' -> cd_raw_aux_hom_before l acc_before rhs'
| _ -> ty_error2 l ty_error_string_aux_hom ""
and 
cd_raw_aux_hom_after l (acc_before :string list) (acc_after :string list) (rhs :raw_hom_spec_el list) =
match rhs with
| [] -> (acc_before,acc_after,l)
| Raw_hom_string "_"::rhs' -> ty_error2 l ty_error_string_aux_hom ""
| Raw_hom_string s::rhs' -> cd_raw_aux_hom_after l acc_before (acc_after@[s]) rhs'
| Raw_hom_blanks s::rhs' -> cd_raw_aux_hom_after l acc_before acc_after rhs'
| _ -> ty_error2 l ty_error_string_aux_hom ""

let aux_hom_of_raw_rule rr : (string list * string list * loc) option  =
  let auxhoms = List.filter (function (hn,rhs,l) -> hn="aux") rr.raw_rule_homs in
  match auxhoms with
  | [] -> None
  | [(hn,rhs,l)] -> Some (cd_raw_aux_hom_before l [] rhs)
  | _ -> ty_error2 rr.raw_rule_loc "more than one aux hom" ""

let aux_rule_name rr = rr.raw_rule_ntr_name
let auxed_rule_name rr = rr.raw_rule_ntr_name ^ "_aux"

let aux_rule (rr:raw_rule) ((before :string list),(after : string list), (l :loc)) : raw_rule =
  let aux_prod = 
    { raw_prod_name = (if rr.raw_rule_pn_wrapper<>"" then rr.raw_rule_pn_wrapper else String.capitalize rr.raw_rule_ntr_name ^"_") ^ "aux";
      raw_prod_flavour = Bar;
      raw_prod_categories = [];
      raw_prod_es = 
      begin
	let raw_ident_of_string s = Raw_ident(l,(l,s)) in
	List.map raw_ident_of_string before
	@ [raw_ident_of_string (auxed_rule_name rr)]
	@ List.map raw_ident_of_string after
      end;
      raw_prod_homs = [];
      raw_prod_bs = [];
      raw_prod_loc = l } in
  { raw_rule_ntr_name = aux_rule_name rr;
    raw_rule_ntr_names = [aux_rule_name rr,[]];
    raw_rule_pn_wrapper = "";
    raw_rule_ps = [aux_prod];
    raw_rule_homs = List.filter (function (hn,_,_) ->  hn="auxparam") rr.raw_rule_homs;
    raw_rule_categories = ["aux"];
    raw_rule_loc = l }
let auxed_rule (rr:raw_rule) : raw_rule =
  (match rr.raw_rule_ntr_names with
  | (_,homs)::_ -> if homs <> [] then ty_error2 rr.raw_rule_loc "rules with aux homs cannot have homs on the principal nonterminal root" ""
  | _ -> ());
  { rr with 
    raw_rule_ntr_name = auxed_rule_name rr;
    raw_rule_ntr_names = [(auxed_rule_name rr,[])]@List.tl rr.raw_rule_ntr_names;
  }

let auxify_rules (ri :raw_item) : raw_item =
  match ri with
  | Raw_item_rs raw_rs ->   
      let rec f raw_rs = 
	match raw_rs with
	| [] -> []
	| rr::raw_rs' -> 
	    (match aux_hom_of_raw_rule rr with
	    | None -> rr :: f raw_rs'
	    | Some aux_hom -> auxed_rule rr :: aux_rule rr aux_hom :: f raw_rs') in
      Raw_item_rs (f raw_rs)
  | _ -> ri

(* auxiliaries ************************************************************* *)

(* TODO: this old-style concat and merge code should (for tidyness) be
rewritten over the new (raw_item) raw type *)

let rsd_of_ri ri = match ri with
| Raw_item_md raw_md ->        { empty_raw_sd with raw_sd_mds=[raw_md] }
| Raw_item_rs raw_rs ->        { empty_raw_sd with raw_sd_rs=raw_rs }
| Raw_item_dcs raw_dcs ->      { empty_raw_sd with raw_sd_dcs=[raw_dcs] }
| Raw_item_srs raw_srs ->      { empty_raw_sd with raw_sd_srs=raw_srs }
| Raw_item_crs raw_crs ->      { empty_raw_sd with raw_sd_crs=raw_crs }
| Raw_item_sbs raw_sbs ->      { empty_raw_sd with raw_sd_sbs=raw_sbs }
| Raw_item_fvs raw_fvs ->      { empty_raw_sd with raw_sd_fvs=raw_fvs }
| Raw_item_embed raw_embeds -> { empty_raw_sd with raw_sd_embed=raw_embeds }
| Raw_item_pas raw_pas ->      { empty_raw_sd with raw_sd_pas=raw_pas }
| Raw_item_hs raw_hs ->        { empty_raw_sd with raw_sd_hss=[raw_hs] }
| Raw_item_coq_section raw_qs  -> empty_raw_sd   (* no rep for this in old type *)
| Raw_item_coq_variable raw_qv  -> empty_raw_sd   (* no rep for this in old type *)

let append_rsd rsd rsd' =
  { raw_sd_mds = rsd.raw_sd_mds @ rsd'.raw_sd_mds;
    raw_sd_rs  = rsd.raw_sd_rs  @ rsd'.raw_sd_rs;
    raw_sd_dcs = rsd.raw_sd_dcs @ rsd'.raw_sd_dcs;
    raw_sd_srs = rsd.raw_sd_srs @ rsd'.raw_sd_srs;
    raw_sd_crs = rsd.raw_sd_crs @ rsd'.raw_sd_crs;
    raw_sd_sbs = rsd.raw_sd_sbs @ rsd'.raw_sd_sbs;
    raw_sd_fvs = rsd.raw_sd_fvs @ rsd'.raw_sd_fvs;
    raw_sd_embed = rsd.raw_sd_embed @ rsd'.raw_sd_embed;
    raw_sd_hss = rsd.raw_sd_hss @ rsd'.raw_sd_hss;
    raw_sd_pas = rsd.raw_sd_pas @ rsd'.raw_sd_pas;
    raw_sd_loc = dummy_loc }

(* let rec rsds_of_ris ris = match ris with *)
(* | [] -> empty_raw_sd *)
(* | ri::ris' -> append_rsd (rsd_of_ri ri) (rsds_of_ris ris') *)

let rec concat_language_fragments_per_file (rsds:raw_syntaxdefn list) : raw_syntaxdefn =
  match rsds with
  | [] ->
      empty_raw_sd
  | rsd0::rsds' ->
      let rsd_c = concat_language_fragments_per_file  rsds' in
      append_rsd rsd0 rsd_c


let rec concat_language_fragments (rsds:raw_syntaxdefn list) : raw_syntaxdefn =
  match rsds with
  | [] ->
      empty_raw_sd
  | rsd0::rsds' ->
      let rsd_c = concat_language_fragments rsds' in
      append_rsd rsd0 rsd_c

(* let concat_language_fragments_per_file (after_some_defn:bool) (rsds:raw_syntaxdefn list) : raw_syntaxdefn = raise WorkInProgress *)
(* let concat_language_fragments (rsds:raw_syntaxdefn list) : raw_syntaxdefn = raise WorkInProgress *)


(* first-draft code to merge language fragments *)
(* NB: at present this does no error checking - it should...*)
  
let collect : ('a*'b) list -> ('a * 'b list) list =
  function xys -> 
    let rec f acc xys =
      match xys with
      | [] -> acc
      | (x,y)::xys -> 
          if List.mem_assoc x acc then
            let ys = List.assoc x acc in
            let acc' = List.remove_assoc x acc in
            let acc'' = acc'@[(x,ys@[y])] in
            f acc'' xys
          else f (acc@[(x,[y])]) xys in
    f [] xys

let collect = (* : ('a -> 'key) -> 'a list -> 'a list list = *)
  fun extract_key xs ->
    let assoc = List.map (function x -> (extract_key x,x)) xs in
    let collected_assoc = collect assoc in
    List.map snd collected_assoc 

(* to merge the structure informations properly, we need to return
informations about which rules have been merged *)

let merge_raw_rules (rrs:raw_rule list) : raw_rule list * (nontermroot*loc*nontermroot*loc) list =  
  let merged = ref [] in
  let collected_rules = collect (function rr -> rr.raw_rule_ntr_name) rrs in
  let append_raw_rule (rr:raw_rule) (rr':raw_rule) : raw_rule =
    merged := (rr.raw_rule_ntr_name,rr.raw_rule_loc, rr'.raw_rule_ntr_name,rr'.raw_rule_loc)::!merged;
    { rr with raw_rule_ps = rr.raw_rule_ps @ rr'.raw_rule_ps } in
  let rec f rrs = match rrs with
  | [] -> Auxl.int_error "merge_raw_rules"
  | [rr] -> rr
  | rr::rr'::rrs -> append_raw_rule rr (f (rr'::rrs)) in
  let mapped = List.map f collected_rules in
  (* print_endline "*** merged infos"; *)
  (* print_endline (String.concat "\n" (List.map (fun (x,xl,y,yl) -> x^":"^(Location.pp_loc xl)^"\n    "^y^":"^(Location.pp_loc yl)) !merged)); *)
  (* print_endline "*** end merged infos"; *)
  (mapped,!merged)

let merge_raw_defns (rds:raw_defn list) : raw_defn list =
  let collected_defns = collect (function rd->rd.raw_d_name) rds in
  let append_raw_defn (rd:raw_defn) (rd':raw_defn) : raw_defn =
    { rd with raw_d_body = rd.raw_d_body (*@ [Raw_blankline (dummy_loc,"")]*)@rd'.raw_d_body }in
  let rec f rds = match rds with
  | [] -> Auxl.int_error "merge_raw_defns"
  | [rd] -> rd
  | rd::rd'::rds -> append_raw_defn rd (f (rd'::rds)) in
  List.map f collected_defns 

let merge_raw_fundefns (rfds:raw_fundefn list) : raw_fundefn list =
  let collected_fundefns = collect (function rfd->rfd.raw_fd_name) rfds in
  let append_raw_fundefn (rfd:raw_fundefn) (rfd':raw_fundefn) : raw_fundefn =
    { rfd with raw_fd_clauses = rfd.raw_fd_clauses @ rfd'.raw_fd_clauses }in
  let rec f rfds = match rfds with
  | [] -> Auxl.int_error "merge_raw_fundefns"
  | [rfd] -> rfd
  | rfd::rfd'::rfds -> append_raw_fundefn rfd (f (rfd'::rfds)) in
  List.map f collected_fundefns 

let merge_raw_fun_or_reln_defnclasses (rfrdcs:raw_fun_or_reln_defnclass list) : raw_fun_or_reln_defnclass list =
  let collected_fun_or_reln_defnclasses = 
    collect 
      (function rfrdc->match rfrdc with Raw_FDC rfdc -> "fun",rfdc.raw_fdc_name| Raw_RDC rdc -> "rel",rdc.raw_dc_name) 
      rfrdcs in
  let append_raw_fun_or_reln_defnclass (rfrdc:raw_fun_or_reln_defnclass) (rfrdc':raw_fun_or_reln_defnclass) : raw_fun_or_reln_defnclass =
    match rfrdc,rfrdc' with
    | Raw_FDC rfdc,Raw_FDC rfdc' -> 
        Raw_FDC { rfdc with raw_fdc_fundefns = rfdc.raw_fdc_fundefns @ rfdc'.raw_fdc_fundefns }
    | Raw_RDC rdc,Raw_RDC rdc' ->
        Raw_RDC { rdc with raw_dc_defns = rdc.raw_dc_defns @ rdc'.raw_dc_defns }
    | _,_ -> Auxl.int_error "merge_raw_fun_or_reln_defnclasses 2" in
  let rec f rfrdcs = match rfrdcs with
  | [] -> Auxl.int_error "merge_raw_fun_or_reln_defnclasses"
  | [rfrdc] -> rfrdc
  | rfrdc::rfrdc'::rfrdcs -> append_raw_fun_or_reln_defnclass rfrdc (f (rfrdc'::rfrdcs)) in
  List.map 
    (function rfrdc -> 
      match rfrdc with 
      | Raw_FDC rfdc -> Raw_FDC { rfdc with raw_fdc_fundefns = merge_raw_fundefns rfdc.raw_fdc_fundefns } 
      | Raw_RDC rdc -> Raw_RDC  { rdc with raw_dc_defns = merge_raw_defns rdc.raw_dc_defns })
    (List.map f collected_fun_or_reln_defnclasses )



let merge_language_fragments (rsd:raw_syntaxdefn) : raw_syntaxdefn =
  let (merged_raw_rules,_) = merge_raw_rules rsd.raw_sd_rs in (* FZ tasteless *)
  { rsd with 
    raw_sd_rs = merged_raw_rules;
    raw_sd_dcs = merge_raw_fun_or_reln_defnclasses rsd.raw_sd_dcs
  }


(* check that for each pair in the Subrule part of srs that there is
   (up to the Subrule part of srs) a subgrammar relationship between
   the definitions of two rules *)
let rec subelement (subrule_graph:subrule_graph) (el:element) (eu:element) : bool =
  match el,eu with
  | Lang_nonterm (ntr_primaryl, (ntr_as_writtenl, suffixl)), 
    Lang_nonterm (ntr_primaryu, (ntr_as_writtenu, suffixu)) ->
      ( ntr_primaryl = ntr_primaryu 
      || List.mem (ntr_primaryl, ntr_primaryu)  subrule_graph )
  | Lang_metavar _, Lang_metavar _ -> el = eu
  | Lang_terminal _, Lang_terminal _ -> el = eu
  | Lang_option els', Lang_option eus' -> subelements subrule_graph els' eus'
  | Lang_sugaroption els', Lang_sugaroption eus' -> els' = eus'
  | Lang_list elbl, Lang_list elbu -> 
      elbl.elb_tmo=elbu.elb_tmo && elbl.elb_boundo = elbu.elb_boundo && subelements subrule_graph elbl.elb_es elbu.elb_es
  | _,_ -> false 

and subelements 
    (subrule_graph:subrule_graph) (els:element list) (eus:element list) : bool =
  try 
    List.for_all2 (subelement subrule_graph) els eus
  with
    Invalid_argument _ -> false 
            
let subprod (subrule_graph:subrule_graph) (pl:prod) (pu:prod) : bool =
  subelements subrule_graph pl.prod_es pu.prod_es 
        
let subrule (xd:syntaxdefn) (include_meta_prods:bool)
    (srl:nontermroot) (sru:nontermroot) : (prodname*prodname) list =

  let subrule_graph = xd.xd_srd.srd_subrule_graph in
  let rl = Auxl.rule_of_ntr xd srl in
  let ru = Auxl.rule_of_ntr xd sru in
      
  List.map
    (fun pl -> 
      let pus = List.filter 
          (fun pu -> (include_meta_prods || not(pu.prod_meta)) && subprod subrule_graph pl pu) ru.rule_ps in
      match pus with 
      | [] -> 
          ty_error
	    ( "subrule check failed: production "
	      ^ Auxl.the (Grammar_pp.pp_prod error_opts xd "" "" pl) 
	      ^ " of rule " ^ rl.rule_ntr_name
	      ^ " cannot be matched in rule " ^ ru.rule_ntr_name) ""
      | [pu] -> (pl.prod_name,pu.prod_name)
      | pu::pu'::pus' -> 
          Auxl.warning 
            ("production \""^pl.prod_name^"\" is a subproduction of more than one production: "^String.concat ", " (List.map (function pu -> "\""^pu.prod_name^"\"") pus) ^" (taking the first)\n");
          (pl.prod_name,pu.prod_name)
    )
    (List.filter (fun pl-> (include_meta_prods || not(pl.prod_meta))) rl.rule_ps)



(*  the raw_x -> x conversion functions *)

(*  TODO treating all Not_found as Hom_terminal may disguise many  typos?  Used to have this here: tcheck2' ... *)

let allowable_hom_data = 
  [ 
    ( Hu_root    , (["isa";"coq";"hol";"lem";(*"twf";*)"tex";"ocaml"], 
                    "nonterminal, metavar or indexvar root"));
    ( Hu_metavar , (["isa";"coq";"hol";"lem";(*"twf";*)"tex";"ocaml";"com";"coq-equality";"lex";"texvar";"isavar";"holvar";"lemvar";"ocamlvar";"repr-locally-nameless";(*"repr-nominal";*)"phantom"],
                    "metavar declaration"));
    ( Hu_rule    , (["isa";"coq";"hol";"lem";(*"twf";*)"tex";"ocaml";"com";"coq-equality";"coq-universe";(*"icht";*)"icho";"ichlo";"ich";"ichl";"ic";"ch";"ih";"phantom";"aux";"auxparam"],
                    "rule"));
    ( Hu_rule_meta, (["com"], "special rule"));
    ( Hu_prod    , (["isa";"coq";"hol";"lem";(*"twf";*)"tex";"texlong";"ocaml";"com";"order";"isasyn";"isaprec";(*"icht";*)"icho";"ichlo";"ich";"ichl";"ic";"ch";"ih";
                     "disambiguate";"prec";"leftassoc";"rightassoc"],
                    "production"));
    ( Hu_prod_tm , (["isa";                      "tex";"lex";  "com"; "prec";"leftassoc";"rightassoc"],"production of the terminals grammar"));
    ( Hu_drule   , ([                                          "com"],"definition rule"));
    ( Hu_defn    , ([                            "tex";        "com";"isasyn";"isaprec";"disambiguate";"lemwcf"],"definition"));
    ( Hu_defnclass, (["coq-universe"],"defns block"));
    ( Hu_fundefn , (["isa";"coq";"hol";"lem";(*"twf";*)"tex";        "com";"order";"isasyn";"isaprec";(*"icht";*)"icho";"ichlo";"ich";"ichl";"ic";"ch";"ih";"coq-struct"],"function definition"));
    ( Hu_fundefnclass, ([(* "isa-proof";*)"hol-proof"],"funs block"));
    ( Hu_subrule,  (["isa-proof"],"subrule definition"));
    ( Hu_subst,    (["isa-proof"],"substitution definition"));
    ( Hu_freevar,  (["isa-proof";"isa-set"],"free variable definition"));
    (* ( Hu_embed   , (["isa";"coq";"hol";"lem";(\*"twf";*\)"tex";"ocaml";"isa-auxfn-proof";"isa-subrule-proof"],"embed section")); *)
    ( Hu_deadcode, ([], "Internal error: Hu_deadcode"));
  ] 

let embed_allowable_homs = ["coq";"coq-lib";
                            "isa";"isa-import";"isa-auxfn-proof";"isa-subrule-proof";"isa-lib";
                            "hol";"lem";
                            "tex";"tex-preamble";"tex-wrap-pre";"tex-wrap-post";
                            (*"twf";*)"ocaml"]

let list_form_allowable_homs =["isa";"coq";"hol";"lem";"ic";"ch";"ih";"ich";"ichl";"icho";"ichlo";(*"icht";*)"coq-struct";"ocaml"] 

let cd_disambiguate_hom name rhs hs =
  try 
    let (_,_,l0) = List.find (fun (hn,_,_) -> hn="disambiguate") rhs in
    let es = List.assoc "disambiguate" hs in
    let err l0 =
      ty_error2 l0 ("invalid argument to disambiguate hom (must be '' or '<terminal>' or '<terminal> <terminal>')") ""
    in
    match es with
    | [] -> Some (":"^name^":", "")
    | [Hom_string s] -> 
        (try match Str.split (Str.regexp "[ \t\n\r]+") s with
          | [] -> Some (":"^name^":", "")
          | [x] -> Some (x, "")
          | [x;y] -> Some (x, y)
          | _ -> err l0
         with _ -> err l0)
    | _ -> err l0
  with Not_found -> None 


let rec cd_hom hu c (es : element list) ((hn,hs,l0):raw_homomorphism): homomorphism =
  debug ("es="^String.concat "#" (List.map Grammar_pp.pp_plain_element es)^"\n");

  let (allowable_homs,s) = List.assoc hu allowable_hom_data in
  if not(List.mem hn allowable_homs) then 
    ty_error2 l0 ("illegal hom \""^hn^"\" for "^s
		  ^"  (the allowable homs here are "
		  ^String.concat ", " allowable_homs^")") "";

  let rec rule_has_terminal (s: string) es = match es with 
    | [] -> false
    | Lang_terminal t :: _ when s = t -> true
    | _::es -> rule_has_terminal s es in

  let rec index_of_ident : raw_ident -> element list -> int -> int
      = fun (l,s) es i -> 
        match es with 
        | [] -> raise Not_found 
        | e::es' -> 
            match e with
            | Lang_nonterm (_,nt) -> 
                if s = Grammar_pp.pp_plain_nonterm nt then i
                else index_of_ident (l,s) es' (i+1)
            | Lang_metavar (_,mv) ->
                if s = Grammar_pp.pp_plain_metavar mv then i
                else index_of_ident (l,s) es' (i+1)
            | Lang_terminal _ ->
                index_of_ident (l,s) es' i
            | Lang_sugaroption _ ->
                index_of_ident (l,s) es' i
            | Lang_option _  -> 
                failwith "homs for prods containing options not implemented"
            | Lang_list _ -> 
                index_of_ident (l,s) es' (i+1) in
  
  let rec filter_e e = match e with
  | Lang_nonterm (_,_) 
  | Lang_metavar (_,_) -> Some e
  | Lang_terminal _ -> None
  | Lang_sugaroption _ 
  | Lang_option _  -> 
      failwith "homs for prods containing options not implemented"
  | Lang_list elb -> 
      Some (Lang_list {elb with elb_es=filter_es elb.elb_es } )
  and filter_es es = Auxl.option_map filter_e es in
                 
  let rec index_of_dotform : element_list_body -> element list -> int -> int
      = fun elb es i -> 
        match es with 
        | [] -> raise Not_found 
        | e::es' -> 
            match e with
            | Lang_nonterm (_,nt) -> 
                index_of_dotform elb es' (i+1)
            | Lang_metavar (_,mv) ->
                index_of_dotform elb es' (i+1)
            | Lang_terminal _ ->
                index_of_dotform elb es' i
            | Lang_sugaroption _ ->
                index_of_dotform elb es' i
            | Lang_option _  -> 
                failwith "homs for prods containing options not implemented"
            | Lang_list elb' -> 
                if elb.elb_boundo=elb'.elb_boundo
                    && filter_es elb.elb_es = filter_es elb'.elb_es
                then i
                else index_of_dotform elb es' (i+1) in

  let rec agglomerate_strings : hom_spec_el list -> string option -> hom_spec_el list =
    fun hses so ->
      match hses,so with
      | [],None -> []
      | [],Some s -> [Hom_string s]
      | Hom_string s :: hses', None -> agglomerate_strings hses' (Some s)
      | Hom_string s :: hses', Some s'->agglomerate_strings hses' (Some (s'^s))
      | hse :: hses', None -> 
          hse :: agglomerate_strings hses' None 
      | hse :: hses', Some s -> 
          Hom_string s:: hse :: agglomerate_strings hses' None in

  let is_blankish =
    let blankish = Str.regexp "\\(\\ \\|\009\\|\012\\)*" in
    function s ->
      (Str.string_match blankish s 0  && Str.match_end () = String.length s) in
  
  let rec cd_hom_el c hse =
    ( match hse with
    | Raw_hom_string s -> Hom_string s
    | Raw_hom_blanks s -> Hom_string s
    | Raw_hom_ident ris ->
	(( try
          let ris' = List.filter (function (l,s) -> not (is_blankish s)) ris in
	  let (id,fvs) = 
	    let t = List.rev ris' in
	    (List.hd t, List.rev (List.tl t)) in
	  ( try
	    let inx = index_of_ident id es 0 in
	    let fvis = List.map (fun id -> index_of_ident id es 0) fvs in
	    if List.length fvs = 0 
	    then Hom_index inx
	    else Hom_ln_free_index (fvis,inx)
	  with Not_found -> 
(* (\* hack to allow explicit indexes, for testing purposes *\) *)
(*               (try Hom_index (int_of_string s) with Failure _ ->  *)
(*                 Hom_terminal s)) *)
(* *)
(* hmm - maybe we should check that this s is in fact one of the terminals *)
(* of the grammar.  But that info isn't to hand (eg in c) at present *)
              if not (rule_has_terminal (snd id) es) then begin
                Auxl.warning ("Free variables in hom element " ^ Grammar_pp.pp_raw_hom_spec_el hse 
                              ^ " at " ^ Location.pp_loc l0)
              end;
              Hom_terminal (snd id) )
	with 
	  Not_found -> ty_error2 l0 
              ( "hom inner must have either a singleton or a dot form in [["
	       ^ String.concat "" (List.map snd ris) ^ "]]")
             "" ))

    | Raw_hom_ident_dots (l0,ris1,n,ris2) -> 
        let reconstructed_string = 
          String.concat "" (List.map snd ris1 @[Grammar_pp.pp_raw_dots n]@ List.map snd ris2) in
        (*print_string ("******"^reconstructed_string^"*******\n");flush stdout;*)
        if not(List.mem hn list_form_allowable_homs) then 
          ty_error2 l0 ("hom \""^hn^"\" cannot refer to a dot form (the only homs here that can are "^String.concat ", " list_form_allowable_homs^")") "";

        let ris1' = List.filter (function (l,s) -> not (is_blankish s)) ris1 in
        let ris2' = List.filter (function (l,s) -> not (is_blankish s)) ris2 in
        let raw_element_of_raw_ident ((l,_) as ri) = Raw_ident (l,ri) in
        let res1 = List.map raw_element_of_raw_ident ris1' in
        let res2 = List.map raw_element_of_raw_ident ris2' in
        let res =  res1 @ [Raw_dots(l0,n)] @ res2 in
        debug(reconstructed_string^"\n");
        debug(String.concat "#" (List.map Grammar_pp.pp_raw_element res));
        let es_inner = cd_elements c res in
        let elb_inner = (match es_inner with
        | [ Lang_list elb ] -> elb
        | _ -> ty_error2 l0 
              ("hom inner [["
               ^ reconstructed_string
               ^ "]] is not a single dot form") "") in
        (match elb_inner.elb_tmo with
        | None -> ()
        | Some tm ->  ty_error2 l0 
              ("hom inner [["
               ^ reconstructed_string
               ^ "]] should not have any terminals (here \""^tm^"\")") "");
        debug (Grammar_pp.pp_plain_element (Lang_list elb_inner)^"\n");
        (try Hom_index (index_of_dotform elb_inner es 0 )
        with Not_found -> ty_error2 l0 
            ("dotform hom inner [["
             ^ reconstructed_string
             ^ "]] not found in production") "")
    | Raw_hom_ident_comp (l0,ris1,rcb) -> 
        let b,ivr = cd_comp_bound c rcb in
        let reconstructed_string = 
          Grammar_pp.pp_COMP_LEFT
          ^ String.concat "" (List.map snd ris1)
          ^ Grammar_pp.pp_COMP_MIDDLE
          ^ Grammar_pp.pp_raw_comp_bound rcb
          ^ Grammar_pp.pp_COMP_RIGHT in
        if not(List.mem hn list_form_allowable_homs) then 
          ty_error2 l0 ("hom \""^hn^"\" cannot refer to a list form (the only homs here that can are "^String.concat ", " list_form_allowable_homs^")") "";

        let ris1' = List.filter (function (l,s) -> not (is_blankish s)) ris1 in
        let raw_element_of_raw_ident ((l,_) as ri) = Raw_ident (l,ri) in
        let res1 = List.map raw_element_of_raw_ident ris1' in
        let res =  res1 in
        debug(reconstructed_string^"\n");
        debug(String.concat "#" (List.map Grammar_pp.pp_raw_element res));
        let es_inner0 = cd_elements c res in
        let es_inner = 
          try
            List.map (Merge.abstract_indexvar_element ivr 0) es_inner0
          with
            Merge.Abstract_indexvar_non_linear -> 
              ty_error2 l0("index \""^ivr^"\" not used linearly in each nonterm and metavar") "" in
        let elb_inner = 
          { elb_boundo = Some b;
            elb_tmo = None;
            elb_es = es_inner } in
        debug (Grammar_pp.pp_plain_element (Lang_list elb_inner)^"\n");
        (try Hom_index (index_of_dotform elb_inner es 0 )
        with Not_found -> ty_error2 l0 
            ("dotform hom inner [["
             ^ reconstructed_string
             ^ "]] not found in production") "")) in

  
  let rec strip_leading_trailing_blanks hs = 
    let rec strip_leading_blanks hs = 
      ( match hs with
      | [] -> []
      | Raw_hom_blanks s :: hs' -> strip_leading_blanks hs'
(*      | Raw_hom_string s :: hs' when is_blankish s -> strip_leading_blanks hs'*)
      | h::hs' -> h::hs') in
    List.rev (strip_leading_blanks (List.rev (strip_leading_blanks hs))) in
  
  (hn, agglomerate_strings (List.map (cd_hom_el c) (strip_leading_trailing_blanks hs)) None)


and cd_homs_icho (c: cd_env) (hs: homomorphism list) : homomorphism list = 
    match hs with 
      | [] -> []
      | (hn,hs)::hs' -> 
          if hn = "ic" then 
            ("isa",hs)::("coq",hs)::(cd_homs_icho c hs') 
          else if hn = "ih" then 
            ("isa",hs)::("hol",hs)::(cd_homs_icho c hs') 
          else if hn = "ch" then 
            ("hol",hs)::("coq",hs)::(cd_homs_icho c hs') 
          else if hn = "ich" then 
            ("isa",hs)::("hol",hs)::("coq",hs)::(cd_homs_icho c hs') 
(*           else if hn = "icht" then  *)
(*             ("isa",hs)::("hol",hs)::("coq",hs)::("twf",hs)::(cd_homs_icho c hs')  *)
          else if hn = "icho" then 
            ("isa",hs)::("hol",hs)::("coq",hs)::("ocaml",hs)::(cd_homs_icho c hs') 
          else if hn = "ichl" then 
            ("isa",hs)::("hol",hs)::("coq",hs)::("lem",hs)::(cd_homs_icho c hs') 
          else if hn = "ichlo" then 
            ("isa",hs)::("hol",hs)::("coq",hs)::("lem",hs)::("ocaml",hs)::(cd_homs_icho c hs') 
          else 
            (hn,hs)::(cd_homs_icho c hs') 

and cd_mse c (mse:raw_mse) : mse =
  ( match mse with
  | Raw_MVorNTExp (_,(_,s)) -> 
      ( match c.ident_lexer s Location.dummy_pos  (* TODO more useful pos *) with
      | OP_Some (Tok_metavar (_,mvr)) -> MetaVarExp mvr
      | OP_Some (Tok_nonterm (_,ntr)) -> NonTermExp ntr
      | _ -> 
          ty_error2 (Auxl.loc_of_raw_mse mse)
            ("MSE: \""^s^"\" is not a metavar or nonterm" ) "")
  | Raw_MVorNTListExp_dotform (_,(_,s1),n,(_,s2)) -> 
      ( match c.ident_lexer s1 Location.dummy_pos,c.ident_lexer s2 Location.dummy_pos  (* TODO more useful pos *) with
      | OP_Some (Tok_metavar (_,mv)),OP_Some (Tok_metavar (_,mv')) -> 
          ( match Merge.merge_metavar n (mv,mv') with
          | (Some b,mv'') -> MetaVarListExp(mv'',b)
          | (None,_) -> 
              ty_error2 (Auxl.loc_of_raw_mse mse)
                ("MSE: no nontrivial bound for metavars "
                 ^ Grammar_pp.pp_plain_metavar mv 
                 ^ " and "
                 ^ Grammar_pp.pp_plain_metavar mv') 
                "")
      | OP_Some (Tok_nonterm (_,nt)),OP_Some (Tok_nonterm (_,nt')) -> 
          ( match Merge.merge_nonterm n (nt,nt') with
          | (Some b,nt'') -> NonTermListExp(nt'',b)
          | (None,_) -> 
              ty_error2 (Auxl.loc_of_raw_mse mse)
                ("MSE: no nontrivial bound for nonterms "
                 ^ Grammar_pp.pp_plain_nonterm nt 
                 ^ " and "
                 ^ Grammar_pp.pp_plain_nonterm nt') 
                "")
      | _ -> 
          ty_error2 (Auxl.loc_of_raw_mse mse)
            ("MSE: not a metavar or nonterm" )
            "")
  | Raw_MVorNTListExp_comp (_,(_,s1),rcb) -> 
      let b,ivr = cd_comp_bound c rcb in
      ( match c.ident_lexer s1 Location.dummy_pos (* TODO more useful pos *) with
      | OP_Some (Tok_metavar (_,(mvr,suff))) -> 
          let suff' = 
            try Merge.abstract_indexvar_suffix_linear ivr 0 suff 
            with Merge.Abstract_indexvar_non_linear -> 
              ty_error2 (Auxl.loc_of_raw_mse mse)
                ("MSE: indexvar \""^ivr
                 ^ "\" does not occur linearly in metavar"
                 ^ Grammar_pp.pp_plain_metavar (mvr,suff)) "" in
          MetaVarListExp((mvr,suff'),b)
      | OP_Some (Tok_nonterm (_,(ntr,suff))) -> 
          let suff' = 
            try Merge.abstract_indexvar_suffix_linear ivr 0 suff 
            with Merge.Abstract_indexvar_non_linear -> 
              ty_error2 (Auxl.loc_of_raw_mse mse)
                ("MSE: indexvar \""^ivr
                 ^ "\" does not occur linearly in nonterm"
                 ^ Grammar_pp.pp_plain_nonterm (ntr,suff)) "" in
          NonTermListExp((ntr,suff'),b)
      | _ -> 
          ty_error2 (Auxl.loc_of_raw_mse mse)
            ("MSE: not a metavar or nonterm" )
            "")
  | Raw_Aux (_,(_,f),(_,nt)) -> 
        (*    print_string ("\nRaw_Aux: "^f^" "^nt^" ");  *)
      ( match c.ident_lexer nt Location.dummy_pos (* TODO more useful pos *) with
      | OP_Some (Tok_nonterm(_,(ntr,suff))) ->  Aux (f,(ntr,suff))
      | _ ->
          ty_error2 (Auxl.loc_of_raw_mse mse)
	    ("MSE: not a nonterm in application of auxiliary " ^ f) "" )
  | Raw_AuxList_dotform (_,(_,f),(_,nt1),n,(_,nt2)) -> 
        (*    print_string ("\nRaw_Aux: "^f^" "^nt^" ");  *)
      ( match c.ident_lexer nt1 Location.dummy_pos,c.ident_lexer nt2 Location.dummy_pos (* TODO more useful pos *) with
      | OP_Some (Tok_nonterm(_,nt)),OP_Some (Tok_nonterm(_,nt')) ->  
          ( match Merge.merge_nonterm n (nt,nt') with
          | (Some b,nt'') -> AuxList (f,nt'',b)
          | (None,_) -> 
              ty_error2 (Auxl.loc_of_raw_mse mse)
                ("MSE: no nontrivial bound for nonterms "
                 ^ Grammar_pp.pp_plain_nonterm nt 
                 ^ " and "
                 ^ Grammar_pp.pp_plain_nonterm nt') 
                "")
      | _ -> 
          ty_error2 (Auxl.loc_of_raw_mse mse)
	    ("MSE: auxiliary " ^ f ^ " applied to a dot form which does not consist of two nonterms") "" )
  | Raw_AuxList_comp (_,(_,f),(_,nt1),rcb) -> 
      let b,ivr = cd_comp_bound c rcb in
      ( match c.ident_lexer nt1 Location.dummy_pos (* TODO more useful pos *) with
      | OP_Some (Tok_nonterm (_,(ntr,suff))) -> 
          let suff' = 
            try Merge.abstract_indexvar_suffix_linear ivr 0 suff 
            with Merge.Abstract_indexvar_non_linear -> 
              ty_error2 (Auxl.loc_of_raw_mse mse)
                ("MSE: indexvar \""^ivr
                 ^ "\" does not occur linearly in nonterm"
                 ^ Grammar_pp.pp_plain_nonterm (ntr,suff)) "" in
          AuxList(f,(ntr,suff'),b)
      | _ -> 
          ty_error2 (Auxl.loc_of_raw_mse mse)
	    ("MSE: auxiliary " ^ f ^ " applied to a list form which does not consist of a nonterm") "" )
  | Raw_Union (_, mse,mse') -> Union (cd_mse c mse , cd_mse c mse')
  | Raw_Empty _ -> Empty )
    
and cd_bindspec c (bs:raw_bindspec) : bindspec =
  ( match bs with    
  | Raw_Bind (_,mse,(_,nt)) -> 
      ( match c.ident_lexer nt Location.dummy_pos  (* TODO more useful pos *) with
      | OP_Some (Tok_nonterm (_,ntr)) -> Bind (cd_mse c mse, ntr) 
      | _ -> 
          ty_error2 (Auxl.loc_of_raw_bindspec bs)
            ("bindspec must have a nonterminal on the right hand side, not \""^nt^"\"") "" )
  | Raw_AuxFnDef(_,(_,f),mse) -> AuxFnDef(f, cd_mse c mse)
  | Raw_NamesEqual(_,mse,mse') -> NamesEqual(cd_mse c mse, cd_mse c mse')
  | Raw_NamesDistinct(_,mse,mse') -> NamesDistinct(cd_mse c mse, cd_mse c mse')
  | Raw_AllNamesDistinct(_,mse) -> AllNamesDistinct(cd_mse c mse) )

and cd_metavarrep c (raw_mvd_name: string) (mvr:raw_metavarrep) : metavarrep =
  List.map 
    (cd_hom Hu_metavar c [Lang_metavar (raw_mvd_name,(raw_mvd_name,[]))])
    mvr

and cd_prod c (rn:string) (pnw:string) (targets:string list) (rule_homs_for_targets:string list) (p:raw_prod) : prod =
  let bracket_commas xl =
    let rec gocomma xl = match xl with 
      | [] -> []
      | [x] -> xl
      | x::xl -> x :: Hom_string "," :: gocomma xl in
    match xl with 
    | []  -> []
    | [x] -> xl 
    | _   -> Hom_string "(" :: gocomma xl @ [Hom_string ")"] in
  let cd_order_normal prod_name homs =
    try 
      let oh = 
	List.filter 
	  (fun h -> match h with Hom_index _ -> true | _ -> false) 
	  (List.assoc "order" homs) in
      let oh_coq = ( "coq", (Hom_string ("("^prod_name))::oh@[Hom_string ")"] ) in
      let oh_isa = ( "isa", (Hom_string ("("^prod_name))::oh@[Hom_string ")"] ) in
      let oh_hol = 
	let of_s = if List.length oh = 0 then "" else " of " in
	( "hol", (Hom_string ("("^prod_name^of_s))::oh@[Hom_string ")"] ) in
      let oh_caml= ( "ocaml", (Hom_string ("("^prod_name))::bracket_commas oh @[Hom_string ")"] ) in
(*      let oh_lem = ( "lem", (Hom_string ("("^prod_name))::bracket_commas oh @[Hom_string ")"] ) in *)
      let oh_lem = ( "lem", (Hom_string ("("^prod_name))::oh@[Hom_string ")"] ) in (* LemTODO25: *)

      homs @ [oh_coq; oh_isa; oh_hol; oh_caml; oh_lem]
    with Not_found -> homs
  in
  let cd_order_funmeta prod_name homs elems =
    let oh = 
      try 
	List.filter 
	  (fun h -> match h with Hom_index _ -> true | _ -> false) 
	  (List.assoc "order" homs) 
      with Not_found ->
	let rec go n l = if n = 0 then l else go (n - 1) (Hom_index (n - 1) :: l) in
        go (List.length 
              (List.filter (function Lang_nonterm _ | Lang_metavar _ -> true | _ -> false)
                 elems)) []
    in
    let oh_coq = ( "coq", (Hom_string ("("^prod_name))::oh@[Hom_string ")"] ) in
    let oh_isa = ( "isa", (Hom_string ("("^prod_name))::oh@[Hom_string ")"] ) in
    let oh_hol = ( "hol", (Hom_string ("("^prod_name))::oh@[Hom_string ")"] ) in
    let oh_lem = ( "lem", (Hom_string ("("^prod_name))::oh@[Hom_string ")"] ) in
    let oh_caml= ( "ocaml", (Hom_string ("("^prod_name))::oh @[Hom_string ")"] ) in
    let oh_ord = ( "order", oh ) in
    List.filter (fun x -> fst x <> "order") homs @ [oh_coq; oh_lem; oh_isa; oh_hol; oh_caml; oh_ord]
  in
  let es = cd_elements c p.raw_prod_es in
  let hu = if rn="terminals" then Hu_prod_tm else Hu_prod in
  let prod_sugar = List.mem "S" (List.map snd p.raw_prod_categories) in
  let prod_meta = prod_sugar || List.mem "M" (List.map snd p.raw_prod_categories) in
  let prod_funmeta = List.mem "F" (List.map snd p.raw_prod_categories) in
  let prod_name = pnw ^ p.raw_prod_name in
  let cd_order homs =
    if prod_funmeta then cd_order_funmeta p.raw_prod_name homs es
    else cd_order_normal prod_name homs
  in
  let hs = cd_order (cd_homs_icho c (List.map (cd_hom hu c es) p.raw_prod_homs)) in
  let p' = 
    { prod_name = prod_name; 
      prod_flavour = p.raw_prod_flavour; 
      prod_meta = prod_meta;
      prod_sugar = prod_sugar;
      prod_categories = List.fold_left (fun s (_,c) -> StringSet.add c s)
                                       StringSet.empty p.raw_prod_categories;
      prod_disambiguate = cd_disambiguate_hom prod_name p.raw_prod_homs hs;
      prod_es = es;
      prod_homs = List.filter (fun (hn,_) -> hn <> "disambiguate") hs;
      prod_bs = List.map (cd_bindspec c) p.raw_prod_bs;
      prod_loc = p.raw_prod_loc } in
  if p'.prod_meta && rn<>"terminals" then begin
    let def_homs = List.map fst p'.prod_homs in
    if List.mem "order" def_homs && not prod_funmeta
    then ty_error2 p.raw_prod_loc ("illegal hom \"order\" in meta or sugar production") "";
    List.iter 
      (function target -> 
        if not (List.mem target def_homs) 
        then ty_error2 p.raw_prod_loc 
            ("meta or sugar production must have a hom for each target - here \""
             ^target^"\" is missing") "") 
      targets;
  end;
(*   if not(p'.prod_meta) then *)
(*     let def_homs = List.map fst p'.prod_homs in *)
(*     if not (List.mem "order" def_homs) then *)
(*       List.iter *)
(* 	(function forbidden_hom -> *)
(* 	  if List.mem forbidden_hom def_homs  *)
(* 	  then ty_error2 p.raw_prod_loc  *)
(*               ("illegal hom \""^forbidden_hom^"\" for non-meta production") "") *)
(* 	["coq";"isa";"hol"]; *)
(*   else (); *)
  p'

and cd_elements c (res:raw_element list) : element list =
    (* find all positions i of a list [x0;...xi; ... xn] such that (p xi) *)
  
  let l =  (* use location of 0th element for error reporting - not ideal *)
    if List.length res >=1 then 
      let re_first = (List.nth res 0) in
      let re_last = (List.nth res (List.length res -1)) in
      let l_first,l_last = Auxl.loc_of_raw_element re_first, Auxl.loc_of_raw_element re_last in
      Location.merge_locs l_first l_last 
    else 
      dummy_loc in

  let sres = List.map (cd_element c) res in

  let find_all_indices p xs =
    let rec f n xs = 
      ( match xs with 
      | []-> []
      | x::xs -> if p x then n::f (n+1) xs else f (n+1) xs ) in
    f 0 xs in

  let dot_indices = 
    find_all_indices 
      ( fun re -> 
	( match re with
	| Sr_dots _ -> true
	| Sr_el _ -> false ) )
      sres in 

  let len = List.length sres in

  let rec sublist n i xs = (* n elements starting from i *) 
    if n=0 then [] else List.nth xs i :: sublist (n-1) (i+1) xs in

  let nodots : semiraw_element list -> element list =
    function sres' -> List.map 
        (function sre -> 
          match sre with
          | Sr_el e -> e 
          | Sr_dots _ -> raise (Invalid_argument "nodots: overlapping dots") )
        sres' in
  
  let dot_form_extent : int -> (int * int * element)
      = fun d ->
        if (d<=0 || d>=len-1)  then
          ty_error2 
            (Auxl.loc_of_raw_element (List.nth res d) )
            "dot form at left or right end" 
            "";

        let dotminlength = match List.nth sres d with
        | Sr_dots n -> n
        | _ -> raise ThisCannotHappen in
        
        let terminal_separated =  
          ( match List.nth sres (d-1), List.nth sres (d+1) with
	  | (Sr_el(Lang_terminal tm)), (Sr_el(Lang_terminal tm')) ->
              tm=tm'
          | _ -> false ) in

	let rec merge_sublist n i j = 
          let sublistl0 = sublist n i sres in
          let sublistu0 = sublist n j sres in
          let sublistl,sublistu =
            try
              nodots(sublistl0),nodots(sublistu0)
            with
              Invalid_argument _ -> raise (Merge.Merge "dots") in
          let (bo,es) = Merge.merge_element_list dotminlength (sublistl,sublistu) in
          (bo,es) in

        let merge_each_side n =
          if terminal_separated 
	  then merge_sublist n (d-1-n) (d+2) 
	  else merge_sublist n (d-n) (d+1) in

        let max_possible_same_each_side = 
	  if terminal_separated 
	  then min (d-1) (len-d-1-1) 
	  else min (d) (len-d-1) in
        
	let rec max_same_each_side n = 
	  try (n,merge_each_side n)
          with Merge.Merge _ -> max_same_each_side (n-1) in
        
        let width,(bo,es')= max_same_each_side max_possible_same_each_side in
        if (width<=0) then
          ty_error2 
            (Auxl.loc_of_raw_element (List.nth res d) )
	    "dot form has no non-empty identical sequence on each side (perhaps due to a missing indexvar declaration)" 
            "";
        
        if terminal_separated then 
          let tm = 
	    ( match (List.nth sres (d-1)) with 
	    | Sr_el(Lang_terminal tm) -> tm
	    | _ -> raise ThisCannotHappen ) in
          (d-1-width,      (* left end *)
           d+1+width+1,    (* right end + 1 *)
           Lang_list 
             { elb_boundo = bo;
               elb_tmo = Some tm;
               elb_es = es' (* List.map cd_element c (sublist width (d-1-width) es)*) })
        else
          (d-width,
           d+width+1,
           Lang_list 
             { elb_boundo = bo;
               elb_tmo = None;
               elb_es = es'(*List.map cd_element c (sublist width (d-width) es)*)})
  in
  let dot_form_extents = List.map dot_form_extent dot_indices in

    (* walk along es gluing together the dot form extents and the normal *)
    (* elements inbetween, looking for overlaps *)
  let rec process_es : int -> (int*int*element) list -> element list
      = fun i extents ->
        match extents with
        | [] -> (*List.map cd_element*) nodots(sublist (len-i) i sres) 
        | (left,right,e)::extents' -> 
            if (left < i) then
              ty_error2 
                (Auxl.loc_of_raw_element(List.nth res i) )
	        "overlapping dot forms" 
                "";
              (*List.map cd_element*) nodots(sublist (left-i) i sres) 
            @ [e]
            @ process_es right extents' in
  let es = process_es 0 dot_form_extents in
  
  (* check that no non-empty bound is repeated *)
  let ne_bo_of_elements es = 
    Auxl.option_map 
      (function e -> match e with
      | Lang_list elb -> elb.elb_boundo
      | _ -> None)
      es in
  (match Auxl.find_first_duplicate (ne_bo_of_elements es) with
  | None -> ()
  | Some b -> 
      ty_error2 
        l 
        ("bound "^Grammar_pp.pp_plain_bound b^" used for multiple dot forms in production") 
        "");

  (*check that there is no empty bound (debatable whether we always want this)*)
  if List.exists
      (function e -> match e with
      | Lang_list elb when elb.elb_boundo = None -> true
      | _ -> false)
      es
  then
    ty_error2
      l 
      ("empty bound in dot form in production")
      ""
  else ();

  (*check that there is no repeated nonterm or metavar (debatable whether we always want this)*)
  let nts = Auxl.nts_list_used_in_es es in
  (match Auxl.find_first_duplicate nts with
  | None -> ()
  | Some (ntr_primary,nt_as_written,pe) -> 
      ty_error2 l ("repeated nonterminal \""^Grammar_pp.pp_plain_nonterm nt_as_written^"\" in production") "");
  let mvs = Auxl.mvs_list_used_in_es es in
  (match Auxl.find_first_duplicate mvs with
  | None -> ()
  | Some (mvr_primary,mv_as_written,pe) -> 
      ty_error2 l ("repeated metavar \""^Grammar_pp.pp_plain_metavar mv_as_written^"\" in production") "");


  es
    
    

and cd_element c (e:raw_element) : semiraw_element =
  (* print_string ("cd_element: \""^Grammar_pp.pp_raw_element e^"\"\n");flush stdout; *)
  match e with
  | Raw_ident (l,(_,i)) -> 
        (* print_string ("i=\""^i^"\"\n");flush stdout; *)
      ( match c.ident_lexer i Location.dummy_pos  (* TODO more useful pos *)  with
      | OP_Some (Tok_metavar(_,(mvr,suffix))) -> 
	  Sr_el(Lang_metavar ((try c.primary_mvr_of_mvr mvr with Not_found -> Auxl.int_error "mvr not found in cd_element"), (mvr,suffix)))
      | OP_Some (Tok_nonterm(_,(ntr,suff))) -> 
          (* print_string ("+++++++"^ntr^"++++++\n");flush stdout; *)
	  (*let x = *)Sr_el(Lang_nonterm (c.primary_ntr_of_ntr ntr,(ntr,suff))) (*in*)
          (*print_string ("++++---"^ntr^"++++++\n");flush stdout;x *)
(*       | Some (Tok_terminal _ ) -> raise ThisCannotHappen *)
(*       | Some (Tok_dots _ ) -> raise ThisCannotHappen *)
(*       | Some (Tok_otherident (p,i)) -> Sr_el(Lang_terminal i) *)
      | OP_Many toks -> 
          ty_error2 l("raw ident \""^i^"\" has multiple lexes: "^String.concat " " (List.map Grammar_pp.pp_plain_mytoken toks)) ""
      | OP_None -> Sr_el(Lang_terminal i ))
(*   | Raw_option (_,es) -> Sr_el(Lang_option (cd_elements c es)) *)
(*   | Raw_list (_,es) ->  *)
(*       Sr_el(Lang_list  *)
(*               {elb_boundo = None; *)
(*                elb_tmo = None; *)
(*                elb_es = cd_elements c es}) *)
(*   | Raw_nelist (_,es) ->  *)
(*       Sr_el(Lang_list  *)
(*               {elb_boundo = None;  (\* TODO: should record it non-empty *\) *)
(*                elb_tmo = None; *)
(*                elb_es = cd_elements c es}) *)
(*   | Raw_sugaroption (_,e) ->  *)
(*       ( match (cd_element c e) with *)
(*       | Sr_el(Lang_terminal t) -> Sr_el(Lang_sugaroption t) *)
(*       | _ ->  *)
(*           ty_error2  *)
(*             (Auxl.loc_of_raw_element e ) *)
(*             "non terminal in optional sugar"  *)
(*             "" ) *)
  | Raw_dots (_,n) -> Sr_dots n
  | Raw_comp(l,res,rcb,rio) -> 
      let b,ivr = cd_comp_bound c rcb in
      let tmo = match rio with None -> None | Some (_,tm) -> Some tm in
      let es = cd_elements c res in
      let es' = 
        try
          List.map (Merge.abstract_indexvar_element ivr 0) es 
        with
          Merge.Abstract_indexvar_non_linear -> 
            ty_error2 l("index \""^ivr^"\" not used linearly in each nonterm and metavar") "" in
      let elb = { elb_boundo = Some b;
                  elb_tmo = tmo;
                  elb_es = es' } in
      Sr_el(Lang_list elb)
  | (Raw_sugaroption (_, _)|Raw_nelist (_, _)|Raw_list (_, _)|Raw_option (_, _))
      -> Auxl.error "internal: sugaroption, nelist, list and option not supported"

and cd_comp_bound : cd_env -> raw_comp_bound -> bound * metavarroot
    = fun c rcb -> match rcb with
    | Raw_bound_comp(l,(_,ivr)) -> 
        if not(List.mem ivr c.all_indexvar_synonyms) then
          ty_error2 l ("\""^ivr^"\" used as an index but not declared as an indexvar") "";
        Bound_comp {bc_variable=ivr},ivr
    | Raw_bound_comp_u(l,(_,ivr),(_,ivr_u)) ->  
        if not(List.mem ivr c.all_indexvar_synonyms) then
          ty_error2 l ("\""^ivr^"\" used as an index but not declared as an indexvar") "";
        if not(List.mem ivr_u c.all_indexvar_synonyms) then
          ty_error2 l ("\""^ivr_u^"\" used as an upper bound but not declared as an indexvar") "";
        Bound_comp_u {bcu_variable=ivr;bcu_upper=Si_var (ivr_u,0)} ,ivr
    | Raw_bound_comp_lu(l,(_,ivr),(_,foo_l),n,(_,ivr_u)) -> 
        if not(List.mem ivr c.all_indexvar_synonyms) then
          ty_error2 l ("\""^ivr^"\" used as an index but not declared as an indexvar") "";
(*         let ao = Lexicalgoo.decompose_fancy_indexvar c.all_indexvar_synonyms ivr_u in *)
        let ao = Term_parser.one_parse (Term_parser.parse_lu_upperbound c.all_indexvar_synonyms) ivr_u in 
        let siv = 
          (match ao with
          | OP_None -> 
              ty_error2 l ("\""^ivr_u^"\" used as an upper bound but not declared as an indexvar") ""
          | OP_Many sivs -> 
              ty_error2 l ("\""^ivr_u^"\" has multiple lexes: "^String.concat " " (List.map Grammar_pp.pp_plain_suffix_item  sivs)) ""
          | OP_Some siv -> siv) in
        let lo = Term_parser.one_parse (Term_parser.parse_lu_lowerbound) foo_l in 
        match lo with 
        | OP_None ->  
            ty_error2 l ("\""^foo_l^"\" used as a lower bound but not a literal number") ""
        | OP_Many ss -> 
            ty_error2 l ("\""^foo_l^"\" has multiple lexes: "^String.concat " " (List.map (fun s->s) ss)) ""
        | OP_Some _ -> ();
(*       if not(List.mem (foo_l c.all_indexvar_synonyms) then *)
(*         ty_error2 l ("\""^foo_l^"\" used as a lower bound but not declared as an indexvar") ""; *)
        Bound_comp_lu {bclu_variable=ivr;bclu_lower=Si_num foo_l;bclu_upper=siv;bclu_length=n} , ivr


        
and cd_subrule c (sr:raw_subrule) : subrule =
  (* for each Subrule or Contextrule, look up the primary ntrs involved *)
  try
    { sr_lower = c.primary_ntr_of_ntr sr.raw_sr_lower;
      sr_upper = c.primary_ntr_of_ntr sr.raw_sr_upper;
      sr_top = "dummy";
      sr_homs = List.map (cd_hom Hu_subrule c []) sr.raw_sr_homs;  (* TODO is that [] sensible? *)
      sr_loc = sr.raw_sr_loc }
  with
    Not_found -> 
      ty_error2 
        (Auxl.loc_of_raw_subrule sr)
        ("undefined nonterminal root ("^sr.raw_sr_lower^" or "^sr.raw_sr_upper^") used in subgrammar declaration")
        ""

and cd_subrules c (rsrs:raw_subrule list) : subrule list * subrule_data=
  let srs0 = List.map (cd_subrule c) rsrs in

  (* calculate the transitive closure of the subrule relationship *)
  let nodes0 = Auxl.remove_duplicates (List.flatten (List.map (fun sr -> [sr.sr_lower;sr.sr_upper]) srs0)) in
  
  let edges0 = ntrpairsetoflist 
      (List.map
         (fun sr -> (sr.sr_lower,sr.sr_upper)) srs0) in

  (* the closure function that we want a fixed point of *)
  let f : NtrPairSet.t -> NtrPairSet.t =
    fun ntrpairs0 ->
      let ntrpairs1 = NtrPairSet.elements ntrpairs0 in
      let new_edges =
        List.flatten 
          (List.map (fun (ntr,ntr') -> 
            Auxl.option_map (fun (ntr'',ntr''') -> 
              if ntr'=ntr'' then Some (ntr,ntr''') else None) ntrpairs1) ntrpairs1) in
      NtrPairSet.union ntrpairs0 (ntrpairsetoflist new_edges) in
  
  let rec fixedpoint : (NtrPairSet.t -> NtrPairSet.t) -> NtrPairSet.t -> NtrPairSet.t =
    fun f x ->
      let x' = f x in
      if NtrPairSet.equal x x' then x' else f x' in

  let tc_edges = NtrPairSet.elements (fixedpoint f edges0) in

  (* report error if there is a cycle *)
  let ntrs_in_cycles = Auxl.option_map (fun (ntr,ntr') -> if ntr=ntr' then Some ntr else None) tc_edges in
  if ntrs_in_cycles <> [] then 
      ty_error ("subrule order has a cycle containing: "^String.concat " " (List.map (fun ntr -> "\""^Grammar_pp.pp_plain_nontermroot ntr^"\"") ntrs_in_cycles)) "";

  let top_nodes = List.filter (fun ntr -> not (List.exists (fun (ntr',ntr'')-> ntr=ntr') tc_edges )) nodes0 in

  let tops_above ntr = Auxl.option_map (fun (ntr',ntr'') -> if ntr'=ntr &&  List.mem ntr'' top_nodes then Some ntr'' else None) tc_edges in

  List.iter 
    (fun ntr -> match tops_above ntr with [] | [_] -> () | ntrs -> 
      ty_error ("subrule order has multiple tops above \""^ntr^"\", ie "^String.concat " " (List.map (fun ntr -> "\""^Grammar_pp.pp_plain_nontermroot ntr^"\"") ntrs)) "") 
    nodes0;
      
  let promote_to_top ntr = 
    if List.mem ntr top_nodes then 
      ntr
    else
      snd (List.find (fun (ntr',ntr'') -> ntr'=ntr &&  List.mem ntr'' top_nodes) tc_edges) in
  
  let srs1 = List.map (fun sr -> {sr with sr_top = promote_to_top sr.sr_upper }) srs0 in

  let (psd : proper_subntr_data) = List.map (fun ntr -> ntr,Auxl.option_map (fun (ntr',ntr'')-> if ntr=ntr'' then Some ntr' else None) tc_edges) nodes0 in

  srs1,
  {srd_proper_subntr_data=psd;
   srd_subrule_graph=tc_edges;
   srd_subrule_pn_promotion = [] (* this is a placeholder, filled in by the subrule testing after we've built a preliminary xd *)}





and cd_contextrule c (cr:raw_contextrule) : contextrule =
  try
    { cr_ntr = c.primary_ntr_of_ntr cr.raw_cr_ntr;
      cr_target = c.primary_ntr_of_ntr cr.raw_cr_target;
      cr_hole = c.primary_ntr_of_ntr cr.raw_cr_hole;
      cr_homs = List.map (cd_hom Hu_deadcode c []) cr.raw_cr_homs; (* TODO is that [] sensible? *)
      cr_loc = cr.raw_cr_loc }
  with
    Not_found -> 
      ty_error2 
        (Auxl.loc_of_raw_contextrule cr)
        "undefined nonterminal root used in context rule declaration"
        ""
and cd_subst c (srs:subrule list) (subst:raw_subst) : subst =
  let l = (Auxl.loc_of_raw_subst subst) in
  let this = 
    try c.primary_ntr_of_ntr subst.raw_sb_this 
    with Not_found -> 
        ty_error2 l ("undefined nonterminal root \""^subst.raw_sb_this^"\" used in substitution declaration")"" in
  if List.exists (fun sr -> sr.sr_lower = this) srs then
    ty_error2 l
      ("nonterminal root \""^subst.raw_sb_this^"\" of a subrule used in substitution declaration") "";
  let that = 
    try Mvr(c.primary_mvr_of_mvr subst.raw_sb_that) 
    with Not_found -> 
      try 
        let ntr = c.primary_ntr_of_ntr subst.raw_sb_that in
        if List.exists (fun sr -> sr.sr_lower = ntr) srs then
          ty_error2 l
            ("nonterminal root \""^subst.raw_sb_that^"\" of a subrule used in substitution declaration") "";
        Ntr ntr
      with Not_found -> 
        ty_error2 l ("undefined nonterm or metavar root \""^subst.raw_sb_that^"\" used in substitution declaration")"" in
  let sb_homs = List.map (cd_hom Hu_subst c []) subst.raw_sb_homs in
  let subst'=
    { sb_name = subst.raw_sb_name;
      sb_this = this;
      sb_that = that;
      sb_multiple = subst.raw_sb_multiple;
      sb_homs = sb_homs;
      sb_loc = l }
  in subst'
    
and cd_freevar c (srs:subrule list) (fv:raw_freevar) : freevar =
  let l = fv.raw_fv_loc in
  let this = 
    try c.primary_ntr_of_ntr fv.raw_fv_this 
    with Not_found -> 
        ty_error2 l ("undefined nonterminal root \""^fv.raw_fv_this^"\" used in freevar declaration")"" in
  if List.exists (fun sr -> sr.sr_lower = this) srs then
    ty_error2 l
      ("nonterminal root \""^fv.raw_fv_this^"\" of a subrule used in freevar declaration") "";
  let that = 
    try Mvr(c.primary_mvr_of_mvr fv.raw_fv_that) 
    with Not_found -> 
      try 
        let ntr = c.primary_ntr_of_ntr fv.raw_fv_that in
        if List.exists (fun sr -> sr.sr_lower = ntr) srs then
          ty_error2 l
            ("nonterminal root \""^fv.raw_fv_that^"\" of a subrule used in freevars declaration") "";
        Ntr ntr
      with Not_found -> 
        ty_error2 l ("undefined nonterm or metavar root \""^fv.raw_fv_that^"\" used in freevars declaration")"" in
  let fv_homs = List.map (cd_hom Hu_freevar c []) fv.raw_fv_homs in
  { fv_name = fv.raw_fv_name;
    fv_this = this;
    fv_that = that;
    fv_homs = fv_homs;
    fv_loc = l }
    
and cd_embeds c (rel:raw_embed list) : embed list =
  let allowed (l,hn,es) =
    if not(List.mem hn embed_allowable_homs)
    then ty_error2 l ("illegal hom \""^hn^"\" for embed (the allowable homs here are "
		  ^String.concat ", " embed_allowable_homs^")") ""
  in
  List.iter allowed rel;
  List.map Auxl.collapse_embed rel

and cd_parsing_annotation all_prod_names (par:raw_parsing_annotations) : parsing_annotation list =
  let check_prod_name raw_pn = 
    if not (List.mem raw_pn all_prod_names) then 
      ty_error2 
        (Auxl.loc_of_raw_parsing_annotation par)
        ("undefined prodname \""^raw_pn^"\" used in parsing annotation declaration")
        "" in
  List.map 
      (fun (raw_pn1,pa,raw_pn2) -> 
        check_prod_name raw_pn1;
        check_prod_name raw_pn2;
        (raw_pn1, pa, raw_pn2)) 
    par.raw_pa_data
    
and cd_parsing_annotations c pars =
  { pa_data = List.flatten (List.map (cd_parsing_annotation c) pars); }
(*     pa_loc = dummy_loc } *)

(* check_and_disambiguate ********************************************** *)
let check_structure (xd:syntaxdefn) (str:structure) : unit =

  (* check that the dependencies are compatible with the source structure *)

  (* 1- for all Struct_rs entries, 
        check that all the dependencies preceed the entry in the source structure *)
  let deps = xd.xd_dep in

  let rec check_rs seen tosee dep_graph =
    match tosee with
    | [] -> 
	()
    | (fn,(Struct_rs rg))::stres ->
	(* for all r in rg, verify that all its deps are in rg or in seen *)
	let rec int_check_rg rgseen rgtosee =
	  ( match rgtosee with
	  | [] -> ()
	  | r::rs -> 
	      if not ((Auxl.rule_of_ntr xd r).rule_semi_meta)
	      then begin
		let r_deps = 
		  (List.assoc (Ntr r) dep_graph) in
		List.iter
		  (fun rd ->
		    match rd with 
		    | Mvr _ -> ()
		    | Ntr rd -> 
			if not (List.mem rd (rgtosee@rgseen)) 
			then ty_error ("rule \""^r^"\" depends on rule \"" ^rd
				       ^"\" which belongs to a future group of rules.\n") "")
		  r_deps; 
	      end;
	      int_check_rg (r::rgseen) rs)
	in 
	int_check_rg seen rg;
	check_rs (rg@seen) stres dep_graph
    | stre::stres -> 
	check_rs seen stres dep_graph
  in
  List.iter (fun (_,dep) -> check_rs [] str (dep.xd_dep_graph_nontran)) deps

      (* (\* error check: if a group mentions a rule not in rs, *\) *)
      (* (\* complain about recursion between non-adiacent rule definitions *\) *)
      (* (\* FZ: this should be in grammar_typecheck, not here *\) *)
      (* if List.for_all  *)
      (* 	  (fun rg ->  *)
      (* 	    List.for_all  *)
      (* 	      ( fun ntmvr -> match ntmvr with  *)
      (* 	      | Mvr _ -> true  *)
      (* 	      | Ntr ntr -> List.mem ntr ntrs_rs)  *)
      (* 	      rg) *)
      (* 	  relevant_deps *)
      (* then relevant_deps *)
      (* else Auxl.error "recursion between non-adjacent rule definitions" *)



(** This constructs an internal representation of a grammar from a raw
    representation, typechecking the grammar on the way *)
let rec check_and_disambiguate (generate_aux_rules:bool) (targets:string list) (source_filenames:string list) (merge_fragments:bool)  (ris_per_file:raw_item list list)
    : syntaxdefn * structure * raw_fun_or_reln_defnclass list =

  (* now we have in our hand the new ris_per_file that preserves the
  source-file ordering information that we can use in the new
  order-respecting output.  More precisely, the source structure
  informations are stored in the xd structure field. *)

  (* synthesise aux rules *)
  let ris_per_file = if generate_aux_rules then List.map (List.map auxify_rules) ris_per_file else ris_per_file in


  (* rebuild old raw type (rsds) from new raw type (ris) *)
  let (rsd_per_file:raw_syntaxdefn list list) = List.map (List.map rsd_of_ri) ris_per_file in

  (* TODO: for tidyiness, the following code should be rewritten to
  use ris directly rather than via the old-type stuff involving rsds;
  then we can remove the above line *)

  let show_inferred_auxfn_typing = false in
  let show_subrule_data = false in

  (* 1- collect together the metavariable, grammar and definition items *)

  let rsd_per_file_2 = (List.map (fun rsd_part -> concat_language_fragments_per_file rsd_part) rsd_per_file) in

  let rsd = concat_language_fragments rsd_per_file_2 in

  let rsd = if merge_fragments then merge_language_fragments rsd else rsd in

  (* 2- synthesise additional grammar items from the definitions for 
        the syntax of judgements *)

  let sd_prod_of_defn (d:raw_defn) : raw_prod =
    { raw_prod_name = d.raw_d_name;
      raw_prod_flavour = Bar;
      raw_prod_categories = d.raw_d_categories;
      raw_prod_es = d.raw_d_es;
      raw_prod_homs = List.filter (function (hn,_,_) -> hn <> "lemwcf") d.raw_d_homs;
      raw_prod_bs = [];
      raw_prod_loc = d.raw_d_loc } in

  let lang_rule_of_defnclass (dc:raw_defnclass) : raw_rule =
    { raw_rule_ntr_name = dc.raw_dc_name;
      raw_rule_ntr_names = [dc.raw_dc_name,[]];
      raw_rule_pn_wrapper = dc.raw_dc_wrapper;
      raw_rule_ps = List.map sd_prod_of_defn dc.raw_dc_defns;
      raw_rule_homs = [];
      raw_rule_categories = ["defnclass"];
      raw_rule_loc = dc.raw_dc_loc } in

  let defn_sd_prod_of_fundefn (fd:raw_fundefn) : raw_prod =
    { raw_prod_name = fd.raw_fd_name;
      raw_prod_flavour = Bar;
      raw_prod_categories = []; (* fd.raw_fd_categories; *)
      raw_prod_es = fd.raw_fd_es @ [ Raw_ident (dummy_loc,(dummy_loc,"===")); Raw_ident (dummy_loc,fd.raw_fd_result) ];
      raw_prod_homs = List.filter (function (hn,_,_) -> not (List.mem hn ["coq-struct"])) fd.raw_fd_homs;
      raw_prod_bs = [];
      raw_prod_loc = fd.raw_fd_loc } in

  let defn_lang_rule_of_fundefnclass (fdc:raw_fundefnclass) : raw_rule =
    { raw_rule_ntr_name = fdc.raw_fdc_name;
      raw_rule_ntr_names = [fdc.raw_fdc_name,[]];
      raw_rule_pn_wrapper = "fundefn_";
      raw_rule_ps = List.map defn_sd_prod_of_fundefn fdc.raw_fdc_fundefns;
      raw_rule_homs = [];
      raw_rule_categories = ["fundefnclass"];
      raw_rule_loc = fdc.raw_fdc_loc } in

  let lang_rule_of_fun_or_reln_defnclass (frdc:raw_fun_or_reln_defnclass) : raw_rule =
    match frdc with
    | Raw_FDC fdc -> defn_lang_rule_of_fundefnclass fdc
    | Raw_RDC dc -> lang_rule_of_defnclass dc in

  let add_extra_lang_rules rsd = { rsd with raw_sd_rs = rsd.raw_sd_rs @ List.map lang_rule_of_fun_or_reln_defnclass rsd.raw_sd_dcs } in

  let judgement_nontermroots = 
(*(*    List.flatten (List.map (fun r -> List.map fst r.raw_rule_ntr_names) extra_lang_rules) in*)*)
(*    (List.map (fun r -> r.raw_rule_ntr_name) extra_lang_rules) in *)
    Auxl.option_map (fun frdc -> 
      match frdc with
      | Raw_FDC fdc -> None
      | Raw_RDC dc -> Some dc.raw_dc_name)
      rsd.raw_sd_dcs in




(*   let usage_lang_rule_of_fundefnclass (fdc:raw_fundefnclass) : raw_rule = *)
(*     { raw_rule_ntr_name = fdc.raw_fdc_name; *)
(*       raw_rule_ntr_names = [fdc.raw_fdc_name,[]]; *)
(*       raw_rule_pn_wrapper = fdc.raw_fdc_wrapper; *)
(*       raw_rule_ps = List.map usage_sd_prod_of_fundefn fdc.raw_fdc_fundefns; *)
(*       raw_rule_homs = [];    *)
(*       raw_rule_categories = ["fundefnclass"]; *)
(*       raw_rule_loc = fdc.raw_fdc_loc } in *)


(* Add an extra production for function usage to the right (existing) rule: *)
(* take the raw_rule's and the raw_fun_or_reln_defnclass's. For each *)
(* fundefn, check that there's a rule with the right name, synthesise a *)
(* function usage production to add to the rule, and update the fundefn *)
(* to record the rule name and the rule_pn_wrapper (so that given a *)
(* fundefn we'll later be able to build the appropriate production name) *)

(*  Kathy's bug notes that if you want to define a function with a result *)
(*  nonterm that isn't maximal in the subrule order (eg "v"), then we *)
(*  should add a production to that nonterm and all its super-nonterms, *)
(*  otherwise the subrule check fails.  Restricting to functions that are *)
(*  only allowed to have maximal nonterms as their result types is *)
(*  v. annoying, as you then can't use them in the v grammar.  There's a *)
(*  hacky workaround, which is to manually add function-usage productions *)
(*  to the supergrammars. *)

  let usage_sd_prod_of_fundefn (fd:raw_fundefn) : raw_prod =
    { raw_prod_name = fd.raw_fd_name;
      raw_prod_flavour = Bar;
      raw_prod_categories = [(dummy_loc,"M"); (dummy_loc,"F")]; (* fd.raw_fd_categories; *) (* FUNTODO:  M ? *)
      raw_prod_es = fd.raw_fd_es;
      raw_prod_homs = List.filter (function (hn,_,_) -> not (List.mem hn ["coq-struct"])) fd.raw_fd_homs;  
      raw_prod_bs = [];
      raw_prod_loc = fd.raw_fd_loc } in

  let add_extra_lang_usage_prods rsd =
    let rec extra_lang_usage_prods (rs:raw_rule list) (frdcs:raw_fun_or_reln_defnclass list)  : raw_fun_or_reln_defnclass list * (nontermroot * raw_prod) list =
      match frdcs with
      | [] -> [],[]
      | frdc::frdcs' ->
          let frdcs'',extra_prods = extra_lang_usage_prods rs frdcs' in
          match frdc with
          | Raw_RDC dc ->
              frdc::frdcs'',extra_prods
          | Raw_FDC fdc ->
              let extra_prods',fds' =
                List.split
                  (List.map
                     (function fd ->
                       let r =
                         try
                           List.find
                             (fun r -> List.mem (snd fd.raw_fd_result) (List.map fst r.raw_rule_ntr_names))
                             rs
                         with
                           Not_found -> ty_error2 fd.raw_fd_loc ("function result \""^snd fd.raw_fd_result^"\" must be a nonterminal root") ""
                       in
                       (r.raw_rule_ntr_name, usage_sd_prod_of_fundefn fd),
                       {fd with
                        raw_fd_result_type=r.raw_rule_ntr_name;
                        raw_fd_pn_wrapper=r.raw_rule_pn_wrapper }
                     )
                     fdc.raw_fdc_fundefns) in
              Raw_FDC {fdc with raw_fdc_fundefns = fds'} :: frdcs'', extra_prods'@extra_prods in
    
    
    let frdcs',extra_prods = extra_lang_usage_prods rsd.raw_sd_rs rsd.raw_sd_dcs in

    let rs' = 
      List.map
        (fun r ->
          let extra_prods = Auxl.option_map (fun (ntr,rp)->if ntr=r.raw_rule_ntr_name then Some rp else None) extra_prods in
          {r with raw_rule_ps = r.raw_rule_ps @ extra_prods }
        )
        rsd.raw_sd_rs in
  
    { rsd with raw_sd_rs=rs'; raw_sd_dcs=frdcs' } in

    
(*     let extra_lang_usage_prods  : (nontermroot * raw_prod) list =  *)
(*       List.flatten  *)
(*         (List.map  *)
(*            (fun frdc -> *)
(*              match frdc with  *)
(*              | Raw_FDC fdc -> List.map (fun fd -> (snd fd.raw_fd_result, usage_sd_prod_of_fundefn fd)) fdc.raw_fdc_fundefns *)
(*              | Raw_RDC dc -> []) *)
(*            frdcs) in *)




(*   let add_in_extra_lang_usage_prods (rs:raw_rule list) (frdcs:raw_fun_or_reln_defnclass list) : raw_rule list = *)
    
(*     let extra_lang_usage_prods  : (nontermroot * raw_prod) list =  *)
(*       List.flatten  *)
(*         (List.map  *)
(*            (fun frdc -> *)
(*              match frdc with  *)
(*              | Raw_FDC fdc -> List.map (fun fd -> (snd fd.raw_fd_result, usage_sd_prod_of_fundefn fd)) fdc.raw_fdc_fundefns *)
(*              | Raw_RDC dc -> []) *)
(*            frdcs) in *)
(*     List.map  *)
(*       (fun r -> *)
(* (\* FUNTODO: the below should match up to _primary_ ntrs *\) *)
(*         let extra_prods = Auxl.option_map (fun (ntr,rp)->if List.mem ntr (List.map fst r.raw_rule_ntr_names) then Some rp else None) extra_lang_usage_prods in *)
(*         {r with raw_rule_ps = r.raw_rule_ps @ extra_prods } *)
(*       )  *)
(*       rs in *)




  (* 3a- synthesise the formula judgement, if needed *)
  
  let formula : raw_rule list =
    
    if List.exists
	(fun r -> (String.compare r.raw_rule_ntr_name "formula") = 0) 
	rsd.raw_sd_rs
    then []
    else
      [ { raw_rule_ntr_name = "formula";
	  raw_rule_ntr_names = ["formula",[]];
	  raw_rule_pn_wrapper = "formula_";
	  raw_rule_ps = [ { raw_prod_name = "judgement";
			    raw_prod_flavour = Bar;
			    raw_prod_categories = [];
			    raw_prod_es = [Raw_ident (dummy_loc,(dummy_loc,"judgement"))];
			    raw_prod_homs = [];
			    raw_prod_bs = [];
			    raw_prod_loc = dummy_loc } ];
	raw_rule_homs = [];
	raw_rule_categories = ["formula"];
	raw_rule_loc = dummy_loc } ] in
   
  (* 3b- synthesise a grammar of all judgements *)

  let prod_of_root ntr = 
    { raw_prod_name = ntr;
      raw_prod_flavour = Bar;
      raw_prod_categories = [];
      raw_prod_es = [Raw_ident (dummy_loc,(dummy_loc,ntr))];
      raw_prod_homs = [];
      raw_prod_bs = [];
      raw_prod_loc = dummy_loc } in

  let judgement : raw_rule =
    { raw_rule_ntr_name = "judgement";
      raw_rule_ntr_names = ["judgement",[]; (*"J",[]*)];
      raw_rule_pn_wrapper = "judgement_";
      raw_rule_ps = List.map prod_of_root judgement_nontermroots;
      raw_rule_homs = [];
      raw_rule_categories = ["judgement"];
      raw_rule_loc = dummy_loc } in

  (* 3c- synthesise a grammar of all user syntax *)

  let user_syntax_nontermroots = 
(*    List.flatten (List.map (fun r -> List.map fst r.raw_rule_ntr_names) rsd.raw_sd_rs) in *)
    (List.map (fun r -> r.raw_rule_ntr_name) rsd.raw_sd_rs) in

  let user_syntax_metavarroots = 
(*    List.flatten (List.map (fun md -> List.map fst md.raw_mvd_names) rsd.raw_sd_mds) in*)
    (List.map (fun md -> md.raw_mvd_name) rsd.raw_sd_mds) in

  let user_syntax : raw_rule =
    { raw_rule_ntr_name = "user_syntax";
      raw_rule_ntr_names = ["user_syntax",[]];
      raw_rule_pn_wrapper = "user_syntax__";
      raw_rule_ps = List.map prod_of_root (user_syntax_metavarroots @ user_syntax_nontermroots);
      raw_rule_homs = [];
      raw_rule_categories = ["user_syntax"];
      raw_rule_loc = dummy_loc } in
  
  let rsd' =      
    { rsd with    
      raw_sd_rs = rsd.raw_sd_rs@formula } in   

  let rsd' = add_extra_lang_usage_prods rsd' in

  let rsd' = add_extra_lang_rules rsd' in

  let rsd' =      
    { rsd' with    
      raw_sd_rs = rsd'.raw_sd_rs @ [judgement] @ [user_syntax] } in   

  debug ( "\nSynthesised raw language:\n"
	  ^  Grammar_pp.pp_raw_syntaxdef rsd'^"\n\n" );

  (* 3d- append the homs from any extra hom sections onto the relevant *)
  (* productions and definitions *)

  let (collected_extra_homs : raw_extra_homs list) =
    List.flatten 
      (List.map
         (function rhs -> 
           List.map (function rhsi-> 
             (rhs.raw_hs_wrapper^rhsi.raw_hsi_name,
              (rhsi.raw_hsi_bs,rhsi.raw_hsi_homs))) 
             rhs.raw_hs_hsis)
         rsd'.raw_sd_hss) in

  let rec fst_map f (xs,y) = (* (f:'a * 'b -> 'a * 'b) ((xs,y):'a list * 'b) : 'a list * 'b = *)
    match xs with 
    | [] -> [],y
    | x::xs1 -> 
        let (x',y')= f (x,y) in
        let (xs1'',y'') = fst_map f (xs1,y') in
        (x'::xs1'',y'') in

  let append_homs_prod : string -> raw_prod * raw_extra_homs list -> raw_prod * raw_extra_homs list =
    function pn_wrapper -> function (rp,rehs) -> 
      let (rehs1,rehs2)= 
        List.partition (function (s,_) -> s = pn_wrapper^rp.raw_prod_name) rehs in
      let homs_for_this_prod = 
        List.flatten (List.map (function (s,(rbs,rhs))->rhs) rehs1) in
      let bs_for_this_prod = 
        List.flatten (List.map (function (s,(rbs,rhs))->rbs) rehs1) in
      { rp with 
        raw_prod_homs = rp.raw_prod_homs @ homs_for_this_prod;
        raw_prod_bs = rp.raw_prod_bs @ bs_for_this_prod;
      }, rehs2 in
  
  let append_homs_rule : raw_rule * raw_extra_homs list -> raw_rule * raw_extra_homs list =
    function (rr,rehs) ->
      let (rps',rehs') = 
        fst_map (append_homs_prod rr.raw_rule_pn_wrapper) (rr.raw_rule_ps,rehs) in
      { rr with raw_rule_ps = rps' }, rehs' in

  let append_homs_rules : raw_rule list * raw_extra_homs list -> raw_rule list * raw_extra_homs list =
    fst_map append_homs_rule in

  let append_homs_defn : string -> raw_defn * raw_extra_homs list -> raw_defn * raw_extra_homs list =
    function dc_wrapper -> function (rd,rehs) -> 
      let (rehs1,rehs2)= 
        List.partition (function (s,_) -> s = dc_wrapper^rd.raw_d_name) rehs in
      let homs_for_this_defn = 
        List.flatten (List.map (function (s,(rbs,rhs))->rhs) rehs1) in
      let bs_for_this_defn = 
        List.flatten (List.map (function (s,(rbs,rhs))->rbs) rehs1) in

      if bs_for_this_defn <> [] then failwith ("cannot have a bindspec for a defn (in a hom section)"); (* TODO add location data to that error *)
      { rd with 
        raw_d_homs = rd.raw_d_homs @ homs_for_this_defn;
      }, rehs2 in
  
  let append_homs_defnclass : raw_defnclass * raw_extra_homs list -> raw_fun_or_reln_defnclass * raw_extra_homs list =
    function (rdc,rehs) ->
      let (rds',rehs') = 
        fst_map (append_homs_defn rdc.raw_dc_wrapper) (rdc.raw_dc_defns,rehs) in
      Raw_RDC { rdc with raw_dc_defns = rds' }, rehs' in

  let append_homs_fundefn : raw_fundefn * raw_extra_homs list -> raw_fundefn * raw_extra_homs list =
    function (rfd,rehs) -> 
      let (rehs1,rehs2)= 
        List.partition (function (s,_) -> s = rfd.raw_fd_name) rehs in
      let homs_for_this_fundefn = 
        List.flatten (List.map (function (s,(rbs,rhs))->rhs) rehs1) in
      let bs_for_this_fundefn = 
        List.flatten (List.map (function (s,(rbs,rhs))->rbs) rehs1) in

      if bs_for_this_fundefn <> [] then failwith ("cannot have a bindspec for a fundefn (in a hom section)"); (* TODO add location data to that error *)
      { rfd with 
        raw_fd_homs = rfd.raw_fd_homs @ homs_for_this_fundefn;
      }, rehs2 in

  let append_homs_fundefnclass : raw_fundefnclass * raw_extra_homs list -> raw_fun_or_reln_defnclass * raw_extra_homs list =
    function (rfdc,rehs) ->
      let (rfds',rehs') = 
        fst_map (append_homs_fundefn) (rfdc.raw_fdc_fundefns,rehs) in
      Raw_FDC { rfdc with raw_fdc_fundefns = rfds' }, rehs' in

  let append_homs_fun_or_reln_defnclass : raw_fun_or_reln_defnclass * raw_extra_homs list -> raw_fun_or_reln_defnclass * raw_extra_homs list =
    function (rfrdc,rehs) -> match rfrdc with
    | Raw_FDC rfdc -> append_homs_fundefnclass (rfdc,rehs)
    | Raw_RDC rdc -> append_homs_defnclass (rdc,rehs) in

  let append_homs_fun_or_reln_defnclasss =
    fst_map append_homs_fun_or_reln_defnclass in

  let (raw_sd_rs',rehs') = append_homs_rules (rsd'.raw_sd_rs, collected_extra_homs) in

  let (raw_sd_dcs',rehs'') = append_homs_fun_or_reln_defnclasss (rsd'.raw_sd_dcs, rehs') in

  if rehs'' <> [] then failwith ("hom section contains items for nonexistent production or defn names: "^String.concat ", " (List.map fst rehs'')) (* TODO add location data to that error *);

  let rsd' =       
    { rsd' with raw_sd_rs = raw_sd_rs'; raw_sd_dcs=raw_sd_dcs' } in   



(* TODO: as part of grammar well-formedness we should check:

- all suffixed nontermroots, suffixed metavarroots and terminals are
  pairwise disjoint regexps
- all nontermroots and metavarroots are idents (this is enforced by
  grammar_lexer.mll)
- all terminals are either idents or strings that do not contain
  blanks and do not have an ident prefix (equivalently, do not start
  with a letter [A-Z]\\|[a-z]
- the user-defined rules, except "formula", do not mention any of the
  synthesised judgement nonterminals, or indeed "formula".
- substitutions are only for generate_free_type ntrs *)

  (* 4- collect together all the primary metavar roots *)
  
  (* make an association list of metavar roots - primary to the synonyms *)
  let mvrs_assoc : (metavarroot * metavarroot list) list =
    List.map (fun md -> md.raw_mvd_name, (List.map fst md.raw_mvd_names)) rsd'.raw_sd_mds in
  (* and one in the other direction *)
  let mvrs_assoc_op : (metavarroot * metavarroot) list =
    List.concat 
      (List.map (function (mvr_p,mvrs) -> 
	List.map (fun mvr' -> (mvr',mvr_p)) mvrs) mvrs_assoc) in
  let primary_mvr_of_mvr mvr = 
    (*print_string ("<<"^Grammar_pp.pp_plain_metavarroot mvr^">>\n");flush stdout; *)
    List.assoc mvr mvrs_assoc_op in

  (* collect together all the (primary or synonym) metavar roots, antisorted *)
(*  let mvrs_all = 
    List.sort 
      (fun a -> fun b -> compare b a) 
      (List.concat (List.map (fun md -> (List.map fst md.raw_mvd_names)) rsd'.raw_sd_mds)) in *)
  let mvrs_nonindex = 
    List.sort 
      (fun a -> fun b -> compare b a) 
      (List.concat 
         (List.map 
            (fun md -> (List.map fst md.raw_mvd_names)) 
            (List.filter (function md->not md.raw_mvd_indexvar) rsd'.raw_sd_mds))) in
  let mvrs_index = 
    List.sort 
      (fun a -> fun b -> compare b a) 
      (List.concat 
         (List.map 
            (fun md -> (List.map fst md.raw_mvd_names)) 
            (List.filter (function md->md.raw_mvd_indexvar) rsd'.raw_sd_mds))) in
  
  (* 5- collect together all the primary nonterminal roots *)

  (* make an association list of nonterminal roots - primary to the synonyms *)
  let ntrs_assoc : (nontermroot * nontermroot list) list =
    List.map 
      (fun rr -> rr.raw_rule_ntr_name, (List.map fst rr.raw_rule_ntr_names)) 
      rsd'.raw_sd_rs in
  (* and one in the other direction *)
  let ntrs_assoc_op : (nontermroot * nontermroot) list =
    List.concat 
      (List.map (function (ntr_p,ntrs) ->
	List.map (fun ntr' -> (ntr',ntr_p)) ntrs) ntrs_assoc) in
(*  print_string ("ntrs_assoc_op =\n "^String.concat "\n" (List.map (function (ntr1,ntr2) -> ntr1 ^"|-> " ^ ntr2) ntrs_assoc_op)^"\n");flush stdout; *)
  let primary_ntr_of_ntr ntr = List.assoc ntr ntrs_assoc_op in
  (* collect together all the (primary or synonym) nonterm roots, antisorted *)
  let ntrs_all = 
    List.sort 
      (function a -> function b -> compare b a) 
      (List.concat (List.map 
		      (fun rr -> (List.map fst rr.raw_rule_ntr_names)) 
		      rsd'.raw_sd_rs)) in
  (* collect together all the nontermroots, primaried, that occur on the left of a <::  *)
  let wrapped_primary_ntr_of_ntr ntr = try
    primary_ntr_of_ntr ntr 
  with
  | Not_found -> ty_error ("\""^ntr^"\" in subrule declaration is not a nonterminal root ") "" in
  let srs_lowers = List.map (fun sr -> (wrapped_primary_ntr_of_ntr sr.raw_sr_lower)) rsd'.raw_sd_srs in
(*  let srs_uppers = List.map (fun sr -> (wrapped_primary_ntr_of_ntr sr.raw_sr_upper)) rsd'.raw_sd_srs in *)
  
  (* 6- make a preliminary ident_lexer that doesn't know about any terminals *)

  (*  let (_,ident_lexer) = Lexicalgoo.make_ident_lexer mvrs_nonindex mvrs_index ntrs_all [] in*)

  let ident_lexer = Term_parser.make_ident_lexer mvrs_nonindex mvrs_index ntrs_all in

  (* an ident is a terminal iff it can't be lexed by the above.  this is *)
  (* used in the dotdot processing - really (for style and efficiency) *)
  (* we should disambiguate all the idents before doing that... *)

(*   let isterminal s = *)
(* (*     if not (Str.string_match Lexicalgoo.ident s 0 && *) *)
(* (*             Str.match_end () = String.length s)  *) *)
(* (*     then true *) *)
(* (*     else  *) *)
(*      ( match ident_lexer s Location.dummy_pos  with *)
(*       | OP_Some (Tok_nonterm _ )  -> false *)
(*       | OP_Some (Tok_metavar _ )  -> false *)
(* (*       | Some (Tok_terminal _ ) -> raise ThisCannotHappen *) *)
(* (*       | Some (Tok_otherident _) -> true *) *)
(* (*       | Some (Tok_dots _) -> false *) *)
(*       | OP_Many _ -> false *)
(*       | OP_None -> true ) in *)

  let c =
    { ident_lexer = ident_lexer;
      primary_mvr_of_mvr = primary_mvr_of_mvr;
      primary_ntr_of_ntr = primary_ntr_of_ntr;
      all_indexvar_synonyms = mvrs_index;
    } in


  (* 8- define the remaining raw_x -> x conversion functions *)
  let rec cd_rule c (r:raw_rule) : rule =
    let rule_semi_meta = 
      (    List.mem "defnclass" r.raw_rule_categories
         || List.mem "fundefnclass" r.raw_rule_categories
         || r.raw_rule_ntr_name = "judgement"
         || r.raw_rule_ntr_name = "formula"
         || r.raw_rule_ntr_name = "terminals"
         || r.raw_rule_ntr_name = "user_syntax" ) in
    let rule_judgement = 
      List.mem r.raw_rule_ntr_name judgement_nontermroots in

    let rule_homs = cd_homs_icho c 
        (List.map 
           (cd_hom (if rule_semi_meta then Hu_rule_meta else Hu_rule) c 
              [Lang_nonterm (r.raw_rule_ntr_name,(r.raw_rule_ntr_name,[]))]) 
           r.raw_rule_homs) in
    let rule_homs = 
      if r.raw_rule_ntr_name = "formula" then
        [("coq", [Hom_string "Prop"]); ("hol", [Hom_string "bool"]); 
         ("lem", [Hom_string "bool"]);
         ("isa", [Hom_string "bool"]); ("ocaml", [Hom_string "bool"])] 
      else rule_homs in
    
    let rule_homs_for_targets = List.filter (function s -> List.mem s targets) (List.map fst rule_homs) in
    let rule_phantom = (try let _ = List.assoc "phantom" rule_homs in true with Not_found -> r.raw_rule_ntr_name = "formula") in

    { rule_ntr_name = r.raw_rule_ntr_name;
      rule_ntr_names = List.map 
        (function s,rhoms -> (s, List.map (cd_hom Hu_root c []) rhoms)) 
        r.raw_rule_ntr_names; 
      rule_pn_wrapper = r.raw_rule_pn_wrapper;
      rule_ps = List.map (cd_prod c r.raw_rule_ntr_name r.raw_rule_pn_wrapper targets rule_homs_for_targets) r.raw_rule_ps;
      rule_homs = rule_homs;
      rule_meta = 
      ( rule_semi_meta
      || List.mem r.raw_rule_ntr_name srs_lowers
      || rule_phantom ) ;
      rule_semi_meta =  rule_semi_meta;
      rule_phantom = rule_phantom;
      rule_judgement = rule_judgement;
      rule_loc = r.raw_rule_loc } in

  (* 9- build a preliminary syntax defn, without dependencies or auxfns *)

  (* embed preamble are those embeds labeled by tex-preamble *)
  let raw_embed_preamble = 
    Auxl.option_map
      (fun (l,hn,he) ->
         match hn with
         | "tex-preamble" -> Some (l,"tex",he)
         | "tex-wrap-pre"
         | "tex-wrap-post" -> Some (l,hn,he)
         | _              -> None) 
      rsd'.raw_sd_embed in

  (* calculate additional file names that the Isabelle header should include (isa-import) *)
  let raw_isa_imports = 
    let get_string r e = match e with
      | Embed_string(_,s) -> s :: r
      | Embed_inner _ -> r in
    List.rev 
      (List.fold_left
        (fun r (l,hn,he) ->
           match hn with
           | "isa-import" -> List.fold_left get_string r he
           | _            -> r) 
        [] rsd'.raw_sd_embed) in
   
  let xd =
    let srs,srd = cd_subrules c rsd'.raw_sd_srs in
    let rs = List.map (cd_rule c) rsd'.raw_sd_rs in
    let all_prod_names = List.flatten (List.map (fun r -> List.map (fun p->p.prod_name) r.rule_ps) rs) in
    { xd_mds = List.map 
	(fun (mvd:raw_metavardefn) -> 
	  let mvd_rep = cd_metavarrep c mvd.raw_mvd_name mvd.raw_mvd_rep in 
	  let ln =
	    try let _ = List.assoc "repr-locally-nameless" mvd_rep in true 
	    with Not_found -> false in 
	  { mvd_name = mvd.raw_mvd_name; 
	    mvd_names = List.map
              (function s,rhoms->(s,List.map (cd_hom Hu_root c []) rhoms))
              mvd.raw_mvd_names; 
	    mvd_rep = if ln then ("coq",[(Hom_string "var")])::mvd_rep else mvd_rep;
            mvd_indexvar = mvd.raw_mvd_indexvar;
	    mvd_locally_nameless = ln;
	    mvd_phantom = 
	      if ln && (String.compare mvd.raw_mvd_name "var" = 0) 
	      then true (* FZ HACK to avoid var = var definition in locally nameless *) 
	      else (try let _ = List.assoc "phantom" mvd_rep in true with Not_found -> false);
	    mvd_loc = mvd.raw_mvd_loc;
          } ) 
	rsd'.raw_sd_mds;
      xd_rs = rs;
      xd_dep = List.map (fun x -> (x,empty_dependencies)) ("ascii"::targets);
      xd_srs = srs;
      xd_srd = srd;
      xd_crs = List.map (cd_contextrule c) rsd'.raw_sd_crs;
      xd_axs = [];  (* this is overridden by something more sensible below *)
      xd_sbs = List.map (cd_subst c srs) rsd'.raw_sd_sbs;
      xd_fvs = List.map (cd_freevar c srs) rsd'.raw_sd_fvs;
      xd_embed_preamble = cd_embeds c raw_embed_preamble;
      xd_embed = cd_embeds c rsd'.raw_sd_embed;
      xd_isa_imports = raw_isa_imports;
      xd_pas = cd_parsing_annotations all_prod_names rsd'.raw_sd_pas;
    } in

  (*  - pull the names of defined auxiliary functions, paired with the *)
  (*    primary ntrs that they operate on, from the non-meta rules of the grammar *)
  (*    (recall non-meta excludes rules that appear on the left of a subrule decl) *)

  (* TODO: should check the bindspecs are consistent across subrules *)

  let rec extract_auxfns_bindspec ntr b = 
    ( match b with
    | Bind (mse,nt) -> []
    | AuxFnDef (f,mse) -> [(f,ntr)]
    | NamesEqual (mse,mse') -> []
    | NamesDistinct (mse,mse') -> []
    | AllNamesDistinct (mse) -> [] )
            
  and extract_auxfns_production ntr p = 
    Auxl.setlist_list_union 
      (List.map (extract_auxfns_bindspec ntr) (p.prod_bs))
          
  and extract_auxfns_rule r = 
    Auxl.setlist_list_union 
      (List.map 
         (extract_auxfns_production r.rule_ntr_name) 
         r.rule_ps)
          
  and extract_auxfns_syntaxdefn sd =
    let auxfns0 = Auxl.setlist_list_union 
	(List.map extract_auxfns_rule 
           (List.filter (fun r -> not r.rule_meta) xd.xd_rs)) in
    let comp (f,ntr) (f',ntr') = 
      let x = String.compare f f' in
      if x <> 0 then x else compare ntr ntr' in
    List.sort comp auxfns0 in

  let (auxfns : (auxfn * nontermroot) list) = extract_auxfns_syntaxdefn xd in

   (* print_string "extracted auxfns:\n"; *)
   (* List.iter (function (f,ntr) -> print_string (f^": "^ntr^" -> "^"?"^"\n")) auxfns; *)

  (* 10- check the syntax defn *)

  (* TODO: typecheck resulting productions (depending on the fact that
     the extract_ functions have already performed some sanity checks
     - we should really decouple these) *)

  let nt_in_es (x:nontermroot*nonterm*prod_env) (es:element list) : bool =
    (* print_string ("<<<"^Grammar_pp.pp_plain_nts_elem x^"   "^Grammar_pp.pp_plain_ntset (Auxl.nts_used_in_es es)^">>>");flush stdout; *)
    NtSet.mem x (Auxl.nts_set_used_in_es es) in

  let mv_in_es (x:metavarroot*metavar*prod_env) (es:element list) : bool =
    MvSet.mem x (Auxl.mvs_set_used_in_es es) in

  (* check all production names are distinct *)
  let all_prod_names = List.flatten (List.map (function r -> (List.map (function p -> p.prod_name,p.prod_loc) r.rule_ps)) xd.xd_rs) in
  let rec find_first_duplicate2 pnls = 
    match pnls with
    | (pn,l)::pnls' -> 
        (try 
          let l' = List.assoc pn pnls' in
          ty_error ("production name \""^pn^"\" is used for multiple productions, at "^Location.pp_loc l^" and "^Location.pp_loc l') ""
        with Not_found ->
          find_first_duplicate2 pnls')
    | [] -> () in
  find_first_duplicate2 all_prod_names;


  (* check sanity properties and accumulate type constraints on aux fns *)
  let rec t_mse ntr (es : element list) mse (l : loc) : mse_type =
    match mse with
    | MetaVarExp ((mvr,suff) as mv) ->
	if not (mv_in_es (Auxl.primary_mvr_of_mvr xd mvr,mv,[]) es) 
        then 
          ty_error2 
            l
            ( "metavariable " 
              ^ Grammar_pp.pp_metavar error_opts xd mv
	      ^ " in MSE not in scope" )
            "t_mse MetaVarExp";
        [ Mse_ty_ntmvr (Mvr(Auxl.primary_mvr_of_mvr xd mvr)) ]
    | NonTermExp ((ntr,suff) as nt) ->
        if not(nt_in_es (Auxl.primary_ntr_of_ntr xd ntr,nt,[]) es)
        then 
          ty_error2
            l
            ( "nonterminal " ^ Grammar_pp.pp_nonterm error_opts xd nt
	      ^ " in MSE not in scope" )
            "t_mse NonTermExp";
        [ Mse_ty_ntmvr (Ntr(Auxl.primary_ntr_of_ntr xd ntr)) ]
    | MetaVarListExp ((mvr,suff) as mv,b) -> 
	if not(mv_in_es (Auxl.primary_mvr_of_mvr xd mvr,mv,[(Some b)]) es) 
        then
          ty_error2 
            l
            ( "Metavariable " ^ Grammar_pp.pp_metavar error_opts xd mv
	      ^ " in MSE not in scope" )
            "t_mse MetaVarListExp";
        [ Mse_ty_ntmvr (Mvr(Auxl.primary_mvr_of_mvr xd mvr)) ]
    | NonTermListExp ((ntr,suff) as nt,b) -> 
        if not(nt_in_es (Auxl.primary_ntr_of_ntr xd ntr,nt,[(Some b)]) es) 
        then 
          ty_error2 
            l
            ( "Nonterminal " ^ Grammar_pp.pp_nonterm error_opts xd nt
	      ^ " in MSE not in scope" )
            "t_mse NonTermListExp";
        [ Mse_ty_ntmvr (Ntr(Auxl.primary_ntr_of_ntr xd ntr)) ]
    | Aux (f,((ntr,suff) as nt)) ->
        (* print_string ("\nt_mse Aux: "^f^" "^ntr'^"\n");   *)
        if not (nt_in_es (Auxl.primary_ntr_of_ntr xd ntr,nt,[]) es) 
        then 
          ty_error2 
            l
            ( "Nonterminal " ^ Grammar_pp.pp_nonterm error_opts xd nt
	      ^" in MSE not in scope")
            "t_mse Aux 1";
(* this seems bogus duplication of the one below? *)
(*         tcheck3'' (List.exists (fun (f'',ntr'') -> f=f'' && ntr'=ntr'') auxfns) l *)
(*           ( "Auxiliary " ^ f ^ " in MSE not defined for nonterminal root "  *)
(* 	    ^ Grammar_pp.pp_nontermroot error_opts xd ntr') "t_mse Aux2" ; *)
        if not (List.exists
                     (fun (f'',ntr'') -> f=f'' && Auxl.promote_ntr xd (primary_ntr_of_ntr ntr)=ntr'')
                     auxfns) 
        then
          ty_error2
            l
            ( "Auxiliary " ^ f ^ " in MSE not defined over nonterminal root "
	      ^ Grammar_pp.pp_nontermroot error_opts xd ntr )
	    "t_mse Aux3";
        [ Mse_ty_aux f ]
    | AuxList (f,((ntr,suff) as nt),b) -> 
        (* print_string ("\nt_mse Aux: "^f^" "^ntr'^"\n");   *)
        if not (nt_in_es (Auxl.primary_ntr_of_ntr xd ntr,nt,[(Some b)]) es) 
        then
          ty_error2
            l
            ( "nonterminal " ^ Grammar_pp.pp_nonterm error_opts xd nt
	      ^" in MSE not in scope")
            "t_mse AuxList 1";
(* this seems bogus duplication of the one below? *)
(*         tcheck3'' (List.exists (fun (f'',ntr'') -> f=f'' && ntr'=ntr'') auxfns) l *)
(*           ( "Auxiliary " ^ f ^ " in MSE not defined for nonterminal root "  *)
(* 	    ^ Grammar_pp.pp_nontermroot error_opts xd ntr') "t_mse Aux2" ; *)
        if not(List.exists
                     (fun (f'',ntr'') -> f=f'' && Auxl.promote_ntr xd (primary_ntr_of_ntr ntr)=ntr'')
                     auxfns)
        then
          ty_error2
            l
            ( "auxiliary " ^ f ^ " in MSE not defined over nonterminal root "
	      ^ Grammar_pp.pp_nontermroot error_opts xd ntr )
	    "t_mse AuxList3";
        [ Mse_ty_aux f ]
    | Union(mse,mse') -> t_mse ntr es mse l @ t_mse ntr es mse' l
    | Empty -> []

  and t_bindspec ntr (es : element list) (l : loc) (b : bindspec) : mse_type = 
    match b with
    | Bind(mse,((ntr,suff) as nt)) -> 
        let mse_ty = (t_mse ntr es mse l) in
        if not (nt_in_es (Auxl.primary_ntr_of_ntr xd ntr,nt,[]) es) 
        then 
          ty_error2 
            l
            ( "nonterminal " ^ Grammar_pp.pp_nonterm error_opts xd nt 
	      ^ " in MSE not in scope" ) 
            "t_bindspec Bind";
        (* forbid manifestly null mse's so that all mses seen later have a unique type *)
        let rec is_null_mse mse = match mse with
        | MetaVarExp (mv) -> false
        | NonTermExp (nt) -> false
        | Aux (f,nt) -> false
        | MetaVarListExp (mv,b) -> false
        | NonTermListExp (nt,b) -> false
        | AuxList (f,nt,b) -> false
        | Union(mse,mse') -> is_null_mse mse && is_null_mse mse'
        | Empty -> true in
        if (is_null_mse mse)
        then 
          ty_error2
            l
            "manifestly null mse"  
            "t_bindspec Bind2";
        mse_ty 
    | AuxFnDef(f,mse) -> 
        let mse_ty = t_mse ntr es mse l in
        (Mse_ty_aux f)::mse_ty 
    | NamesEqual(mse,mse') -> t_mse ntr es mse l @ t_mse ntr es mse' l
    | NamesDistinct(mse,mse') -> t_mse ntr es mse l @ t_mse ntr es mse' l
    | AllNamesDistinct(mse) -> t_mse ntr es mse l

      (* there is no t_element as anything that isn't recognised as a nonterminal or
      metavar is treated as a terminal *)

  and t_prod_non_rule_meta (ntr:nontermroot) (p:prod) : mse_type list =
    (* TODO: if we're doing uniqueness checking (which we should be if we're generating *)
    (* any isa or coq functions that depend on it) walk over *)
    (*   mvs_list_used_in_es p.prod_es *)
    (*   nts_list_used_in_es p.prod_es *)
    (* checking for repeated metavars/nonterms,  un-indexed metavars/nonterms inside lists, etc *)

    if p.prod_meta then
      (if ([]<> p.prod_bs)
      then 
        ty_error2 
          p.prod_loc
          "nonempty bindspec in a meta or sugar production"
          "";
       [])
    else (
      let mse_tys = List.map Auxl.remove_duplicates
          (List.map (t_bindspec ntr p.prod_es p.prod_loc) p.prod_bs) in
      let rec fs_actually_here bs = 
        ( match bs with
        | [] -> []
        | b :: bs -> 
	    ( match b with
            | AuxFnDef(f,mse) -> f :: fs_actually_here bs
            | _ -> fs_actually_here bs ) ) in
      let fs_should_be_here = 
        List.map fst (List.filter (fun (f',ntr') -> ntr=ntr') auxfns) in          
      if (List.sort compare (fs_actually_here p.prod_bs) <>
	       List.sort compare fs_should_be_here)  
      then 
        ty_error
          ("auxiliaries are not uniquely defined in production " ^ p.prod_name) 
          "t_production 1";
      mse_tys);

(*     let mvs = option_map  *)
(*         (fun e ->  *)
(* 	  ( match e with  *)
(* 	  | Lang_metavar (mvr_p,mvr_aw) -> Some mvr_aw *)
(* 	  | _ -> None )) p.prod_es in *)
(*     let nts = option_map  *)
(*         (fun e ->  *)
(* 	  ( match e with  *)
(* 	  | Lang_nonterm (ntr_p,ntr_aw) -> Some ntr_aw *)
(* 	  | _ -> None )) p.prod_es in *)

(*             (match firstdup mvs with  *)
(*               None -> ()  *)
(*             | Some mv -> tcheck' false  ("Repeated metavariable "^Grammar_pp.pp_metavar m mv^" in production "^p.prod_name) "t_production 2"); *)
(*             match firstdup nts with  *)
(*               None -> ()  *)
(*             | Some nt -> tcheck' false  ("Repeated nonterminal "^Grammar_pp.pp_nonterm m nt^" in production "^p.prod_name) "t_production 2"  *)

  and t_rule (r:rule) : mse_type list =
    let ns = List.map (fun p -> p.prod_name) r.rule_ps in
    ( match firstdup ns with 
    | None -> () 
    | Some x -> ty_error ("Repeated production name \"" ^ x^"\"") "t_productions 1");
    let mse_tys = 
      if r.rule_meta 
      then []
      else List.flatten 
          (List.map (t_prod_non_rule_meta r.rule_ntr_name) r.rule_ps) in
    mse_tys in

  (* perform the above checks and accumulate all the type constraints on aux fns *)  
  let mse_tys = List.flatten (List.map t_rule xd.xd_rs) in 

  (* omit null constraints *)
  let mse_tys' = List.filter 
      (function mse_ty -> match mse_ty with
      | [] -> false
      | [_] -> false
      | _ -> true)
      mse_tys in
  (* let _ = print_string (Grammar_pp.pp_plain_mse_tys mse_tys') in *)

  (* Now: (1) build the `transitive closure' of mse_tys', identifying *)
  (* any two lists that contain the same auxfn. (2) remove duplicates in *)
  (* each list.  (3) if any list contains either zero or more than one *)
  (* Mse_ty_ntmvr then raise an error, for an unconstrained or *)
  (* overconstrained auxfn.  (4) store in xd the `type' of each auxfn. *)

  (* create a graph with a node for each auxfn name and an edge between any *)
  (* two nodes that occur in the same type constraint *)

  let g = G.create () in

  let rec add_vertices xs n acc = match xs with
  | [] -> acc
  | f::fs -> 
      let v=G.V.create n in
      G.add_vertex g v; 
      add_vertices fs (n+1) ((f,n,v)::acc) in

  let auxfn_names = Auxl.remove_duplicates 
      (List.map (function (f,ntr)->f) auxfns) in

  let vertex_info =  add_vertices auxfn_names 0 [] in

  let vertex_of_auxfn f = List.assoc f 
      (List.map (function(f,n,v)->f,v) vertex_info) in

  let auxfn_of_vertex v = List.assoc v 
      (List.map (function(f,n,v)->v,f) vertex_info) in
  
  let edge_data = List.map
      (Auxl.option_map
         (function mse_tyi -> match mse_tyi with
         | Mse_ty_ntmvr _ -> None
         | Mse_ty_aux f -> Some f))
      mse_tys' in
  
  let add_product_edges fs =
    List.iter (function f1 ->
      List.iter (function f2 ->
        let v_f1 = vertex_of_auxfn f1 in
        let v_f2 = vertex_of_auxfn f2 in
        G.add_edge g v_f1 v_f2)
        fs)
      fs in

  (* add all product edges *)
  List.iter add_product_edges edge_data;

  (* and add any missing reflexive_edges *)
  List.iter (function f1 ->
    let v_f1 = vertex_of_auxfn f1 in
    G.add_edge g v_f1 v_f1)
    auxfn_names;
  
  (* now compute the strongly connected components of g *)
  let (scc_vertex_sets : G.V.t list list) = G.Components.scc_list g in

  (* for each component collect all the associated Mse_ty_ntmvr from mse_tys'*)
  let is_associated  (vs : G.V.t list) (mse_ty : mse_type_item list) : bool =
    List.exists 
      (function v -> List.mem (Mse_ty_aux (auxfn_of_vertex v)) mse_ty) vs in

  let ntmvrs_of_component (vs : G.V.t list) : nt_or_mv_root list =
    Auxl.remove_duplicates
      (Auxl.option_map
         (function mse_tyi -> match mse_tyi with
         | Mse_ty_ntmvr ntmvr -> Some ntmvr
         | Mse_ty_aux _ -> None)
         (List.concat (List.filter (is_associated vs) mse_tys'))) in

  (* raise an error for any non-singletons, otherwise record the result *)
  let components_with_ntmvr : (G.V.t list * nt_or_mv_root) list =
    List.map (function vs ->
      let ntmvrs = ntmvrs_of_component vs in
      match ntmvrs with
      | [ntmvr] -> (vs,ntmvr)
      | [] -> ty_error (
          "auxfns "
          ^ String.concat " " (List.map (function v->auxfn_of_vertex v) vs)
          ^ " have unconstrained result type") ""
      | _ -> ty_error (
          "auxfns "
          ^ String.concat " " (List.map (function v->auxfn_of_vertex v) vs)
          ^ " have overconstrained result type: "
          ^ String.concat " "(List.map Grammar_pp.pp_plain_nt_or_mv_root ntmvrs
                             )) "")
      scc_vertex_sets in
  
  (* and put in the proper form for the collected types of all auxfns *)
  let axs = List.map
      (function f ->
        let v = vertex_of_auxfn f in
        let ntmvr = snd
            (List.find 
               (function (vs,ntmvr) -> List.mem v vs) 
               components_with_ntmvr) in
        let ntrs = Auxl.option_map 
            (function (f',ntr')-> if f'=f then Some ntr' else None) 
            auxfns in
        (f,(ntrs,ntmvr)))
      auxfn_names in

  (* hack for testing purposes: hardcoded value for test5 *)
(*  let axs = if mse_tys'= [ [Mse_ty_aux "bo"; Mse_ty_ntmvr(Mvr "x")] ] then ["bo",(["pat"],Mvr "ident")] else [] in *)

  if show_inferred_auxfn_typing then (
    print_string "inferred auxfn typing:\n";
    List.iter (function (f,(ntrs,ntmvr)) -> print_string (
      f ^": "
      ^ String.concat " " (List.map Grammar_pp.pp_plain_nontermroot ntrs)
      ^ " -> "
      ^ Grammar_pp.pp_plain_nt_or_mv_root ntmvr
      ^ "\n"))
      axs); 

  let xd = { xd with xd_axs = axs } in

(* hack: to allow repeated secondary nonterm roots, comment out the second of these *)
  let ns = List.flatten 
      (List.map (fun r -> List.map fst r.rule_ntr_names) xd.xd_rs) in
  ( match firstdup ns with 
  | None -> () 
  | Some v -> ty_error ("repeated rule name "^v^"") "t_grammar 1");
  
  (* check that subrules don't involve any semi-meta rules. *)
  (* TODO: should also check that they don't involve any rules with type homs *)

  let nodes0 = Auxl.remove_duplicates (List.flatten (List.map (fun sr -> [sr.sr_lower;sr.sr_upper]) xd.xd_srs)) in
  List.iter 
    (fun ntr -> 
      if (Auxl.rule_of_ntr xd ntr).rule_semi_meta 
      then ty_error ("cannot have semi-meta rule \""^ntr^"\" in a subrule relationship") "") 
    nodes0 ;


(*   List.iter  *)
(*     (fun srl ->  *)
(*       if List.mem srl srs_uppers *)
(*       then  *)
(* 	ty_error  *)
(* 	  ("primary nonterminal root "  *)
(* 	   ^ srl  *)
(* 	   ^ " is used on both the left and right of a subrule declaration") "") *)
(*     srs_lowers; *)

(*   let rec nodups xs =  *)
(*     ( match xs with *)
(*     | [] -> () *)
(*     | x::xs ->  *)
(*         if List.mem x xs  *)
(*         then  *)
(*           ty_error  *)
(* 	    ( "primary nonterminal root " *)
(* 	      ^ x *)
(* 	      ^ " is used more than once on the left of a subrule declaration") *)
(* 	    "" *)
(*         else nodups xs ) in *)
(*   nodups srs_lowers; *)

  List.iter 
    (fun sr -> ignore(subrule xd true sr.sr_lower sr.sr_upper)) xd.xd_srs;

  (* as an internal consistency check, also check against the tops - should always succeed*)
  (* Further, record the production promotion maps *)
  let srd_subrule_pn_promotion = 
    List.map 
      (fun sr -> (sr.sr_lower,(sr.sr_top,subrule xd true sr.sr_lower sr.sr_top))) xd.xd_srs in


  let xd = {xd with xd_srd={xd.xd_srd with srd_subrule_pn_promotion=srd_subrule_pn_promotion}} in
  if show_subrule_data then 
    print_string (Grammar_pp.pp_plain_subrule_data xd.xd_srd);

(* P thinks we don't need this bit no more *)
(*   (\* add "subruleleft" to the categories of all rules that appear on *)
(*      the left of a subrule declaration *\) *)
(*   let sd_rs_l = 	     *)
(*     List.map  *)
(*       (fun r -> *)
(*         if List.mem r.rule_ntr_name srs_lowers  *)
(* 	then r *)
(*    (\*  FZ !!! {r with rule_categories= "subruleleft":: r.rule_categories } *\) *)
(*         else r) *)
(*       xd.xd_rs in *)
(*   let xd = {xd with sd_rs = sd_rs_l} in *)


(* TODO: check that any homomorphisms in srs are well-formed - ie, *)
(* that they only mention the ntr on the left *)

  (* VV: We do not check that contextrules with the hole filled are of the
     right type right now, but later when a parser has been constructed. *)

  let rec count_holes_element (el:element) : int =
    match el with
    | Lang_nonterm _ -> 0
    | Lang_terminal "__" -> 1
    | Lang_terminal _ -> 0
    | Lang_metavar _ -> 0
    | Lang_list elb -> count_holes_elements elb.elb_es
    | Lang_option _  | Lang_sugaroption _ ->
        ty_error
	  ( "count_holes_rule check failed: hole __ found in an"
	    ^ " option or sugaroption form") ""

  and count_holes_elements (els:element list) : int =
      List.fold_left (+) 0 (List.map count_holes_element els) in
      
  let count_holes_prod (pl:prod) : unit =
    let n = count_holes_elements pl.prod_es in
    if n <> 1 then
      ty_error( "count_holes_rule check failed: hole __ found nonlinearly "
		^ "(" ^ string_of_int n ^ " times) in production "
		^ Auxl.the (Grammar_pp.pp_prod error_opts xd "" "" pl)) ""
    else () in

  let count_holes_rule (srl:nontermroot) : unit =
    let rl = Auxl.rule_of_ntr xd srl in
    List.iter count_holes_prod rl.rule_ps in

  List.iter count_holes_rule (List.map (fun cr -> cr.cr_ntr) xd.xd_crs);

  (* Check that the hole of a ctxrule is not instantiated by a nonterm that can be promoted *)
  let ctxrule_can_promote_hole ntr =
    let ntr_p = Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd ntr) in 
    if not (String.compare ntr ntr_p = 0)
    then ty_error( "ctxrule_can_promote check failed: the type of hole "
		   ^ ntr ^ " can be promoted to " ^ ntr_p ) ""
    else () in
  List.iter (fun cr -> ctxrule_can_promote_hole cr.cr_hole) xd.xd_crs;

  (* Check that the grammar cannot yield a parser that diverges. *)
  let es_in_ntrs ntrs es = match es with
  | Lang_nonterm (ntr, _) -> List.mem ntr ntrs
  | _ -> raise ThisCannotHappen
  in
  (* Filter out the productions that have terminals *)
  let element_nonterm e = 
    match e with
    | Lang_nonterm _ -> true
    | _ -> false
  in 
  let rec filter_xd xd =
    { xd with xd_rs = List.map filter_rule xd.xd_rs }
  and filter_rule r = 
    { r with rule_ps = List.filter (fun p -> List.for_all element_nonterm p.prod_es) r.rule_ps }
  in
  let nts_only_tmp = filter_xd xd in
  let nts_only = { nts_only_tmp with xd_rs = List.filter (fun r -> r.rule_ps <> []) nts_only_tmp.xd_rs }
  in
  (* Compute the non-terminals that can derive the empty string *)
  let is_prod_nullable nulls p = 
    List.for_all (es_in_ntrs nulls) p.prod_es
  in
  let is_rule_nullable nulls r = 
    List.exists (is_prod_nullable nulls) r.rule_ps
  in
  let rec accumulate_nulls nulls rs =
    let (new_nulls, new_rs) = List.partition (is_rule_nullable nulls) rs in
      if new_nulls = [] then
        nulls
      else
        accumulate_nulls (List.concat (List.map (fun r -> List.map fst r.rule_ntr_names) new_nulls) @ nulls)
                         new_rs
  in
  let nullable_ntrs = accumulate_nulls [] nts_only.xd_rs
  in
  (* Build a graph of trivial cycles *)
  let g = G.create () in

  let rec add_vertices ntrs n acc = match ntrs with
  | [] -> acc
  | ntr::ntrs -> 
      let v=G.V.create n in
      G.add_vertex g v; 
      add_vertices ntrs (n+1) ((ntr,n,v)::acc) in

  let possible_ntrs = List.concat (List.map (fun r -> List.map fst r.rule_ntr_names) xd.xd_rs) in
  
  let vertex_info =  add_vertices possible_ntrs 0 [] in

  let vertex_of_ntr ntr = List.assoc ntr 
      (List.map (function(ntr,n,v)->ntr,v) vertex_info) in

  let ntr_of_vertex v = List.assoc v 
      (List.map (function(ntr,n,v)->v,ntr) vertex_info) in

  (* self-edges are errors *)
  let add_edges froms tos = 
    List.iter (fun ntr1 -> let idx1 = vertex_of_ntr ntr1 in 
    List.iter (fun ntr2 ->
      if ntr2 = ntr1 then
        ty_error ("non-terminal " ^ ntr1 ^ " has a non-productive self-loop.") ""
      else
        G.add_edge g idx1 (vertex_of_ntr ntr2))
      tos)
      froms
  in

  let extr_ntr e =
    match e with
    | Lang_nonterm (ntr, _) -> ntr
    | _ -> raise ThisCannotHappen in

  let add_edges_for_p from_ntrs p =
    let (nulls, others) = List.partition (es_in_ntrs nullable_ntrs) p.prod_es in
    let others = List.map extr_ntr others in
    let nulls = List.map extr_ntr nulls in 
    match others with
    | [] -> add_edges from_ntrs nulls
    | [other] -> add_edges from_ntrs [other]
    | _ -> ()
  in  
 
  let add_edges_for_r r = 
    List.iter (add_edges_for_p (List.map fst r.rule_ntr_names))
              r.rule_ps

  in
  List.iter add_edges_for_r nts_only.xd_rs;
  (* nontrivial SCCs are errors *)
  let rec ntrs_to_string ntrs =
    match ntrs with
    | [] -> ""
    | [ntr] -> "\"" ^ ntr_of_vertex ntr ^ "\""
    | ntr::ntrs -> "\"" ^ ntr_of_vertex ntr ^ "\", " ^ ntrs_to_string ntrs
  in
  let (scc_vertex_sets : G.V.t list list) = G.Components.scc_list g in
  List.iter (fun x ->
               if List.length x > 1 then
                 ty_error ("There is a non-productive cycle among the following non-terminals: " ^ ntrs_to_string x) ""
               else
                 ())
            scc_vertex_sets;

  (* 11 compute the structure *)
  (* a- map to structure entries *)
  let structure_mds =
    List.map 
      (fun mvd -> (mvd.mvd_loc, (Struct_md mvd.mvd_name)))
      xd.xd_mds in
  let structure_rs =
    Auxl.option_map
      (fun r -> if r.rule_semi_meta then None else Some (r.rule_loc, (Struct_rs [r.rule_ntr_name])))
      xd.xd_rs in
  let structure_srs = 
    let candidate = 
      List.map
        (fun sr -> (sr.sr_loc, (Struct_srs [(sr.sr_lower, sr.sr_upper)])))
        xd.xd_srs in 
    if merge_fragments 
    then List.rev (Auxl.remove_duplicates2 (fun (_,s1) -> fun (_,s2) -> (compare s1 s2) = 0 ) (List.rev candidate))
    else 
      ( match Auxl.find_first_duplicate2 (fun (_,s1) -> fun (_,s2) -> (compare s1 s2) = 0 ) (List.rev candidate) with
      | None -> candidate 
      | Some s -> ty_error ("duplicated subrule: "^(Auxl.dump_structure_entry s)) "" ) in
  let structure_crs = 
    List.map
      (fun cr -> (cr.cr_loc, (Struct_crs [(cr.cr_ntr, cr.cr_target, cr.cr_hole)])))
      xd.xd_crs in
  let structure_axs = 
    List.map 
      (fun (f,(ntrl, ntmvr)) -> 
        (* pick up the max loc of all the locs of the nonterms mentioned in t *)
        let ls = 
          List.map
            (fun ntr ->
              fst (List.find (function (_,Struct_rs ntrs) -> List.mem ntr ntrs | _ -> assert false) structure_rs))
            ntrl in
        let mls =
          Auxl.fold_left1 
            (fun x y -> if Location.compare_locs source_filenames (List.hd x) (List.hd y) = 1 then x else y)
            ls in
          (mls, Struct_axs [f]))
      xd.xd_axs in 
  let structure_sbs = 
    List.map
      (fun sb -> (sb.sb_loc, (Struct_sbs [(sb.sb_name, sb.sb_this, sb.sb_that)])))
      xd.xd_sbs in
  let structure_fvs = 
    List.map
      (fun fv -> (fv.fv_loc, (Struct_fvs [(fv.fv_name, fv.fv_this, fv.fv_that)])))
      xd.xd_fvs in
  let structure_embed = 
    let all_embeds = xd.xd_embed_preamble @ xd.xd_embed in
    List.map (fun (l,m,e) -> (l,Struct_embed (l,m,e))) all_embeds  (* FZ this duplicates a lot of informations...  FIXME *)
  in
  let structure_dcs =
    List.map
      (fun dc -> 
        match dc with
        | Raw_FDC fdc -> (fdc.raw_fdc_loc, Struct_fun_or_defnclass fdc.raw_fdc_name)
        | Raw_RDC rdc -> (rdc.raw_dc_loc, Struct_fun_or_defnclass rdc.raw_dc_name))
      raw_sd_dcs' in

  let unsorted_structure =
    structure_mds 
    @ structure_rs 
    @ structure_srs 
    @ structure_crs 
    @ structure_axs 
    @ structure_sbs
    @ structure_fvs
    @ structure_embed 
    @ structure_dcs in
  
  (* print_endline "****** begin unsorted"; *)
  (* print_endline (Auxl.dump_structure unsorted_structure); *)
  (* print_endline "****** end unsorted"; *)

  (* b- sort *)
  let compare_loc_info l1 l2 =
    match l1,l2 with
    | hl1::_, hl2::_ -> 
        Location.compare_locs source_filenames hl1 hl2
    | [], hl2::_ -> -1 
    | hl1::_, [] -> 1  
    | _ -> 0  in

  let sorted_structure =
    List.sort 
      (fun (l1,s1) (l2,s2) ->
        compare_loc_info l1 l2)
      unsorted_structure in

  (* print_endline "****** begin sorted"; *)
  (* print_endline (Auxl.dump_structure sorted_structure); *)
  (* print_endline "****** end sorted"; *)

  (* c- collapse rule blocks *)

  let collapsed_structure = 
    let must_collapse stre =
      match stre with
      | Struct_rs _ | Struct_srs _ | Struct_crs _ | Struct_axs _ | Struct_sbs _ | Struct_fvs _ -> true
      | Struct_md _ | Struct_embed _ | Struct_fun_or_defnclass _ -> false in

    let collapsables stre1 stre2 =
      match (stre1,stre2) with
      | (Struct_rs _,Struct_rs _) -> true
      | (Struct_srs _,Struct_srs _) -> true
      | (Struct_crs _,Struct_crs _) -> true
      | (Struct_axs _,Struct_axs _) -> true
      | (Struct_sbs _,Struct_sbs _) -> true
      | (Struct_fvs _,Struct_fvs _) -> true
      | _ -> false in

    let collapsed stre1 stre2 = 
      match (stre1,stre2) with
      | (Struct_rs l1,Struct_rs l2) -> Struct_rs (l1@l2)
      | (Struct_srs l1,Struct_srs l2) -> Struct_srs (l1@l2)
      | (Struct_crs l1,Struct_crs l2) -> Struct_crs (l1@l2)
      | (Struct_axs l1,Struct_axs l2) -> Struct_axs (l1@l2)
      | (Struct_sbs l1,Struct_sbs l2) -> Struct_sbs (l1@l2)
      | (Struct_fvs l1,Struct_fvs l2) -> Struct_fvs (l1@l2)
      | _ -> Auxl.error "internal: collapsing incompatible structure elements.\n" in

    let out_c_a current auxfns =
      match current,auxfns with
      | None, [] -> []
      | Some (l,rsec), [] -> [(l,rsec)]
      | None, xs -> Auxl.error "internal: out_c_a, auxfns but undefined current"
      | Some (l,rsec), xs -> (l,rsec)::[(l,Struct_axs xs)]
    in

    let rec collapse current auxfns strs =
      match strs with
      | [] -> out_c_a current auxfns

      | (l,s)::ss -> 
          if must_collapse s then (
            match current with
            | None -> collapse (Some (l,s)) [] ss
            | Some (lc,sc) -> 
                if (collapsables sc s) && Location.same_file l lc
                then  collapse (Some (lc,(collapsed sc s))) auxfns ss
                else 
                  ( match s with
                  | Struct_axs axs -> collapse (Some (lc,sc)) (axs@auxfns) ss
                  | _ -> (out_c_a current auxfns )@(collapse (Some (l,s)) [] ss) ))
          else (
            (out_c_a current auxfns)@((l,s)::(collapse None [] ss)) )
    in
    collapse None [] sorted_structure
    
  in

  (* print_endline "****** begin collapsed"; *)
  (* print_endline (Auxl.dump_structure collapsed_structure); *)
  (* print_endline "****** end collapsed"; *)

  (* b1- update the collapsed infos with the merge infos *)
   
    (*let merged_structure =*)
    (* TODO *)
    (* (\* two phases: 1- find the mvds that depend on the merged ntrs, 2- update their struct infos *\) *)
    (* let new_locs_of_mvds = *)
    (*   List.map  *)
    (*     (fun (ntr1,lntr1,ntr2,lntr2) -> *)
    (*       (\* find all the mvds on which ntr2 depends *\) *)
    (*       xd *)
    (*     ) *)
    (*   merge_struct_datas in *)

    (* List.map (fun (l,s) -> *)
    (*   match s with *)
    (*   | Struct_rs *)
    (*   | ->  *)
    (*   ) *)
    (*collapsed_structure in*)

  (* print_endline "****** begin merged"; *)
  (* print_endline (Auxl.dump_structure merged_structure); *)
  (* print_endline "****** end merged"; *)

  (* d- forget locations - but not file names *)
  let structure = 
    List.map (fun (l,s) -> (Location.extract_file l, s)) collapsed_structure in

  (* 12- compute the dependencies *)
  let deps = List.map 
      (fun x -> (x, Dependency.compute_dependencies xd x)) 
      ("ascii"::targets) in
  let xd = { xd with xd_dep = deps } in

  (* 13- check that dependencies and structure agree *)
  if not(merge_fragments) then check_structure xd structure;

  (* 14- the answer *)
  (xd, structure, rsd'.raw_sd_dcs)


let check_with_parser (lookup : made_parser) (xd: syntaxdefn) : unit =
  (* check that for each pair in the context rules that there is (up
    to the contextrule relation (and subrule??) a ctxgrammar
    relationship between the definitions of the two rules.  For now
    allow only linear contexts. *)
  let ctxrule (hole:nontermroot) (ntr:nontermroot) (target:nontermroot) : unit =  
    let rl = Auxl.rule_of_ntr xd ntr in 
    List.iter 
      (fun pl ->
        ( match Context_pp.context_app_rhs error_opts xd lookup (hole,[]) target rl pl with  
                (* FZ think about error_opts and the empty suffix *)
        | (false, _) -> 
            ty_error
              ( "ctxrule check failed: production\n"
       	        ^ Auxl.the (Grammar_pp.pp_prod error_opts xd "" "" pl)
       	        ^ "\n of rule " ^ ntr
       	        ^ " cannot be matched in rule " ^ target) ""
        | (true, _) -> () ))
      rl.rule_ps
  in         
  (* for each rule, test all productions *)
  List.iter (fun cr -> ctxrule cr.cr_hole cr.cr_ntr cr.cr_target) xd.xd_crs; 

