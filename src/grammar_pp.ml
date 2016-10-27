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

exception ThisCannotHappen

let c = ref 100 (* FZ *)

let debug s = () (* print_string s; flush stdout*)

(* 

Some of the grammar pp functions come in several flavours, with
more-or-less environment.  For example, we have:

pp_plain_nonterm nt    

  just gives a crude ASCII version of nt, primarily for use in error
  messages etc where we don't have a syntax defn to hand

pp_nonterm m xd nt

  gives a normal Ascii/Tex/Coq/Isa pp of nt, depending on the mode m
  and syntax defn xd.  This is only really sensible for nt which are
  known not to contain a suffix item of the form Si_index i.

  (currently this is implemented using the _with_sie version, passing
  an empty sie)

pp_nonterm_with_sie m xd sie nt

  as above, but any suffix item "Si_index i" is replaced by the i'th
  element of the suffix index environment sie.

pp_nonterm_with_de_with_sie m xd sie de nt

  as above, but first we lookup nt in the de2 component of de.  If
  it's not found, we revert to the above, otherwise (eg for an l'j
  where there is a list l'1..l'n) we generate isa/coq code for a
  projection from a List.nth of a list var.  This is only defined for
  Coq/Isa modes, not for Ascii/Tex modes.

Moreover, sometimes we pp pieces of a production directly, and
sometimes by synthesising a symterm and then pping that.  In
particular, when we want to generate an Isa/Coq list variable (say
from a bindspec x1..xn) we do this.

All this should perhaps be rationalised...

*)


let pp_source_location m l =
  let s = Location.pp_t_source l in
  match m with
  | Ascii _ 
  | Tex _ -> Printf.sprintf "%% %s\n" s
  | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _  ->  Printf.sprintf "(* %s *)\n" s
  | Lex _ | Yacc _ -> ""  



(* utilities *********************************************************** *)

let list_append m = match m with | Lem _ | Hol _ -> " ++ " | _ -> " @ "

let pad n s = 
   let m = n - String.length s in 
   if m>=1 then s ^ String.make m ' ' else s

let pad2 n s s' = 
   let m = n - String.length s in 
   if m>=1 then s' ^ String.make m ' ' else s'

(* ASCII tokens ******************************************************** *)

(* NB THIS LEXICAL DATA MUST BE CONSISTENT WITH grammar_lexer.mll AND 
   THE ... IN lexicalgoo.ml *)
let pp_CCE                = "::=" 
let pp_BAR                = "|"   
let pp_LEFTBRACE          = "{"   
let pp_RIGHTBRACE         = "}"   
let pp_RIGHTBRACEPLUS     = "}+"  
let pp_LEFTBRACKET        = "["   
let pp_RIGHTBRACKET       = "]"   
let pp_DOUBLELEFTBRACKET  = "[["  
let pp_DOUBLERIGHTBRACKET = "]]"  
let pp_DOUBLELEFTBRACE    = "{{"  
let pp_DOUBLERIGHTBRACE   = "}}"  
let pp_COLONCOLON         = "::"  
let pp_LTCOLONCOLON       = "<::"  
let pp_UNDERSCORECOLONCOLON  = "_::"  
let pp_DOTDOT             = ".."     
let pp_DOTDOTDOT          = "..."  
let pp_DOTDOTDOTDOT       = "...."  
let pp_EMBED              = "embed"
let pp_HOMS               = "homs"
let pp_METAVAR            = "metavar"
let pp_RULES              = "grammar"
let pp_SUBRULES           = "subrules"      (* FZ CHECK *)
let pp_CONTEXTRULES       = "contextrules"  (* FZ CHECK *)
let pp_SUBSTITUTIONS      = "substitutions" (* FZ CHECK *)
let pp_FREEVARS           = "freevars" (* FZ CHECK *)
let pp_BY                 = "by"
let pp_DEFN               = "Defn"
let pp_DEFNCLASS          = "Defns"
let pp_FUNDEFN            = "fun"
let pp_FUNDEFNCLASS       = "funs"
let pp_BIND_LEFT_DELIM    = "(+"

let pp_BIND_RIGHT_DELIM   = "+)"
let pp_BIND               = "bind"
let pp_IN                 = "in"
let pp_NAMES              = "names"
let pp_DISTINCTNAMES      = "distinctnames"
let pp_UNION              = "union"
let pp_EQ                 = "="
let pp_HASH               = "#"
let pp_LPAREN             = "("
let pp_RPAREN             = ")"
let pp_EMPTY              = "{}"

let pp_COMP_LEFT          = "</"
let pp_COMP_MIDDLE        = "//"
let pp_COMP_RIGHT         = "/>"
let pp_COMP_IN            = "IN"
  (* Lexicalgoo.listform and Grammar_pp.COMP_LEFT etc must be consistent *)

let quoted_tokens = 
  [ pp_CCE; pp_BAR; 
(* for BNF options etc *)
(* pp_LEFTBRACE; pp_RIGHTBRACE; pp_LEFTBRACKET; *)
(*    pp_RIGHTBRACKET; pp_DOUBLELEFTBRACKET; pp_DOUBLERIGHTBRACKET; *)
    pp_DOUBLELEFTBRACE; pp_DOUBLERIGHTBRACE; pp_COLONCOLON; pp_DOTDOT; 
    pp_DOTDOTDOT; pp_DOTDOTDOTDOT; pp_METAVAR; pp_RULES; pp_BY; pp_DEFN; 
    pp_DEFNCLASS; pp_LTCOLONCOLON; pp_UNDERSCORECOLONCOLON; pp_SUBRULES; 
    pp_SUBSTITUTIONS; pp_FREEVARS; pp_EMBED; pp_HOMS; pp_BIND_LEFT_DELIM; "" (* ; "''" *) ]

let quote_ident s = if List.mem s quoted_tokens then "'"^s^"'" else s

(** pp raw grammars ***************************************************** *)

let rec     
    pp_raw_ident_desc s =  s (*quote_ident s*)

and pp_raw_ident (_,s) = pp_raw_ident_desc s
    
and pp_raw_metavardefn mvd =
  pp_METAVAR ^ " " ^ (String.concat " , " 
                        (List.map 
                           (function (n,homs)->
                             n
                             ^ String.concat " " (List.map pp_raw_homomorphism homs))
                           mvd.raw_mvd_names)
                     ) ^ " "
  ^ pp_CCE ^ " " ^ pp_raw_metavarrep mvd.raw_mvd_rep ^ "\n"

and pp_raw_metavarrep mvd_rep = 
  String.concat " " (List.map pp_raw_homomorphism mvd_rep)

and pp_raw_homomorphism (hn,hs,l) = 
  pp_DOUBLELEFTBRACE ^ " " ^ hn ^ " " ^ pp_raw_hom_spec hs ^ " " 
  ^ pp_DOUBLERIGHTBRACE

and pp_raw_hom_spec hs = 
  String.concat " " (List.map pp_raw_hom_spec_el hs)

and pp_raw_hom_spec_el hse = match hse with
| Raw_hom_string s -> pp_raw_ident_desc s
| Raw_hom_blanks s -> pp_raw_ident_desc s
| Raw_hom_ident ris -> 
    pp_DOUBLELEFTBRACKET 
    ^ String.concat " " (List.map pp_raw_ident ris)
    ^ pp_DOUBLERIGHTBRACKET
| Raw_hom_ident_dots (l,ris,n,ris') -> 
    pp_DOUBLELEFTBRACKET 
    ^ String.concat " " (List.map pp_raw_ident ris)
    ^ pp_raw_dots n
    ^ String.concat " " (List.map pp_raw_ident ris')
    ^ pp_DOUBLERIGHTBRACKET
| Raw_hom_ident_comp (l,ris,rcb) -> 
    pp_DOUBLELEFTBRACKET ^" "
    ^ pp_COMP_LEFT
    ^ String.concat " " (List.map pp_raw_ident ris)
    ^ pp_COMP_MIDDLE
    ^ pp_raw_comp_bound rcb
    ^ pp_COMP_RIGHT ^" "
    ^ pp_DOUBLERIGHTBRACKET

and pp_raw_embedmorphism  (l,hn,es) =
  pp_DOUBLELEFTBRACE ^ " "
  ^ hn ^ " "
  ^ (pp_raw_embed_spec  es) ^ " "
  ^ pp_DOUBLERIGHTBRACE

and pp_raw_embed_spec es = 
  String.concat "" (List.map (pp_raw_embed_spec_el ) es)

and pp_raw_embed_spec_el ese = 
  match ese with
  | Embed_string (l,s) ->  s
  | Embed_inner (l,s) -> pp_DOUBLELEFTBRACKET^s^pp_DOUBLERIGHTBRACKET 

and pp_raw_bindspec b = 
  match b with
  | Raw_Bind (l,mse,ri) -> 
      pp_BIND^" " ^  pp_raw_mse mse ^ " " 
      ^ pp_IN ^ " " ^ pp_raw_ident ri
  | Raw_AuxFnDef (l,f,mse) -> 
      pp_raw_ident f ^ "" ^ pp_EQ ^ "" ^ pp_raw_mse mse
  | Raw_NamesEqual (l,mse,mse') -> 
      pp_NAMES ^ "" ^ pp_LPAREN ^ "" ^ pp_raw_mse mse ^ "" ^ pp_RPAREN 
      ^ "" ^ pp_EQ ^ "" ^ pp_NAMES ^ "" 
      ^ pp_LPAREN ^ "" ^ pp_raw_mse mse' ^ "" ^ pp_RPAREN
  | Raw_NamesDistinct (l,mse,mse') -> 
      pp_NAMES ^ "" ^ pp_LPAREN ^ "" ^ pp_raw_mse mse ^ "" ^ pp_RPAREN
      ^ "" ^ pp_HASH ^ "" ^ pp_NAMES ^ "" ^ pp_LPAREN ^ "" 
      ^ pp_raw_mse mse' ^ "" ^ pp_RPAREN
  | Raw_AllNamesDistinct (l,mse) -> 
      pp_DISTINCTNAMES ^ "" ^ pp_LPAREN ^ "" ^ pp_raw_mse mse 
	  ^ "" ^ pp_RPAREN

and pp_raw_bindspec_list bs = 
  match bs with
  | [] -> "" 
  | [b] -> 
      pp_BIND_LEFT_DELIM ^ " " 
      ^ (pp_raw_bindspec b) ^ " "
      ^ pp_BIND_RIGHT_DELIM
  | bs ->  
      pp_BIND_LEFT_DELIM ^ " " 
      ^ (String.concat 
           " " 
           (List.map (pp_raw_bindspec) bs))
      ^ " " ^ pp_BIND_RIGHT_DELIM 

and pp_raw_mse mse = 
  match mse with
  | Raw_MVorNTExp (l,ri) -> pp_raw_ident ri
  | Raw_MVorNTListExp_dotform (l,ri1,n,ri2) -> pp_raw_ident ri1 ^ pp_raw_dots n ^ pp_raw_ident ri2
  | Raw_MVorNTListExp_comp (l,ri,rcb) -> pp_COMP_LEFT ^ pp_raw_ident ri ^ pp_COMP_MIDDLE ^ pp_raw_comp_bound rcb ^ pp_COMP_RIGHT
  | Raw_Aux(l,f,nt) -> 
      pp_raw_ident f ^ ""^pp_LPAREN ^ "" ^ pp_raw_ident nt ^ "" ^ pp_RPAREN
  | Raw_AuxList_dotform(l,f,nt1,n,nt2) -> 
      pp_raw_ident f ^ ""^pp_LPAREN ^ "" ^ pp_raw_ident nt1 ^ "" ^pp_raw_dots n ^ pp_raw_ident nt2 ^ "" ^ pp_RPAREN
  | Raw_AuxList_comp(l,f,nt,rcb) -> 
      pp_raw_ident f ^ ""^pp_LPAREN ^ "" ^ pp_COMP_LEFT ^ pp_raw_ident nt ^ pp_COMP_MIDDLE ^pp_raw_comp_bound rcb ^ pp_COMP_RIGHT ^ pp_RPAREN
  | Raw_Union(l,mse,mse') -> 
      pp_raw_mse mse ^ " "^pp_UNION^" " ^ pp_raw_mse mse'
  | Raw_Empty(l) -> 
      pp_EMPTY

and pp_raw_element e = match e with
| Raw_ident (_,ri) -> pp_raw_ident ri
| Raw_option (_,res) -> 
    pp_LEFTBRACKET ^ " " ^ String.concat " " (List.map pp_raw_element res) 
    ^ " " ^ pp_RIGHTBRACKET
| Raw_list (_,res) -> 
    pp_LEFTBRACE^" " ^ String.concat " " (List.map pp_raw_element res) 
    ^ " " ^ pp_RIGHTBRACE
| Raw_nelist (_,res) -> 
    pp_LEFTBRACE^" " ^ String.concat " " (List.map pp_raw_element res) 
    ^ " " ^ pp_RIGHTBRACEPLUS
| Raw_sugaroption (_,re) -> 
    pp_DOUBLELEFTBRACKET^" " 
    ^ (pp_raw_element re) ^ " " 
    ^ pp_DOUBLERIGHTBRACKET
| Raw_dots (_,n) -> " " ^ pp_raw_dots n ^ " "
| Raw_comp(_,res,rcb,rio) ->
    pp_COMP_LEFT^" "
    ^ String.concat " " (List.map pp_raw_element res)
    ^ pp_COMP_MIDDLE ^" "
    ^ (match rio with None -> "" | Some (_,tm) -> tm     ^ pp_COMP_MIDDLE ^" ")
    ^ pp_raw_comp_bound rcb ^" "
    ^ pp_COMP_RIGHT

and pp_raw_comp_bound rcb = match rcb with
| Raw_bound_comp(l,ri) -> pp_raw_ident ri
| Raw_bound_comp_u(l,ri,ri_u) ->
    pp_raw_ident ri ^" "
    ^ pp_COMP_IN ^" "
    ^ pp_raw_ident ri_u ^" "
| Raw_bound_comp_lu(l,ri,ri_l,n,ri_u) ->
    pp_raw_ident ri ^" "
    ^ pp_COMP_IN ^" "
    ^ pp_raw_ident ri_l ^" "
    ^ pp_raw_dots n ^ " "            
    ^ pp_raw_ident ri_u ^" "

and pp_raw_dots n = 
  match n with
  | 0 -> pp_DOTDOT 
  | 1 -> pp_DOTDOTDOT
  | 2 -> pp_DOTDOTDOTDOT 
  | _ -> Auxl.error "internal: >2 in pp_raw_dots"

and pp_raw_prod p = 
  pad 60 ((match p.raw_prod_flavour with Bar -> pp_BAR)    
	  ^ " " 
	  ^ (String.concat " " (List.map pp_raw_element p.raw_prod_es ))) 
  ^ " " ^ pp_COLONCOLON ^ " " 
  ^ pad 1 (String.concat " " (List.map pp_raw_ident p.raw_prod_categories)) 
  ^ " " ^ pp_COLONCOLON ^ " " ^ p.raw_prod_name 
  ^ "  " ^ pp_raw_bindspec_list p.raw_prod_bs
  ^ "  " ^ (String.concat " " (List.map pp_raw_homomorphism p.raw_prod_homs))

and pp_raw_rule r =
  (String.concat " , " (List.map 
                          (function (n,homs)->
                            n
                            ^ String.concat " " (List.map pp_raw_homomorphism homs))
                          r.raw_rule_ntr_names))
  ^ " " ^ pp_COLONCOLON ^ " " ^ pp_raw_ident_desc r.raw_rule_pn_wrapper
  ^ " " ^ pp_CCE 
  ^ String.concat " " (List.map pp_raw_homomorphism r.raw_rule_homs) 
  ^ "\n" ^ "  " 
  ^ String.concat "  " 
      (List.map (fun rp -> pp_raw_prod rp ^ "\n") r.raw_rule_ps)

and pp_raw_subrule sr =
  pp_raw_ident_desc sr.raw_sr_lower ^ " " ^ pp_LTCOLONCOLON ^ " " 
  ^ pp_raw_ident_desc sr.raw_sr_upper ^ " " 
  ^ String.concat " " (List.map pp_raw_homomorphism sr.raw_sr_homs) 

and pp_raw_contextrule cr =
  pp_raw_ident_desc cr.raw_cr_ntr ^ " " ^ pp_UNDERSCORECOLONCOLON ^ " " 
  ^ pp_raw_ident_desc cr.raw_cr_target  ^ " " ^ " " ^ pp_COLONCOLON ^ " " 
  ^ pp_raw_ident_desc cr.raw_cr_hole ^ " " 
  ^ String.concat " " (List.map pp_raw_homomorphism cr.raw_cr_homs) 

and pp_raw_subst sb = 
  pp_raw_ident_desc sb.raw_sb_name ^ " "
  ^ pp_raw_ident_desc sb.raw_sb_this ^ " "
  ^ pp_raw_ident_desc sb.raw_sb_that
  ^ String.concat " " (List.map pp_raw_homomorphism sb.raw_sb_homs) 

and pp_raw_freevar fv = 
  pp_raw_ident_desc fv.raw_fv_name ^ " "
  ^ pp_raw_ident_desc fv.raw_fv_this ^ " "
  ^ pp_raw_ident_desc fv.raw_fv_that
  ^ String.concat " " (List.map pp_raw_homomorphism fv.raw_fv_homs) 

and pp_raw_item ri = 
  match ri with 
  | Raw_item_md raw_md -> pp_raw_metavardefn raw_md
  | Raw_item_rs raw_rs -> pp_RULES ^ "\n" 
      ^ String.concat "\n" (List.map pp_raw_rule raw_rs)
  | Raw_item_dcs raw_dcs -> pp_raw_fun_or_reln_defnclass raw_dcs
  | Raw_item_srs raw_srs -> pp_SUBRULES ^ "\n" 
      ^ String.concat "\n" (List.map pp_raw_subrule raw_srs) 
  | Raw_item_crs raw_crs -> pp_CONTEXTRULES ^ "\n" 
      ^ String.concat "\n" (List.map pp_raw_contextrule raw_crs) 
  | Raw_item_sbs raw_sbs -> pp_SUBSTITUTIONS ^ "\n" 
      ^ String.concat "\n" (List.map pp_raw_subst raw_sbs)
  | Raw_item_fvs raw_fvs -> pp_FREEVARS ^ "\n" 
      ^ String.concat "\n" (List.map pp_raw_freevar raw_fvs)
  | Raw_item_embed raw_embeds -> pp_EMBED ^ "\n" 
	^ String.concat "\n" (List.map pp_raw_embedmorphism raw_embeds)
	^ "\n" 
  | Raw_item_pas raw_pas -> "TODO: raw parsing annotation"
  | Raw_item_hs raw_hs -> "TODO: raw hom section"
  | Raw_item_coq_variable _ -> "TODO: coq variable"
  | Raw_item_coq_section _ -> "TODO: coq section"
        

and pp_raw_syntaxdef xd =
  String.concat "" (List.map pp_raw_metavardefn xd.raw_sd_mds) 
  ^ ( match xd.raw_sd_rs with 
    [] -> "" 
    | rrs -> pp_RULES ^ "\n" 
	^ String.concat "\n" (List.map pp_raw_rule xd.raw_sd_rs) )
  ^ "\n" 
  ^ ( match xd.raw_sd_srs with 
    [] -> "" 
    | srs -> pp_SUBRULES ^ "\n" 
	^ String.concat "\n" (List.map pp_raw_subrule xd.raw_sd_srs) )
  ^ "\n" 
  ^ ( match xd.raw_sd_crs with      
    [] -> "" 
    | crs -> pp_CONTEXTRULES ^ "\n" 
	^ String.concat "\n" (List.map pp_raw_contextrule xd.raw_sd_crs) )
  ^ "\n" 
  ^ ( match xd.raw_sd_sbs with 
    [] -> "" 
    | sbs -> pp_SUBSTITUTIONS ^ "\n" 
	^ String.concat "\n" (List.map pp_raw_subst xd.raw_sd_sbs) )
  ^ "\n"
  ^ ( match xd.raw_sd_fvs with 
    [] -> "" 
    | fvs -> pp_FREEVARS ^ "\n" 
	^ String.concat "\n" (List.map pp_raw_freevar xd.raw_sd_fvs) )
  ^ "\n"
  ^ ( match xd.raw_sd_embed with 
    [] -> "" 
    | _ -> 
	pp_EMBED ^ "\n" 
	^ String.concat "\n" (List.map pp_raw_embedmorphism xd.raw_sd_embed)
	^ "\n"  )
  ^ String.concat "\n" (List.map pp_raw_fun_or_reln_defnclass xd.raw_sd_dcs)
  ^ "\n"
  (* ^ ( match xd.raw_sd_embed_postamble with *)
  (*   [] -> "" *)
  (*   | _ -> *)
  (*       pp_EMBED ^ "\n" *)
  (*       ^ String.concat "\n" (List.map pp_raw_embedmorphism xd.raw_sd_embed_postamble) *)
  (*       ^ "\n"  ) *)
  ^ "\n"

and pp_raw_line x = match x with
| Raw_line (_,s) -> s
| Raw_lineline (_,s1,s2) -> s1 ^ s2
| Raw_blankline (_,s) -> "\n"
| Raw_commentline (_,s) -> "%\n"

and pp_raw_defnclass dc =
  pp_DEFNCLASS ^ "\n" ^ dc.raw_dc_name ^ " " ^ pp_COLONCOLON ^ " " 
  ^ pp_raw_ident_desc dc.raw_dc_wrapper ^ " " ^ pp_CCE ^ "\n\n" 
  ^ String.concat "\n" (List.map pp_raw_defn dc.raw_dc_defns)
  
and pp_raw_defn d =
  pp_DEFN ^ "\n" 
  ^ (String.concat " " (List.map pp_raw_element d.raw_d_es)) 
  ^ " " ^ pp_COLONCOLON ^ " " 
  ^ pad 1 (String.concat " " (List.map pp_raw_ident d.raw_d_categories))
  ^ " " ^ pp_COLONCOLON ^ " " ^ pp_raw_ident_desc d.raw_d_name ^ " "
  ^ " " ^ pp_COLONCOLON ^ " " ^ pp_raw_ident_desc d.raw_d_wrapper ^ " "
  ^ String.concat " " (List.map pp_raw_homomorphism d.raw_d_homs) 
  ^ pp_BY ^ "\n\n" ^ (String.concat "\n" (List.map (* pp_raw_line*) pp_semiraw_rule d.raw_d_body))

and pp_raw_fundefnclass fdc =
  pp_FUNDEFNCLASS ^ "\n" ^ fdc.raw_fdc_name ^ " " ^ pp_CCE ^ "\n\n " 
(*  ^ pp_raw_ident_desc fdc.raw_fdc_wrapper ^ " " ^ pp_CCE ^ "\n\n"  *)
  ^ String.concat "\n" (List.map pp_raw_fundefn fdc.raw_fdc_fundefns)
  
and pp_raw_fundefn fd =
  pp_FUNDEFN ^ "\n" 
  ^ (String.concat " " (List.map pp_raw_element fd.raw_fd_es)) 
  ^ " " ^ pp_COLONCOLON ^ " " 
  ^ (pp_raw_ident fd.raw_fd_result) 
  ^ " // " ^fd.raw_fd_pn_wrapper ^ " "  
(*  ^ pad 1 (String.concat " " (List.map pp_raw_ident d.raw_d_categories)) *)
  ^ " " ^ pp_COLONCOLON ^ " " ^ pp_raw_ident_desc fd.raw_fd_name ^ " "
(*   ^ " " ^ pp_COLONCOLON ^ " " ^ pp_raw_ident_desc fd.raw_fd_wrapper ^ " "*)
  ^ String.concat " " (List.map pp_raw_homomorphism fd.raw_fd_homs) 
  ^ pp_BY ^ "\n\n" ^ (String.concat "\n" (List.map (* pp_raw_line*) pp_raw_funclause fd.raw_fd_clauses))

and pp_raw_funclause (l,s) = s

and pp_raw_fun_or_reln_defnclass rfrdc = 
  match rfrdc with
  | Raw_FDC rfdc -> pp_raw_fundefnclass rfdc
  | Raw_RDC rdc -> pp_raw_defnclass rdc

and pp_semiraw_rule = function
  | Lineless_rule (l,lss) -> 
      "[[\n"
      ^ (String.concat "" (List.map (function (l,s) -> "| "^s^"\n") lss)) 
      ^ "]]\n"
  | Lined_rule (l,lss1,ls,lss2) -> 
      "[[\n"
      ^ (String.concat "" (List.map (function (l,s) -> "| "^s^"\n") lss1))
      ^ "---------------"
      ^ snd ls
      ^ (String.concat "" (List.map (function (l,s) -> "| "^s^"\n") lss2)) 
      ^ "]]\n"
  | Defncom (l,es) ->
      "[[\n"
      ^ pp_raw_embed_spec es
      ^ "]]\n"

(** make a canonical symterm from a production *)

(* TODO: for now this assumes that each production uses nonterminals *)
(* affinely, and that the pp_symterm prints them in the most obvious way *)

(* TODO: the following assumes that no name clashes will be introduced in a *)
(* production by mapping all primary ntrs to secondary ntrs, where they *)
(* exist.  This is not true in general *)

(* let si_indexes_of_suff suff = List.filter (function suffi -> match suffi with *)
(* | Si_num _ -> false *)
(* | Si_punct _ -> false *)
(* | Si_var (_,_) -> false *)
(* | Si_index _ -> true) suff *)


(* let secondary_mvr m xd mvrp mvr = *)
(*   if mvr=mvrp then *)
(*     let mvd = Auxl.mvd_of_mvr xd mvr in *)
(*     (match m with *)
(*     | Coq _ | Hol _ | Isa _ -> *)
(*         (match mvd.mvd_names with *)
(*         | [] -> failwith "internal error: empty list of mvd names" *)
(*         | [_] ->mvr *)
(*         | mvrp'::mvrq'::_ -> fst mvrq') *)
(*     | Ascii _ | Tex _ -> mvr) *)
(*   else *)
(*     mvr *)


(* let new_suff suff suff'' =  *)
(*   let suff1 = si_indexes_of_suff suff in *)
(*   if suff1 = [] then suff'' else suff1 @ [Si_punct "_"] @ suff'' *)

(* let rec canonical_symterm_element_of_element' m xd nts_mapping mvs_mapping e  *)
(*     = match e with *)
(*     | Lang_nonterm (ntrp,((ntr,suff) as nt)) ->  *)
(*         let nt'' =  *)
(*           (match m with  *)
(*           | Ascii _ | Tex _ (\*->  (ntr,suff)  *\) *)
(*           | Coq _ | Hol _ | Isa _ ->  *)
(*               let ntr' = secondary_ntr m xd ntrp ntr in *)
(*               let nt' = ntr',suff in *)
(*               let (_,suff'') = Auxl.fresh_nt (List.map snd !nts_mapping) ntr' in *)
(*               (ntr',new_suff suff suff'')) in *)
(*         nts_mapping := (nt,nt'') :: !nts_mapping; *)
(*         Some(Ste_st(dummy_loc,St_nonterm(dummy_loc,ntrp,nt''))) *)
(*     | Lang_metavar (mvrp,((mvr,suff)as mv)) ->  *)
(*         let mv'' = *)
(*           (match m with *)
(*           | Ascii _ | Tex _ (\*->  (mvr,suff) *\) *)
(*           | Coq _ | Hol _ | Isa _ -> *)
(*               let mvr' = secondary_mvr m xd mvrp mvr in *)
(*               let mv' = mvr',suff in *)
(*               let (_,suff'') = Auxl.fresh_mv (List.map snd !mvs_mapping) mvr' in *)
(*               (mvr',new_suff suff suff'')) in *)
(*         mvs_mapping := (mv,mv'') :: !mvs_mapping; *)
(*         Some (Ste_metavar(dummy_loc,mvrp,mv'')) *)
(*     | Lang_terminal _ ->  *)
(*         None  *)
(*     | Lang_list elb ->  *)
(*         let b = (match elb.elb_boundo with *)
(*         | None -> Bound_dotform  *)
(*               {bd_lower=Si_var ("",0);bd_upper=Si_var ("",0);bd_length=2}  *)
(*           (\* above we invent null index variables.  This is ok for tex pp *\) *)
(*           (\* of the canonical symterm of a production, which should be *\) *)
(*           (\* the only case where it occurs *\) *)

(*           (\* raise (Invalid_argument "canonical_symterm_element_of_element no bounds") *\) *)
(*         | Some b ->b) in *)
(*         Some (Ste_list  *)
(*                 (dummy_loc, *)
(*                  [Stli_listform {stl_bound = b; *)
(*                                 stl_elements = Auxl.option_map  *)
(*                                   (canonical_symterm_element_of_element' m xd nts_mapping mvs_mapping) *)
(*                                   elb.elb_es; *)
(*                                 stl_loc = dummy_loc}])) *)
(*     | (Lang_option _ | Lang_sugaroption _)->  *)
(*         raise (Invalid_argument  *)
(*                  "canonical_symterm_element_of_element option cases not implemented")  *)
          
(* let canonical_symterm_node_body_of_prod' m xd nts_mapping mvs_mapping ntr p =  *)
(*   { st_rule_ntr_name = ntr; *)
(*     st_prod_name = p.prod_name; *)
(*     st_es = Auxl.option_map  *)
(*       (canonical_symterm_element_of_element' m xd nts_mapping mvs_mapping) *)
(*       p.prod_es; *)
(*     st_loc = dummy_loc } *)
    

(* let canonical_symterm_element_of_element m xd e =  *)
(*   let nts_mapping,mvs_mapping = ref ([]:(nonterm *nonterm) list),ref ([]:(metavar * metavar) list) in *)
(*   let ste = canonical_symterm_element_of_element' m xd nts_mapping mvs_mapping e in *)
(*   (ste,(!nts_mapping,!mvs_mapping)) *)

(* let canonical_symterm_node_body_of_prod m xd ntr p = *)
(*   let nts_mapping,mvs_mapping = ref ([]:(nonterm *nonterm) list),ref ([]:(metavar * metavar) list) in *)
(*   let stnb = canonical_symterm_node_body_of_prod' m xd nts_mapping mvs_mapping ntr p  in *)
(*   (stnb,(!nts_mapping,!mvs_mapping)) *)


(* the vanilla canonical symterms, without secondarification or freshening *)

let rec canonical_symterm_element_of_element e 
    = match e with
    | Lang_nonterm (ntrp,((ntr,suff) as nt)) -> 
        Some(Ste_st(dummy_loc,St_nonterm(dummy_loc,ntrp,nt)))
    | Lang_metavar (mvrp,((mvr,suff)as mv)) -> 
        Some (Ste_metavar(dummy_loc,mvrp,mv))
    | Lang_terminal _ -> 
        None 
    | Lang_list elb -> 
        let b = (match elb.elb_boundo with
        | None -> Bound_dotform 
              {bd_lower=Si_var ("",0);bd_upper=Si_var ("",0);bd_length=2} 
          (* above we invent null index variables.  This is ok for tex pp *)
          (* of the canonical symterm of a production, which should be *)
          (* the only case where it occurs *)

          (* raise (Invalid_argument "canonical_symterm_element_of_element no bounds") *)
        | Some b ->b) in
        Some (Ste_list 
                (dummy_loc,
                 [Stli_listform {stl_bound = b;
                                 stl_elements = Auxl.option_map 
                                   (canonical_symterm_element_of_element)
                                   elb.elb_es;
                                 stl_loc = dummy_loc}]))
    | (Lang_option _ | Lang_sugaroption _)-> 
        raise (Invalid_argument 
                 "canonical_symterm_element_of_element option cases not implemented") 
          
let canonical_symterm_node_body_of_prod ntr p = 
  { st_rule_ntr_name = ntr;
    st_prod_name = p.prod_name;
    st_es = Auxl.option_map 
      (canonical_symterm_element_of_element)
      p.prod_es;
    st_loc = dummy_loc }
    



(** pp grammars ********************************************************* *)

(* colour definitions ************************************************** *)

let black   = 0
let red     = 1
let green   = 2
let yellow  = 3
let blue    = 4
let magenta = 5
let cyan    = 6
let white   = 7

let _reset = "\x1b[0m"

let _color fg br = Printf.sprintf "\x1b[%u;%um" br (fg+30)

let _w = "\x1b[0;1;4m"

let _r = _color red 0
let _b = _color blue 0  (* was blue 1 *)
let _g = _color green 0

let col_wrap opt col s = if opt.ppa_colour then col ^ s ^ _reset else s

let col_red ao s =  col_wrap ao _r s
let col_black ao s = col_wrap ao _b s
let col_green ao s = col_wrap ao _g s
let col_yellow ao s = col_wrap ao (_color yellow 0) s
let col_blue ao s = col_wrap ao (_color blue 0)  s
let col_magenta ao s = col_wrap ao (_color  magenta 0) s
let col_cyan ao s = col_wrap ao (_color  cyan 0) s 
let col_white ao s = col_wrap ao  (_color  white 0)  s

(* TeX tokens ********************************************************** *)

let classify_TTC_terminal s = if Auxl.is_alpha s then TTC_terminal_alpha else TTC_terminal_symb

let index_of_ttc ttc = match ttc with 
  | TTC_terminal_alpha -> 0
  | TTC_terminal_symb -> 1
  | TTC_nonterm_or_metavar -> 2
  | TTC_space -> 3
  | TTC_dots -> 4
  | TTC_comp -> 5
  | TTC_dummy -> raise ThisCannotHappen 

let spacing_data : string array array = 
  let s  = "\\," in
  let no = "" in 
  [|
(*  left         right: terminal_alpha terminal_symb nonterm_or_metavar space dots comp *)
(*terminal_alpha    *)[|      s       ;      s      ;      s           ; no  ; s  ; s  |];
(*terminal_symb     *)[|      s       ;      no     ;      no          ; no  ; s  ; s  |];
(*nonterm_or_metavar*)[|      s       ;      no     ;      s           ; no  ; s  ; s  |];
(*space             *)[|      no      ;      no     ;      no          ; no  ; no ; no |];
(*dots              *)[|      s       ;      s      ;      s           ; no  ; s  ; s  |];
(*comp              *)[|      s       ;      s      ;      s           ; no  ; s  ; s  |] |]


let spacing_data_debug : string array array = 
  [|
(*  left         right: terminal_alpha terminal_symb nonterm_or_metavar space dots comp *)
(*terminal_alpha    *)[|     "AA"     ;     "AS"    ;     "AN"         ;"AW" ;"AD";"AC"|];
(*terminal_symb     *)[|     "SA"     ;     "SS"    ;     "SN"         ;"SW" ;"SD";"SC"|];
(*nonterm_or_metavar*)[|     "NA"     ;     "NS"    ;     "NN"         ;"NW" ;"ND";"NC"|];
(*space             *)[|     "WA"     ;     "WS"    ;     "WN"         ;"WW" ;"WD";"WC"|];
(*dots              *)[|     "DA"     ;     "DS"    ;     "DN"         ;"DW" ;"DD";"DC"|];
(*comp              *)[|     "CA"     ;     "CS"    ;     "CN"         ;"CW" ;"CD";"CC"|] |]


let pairwise_spacing ttc ttc' = spacing_data.(index_of_ttc ttc).(index_of_ttc ttc')

let rec pp_tex_insert_spacing (es:(string*tex_token_category) list) : string
    = 
  match es with 
  | [] -> ""
  | (s,ttc)::[] -> s
  | (s,ttc)::(((s',ttc')::_) as es') -> s ^ " "^ pairwise_spacing ttc ttc' ^ " "^pp_tex_insert_spacing es'
                                                                          




let pp_tex_BAR                = "|"   
let pp_tex_LEFTBRACKET        = "["   
let pp_tex_RIGHTBRACKET       = "]"   

let pp_tex_BIND               = "\\textsf{bind}"
let pp_tex_IN                 = "\\textsf{in}"
let pp_tex_EQ                 = "="
let pp_tex_NAMES              = "\\textsf{names}"
let pp_tex_LPAREN             = "("
let pp_tex_RPAREN             = ")"
let pp_tex_HASH               = "\\#"
let pp_tex_DISTINCTNAMES      = "\\textsf{distinctnames}"
let pp_tex_EMPTY              = "\\{\\}"
let pp_tex_UNION              = "\\cup "
(* let pp_tex_BEGIN_RULES        = "\\[\n\\begin{array}{llclllll}\n" *)
(* let pp_tex_END_RULES          = "\\end{array}\n\\]\n" *)

(* let pp_tex_COMP               = "\\widetilde{"*) 
(* let pp_tex_COMP               = "\\widehat{" *)
(* let pp_tex_COMP               = "\\overrightarrow{" *)

(* let pp_tex_BIND_LEFT_DELIM    = "" *)
(* let pp_tex_BIND_RIGHT_DELIM   = "" *)

let pp_tex_DOTDOT             = ".."   
let pp_tex_DOTDOTDOT          = "..."  
let pp_tex_DOTDOTDOTDOT       = "...." 

let pp_tex_NAME_PREFIX m       = 
  match m with
  | Tex xo -> xo.ppt_name_prefix
  |  _ -> Auxl.error "internal: pp_tex_NAME_PREFIX"

let pp_tex_METAVARS_NAME m     = "\\"^pp_tex_NAME_PREFIX m^"metavars"
let pp_tex_RULES_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"grammar"
let pp_tex_DEFNSS_NAME m       = "\\"^pp_tex_NAME_PREFIX m^"defnss"
let pp_tex_ALL_NAME m       = "\\"^pp_tex_NAME_PREFIX m^"all"

let pp_tex_RULEHEAD_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"rulehead"
let pp_tex_PROD_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"prodline"
let pp_tex_LONG_PROD_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"longprodline"
let pp_tex_BINDSPEC_PROD_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"bindspecprodline"
let pp_tex_FIRST_LONG_PROD_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"firstlongprodline"
let pp_tex_FIRST_PROD_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"firstprodline"
let pp_tex_PROD_NEWLINE_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"prodnewline"
let pp_tex_INTERRULE_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"interrule"
let pp_tex_AFTERLASTRULE_NAME m        = "\\"^pp_tex_NAME_PREFIX m^"afterlastrule"

let pp_tex_BEGIN_RULES m      = "\\"^pp_tex_NAME_PREFIX m^"grammartabular{\n" 
let pp_tex_END_RULES          = "}"

let pp_tex_BEGIN_METAVARS m      = "\\"^pp_tex_NAME_PREFIX m^"metavartabular{\n" 
let pp_tex_END_METAVARS          = "}"


let pp_tex_DRULE_NAME m = "\\"^pp_tex_NAME_PREFIX m^"drule"
let pp_tex_DRULE_NAME_NAME m = "\\"^pp_tex_NAME_PREFIX m^"drulename"
let pp_tex_USE_DRULE_NAME m = "\\"^pp_tex_NAME_PREFIX m^"usedrule"
let pp_tex_PREMISE_NAME m = "\\"^pp_tex_NAME_PREFIX m^"premise"
let pp_tex_DEFN_BLOCK_NAME m = pp_tex_NAME_PREFIX m^"defnblock"
let pp_tex_FUNCLAUSE_NAME m = "\\"^pp_tex_NAME_PREFIX m^"funclause"
let pp_tex_FUNDEFN_BLOCK_NAME m = pp_tex_NAME_PREFIX m^"fundefnblock"
let pp_tex_NT_NAME m = "\\"^pp_tex_NAME_PREFIX m^"nt"
let pp_tex_MV_NAME m = "\\"^pp_tex_NAME_PREFIX m^"mv"
let pp_tex_KW_NAME m = "\\"^pp_tex_NAME_PREFIX m^"kw"
let pp_tex_SYM_NAME m = "\\"^pp_tex_NAME_PREFIX m^"sym"
let pp_tex_COM_NAME m = "\\"^pp_tex_NAME_PREFIX m^"com"
let pp_tex_COMP_NAME m = "\\"^pp_tex_NAME_PREFIX m^"comp"
let pp_tex_COMP_U_NAME m = "\\"^pp_tex_NAME_PREFIX m^"compu"
let pp_tex_COMP_LU_NAME m = "\\"^pp_tex_NAME_PREFIX m^"complu"

let rec tex_command_escape s = 
  String.concat "" 
    (List.map 
       (fun c -> match c with
       | '_' ->"XX" 
       | '#' -> "YY" 
       | '\'' -> "PP" 
       | '0' -> "Zero"
       | '1' -> "One"
       | '2' -> "Two"
       | '3' -> "Three"
       | '4' -> "Four"
       | '5' -> "Five"
       | '6' -> "Six"
       | '7' -> "Seven"
       | '8' -> "Eight"
       | '9' -> "Nine"
       | _ -> String.make 1 c) 
       (Auxl.char_list_of_string s))

and tex_rule_name m ntr = "\\"^pp_tex_NAME_PREFIX m^tex_command_escape ntr 
and tex_drule_name m s = "\\"^pp_tex_NAME_PREFIX m^"drule"^tex_command_escape s
and tex_defn_name m wrapper s = "\\"^pp_tex_NAME_PREFIX m^"defn"^tex_command_escape (wrapper^s)
and tex_defnclass_name m s = "\\"^pp_tex_NAME_PREFIX m^"defns"^tex_command_escape s

and tex_fundefn_name m s = "\\"^pp_tex_NAME_PREFIX m^"fundefn"^tex_command_escape s
and tex_fundefnclass_name m s = "\\"^pp_tex_NAME_PREFIX m^"fundefns"^tex_command_escape s

and pp_tex_terminal m xd tm =
  try (* firstcheck if this terminal is defined in the terminalsproduction *)
    let term_rule = Auxl.rule_of_ntr xd "terminals" in
    let hom_list = (* FZ define aux function for this *)
      (List.find (fun p -> (List.hd p.prod_es) = (Lang_terminal tm))
	 term_rule.rule_ps).prod_homs in
    let hom = List.assoc "tex" hom_list in
    pp_hom_spec m xd hom
  with Not_found -> (* otherwise, standard behaviour *)
    let es = Auxl.pp_tex_escape tm in
    if (*(String.length es > 1) ||*) (Auxl.is_alpha es)
    then pp_tex_KW_NAME m ^ "{"^es^"}" else pp_tex_SYM_NAME m ^"{"^es ^"}"  

and pp_isa_terminal m xd tm =
  try (* firstcheck if this terminal is defined in the terminalsproduction *)
    let term_rule = Auxl.rule_of_ntr xd "terminals" in
    let hom_list = (* FZ define aux function for this *)
      (List.find (fun p -> (List.hd p.prod_es) = (Lang_terminal tm))
	 term_rule.rule_ps).prod_homs in
    let hom = List.assoc "isa" hom_list in
    pp_hom_spec m xd hom
  with Not_found -> (* otherwise, standard behaviour *)
    tm

(* template  *)
(*   ( *)
(*   match m with  *)
(*     Ascii ao ->  *)
(*   | Tex xo ->  *)
(*   | Coq co ->  *)
(*   | Isa io ->  *)

(*   match m with  *)
(*     Ascii _ ->  *)
(*   | Tex _ ->  *)
(*   | Coq _ ->  *)
(*   | Isa _ ->  *)

and pp_plain_dots n =      
  ( match n with 
  | 0 -> pp_DOTDOT 
  | 1 -> pp_DOTDOTDOT 
  | 2 -> pp_DOTDOTDOTDOT 
  | _ -> raise ThisCannotHappen )

and pp_dots m xd n = 
  match m with
  | Ascii ao -> 
      ( match n with 
      | 0 -> pp_DOTDOT 
      | 1 -> pp_DOTDOTDOT 
      | 2 -> pp_DOTDOTDOTDOT 
      | _ -> raise ThisCannotHappen )
  | Tex xo ->
      ( match n with 
      | 0 -> pp_tex_DOTDOT 
      | 1 -> pp_tex_DOTDOTDOT 
      | 2 -> pp_tex_DOTDOTDOTDOT 
      | _ -> raise ThisCannotHappen )
  | Caml _ | Hol _ | Lem _ | Isa _ | Coq _ | Twf _ | Lex _ | Yacc _ -> 
      raise ThisCannotHappen

and pp_uninterpreted m xd s =
  match m with
  | Ascii ao -> col_cyan ao ("(*"^s^"*)")
  | Caml _ | Coq _ | Isa _ | Hol _ | Lem _ | Lex _ | Yacc _ -> "(*"^s^"*)"  
  | Twf _  -> "%{"^s^"}%"  
  | Tex _ -> 
      let es = Auxl.pp_tex_escape s in
      if (String.length es > 1) || (Auxl.is_alpha es) 
      then "\\mathbf{"^es^"}" else es  (* FZ mathbf should be COLOR *)

and pp_maybe_quote_ident m xd s = 
  match m with 
  | Ascii ao -> quote_ident s
  | Tex _ | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> s

and pp_prod_flavour m xd pf = 
  match m with
  | Ascii _ -> pp_BAR
  | Tex _ -> pp_tex_BAR
  | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen

and pp_plain_terminal tm = tm

and pp_terminal m xd tm = 
  match m with 
  | Ascii ao -> col_green ao (quote_ident tm)
  | Tex _ -> pp_tex_terminal m xd tm
  | Coq _ -> tm
  | Isa _ -> pp_isa_terminal m xd tm
  | Hol _ -> tm
  | Lem _ -> tm
  | Twf _ -> tm
  | Caml _ -> "_" (* tm *)
  | Lex _ | Yacc _ -> tm

and pp_terminal_unquoted m xd tm = 
  match m with 
  | Ascii ao -> col_green ao tm
  | Tex _ -> pp_tex_terminal m xd tm
  | Coq _ -> tm
  | Isa _ -> pp_isa_terminal m xd tm
  | Hol _ -> tm
  | Lem _ -> tm
  | Twf _ -> tm
  | Caml _ -> "_" (* tm *)
  | Lex _ | Yacc _ -> tm

and pp_lang_name m xd ln = ln

and pp_plain_nontermroot ntr = ntr

and pp_plain_metavarroot mvr = mvr

and pp_plain_nonterm (ntr,suff) = ntr^pp_plain_suffix suff

and pp_plain_metavar (mvr,suff) = mvr^pp_plain_suffix suff

and pp_plain_nt_or_mv (ntmvr,suff) =
  match ntmvr with
  | Ntr ntr -> pp_plain_nonterm (ntr,suff)
  | Mvr mvr -> pp_plain_metavar (mvr,suff)

and pp_plain_nt_or_mv_root ntmvr =
  match ntmvr with
  | Ntr ntr -> ntr
  | Mvr mvr -> mvr

and pp_plain_nt_or_mv_root_option ntmvro =
  match ntmvro with
  | None -> "None"
  | Some ntmvr -> "Some("^pp_plain_nt_or_mv_root ntmvr^")"

and pp_plain_hom_spec_el hse =
  match hse with
  | Hom_string s -> "Hom_string "^s
  | Hom_index i -> "Hom_index "^(string_of_int i)
  | Hom_terminal t -> "Hom_terminal "^(pp_plain_terminal t)
  | Hom_ln_free_index _ -> "Hom_ln_free_index"

and capitalize_if_twelf_non_type as_type m s =
  match m,as_type with
  | Twf _,false -> String.capitalize s
  | _,_ -> s

and pp_pseudo_hom_spec_el hse =
  match hse with
  | Hom_string s -> s
  | Hom_terminal tm -> tm
  | _ -> Auxl.int_error ("nontermroot hom contains "^pp_plain_hom_spec_el hse)

and pp_nonterm_with_sie_internal as_type m xd sie (ntr,suff) =
  let pp_hom_spec hs =
    String.concat "" (List.map pp_pseudo_hom_spec_el hs) in
  (* ("<<< "^pp_plain_nonterm (ntr,suff)^" "^string_of_int (List.length sie)^">>>"); *)
  let r = Auxl.rule_of_ntr xd (Auxl.primary_ntr_of_ntr xd ntr) in
  (* per P. request, special treatment when printing a nt for which there is a phantom and a tp hom as a type *)
  let hr = try (Some (List.assoc (Auxl.hom_name_for_pp_mode m) r.rule_homs)) with Not_found -> None in
  if r.rule_phantom && not (hr=None) && as_type
  then begin
    pp_hom_spec (Auxl.the hr)
  end
  else begin
    (* the per-ntr_name hom, if any *)
    let homs = List.assoc ntr r.rule_ntr_names in
    let hso = Auxl.hom_spec_for_pp_mode m homs in
    
    let pp_ntr = match hso with
    | None -> capitalize_if_twelf_non_type as_type m ntr
    | Some hs -> pp_hom_spec hs 
    in

    let auxparam_opt = try Some (List.assoc "auxparam" r.rule_homs) with Not_found -> None in
    let auxparam_prefix_opt = 
      match as_type,m,auxparam_opt with
      | true,Caml _,Some hs | true,Lem _,Some hs -> Some (String.concat "" (List.map (function | Hom_string s -> s | Hom_index _ | Hom_terminal _ | Hom_ln_free_index (_,_) -> Auxl.int_error("illegal auxparam hom "^String.concat ""(List.map pp_plain_hom_spec_el hs))) hs))
      | _,_,_ -> None in
    
    match m with
    | Ascii ao -> 
        if not(ao.ppa_ugly) then
          col_yellow ao (quote_ident (pp_ntr^(pp_suffix_with_sie m xd sie suff)))
        else
          col_yellow ao (quote_ident (pp_ntr^"/"^(pp_suffix_with_sie m xd sie suff)))
    | Tex xo -> 
        (* the per-rule hom, if any *)
        let homs' = 
          (Auxl.rule_of_ntr xd (Auxl.primary_ntr_of_ntr xd ntr)).rule_homs in
        let hso'= Auxl.hom_spec_for_pp_mode m homs' in
        
        (match hso,hso' with
        | None,None ->    (* default if no homs *)
            pp_tex_NT_NAME m ^ "{" 
            ^ (Auxl.pp_tex_escape ntr^(pp_suffix_with_sie m xd sie suff)) ^ "}"
        | Some _, _ ->    (* use per-ntr hom, overriding any per-rule hom *)
            (pp_ntr^(pp_suffix_with_sie m xd sie suff))
        | None,Some hs -> (* use per-rule hom *)
            String.concat "" 
              (apply_hom_spec m xd hs 
                 [Auxl.pp_tex_escape ntr^(pp_suffix_with_sie m xd sie suff)]))
    | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> 
        let s0 = pp_ntr ^ (pp_suffix_with_sie m xd sie suff) in
        let s1 = 
          if as_type then s0
          else Auxl.hide_isa_trailing_underscore m s0 in
        let s = match m with
        | Caml _ -> (match auxparam_prefix_opt with Some p -> p^" "^s1 | None -> s1)
        | Lem _ -> (match auxparam_prefix_opt with Some p -> "("^s1^" "^p^")" | None -> s1)
        | _ -> s1 in
        s
  end

and pp_metavar_with_sie_internal as_type m xd sie (mvr,suff) = 
  (*  print_string ("<<<"^pp_plain_metavar (mvr,suff)^">>>\n");flush stdout; *)
  let pp_hom_spec hs =
    String.concat "" (List.map pp_pseudo_hom_spec_el hs) in
  let mvd = List.find (function mvd -> List.exists (function (mvr',homs)->mvr'=mvr) mvd.mvd_names) xd.xd_mds in
  (* per P. request, special treatment when printing a mv for which there is a phantom and a tp hom as a type *)
  let hr = try (Some (List.assoc (Auxl.hom_name_for_pp_mode m) mvd.mvd_rep)) with Not_found -> None in
  if mvd.mvd_phantom && not (hr=None) && as_type
  then begin
    pp_hom_spec (Auxl.the hr)
  end
  else begin
    (* standard behaviour *)
    let homs = List.assoc mvr mvd.mvd_names in
    let hso = Auxl.hom_spec_for_pp_mode m homs in
    let pp_mvr = match hso with
    | None -> capitalize_if_twelf_non_type as_type m mvr
    | Some hs -> pp_hom_spec hs in
    match m with 
    | Ascii ao -> col_red ao (pp_mvr^(pp_suffix_with_sie m xd sie suff))
    | Tex xo -> 
        (* the per-mvd hom, if any *)
        let homs' = 
          (Auxl.mvd_of_mvr xd (Auxl.primary_mvr_of_mvr xd mvr)).mvd_rep in
        let hso'= Auxl.hom_spec_for_pp_mode m homs' in

        (match hso,hso' with
        | None,None ->    (* default if no homs *)
            pp_tex_MV_NAME m ^  "{" 
            ^ (Auxl.pp_tex_escape mvr^(pp_suffix_with_sie m xd sie suff)) ^ "}"
        | Some _, _ ->    (* use per-mvr hom, overriding any per-mvd hom *)
            (pp_mvr^(pp_suffix_with_sie m xd sie suff))
        | None,Some hs -> (* use per-mvd hom *)
            String.concat "" 
              (apply_hom_spec m xd hs 
                 [Auxl.pp_tex_escape mvr^(pp_suffix_with_sie m xd sie suff)]))

    | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> 
        let s = pp_mvr ^ (pp_suffix_with_sie m xd sie suff) in
        if as_type then s
        else Auxl.hide_isa_trailing_underscore m s
  end

and pp_nt_or_mv_with_sie_internal as_type m xd sie (ntmv,suff) =
  match ntmv with
  | Ntr nt -> pp_nonterm_with_sie_internal as_type m xd sie (nt,suff)
  | Mvr mv -> pp_metavar_with_sie_internal as_type m xd sie (mv,suff)
  
and pp_nt_or_mv_with_de_with_sie_internal as_type m xd sie (de :dotenv) ((ntmvr,suff0) as ntmv) =
  match m with
  | Ascii _ | Tex _ -> pp_nt_or_mv_with_sie_internal as_type m xd sie ntmv
  | Isa _ | Coq _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> 
      let (de1,de2) = de in
      match try Some(List.assoc ntmv de2) with Not_found -> None with
      | None -> pp_nt_or_mv_with_sie m xd sie ntmv
      | Some (suff,suffi,bound) ->
          let de1i = List.assoc bound de1 in
          let non_zero_lower_of_bound (b : bound) : suffix_item option =
            match b with
            | Bound_dotform bd -> 
                if bd.bd_lower = Si_num "0" then None else Some bd.bd_lower 
            | Bound_comp _ -> None
            | Bound_comp_u _ -> None
            | Bound_comp_lu bclu -> 
                if bclu.bclu_lower = Si_num "0" then None else Some bclu.bclu_lower in
          match m with
          | Isa _ -> 
              "((%"^de1i.de1_pattern^" . "^pp_nt_or_mv_with_sie m xd ((Si_var ("_",0))::sie) (ntmvr,suff)^")"
              ^ " (List.nth " ^ de1i.de1_compound_id ^ " " 
              ^ "(" ^ pp_plain_suffix_item suffi 
              ^ 
                (match non_zero_lower_of_bound bound with 
                | None -> ""
                | Some suffi -> " - "^pp_plain_suffix_item suffi)
              ^ ")))"
          | Hol _ -> 
              " ((\\ "^de1i.de1_pattern^" . "^pp_nt_or_mv_with_sie m xd ((Si_var ("_",0))::sie) (ntmvr,suff)^")"
              ^ " (EL "  ^ " " 
              ^ "(" ^ pp_plain_suffix_item suffi 
              ^ 
                (match non_zero_lower_of_bound bound with 
                | None -> ""
                | Some suffi -> " - "^pp_plain_suffix_item suffi)
              ^ ") " ^ de1i.de1_compound_id^")) "
          | Lem _ -> 
              lemTODO "8" (
              " ((fun "^de1i.de1_pattern^" -> "^pp_nt_or_mv_with_sie m xd ((Si_var ("_",0))::sie) (ntmvr,suff)^")"
              ^ " (List.nth "  ^ " " 
              ^ de1i.de1_compound_id 
              ^ " "
              ^ "(" ^ pp_plain_suffix_item suffi 
              ^ 
                (match non_zero_lower_of_bound bound with 
                | None -> ""
                | Some suffi -> " - "^pp_plain_suffix_item suffi)
              ^ ") " ^")) "
             )
          | Coq co ->  
    	      let hyp_var = c:=!c+1; "t"^(string_of_int !c); in (* FZ need a properly freshened name here *)
	      let ty_list = Str.split (Str.regexp "(\\|*\\|)") de1i.de1_coq_type_of_pattern in
              let proj_arg = pp_nt_or_mv_with_sie m xd ((Si_var ("_",0))::sie) (ntmvr,suff) in
              let suffi_s = pp_plain_suffix_item suffi in
	      let nth_pred = 
		if co.coq_expand_lists 
		then 
		  "     nth_list_" ^String.concat "_" ty_list ^ " " 
		  ^ Auxl.paren (suffi_s
			   ^ (match non_zero_lower_of_bound bound with 
			   | None -> ""
			   | Some suffi -> " - "^pp_plain_suffix_item suffi))
		  ^ " " ^ de1i.de1_compound_id 
		else 
		  "     nth_error "
		  ^ de1i.de1_compound_id ^ " "
		  ^ Auxl.paren (suffi_s
			   ^ (match non_zero_lower_of_bound bound with 
			   | None -> ""
			   | Some suffi -> " - "^pp_plain_suffix_item suffi)) in
	       
	      co.coq_non_local_hyp_defn_vars := 
		!(co.coq_non_local_hyp_defn_vars) 
		@ [ (hyp_var,Some de1i.de1_coq_type_of_pattern) ]; (* ; (quant_suffi_s,None) now computed by extract_quantifiers *)
	      co.coq_non_local_hyp_defn := 
		!(co.coq_non_local_hyp_defn) 
		^ nth_pred 
		^ " = Some " ^ hyp_var ^ " ->\n";
	      ( if (String.compare de1i.de1_pattern proj_arg = 0)
	      then hyp_var 
	      else "(match " ^ hyp_var ^ " with " ^ de1i.de1_pattern ^ " => " ^ proj_arg ^" end)" )
          | Ascii _ | Tex _ -> raise ThisCannotHappen
          | Twf _ -> raise TwelfNotImplemented
          | Caml _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_symterm for proper symterms not supported"

and pp_nonterm_with_sie m xd sie (ntr,suff) = 
  pp_nonterm_with_sie_internal false m xd sie (ntr,suff) 

and pp_metavar_with_sie m xd sie (mvr,suff) = 
  pp_metavar_with_sie_internal false m xd sie (mvr,suff) 

and pp_nt_or_mv_with_sie m xd sie (ntmv,suff) =
  pp_nt_or_mv_with_sie_internal false m xd sie (ntmv,suff) 

and pp_nt_or_mv_with_de_with_sie m xd sie (de :dotenv) ((ntmvr,suff0) as ntmv) =
  pp_nt_or_mv_with_de_with_sie_internal false m xd sie de ntmv

and pp_nonterm m xd (ntr,suff) =
  pp_nonterm_with_sie m xd [] (ntr,suff)

and pp_metavar m xd (mvr,suff) = 
  pp_metavar_with_sie m xd [] (mvr,suff) 

and pp_nonterm_with_de_with_sie m xd sie de (ntr,suff0) =
  let ntmv = (Ntr ntr,suff0) in
  pp_nt_or_mv_with_de_with_sie m xd sie de ntmv

and pp_metavar_with_de_with_sie m xd sie de (mvr,suff0) =
  let ntmv = (Mvr mvr,suff0) in
  pp_nt_or_mv_with_de_with_sie m xd sie de ntmv

and pp_nontermroot m xd ntr = 
  pp_nonterm m xd (ntr,[])

and pp_metavarroot m xd mvr =   
  pp_metavar m xd (mvr,[])   

and pp_nontermroot_ty m xd ntr = 
  (*Auxl.pp_type_name m xd*) (pp_nonterm_with_sie_internal true m xd [] (ntr,[]))

and pp_metavarroot_ty m xd mvr =
  (*Auxl.pp_type_name m xd*) (pp_metavar_with_sie_internal true m xd [] (mvr,[]))

and pp_nt_or_mv m xd (ntmv,suff) =
  match ntmv with
  | Ntr nt -> pp_nonterm m xd (nt,suff)
  | Mvr mv -> pp_metavar m xd (mv,suff)

and pp_nt_or_mv_root m xd ntmvr =
  match ntmvr with
  | Ntr ntr -> pp_nontermroot m xd ntr
  | Mvr mvr -> pp_metavarroot m xd mvr
        
and pp_nt_or_mv_root_ty m xd ntmvr =
  match ntmvr with
  | Ntr ntr -> pp_nontermroot_ty m xd ntr
  | Mvr mvr -> pp_metavarroot_ty m xd mvr

and coq_maybe_decide_equality m xd homs ntmvr = 
  match
    try Some (List.assoc "coq-equality" homs) with Not_found -> None
  with
  | None -> ""
  | Some eh ->
      let type_name = pp_nt_or_mv_root_ty m xd ntmvr in
      
      let select x y tn =
	if (String.compare x tn = 0) then y else x in

      let var_1 = select "x" "x'" type_name in
      let var_2 = select "y" "y'" type_name in

      "Lemma eq_" ^ type_name
      ^ ": forall ("^var_1^" "^var_2^" : " ^ type_name ^ ")" 
      ^ ", {"^var_1^" = " ^var_2^"} + {"^var_1^" <> " ^var_2^"}.\n"
      ^ "Proof.\n"
      ^ ( match eh with
        | [ ] -> "  decide equality; auto with ott_coq_equality arith."
        | [ Hom_string s ] -> s 
        | _ -> Auxl.error "malformed coq-equality homomorphism\n" )
      ^ "\nDefined.\n"
      ^ "Hint Resolve eq_" ^ type_name  ^ " : ott_coq_equality.\n"

and pp_metavardefn m xd mvd =
  let pp_com = pp_com_strings m xd mvd.mvd_rep [pp_metavar_with_sie m xd [] (mvd.mvd_name,[])] in
  match m with 
  | Ascii ao ->
      pp_METAVAR ^ " " 
      ^ (String.concat " , "(List.map 
                               (function (mvr,homs)->pp_metavarroot m xd mvr)
                               mvd.mvd_names)) 
      ^ " " ^ pp_CCE ^ " " 
      ^ pp_metavarrep m xd mvd.mvd_rep "" ^ "\n"
  | Tex xo -> 
      " $ "
      ^ (String.concat " ,\\, "(List.map 
				  (function (mvr,homs)->pp_metavarroot m xd mvr)
				  mvd.mvd_names)) 
      ^ " $ & " ^ pp_com ^ " \\\\"
  | _ ->
      ( match mvd.mvd_phantom with
      | true -> ""
      | false -> ( match m with
	| Coq co ->
	    let type_name = pp_metavarroot_ty m xd mvd.mvd_name in
	    "Definition " ^  type_name ^ " := " 
	    ^ pp_metavarrep m xd mvd.mvd_rep type_name ^ "." ^ pp_com ^ "\n"
	    ^ coq_maybe_decide_equality m xd mvd.mvd_rep (Mvr mvd.mvd_name)
	| Caml oo ->
	    let type_name = pp_metavarroot_ty m xd mvd.mvd_name in 
	    "type "
	    ^ type_name 
	    ^ " = " 
	    ^ pp_metavarrep m xd mvd.mvd_rep type_name
	    ^ pp_com ^ "\n"
	| Isa io ->
	    let type_name = pp_metavarroot_ty m xd mvd.mvd_name in 
	    if Auxl.is_nominal_atom m xd mvd
	    then
	      "atom_decl \"" ^ type_name ^ "\"" ^ pp_com ^ "\n"
	    else
	      "types \"" ^ type_name ^ "\" = \"" 
	      ^ pp_metavarrep m xd mvd.mvd_rep type_name^ "\"" ^ pp_com ^ "\n"
	| Hol ho -> 
	    let type_name = pp_metavarroot_ty m xd mvd.mvd_name in 
	    "val _ = type_abbrev(\""
	    ^ type_name
	    ^ "\", ``:"
	    ^ pp_metavarrep m xd mvd.mvd_rep type_name ^ "``);"
	    ^ pp_com ^ "\n"
	| Lem lo -> 
	    let type_name = pp_metavarroot_ty m xd mvd.mvd_name in 
	    "type "
	    ^ type_name
	    ^ " = "
	    ^ pp_metavarrep m xd mvd.mvd_rep type_name
	    ^ pp_com ^ "\n"
	| Twf _ -> 
	    "%abbrev "
	    ^ pp_metavarroot_ty m xd mvd.mvd_name 
	    ^ " : type = nat.\n"
        | Lex _ -> "" 
        | Yacc _ -> ""
	| Ascii _ | Tex _ -> raise Auxl.ThisCannotHappen ))

and pp_metavarrep m xd mvd_rep type_name =
  match m with
  | Ascii ao ->
      pp_homomorphism_list m xd mvd_rep
  | Tex _ | Lex _ | Yacc _ -> 
      Auxl.errorm m "pp_metavarrep"
  | Isa io ->
      ( try
	let hs = List.assoc "isa" mvd_rep in
	pp_hom_spec m xd hs
      with Not_found -> Auxl.warning ("undefined isa metavarrep for "^type_name^"\n"); "UNDEFINED" )
  | Hol ho ->
      ( try
	let hs = List.assoc "hol" mvd_rep in
	pp_hom_spec m xd hs
      with Not_found -> Auxl.warning ("undefined hol metavarrep for "^type_name^"\n"); "UNDEFINED" )
  | Lem lo ->
      ( try
	let hs = List.assoc "lem" mvd_rep in
	pp_hom_spec m xd hs
      with Not_found -> Auxl.warning ("undefined lem metavarrep for "^type_name^"\n"); "UNDEFINED" )
  | Coq co ->
      ( try
	let hs = List.assoc "coq" mvd_rep in
	pp_hom_spec m xd hs
      with Not_found -> Auxl.warning ("undefined coq metavarrep for "^type_name^"\n"); "UNDEFINED" )
  | Twf wo ->
      ( try
	let hs = List.assoc "twf" mvd_rep in
	pp_hom_spec m xd hs
      with Not_found -> Auxl.warning ("undefined Twelf metavarrep for "^type_name^"\n"); "UNDEFINED" )
  | Caml oo ->
      ( try
	let hs = List.assoc "ocaml" mvd_rep in
	pp_hom_spec m xd hs
      with Not_found -> Auxl.warning ("undefined OCaml metavarrep for "^type_name^"\n"); "UNDEFINED" )
	
and pp_prodname m xd pn =  (* FZ this is never called *)
  match m with
  | Caml _ | Lem _ -> String.capitalize (pp_maybe_quote_ident m xd pn)
  | _ -> pp_maybe_quote_ident m xd pn

and pp_category m xd cat = pp_maybe_quote_ident m xd cat

and apply_hom_spec m xd hses ss =
  match hses with
  | [] -> []
  | Hom_string s :: hses' -> 
      s :: apply_hom_spec m xd hses' ss 
  | Hom_index i :: hses' -> 
      (List.nth ss i) :: apply_hom_spec m xd hses' ss
  | Hom_terminal tm :: hses' -> 
      pp_terminal m xd tm :: apply_hom_spec m xd hses' ss
  | Hom_ln_free_index (fvs,i) :: hses' ->
      (* fvs are only taken into account when opening terms in ln_transforms, and should be ignored here *)
      (List.nth ss i) :: apply_hom_spec m xd hses' ss
    
and pp_com_es m xd homs es = 
  match Auxl.hom_spec_for_hom_name "com" homs with
  | None -> ""
  | Some hs ->
    let ss = 
      Auxl.option_map (pp_element m xd [] false) 
      	(List.filter
           (function 
             | (Lang_nonterm (_,_)|Lang_metavar (_,_)|Lang_list _) -> true
             | Lang_terminal _ -> false
             | (Lang_option _|Lang_sugaroption _) -> 
               raise (Invalid_argument "com for prods with option or sugaroptions not implemented"))
           es) in
    match m with
    | Tex _ ->
      pp_tex_COM_NAME m  ^"{"
      ^ String.concat "" (apply_hom_spec m xd hs (List.map (function s -> "$"^s^"$") ss))
      ^ "}" 
    | Isa _ -> " -- {* " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " *}"
    | Coq _ -> " (*r " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " *)" 
    | Hol _ | Lem _ | Caml _ | Lex _ ->  " (* " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " *)" 
    | Yacc _ -> "/* " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " */" 
    | Ascii _ | Twf _ -> ""

and pp_com_strings m xd homs ss =
  match Auxl.hom_spec_for_hom_name "com" homs with
  | None -> ""
  | Some hs ->
    match m with
    | Tex _ ->
      pp_tex_COM_NAME m  ^"{"
      ^ String.concat "" (apply_hom_spec m xd hs (List.map (function s -> "$"^s^"$") ss))
      ^ "}"
    | Isa _ -> " -- {* " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " *}"
    | Coq _ -> " (*r " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " *)"
    | Hol _ | Lem _ | Caml _ | Lex _ ->  " (* " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " *)"
    | Yacc _ -> "/* " ^ String.concat "" (apply_hom_spec m xd hs ss) ^ " */" 
    | Ascii _ | Twf _ -> ""


and pp_homomorphism m xd (hn,hs) =
  match (m,hn) with 
  | (Ascii ao, _) -> 
      pp_DOUBLELEFTBRACE ^ " "
      ^ (pp_hom_name m xd hn) ^ " "
      ^ (pp_hom_spec m xd hs) ^ " "
      ^ pp_DOUBLERIGHTBRACE
(*   (\* these are used only when pp_embeds calls pp_homomorphism *\) *)
(*   | (Coq co, "coq") -> (pp_hom_spec m xd hs)^"\n\n"  *)
(*                        (\* raise ThisCannotHappen *\) *)
(*   | (Isa io, "isa") -> (pp_hom_spec m xd hs)^"\n\n"  *)
(*                        (\* raise ThisCannotHappen *\) *)
(*   | (Hol ho, "hol") -> (pp_hom_spec m xd hs)^"\n\n"  *)
(*                        (\* raise ThisCannotHappen *\) *)
  | (Coq _, _) | (Isa _, _) | (Hol _,_) | (Lem _,_) | (Twf _,_) | (Caml _,_) | (Lex _,_) | (Yacc _, _) -> ""
  | (Tex _, _) -> Auxl.errorm m "pp_homomorphism"

and pp_homomorphism_list m xd homs =
  match m with 
  | Ascii ao -> 
      String.concat " " (List.map (pp_homomorphism m xd) homs)
  | Tex xo -> raise ThisCannotHappen
  | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen

and pp_hom_name m xd hn = pp_maybe_quote_ident m xd hn
  
and pp_hom_spec m xd hs = 
  String.concat "" (List.map (pp_hom_spec_el m xd) hs)

and pp_hom_spec_el m xd hse = 
  match m with 
  | Ascii ao -> 
      ( match hse with
      | Hom_string s ->  s
      | Hom_index i -> pp_DOUBLELEFTBRACKET^string_of_int i^pp_DOUBLERIGHTBRACKET 
      | Hom_terminal s -> pp_DOUBLELEFTBRACKET^s^pp_DOUBLERIGHTBRACKET
      | Hom_ln_free_index (mvs,s) -> 
	  pp_DOUBLELEFTBRACKET
	  ^ String.concat "" (List.map (fun mv -> "("^string_of_int mv^")") mvs)
	  ^ string_of_int s 
	  ^ pp_DOUBLERIGHTBRACKET)
  | Tex xo -> 
      ( match hse with
      | Hom_string s -> s
      | Hom_terminal s -> Auxl.errorm m "pp_hom_spec_el"
      | Hom_index i -> "UNIMPLEMENTED"
      | Hom_ln_free_index _ -> Auxl.errorm m "pp_hom_spec el")
  | Coq _ | Twf _ | Caml _ | Lex _ | Yacc _ -> 
      ( match hse with
      | Hom_string s -> s
      | Hom_terminal s -> Auxl.errorm m "pp_hom_spec_el"
      | Hom_index i -> "UNIMPLEMENTED"
      | Hom_ln_free_index _ -> Auxl.errorm m "pp_hom_spec el")
  | Isa _ | Hol _ | Lem _ ->       
      ( match hse with
      | Hom_string s -> s
      | Hom_terminal s -> s
      | Hom_index i -> "UNIMPLEMENTED"
      | Hom_ln_free_index _ -> Auxl.errorm m "pp_hom_spec el")

and pp_plain_suffix suff = String.concat "" (List.map pp_plain_suffix_item suff)
        
and pp_plain_suffixvar_offset n = 
  if n=0 then "" 
  else if n>0 then "+"^string_of_int n
  else string_of_int n

and pp_tex_suffixvar m xd (s,n) = 
  let mvr = s in
  let mvd = List.find (function mvd -> List.exists (function (mvr',homs)->mvr'=mvr) mvd.mvd_names) xd.xd_mds in
  let homs = List.assoc mvr mvd.mvd_names in
  let hso = Auxl.hom_spec_for_pp_mode m homs in
  let pp_mvr = match hso with
  | None -> mvr
  | Some hs -> 
      String.concat "" (List.map pp_pseudo_hom_spec_el hs) in
  if n=0 then pp_tex_MV_NAME m ^"{"^pp_mvr^"}" 
  else "{"^pp_tex_MV_NAME m ^"{"^pp_mvr^"}"^pp_plain_suffixvar_offset n^"}" 

and pp_ascii_suffixvar (s,n) = 
  if n=0 then s
  else s^pp_plain_suffixvar_offset n

and pp_plain_suffix_item suffi = 
  ( match suffi with
  | Si_num s -> s
  | Si_punct s -> s
  | Si_var (s,n) -> s^pp_plain_suffixvar_offset n
(*  | Si_index i -> "SHOULDNT HAPPEN: Si_index "^string_of_int i ) *)
  | Si_index i -> "["^string_of_int i ^"]")

and pp_plain_sie sie = String.concat ";" (List.map pp_plain_suffix_item sie)

and pp_suffix_with_sie m xd sie suff = 
  match m with 
  | Ascii ao -> 
      if not(ao.ppa_ugly) then
        String.concat "" (List.map (pp_suffix_item_with_sie m xd sie false) suff)
      else
        String.concat "|" (List.map (pp_suffix_item_with_sie m xd sie false) suff)
  | Tex _ ->
      let suff_subscript = List.filter
          (function suffi -> match suffi with
          | Si_num _ -> true
          | Si_var (_,_) -> true 
          | Si_index _ -> true
          | _ -> false) suff in
      let suff_nosubscript = List.filter
          (function suffi -> match suffi with
          | Si_punct "\'" -> true
          | _ -> false) suff in
      String.concat "" (List.map (pp_suffix_item_with_sie m xd sie true) suff_nosubscript)
      ^ (match suff_subscript with 
      | [] -> ""
      | _ -> 
          "_{"
          ^ String.concat "\\," (List.map (pp_suffix_item_with_sie m xd sie true) suff_subscript)
          ^ "}")
  | (Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _) ->
      (String.concat "" (List.map (pp_suffix_item_with_sie m xd sie false) suff)) 


and pp_suffix_item_with_sie m xd sie nosubscript suffi = 
  match m with 
  | Ascii ao -> 
      let s = ( match suffi with
      |	Si_num s -> s
      | Si_punct s -> s
      | Si_var (s,n) -> s^pp_plain_suffixvar_offset n
      | Si_index i -> 
          pp_suffix_item_with_sie m xd sie nosubscript 
            ( (*List.nth sie i*) try List.nth sie i with Failure _ -> Si_num "999")) 
      in
      if ao.ppa_ugly then "["^s^"]" else s
  | (Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _) -> 
      ( match suffi with
      |	Si_num s -> s
      | Si_punct s -> s
      | Si_var (s,n) ->  
          if n=0 then s 
          else failwith "non-zero suffix offset in pp_suffix_item_with_sie"
      | Si_index i -> 
          pp_suffix_item_with_sie m xd sie nosubscript 
            ( (*List.nth sie i*) try List.nth sie i with Failure _ -> Si_num "999") ) 
  | Tex xo ->  
      ( match suffi with
      | Si_num s -> (*if String.length s = 1 then "_"^s else*)
        (if nosubscript then "" else "_")^"{\\mathrm{"^s^"}}"
      | Si_punct s -> s
      | Si_var (s,n) ->  
          (if nosubscript then "" else "_")^pp_tex_suffixvar m xd (s,n)
      | Si_index i -> pp_suffix_item_with_sie m xd sie nosubscript (List.nth sie i) )

(* and pp_plain_bound (suffil,suffiu) = *)
(*   "(" *)
(*   ^ pp_plain_suffix_item suffil ^"," *)
(*   ^ pp_plain_suffix_item suffiu  *)
(*   ^ ")" *)
and pp_plain_bound b = 
  match b with
  | Bound_dotform bd -> 
      "("
      ^ pp_plain_suffix_item bd.bd_lower 
      ^ pp_plain_dots bd.bd_length
      ^ pp_plain_suffix_item bd.bd_upper
      ^ ")"
  | Bound_comp bc ->
      "("
      ^ bc.bc_variable
      ^ ")"
  | Bound_comp_u bcu ->
      "("
      ^ bcu.bcu_variable 
      ^ " IN "
      ^ pp_plain_suffix_item bcu.bcu_upper
      ^ ")"
  | Bound_comp_lu bclu ->
      "("
      ^ bclu.bclu_variable 
      ^ " IN "
      ^ pp_plain_suffix_item bclu.bclu_lower
      ^ pp_plain_dots bclu.bclu_length
      ^ pp_plain_suffix_item bclu.bclu_upper
      ^ ")"
          
and pp_plain_bound_option boundo = 
  match boundo with 
  | None -> "None: "
  | Some bound ->pp_plain_bound bound^": "

and pp_plain_prod_env pe =
  String.concat "; " (List.map pp_plain_bound_option pe)

(* was   String.concat "; " (List.map (function (n,boundo) -> "("^string_of_int n^","^pp_plain_bound_option boundo^")") pe)*)

and pp_plain_mvs_elem ((mvr:metavarroot),(mv:metavar),(pe:prod_env)) =
  "("^pp_plain_metavarroot mvr^","
  ^ pp_plain_metavar mv^","
  ^ pp_plain_prod_env pe ^")"

and pp_plain_nts_elem ((ntr:nontermroot),(nt:nonterm),(pe:prod_env)) =
  "("^pp_plain_nontermroot ntr^","
  ^ pp_plain_nonterm nt^","
  ^ pp_plain_prod_env pe ^")"

and pp_plain_mvset (mvset:MvSet.t) =
  "{"
  ^ String.concat ", " 
      (MvSet.fold 
         (fun x ss -> ss @ [pp_plain_mvs_elem x])
         mvset
         [])
  ^ "}"

and pp_plain_ntset (ntset:NtSet.t) =
  "{"
  ^ String.concat ", " 
      (NtSet.fold 
         (fun x ss -> ss @ [pp_plain_nts_elem x])
         ntset
         [])
  ^ "}"

and pp_plain_dotenv ((de1,de2)) = pp_plain_dotenv1 de1 ^ pp_plain_dotenv2 de2

and pp_plain_dotenv1 de1 = 
  "de1:  "
  ^ String.concat "      " (List.map 
    (function (bound,de1i) ->
      (pp_plain_bound bound ^": "^de1i.de1_compound_id^" "^de1i.de1_pattern^" "^de1i.de1_coq_type_of_pattern^" "^de1i.de1_hol_type_of_compound_id^"\n"))
    de1)

and pp_plain_dotenv2 de2 = 
  "de2:  "
  ^ String.concat " , " 
      (List.map 
         (function (ntmvr,suff) as ntmv,z -> 
           let (suff',suffi,bound) = z in
           pp_plain_nt_or_mv  ntmv ^ "=" 
           ^ pp_plain_nt_or_mv  (ntmvr,suff') ^ "." 
           ^ pp_plain_suffix_item suffi ^ ":" 
           ^ pp_plain_bound bound) 
         de2)
  ^ "\n"

and pp_plain_subntr_data subntr_data = 
  match subntr_data with
  | None -> "None"
  | Some (ntr,ntr') -> "Some("^pp_plain_nontermroot ntr^","^pp_plain_nontermroot ntr'^")"

and pp_plain_dotenv3 de3 = 
  "de3 = "
  ^ String.concat " " 
      (List.map (function (ntmv,subntr_data) -> 
        "("^pp_plain_nt_or_mv ntmv ^ ", " ^ pp_plain_subntr_data subntr_data^")") de3)

and pp_plain_bindspec bs =
  match bs with
  | Bind (mse, nonterm) -> "Bind ("^pp_plain_mse mse^", "^pp_plain_nonterm nonterm^")"
  | AuxFnDef (f,mse) -> "AuxFnDef ("^f^", "^pp_plain_mse mse^")"
  | NamesEqual (_,_) -> "NamesEqual"
  | NamesDistinct (_,_) -> "NamesDistinct"
  | AllNamesDistinct _ -> "AllNamesDistinct"

and pp_bindspec m xd sie de bs = 
  match bs with
  | Bind (mse,nt) -> 
      ( match m with 
      | Ascii ao -> 
          pp_BIND^" " ^  pp_mse_string m xd sie de mse ^ " " 
	  ^ pp_IN ^ " " ^ pp_nonterm m xd nt
      | Tex xo -> 
          pp_tex_BIND ^ "\\; " ^  pp_mse_string m xd sie de mse ^ "\\; "
	  ^ pp_tex_IN ^ "\\; " ^ pp_nonterm m xd nt
      | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen )
  | AuxFnDef (f,mse) -> 
      ( match m with 
      | Ascii ao -> pp_auxfn m xd f ^ "" ^ pp_EQ ^ "" ^ pp_mse_string m xd sie de mse
      | Tex xo -> pp_auxfn m xd f ^ "" ^ pp_tex_EQ ^ "" ^ pp_mse_string m xd sie de mse
      | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen )
  | NamesEqual (mse,mse') -> 
      ( match m with 
      | Ascii ao -> 
          pp_NAMES ^ "" ^ pp_LPAREN ^ "" ^ pp_mse_string m xd sie de mse ^ "" ^ pp_RPAREN 
	  ^ "" ^ pp_EQ ^ "" ^ pp_NAMES ^ "" 
	  ^ pp_LPAREN ^ "" ^ pp_mse_string m xd sie de mse' ^ "" ^ pp_RPAREN
      | Tex xo -> 
          pp_tex_NAMES ^ "" ^ pp_tex_LPAREN ^ "" ^ pp_mse_string m xd sie de mse 
	  ^ "" ^ pp_tex_RPAREN ^ "\\," ^ pp_tex_EQ ^ "\\," ^ pp_tex_NAMES
	  ^ "" ^ pp_tex_LPAREN ^ "" ^ pp_mse_string m xd sie de mse' ^ "" ^ pp_tex_RPAREN
      | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen )
  | NamesDistinct (mse,mse') -> 
      ( match m with 
      | Ascii ao -> 
          pp_NAMES ^ "" ^ pp_LPAREN ^ "" ^ pp_mse_string m xd sie de mse ^ "" ^ pp_RPAREN
	  ^ "" ^ pp_HASH ^ "" ^ pp_NAMES ^ "" ^ pp_LPAREN ^ "" 
	  ^ pp_mse_string m xd sie de mse' ^ "" ^ pp_RPAREN
      | Tex xo -> 
          pp_tex_NAMES ^ "" ^ pp_tex_LPAREN ^ "" ^ pp_mse_string m xd sie de mse 
	  ^ ""^pp_tex_RPAREN ^ "\\," ^ pp_tex_HASH ^ "\\,"
	  ^ pp_tex_NAMES ^ "" ^ pp_tex_LPAREN ^ "" ^ pp_mse_string m xd sie de mse' 
	  ^ ""^pp_tex_RPAREN
      | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen )
  | AllNamesDistinct mse -> 
      ( match m with 
      | Ascii ao -> 
          pp_DISTINCTNAMES ^ "" ^ pp_LPAREN ^ "" ^ pp_mse_string m xd sie de mse 
	  ^ "" ^ pp_RPAREN
      | Tex xo -> 
          pp_tex_DISTINCTNAMES ^ "" ^ pp_tex_LPAREN ^ "" ^ pp_mse_string m xd sie de mse 
	  ^ "" ^ pp_tex_RPAREN
      | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen ) 

and pp_bindspec_list m xd sie de bs = 
  match m with
  | Tex _ -> 
      (List.map (pp_bindspec m xd sie de) bs)

(*       ( match bs with  *)
(*       | [] -> " $ & $ "  *)
(*       | [b] ->  *)
(* 	  "    " ^ pp_tex_BIND_LEFT_DELIM ^ " $ & $ "  *)
(* 	  ^  (pp_bindspec m xd sie de b) ^ "  \\ \n" *)
(* 	  ^ pp_tex_BIND_RIGHT_DELIM *)
(*       | bs ->   *)
(* 	  pp_tex_BIND_LEFT_DELIM ^ " $ & \n $ "  *)
(* 	  ^ (String.concat  *)
(*                " $ \\\\ \n  &&&&      $ "  *)
(*                (List.map (pp_bindspec m xd sie de) bs))  *)
(* 	  ^ (\* " $ & \\ $ " ^*\) pp_tex_BIND_RIGHT_DELIM ) *)
  | Ascii _ | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ | Lex _ | Yacc _ -> raise ThisCannotHappen 

and pp_plain_mse mse = 
  match mse with
  | MetaVarExp mv ->
      "(MetaVarExp "^pp_plain_metavar  mv ^")"
  | NonTermExp nt -> 
      "(NonTermExp "^ pp_plain_nonterm nt ^")"
  | MetaVarListExp (mv,b) ->
      "(MetaVarListExp "^pp_plain_metavar  mv^","^pp_plain_bound b ^")"
  | NonTermListExp (nt,b) ->
      "(NonTermListExp "^pp_plain_nonterm nt^","^pp_plain_bound b ^")"
  | Aux(f,nt) -> 
      "(Aux "^f^"("^ pp_plain_nonterm nt ^"))"
  | AuxList(f,nt,b) -> 
      "(AuxList "^f^"("^ pp_plain_nonterm nt ^","^pp_plain_bound b^"))"
  | Union(mse,mse') -> 
      "(Union "^pp_plain_mse mse^","^pp_plain_mse mse'^")"
  | Empty -> 
      "Empty"

and mse_split_inprod_counter = ref []
and mse_split_prod_counter = ref []

and pp_mse_string m xd sie de mse = 
  let (x,_,_) = (pp_mse m xd sie de false "" None mse) 
  in x

and pp_mse m xd sie de isa_list_name_flag prod_name ntmvro mse : string * nontermroot list * (int_func list) = 
  (* P asks: what is the role of the ntmvro argument here?  *)
  (* print_string ("pp_mse: " ^ pp_plain_mse mse ^"    "^pp_plain_nt_or_mv_root_option ntmvro ^"\n");flush stdout; *)
  match mse with
  | MetaVarExp mv ->
      ( match m with
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Ascii _ | Tex _ -> (* "\\{" ^*)  pp_metavar_with_sie m xd sie mv (* ^ "\\}" *)
      | Isa _ | Hol _ | Lem _ | Caml _ -> "["^pp_metavar_with_sie m xd sie mv^"]"
      | Coq _ -> "(cons " ^ pp_metavar_with_sie m xd sie mv ^ " nil)" 
      | Twf _ -> "(natlist/cons " ^ pp_metavar_with_sie m xd sie mv ^ " natlist/nil)" ), [], []
  | NonTermExp nt -> 
      ( match m with
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Ascii _ | Tex _ -> (* "\\{" ^*)  pp_nonterm_with_sie m xd sie nt (* ^ "\\}" *)
      | Isa _ | Hol _ | Lem _ | Caml _ -> "["^pp_nonterm_with_sie m xd sie nt^"]"
      | Coq _ -> "(cons " ^ pp_nonterm_with_sie m xd sie nt ^ " nil)" 
      | Twf _ -> "(natlist/cons " ^ pp_nonterm_with_sie m xd sie nt ^ " natlist/nil)" ), [], [] 
  | MetaVarListExp (mv,b) ->
      (* fake up a symterm_list_body *)
      let stlb = {stl_bound = b;
                  stl_elements = [Ste_metavar (dummy_loc,Auxl.primary_mvr_of_mvr xd (fst mv),mv) ];
                  stl_loc = dummy_loc } in
      let dummy_prod_es = [Lang_metavar (Auxl.primary_mvr_of_mvr xd (fst mv),mv)] in
      let dummy_tmopt = None in
      (* and pp that *)
      let fake = 
	String.concat "" 
          (List.map fst 
             (pp_symterm_list_body m xd sie de dummy_tmopt false dummy_prod_es stlb)) in
      ( match m with
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Coq co when co.coq_expand_lists ->  (* FZ this should be optimized *)
	  ( match ntmvro with
	  | Some ntmvr ->
	      let typ = pp_nt_or_mv_root_ty m xd ntmvr in  
	      "(unmake_list_"^typ^" "^fake^")", [], []
	  | None ->
	      let s = fst mv in
	      "(unmake_list_"^s ^" "^fake^")", [], [] )
      | _ -> fake, [], [] )

  | NonTermListExp (nt,b) ->
      (* fake up a symterm_list_body *)
      let stlb = {stl_bound = b;
                  stl_elements = [Ste_st(dummy_loc,St_nonterm (dummy_loc,Auxl.primary_ntr_of_ntr xd (fst nt),nt)) ];
                  stl_loc = dummy_loc } in
      let dummy_prod_es = [Lang_nonterm (Auxl.primary_ntr_of_ntr xd (fst nt),nt)] in
      let dummy_tmopt = None in
      (* and pp that *)
      let fake = 
	String.concat "" 
          (List.map fst 
	     (pp_symterm_list_body m xd sie de dummy_tmopt false dummy_prod_es stlb)) in 
      ( match m with
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Coq co when co.coq_expand_lists -> (* FZ this should be optimized *)
	  ( match ntmvro with
	  | Some ntmvr ->
	      let typ = pp_nt_or_mv_root_ty m xd ntmvr in 
	      "(unmake_list_"^typ^" "^fake^")", [], []
	  | None ->
 	      let s = fst nt in
	      "(unmake_list_"^s^" "^fake^")", [], [] )
      | _ -> fake, [], [] )
  | Aux(f,nt) -> 
      ( match m with 
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Ascii ao -> 
          ( pp_auxfn m xd f ^ ""^pp_LPAREN  ^ pp_nonterm_with_sie m xd sie nt 
	    ^ "" ^ pp_RPAREN ), [], []
      | Tex xo -> 
          ( pp_auxfn m xd f ^ "" ^ pp_tex_LPAREN ^ "" 
	    ^ pp_nonterm_with_sie m xd sie nt ^ "" ^ pp_tex_RPAREN ), [], []
      | Isa _ | Coq _ | Hol _ | Lem _ | Twf _ | Caml _ -> 
          let ntrp = pp_nontermroot_ty m xd (Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd (fst nt))) in
	  ( "(" ^ Auxl.auxfn_name f ntrp ntrp ^ " " 
            ^ pp_nonterm_with_sie m xd sie nt^")" ), [], [] )
  | AuxList(f,nt,b) -> 
      let ntrp0 = Auxl.primary_ntr_of_ntr xd (fst nt) in

      (* fake up a symterm_list_body *)
      let ntrp,st,dummy_prod_e = 
        try
          let (sru,srt)=Auxl.promote_ntr' xd ntrp0 in
          srt,
          St_nontermsub (dummy_loc,ntrp0,srt,nt),
          Lang_nonterm(srt , nt)
        with 
          Not_found -> 
            ntrp0,
            St_nonterm (dummy_loc,ntrp0,nt),
            Lang_nonterm(ntrp0 , nt) in
      let stlb = {stl_bound = b;
                  stl_elements = [Ste_st(dummy_loc,st) ];
                  stl_loc = dummy_loc } in
      let dummy_prod_es = [dummy_prod_e] in
      let dummy_tmopt = None in
          (* and pp that *)
      let pp_ntlist = String.concat "" 
          (List.map fst
             (pp_symterm_list_body m xd sie de dummy_tmopt false dummy_prod_es stlb)) in
      ( match m with 
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Ascii ao -> 
          pp_auxfn m xd f ^ ""^pp_LPAREN ^ "" 
          ^ pp_ntlist
	  ^ "" ^ pp_RPAREN, [], []
      | Tex xo -> 
          pp_auxfn m xd f ^ "" ^ pp_tex_LPAREN ^ "" 
	  ^ pp_ntlist
          ^ "" ^ pp_tex_RPAREN, [], []
            
      | Isa io when io.ppi_isa_primrec -> ( 
          (* print_string ("[[[  de "^pp_plain_dotenv de^"]]]\n");flush stdout; *)
          (* let es = stlb.stl_elements in *)
          let (de1,de2) = de in
          let de1i = de1_lookup de1 b in
          let typ_list = 
            List.map (function ((ntmv_root,_),subntr_data) -> 
 	      (*Auxl.pp_isa_type_name*)
	        (pp_nt_or_mv_root_ty m xd 
	           (Auxl.promote_ntmvr xd
		      (Auxl.primary_nt_or_mv_of_nt_or_mv xd ntmv_root))))
              de1i.de1_ntmvsns in
          
	  let typ_tuple =
            let tmp = String.concat "*" typ_list in
	    if (List.length de1i.de1_ntmvsns) > 1 then "("^tmp^")" else tmp in
          let typ = typ_tuple ^ " list" in
          
          let output_typ = 
	    ( match ntmvro with
	    | Some ntmvr -> pp_nt_or_mv_root_ty m xd ntmvr ^ " list" 
	    | None -> "<<<None_in_nmtvro_pp_mse>>>" ) in (* FZ this should never appear in the output *)
          
          let args =   
            String.concat "_" 
	      (List.map (fun ((x,_),_) -> 
		pp_nt_or_mv_root_ty m xd (Auxl.promote_ntmvr xd (Auxl.primary_nt_or_mv_of_nt_or_mv xd x))) de1i.de1_ntmvsns) in

	  let split_suffix =             (* HACK: we do not generate the first prefix *)
	    let pre_split_suffix = 
	      if isa_list_name_flag 
	      then 
		if List.mem typ !mse_split_prod_counter 
		then "_"^prod_name 
		else 
		  ( mse_split_prod_counter := typ::!mse_split_prod_counter; "" )
	      else "" in
	    let counter_suffix = 
	      if isa_list_name_flag then
		try 
		  let c_p = List.assoc (typ^pre_split_suffix) !mse_split_inprod_counter in
		  c_p := !c_p + 1;
		  string_of_int (!c_p)
		with Not_found -> (
		  mse_split_inprod_counter := ((typ^pre_split_suffix),ref 0)::!mse_split_inprod_counter;
		  "" )
	      else ""
	    in
	    pre_split_suffix ^ counter_suffix in
	  
	  let ntrpn = pp_nontermroot_ty m xd ntrp in

          let id_list = Auxl.auxfn_name f ntrpn (args  ^ "_list" ) ^ split_suffix in

          let list_patterns = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in
          
          let rec make_tuple typ_list pattern ntmvsns = (* build the functions over the tuples *)
            let args_list =
	      List.map (fun ((x,_),_) -> 
		pp_nt_or_mv_root_ty m xd (Auxl.promote_ntmvr xd (Auxl.primary_nt_or_mv_of_nt_or_mv xd x))) ntmvsns in
            
            let id_tuple = 
	      if List.length args_list = 1 
	      then (Auxl.auxfn_name f ntrpn (String.concat "_" args_list))
	      else (Auxl.auxfn_name f ntrpn (String.concat "_" args_list)) ^ split_suffix in
            
            let func_tuple = 
              if List.length ntmvsns = 1 
              then [] 
              else begin
                let typ_tuple =
                  if List.length typ_list = 2
                  then "("^String.concat "*" typ_list^")"
                  else "("^(List.hd typ_list)^"*("^String.concat "*" (List.tl typ_list)^"))" in

                let lhs_tl = String.concat "" (List.tl pattern) in 
                let lhs = 
                  if List.length pattern = 2
                  then "("^String.concat "," pattern^")"
                  else "("^(List.hd pattern)^","^lhs_tl^")" in

                let calc, c_deps =
                  let ntrs = 
                    Auxl.option_map 
                      (fun (((x,_),_),p) -> ( match x with Ntr y -> Some (y,p) | _ -> None )) 
                      ( if List.length ntmvsns = 2 
                      then List.combine ntmvsns pattern 
                      else [ (List.hd ntmvsns, List.hd pattern) ] ) in
                  let (auxfn_def_types,_) = List.assoc f xd.xd_axs in
                  let interesting_ntrs =
                    List.filter
                      ( fun (ntr,_) -> List.mem (Auxl.primary_ntr_of_ntr xd ntr) auxfn_def_types )
                      ntrs in
                  let tuple_deps = 
		    List.map (fun (ntr,_) -> Auxl.auxfn_name f ntr ntr) interesting_ntrs in 
                  let tmp =
                    String.concat (list_append m)
                      (List.map (fun (ntr,p) ->
                        let fname = (Auxl.auxfn_name f ntr ntr) in
                        "("^fname ^ " " ^ p^")") interesting_ntrs) in
                  (if List.length ntrs = 1 then tmp else "(" ^ tmp ^ ")"), tuple_deps in

                let rhs, aux_tuple_funcs, deps = 
                  if List.length typ_list = 2
                  then calc, [], c_deps
                  else 
                    let id_aux, aux_tuple_funcs = 
                      make_tuple (List.tl typ_list) (List.tl pattern) (List.tl ntmvsns) in
                    "("^calc^")"^list_append m^"("^ id_aux ^ " " ^lhs_tl^")", aux_tuple_funcs, (id_aux :: c_deps)  (* complete *)
                in

                { r_fun_id = id_tuple;
                  r_fun_dep = deps;
                  r_fun_type = typ_tuple^split_suffix;
                  r_fun_header = (id_tuple ^ " :: \"" ^ typ_tuple ^ " => " ^ output_typ ^"\"\n", "", "");
                  r_fun_clauses = [ "" ,lhs, rhs ] } :: aux_tuple_funcs  

              end
            in
            id_tuple, func_tuple
          in
          let id_tuple, func_tuple = make_tuple typ_list list_patterns de1i.de1_ntmvsns in
     
          ( "(" ^ id_list ^ " " ^ de1i.de1_compound_id ^ ")" ),
          [ id_list ], 
          { r_fun_id = id_list;
            r_fun_dep = [id_list; id_tuple];
            r_fun_type = typ^split_suffix;
            r_fun_header = (id_list ^ " :: \"" ^ typ ^ " => " ^ output_typ ^"\"\n", "", "");
            r_fun_clauses = 
	    [ ( "", "Nil", "[]" );
              ( "", "("^Auxl.hide_isa_trailing_underscore m(args^"_")^"#"^Auxl.hide_isa_trailing_underscore m (args^"_list_")^")", 
                "(" ^ id_tuple ^ " " ^ Auxl.hide_isa_trailing_underscore m(args ^ "_")^")"^list_append m^"(" ^ id_list ^ " " ^ Auxl.hide_isa_trailing_underscore m (args^"_list_")^")" ) ] } 
	  :: func_tuple )

      | Isa io when not io.ppi_isa_primrec ->
	  let ntrp_s = pp_nontermroot m xd ntrp in
	  ( "(concat (map "^Auxl.auxfn_name f ntrp_s ntrp_s ^" ("^pp_ntlist^")))" ), [], []
      | Hol _ ->  ( "(FLAT (MAP "^Auxl.auxfn_name f ntrp ntrp ^" ("^pp_ntlist^")))" ), [], [] 

      | Twf _ -> raise TwelfNotImplemented
      | Caml _ ->  ( "(List.flatten (List.map "^Auxl.auxfn_name f ntrp ntrp ^" ("^pp_ntlist^")))" ), [], [] 
      | Lem _ ->  
	  let ntrp_s = pp_nontermroot m xd ntrp in
          ( lemTODO "9" " (List.concat (List.map "^Auxl.auxfn_name f ntrp_s ntrp_s ^" ("^pp_ntlist^")))" ), [], [] 

      | Coq co when co.coq_expand_lists -> (* FZ share with Isa ? *)
          (* let es = stlb.stl_elements in *)
          let (de1,de2) = de in
          let de1i = de1_lookup de1 b in

	  let ty_list = Str.split (Str.regexp "(\\|*\\|)") de1i.de1_coq_type_of_pattern in
	  let var_list = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in
	  
          let suf = "list_" ^ String.concat "_" ty_list in
          let typ = (*Auxl.pp_coq_type_name*) suf in
          
          let output_typ = 
	    ( match ntmvro with
	    | Some ntmvr -> "list " ^pp_nt_or_mv_root_ty m xd ntmvr 
	    | None -> "<<<None_in_nmtvro_pp_mse>>>" ) in (* FZ this should never appear in the output *)
	  
          let args =   
	    String.concat "_" 
	      (List.map (fun ((x,_),_) -> 
		pp_nt_or_mv_root m xd 
		  (Auxl.promote_ntmvr xd (Auxl.primary_nt_or_mv_of_nt_or_mv xd x))) de1i.de1_ntmvsns) in
          
          let id_list = Auxl.auxfn_name f ntrp (args ^ "_list") in
          
	  let ntrs = (* FZ share with ISA *)
	    Auxl.option_map 
	      (fun ((x,s),_) -> ( match x with Ntr y -> Some (y,s) | _ -> None )) 
	      de1i.de1_ntmvsns in
          let (auxfn_def_types,_) = List.assoc f xd.xd_axs in
          let interesting_ntrs =
	    List.filter
	      ( fun (ntr,s) -> List.mem (Auxl.primary_ntr_of_ntr xd ntr) auxfn_def_types )
	      ntrs in
          let rhs = 
	    let tmp =
	      Auxl.insert_append m
                (List.map (fun (ntr,s) ->
                  let fname = Auxl.auxfn_name f (Auxl.primary_ntr_of_ntr xd ntr) (Auxl.primary_ntr_of_ntr xd ntr) in
                  "(" ^ fname ^ " " ^ ntr^(pp_suffix_with_sie m xd ((Si_var ("_",0))::sie) s)^")") interesting_ntrs) in
	    if List.length interesting_ntrs = 0 then "nil" else tmp in
(*            else if List.length intersting_ntrs = 1 then tmp else "(" ^ tmp ^ ")" in *)

          let tuple_deps = 
	    List.map 
	      (fun (ntr,_) -> Auxl.auxfn_name f (Auxl.primary_ntr_of_ntr xd ntr) (Auxl.primary_ntr_of_ntr xd ntr)) 
	      interesting_ntrs in

	  (* print_endline ("**** " ^ id_list ^ " * " ^ String.concat " " (id_list::tuple_deps)); *)
	  
          ( "(" ^ id_list ^ " " ^ de1i.de1_compound_id ^ ")" ),
          [ id_list ], 
          [ { r_fun_id = id_list;
	      r_fun_dep = id_list :: tuple_deps;
	      r_fun_type = typ;
	      r_fun_header = ( id_list ^ " (l:" ^ typ^")",  (* FZ freshen l *)
			       "", 
          		       ": " ^ output_typ ^ " :=\n  match l with\n");
	      r_fun_clauses = 
	      [ ( "", "Nil_"^suf, "nil" );
                ( "", "Cons_"^suf^" "^ (String.concat " " var_list) ^" "^args^"_list_", 
                  "app ("^rhs^") (" ^ id_list ^ " " ^ args^"_list_)" )
	      ] } ]

      | Coq co when not (co.coq_expand_lists) ->
	  (* adapted from pp_symterm_list_body *)
	  let es = stlb.stl_elements in
	  let (de1,de2)=de in
	  let de1i = de1_lookup de1 stlb.stl_bound in

	  let ty_list = Str.split (Str.regexp "(\\|*\\|)") de1i.de1_coq_type_of_pattern in
	  let var_list = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in
	  let pat_fun,pat_fun_end = 
	    if co.coq_expand_lists 
	    then (String.concat " " (List.map2 (fun x y -> "("^x^":"^y^")") var_list ty_list), "")
	    else 
	      if List.length var_list = 1 
	      then "("^de1i.de1_pattern^":"^de1i.de1_coq_type_of_pattern^")", "" (* FZ FRESHEN pat_ *)
	      else "(pat_:"^de1i.de1_coq_type_of_pattern^") => match pat_ with " ^ de1i.de1_pattern, " end "  
	  in

	  let rec make_aux_calls_se prod_es =
	    ( match prod_es with
	    | [] -> []
	    | (Lang_nonterm (ntr,_))::t -> (Auxl.auxfn_name f ntr ntr) :: make_aux_calls_se t
(*	    | (Lang_metavar (mvr,_))::t -> ("<"^mvr^"> ") :: make_aux_calls_se t *)
	    | _ :: t -> make_aux_calls_se t )
	  in

	  let pp_body = 
	    let se = pp_symterm_elements m xd ((Si_var ("_",0))::sie) de false dummy_prod_es es in 
	    let ce = make_aux_calls_se dummy_prod_es in
	    let tmp = String.concat "," (List.map2 (fun x y -> x^" "^y) ce se) in
	    if (List.length es) > 1 then "("^tmp^")" else tmp in
	    
	  (* hacky optimisation to remove identity maps *)
	  if de1i.de1_pattern=pp_body then de1i.de1_compound_id, [], []
	  else
	    ( "(flat_map (fun "^pat_fun^" => "^pp_body^ pat_fun_end ^ ") "
	      ^ de1i.de1_compound_id
	      ^ ")", [], [] )  )
(*	This is the naive correct thing, but Coq does not like it eg test17.11 *)
(*      "(flat_map "^Auxl.auxfn_name f ntrp ntrp ^" ("^pp_ntlist^"))" *)

  | Union(mse,mse') -> 
      ( match m with 
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Ascii ao -> 
          ( pp_mse_string m xd sie de mse ^ " " ^ pp_UNION ^ " " ^ pp_mse_string m xd sie de mse' ), [], []
      | Tex xo -> 
          ( pp_mse_string m xd sie de mse ^ " " ^ pp_tex_UNION ^ " " ^ pp_mse_string m xd sie de mse' ), [], []

      | Isa _ -> 
	  let (s1,d1,f1) =  pp_mse m xd sie de isa_list_name_flag prod_name ntmvro mse in
	  let (s2,d2,f2) =  pp_mse m xd sie de isa_list_name_flag prod_name ntmvro mse' in
	  (s1 ^ list_append m ^ s2,
	   d1 @ d2,
	   f1 @ f2)
      | Caml _ -> ( pp_mse_string m xd sie de mse ^list_append m^ pp_mse_string m xd sie de mse' ), [], []
      | Lem _ -> ( pp_mse_string m xd sie de mse ^list_append m^ pp_mse_string m xd sie de mse' ), [], []
      | Hol _ -> ( "("^pp_mse_string m xd sie de mse ^list_append m^ pp_mse_string m xd sie de mse' ^")"), [], []
      | Coq _ -> 
	  let (s1,d1,f1) =  pp_mse m xd sie de isa_list_name_flag prod_name ntmvro mse in
	  let (s2,d2,f2) =  pp_mse m xd sie de isa_list_name_flag prod_name ntmvro mse' in
	  ("(app "^s1 ^ " " ^ s2^")",
	   d1 @ d2,
	   f1 @ f2)
      | Twf _ -> ( "(append/natlist " ^ pp_mse_string m xd sie de mse ^ " " ^ pp_mse_string m xd sie de mse' ^")" ), [] , [])
  | Empty -> 
      ( match m with 
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_mse"
      | Ascii ao -> pp_EMPTY, [], []
      | Tex xo -> pp_tex_EMPTY, [], []
      | Isa _ | Hol _ | Lem _ | Caml _ -> "[]", [], []
      | Coq _ -> "nil", [], [] 
      | Twf _ -> "natlist/nil", [], [] 
       )
      
and pp_auxfn m xd f = 
  match m with 
  | Tex xo -> "\\textrm{"^pp_maybe_quote_ident m xd (Auxl.pp_tex_escape f)^"}"
  | _ -> pp_maybe_quote_ident m xd f

and pp_plain_mse_type_item mse_tyi =
  match mse_tyi with
  | Mse_ty_ntmvr (Ntr ntr) -> ntr
  | Mse_ty_ntmvr (Mvr mvr) -> mvr
  | Mse_ty_aux f -> f

and pp_plain_mse_ty mse_ty =
  String.concat " " (List.map pp_plain_mse_type_item mse_ty)
        
and pp_plain_mse_tys mse_tys =
  String.concat "\n" (List.map (function mse_ty -> "[ "^ pp_plain_mse_ty mse_ty^" ]") mse_tys)
  ^"\n"

and pp_plain_element e = 
  match e with
  | Lang_nonterm (ntrp,nt) -> "(Lang_nonterm "^pp_plain_nonterm nt^")"
  | Lang_metavar (mvrp,mv) -> "(Lang_metavar "^pp_plain_metavar mv^")" 
  | Lang_terminal tm ->       "(Lang_terminal "^pp_plain_terminal tm^")"
  | Lang_option es -> "(Lang_option "^String.concat " " (List.map pp_plain_element es)^")"
  | Lang_sugaroption tm ->   "(Lang_sugaroption "^pp_plain_terminal tm^")"
  | Lang_list elb ->  "(Lang_list "^String.concat " " (List.map pp_plain_element elb.elb_es)^")"

and pp_element m xd sie in_type e = 
  match m with
  | Ascii _ | Tex _ ->
      ignore("pp element refactoring in progress");
(* TODO: SHOULD WE USE pp_symterm TO DO THIS FOR Ascii AND Tex, TO AVOID REPETITION OF ALL THE FANCY DOTFORM CODE AND ENSURE CONSISTENCY?*)
(*  This is now only called from the point marked FOOBAZ in pp_com_es and two points in defns.ml.  It should be replaced by the generation of appropriate symterms and then pp of them, to avoid duplication of listform code (which is supported for symterms but not yet here *)

      ( match e with
      | Lang_nonterm (ntrp,nt) ->   
          Some (pp_nonterm_with_sie m xd sie nt) 
      | Lang_metavar (mvrp,mv) ->  
          Some (pp_metavar_with_sie m xd sie mv)
      | Lang_terminal tm ->  
          Some (pp_terminal m xd tm)
      | Lang_option es ->
          ( match m with 
          | Ascii ao -> Some (
              pp_LEFTBRACKET ^ " " 
	      ^ String.concat " " (Auxl.option_map (pp_element m xd sie in_type) es) ^ " "
	      ^ pp_RIGHTBRACKET )
          | Tex xo -> Some (
              pp_tex_LEFTBRACKET ^ " " 
	      ^ String.concat " " (Auxl.option_map (pp_element m xd sie in_type) es) ^ " " 
	      ^ pp_tex_RIGHTBRACKET )
          | Coq _ | Caml _ | Hol _ | Lem _ | Twf _ | Isa _ | Lex _ | Yacc _ -> raise ThisCannotHappen )
      | Lang_sugaroption tm ->  
          Some (pp_terminal m xd tm)
      | Lang_list elb ->  
(*           let pptmo =   *)
(*             ( match elb.elb_tmo with  *)
(* 	    | None -> " "  *)
(* 	    | Some tm -> " " ^ pp_terminal m xd tm ^ " " ) in *)
(*           let (siel,sieu,length) =  *)
(*             ( match elb.elb_boundo with  *)
(*             | None -> (sie,sie,2) *)
(*             | Some (Bound_dotform bd) -> (bd.bd_lower::sie,bd.bd_upper::sie,bd.bd_length)) in *)
(*           let ppbodyl = Auxl.the (pp_elements m xd siel elb.elb_es false false true) in *)
(*           let ppbodyu = Auxl.the (pp_elements m xd sieu elb.elb_es false false true) in *)
(*           Some *)
(*              *)
(*              (\* "[[" ^ *\) *)
(*              ppbodyl ^ pptmo ^ pp_dots m xd length ^ pptmo ^ ppbodyu *)
(*              (\* ^ "]]" *\) *)
(*             )) *)
      Some "pp element refactoring in progress" )

  | Lex _ | Yacc _ ->
      ( match e with
      | Lang_terminal tm ->  Some (pp_terminal m xd tm)
      | Lang_nonterm _ 
      | Lang_metavar _
      | Lang_option _ 
      | Lang_sugaroption _ 
      | Lang_list _ -> None)

  | Coq _ | Isa _ | Hol _ | Lem _ | Twf _ | Caml _ ->
      let check_conflict v t =
        if String.compare v t = 0 
        then Some "_", t
        else Some v, t in
      let vto = 
        ( match e with
        | Lang_nonterm (ntrp,nt) ->   
            let ntrp' = Auxl.promote_ntr xd ntrp in 
            Some (check_conflict (pp_nonterm m xd nt) (pp_nontermroot_ty m xd ntrp'))
        | Lang_metavar (mvrp,mv) ->  
            Some (check_conflict (pp_metavar m xd mv) (pp_metavarroot_ty m xd mvrp))
        | Lang_terminal tm ->  
            (match m with
            | Caml oo when oo.ppo_include_terminals -> Some (None, "terminal")
            | _ -> None)
        | Lang_option es ->
            ( match m with 
            | Coq co -> 
	        ( match pp_elements m xd sie es true false true true with
                | None -> None
                | Some s -> Some (None, "(option "^s^")") )
            | Isa _ | Hol _ | Lem _ | Caml _ -> 
	        ( match pp_elements m xd sie es true false true true with 
                | None -> None
                | Some s -> Some (None, s^ " option"))
            | Twf _ -> raise TwelfNotImplemented
            | Ascii _ | Tex _ | Lex _ | Yacc _ -> raise ThisCannotHappen )
        | Lang_sugaroption tm ->  
            None 
        | Lang_list elb ->  
            ( match m with 
            | Coq co -> 
	        if co.coq_expand_lists 
	        then
		  ( match pp_elements m xd sie elb.elb_es false false true true with
		  | None -> None   (* FZ should be unit list, but list_unit is undefined*)
		  | Some s -> Some (None, "(list_"^s^")") )
	        else
		  ( match pp_elements m xd sie elb.elb_es true false true true with
		  | None -> Some (None, "list unit")
		  | Some s -> Some (None, "list "^s) )
            | Isa _ | Hol _  -> 
	        ( match pp_elements m xd sie elb.elb_es true false true true with  
                | None -> Some (None, "unit list")    
                | Some s -> Some (None, s^ " list"))
            | Lem _  -> 
	        ( match pp_elements m xd sie elb.elb_es true false true true with  
                | None -> Some (None, "list unit")    
                | Some s -> Some (None, "list "^s))
            | Caml oo -> 
                let tmt = match oo.ppo_include_terminals,elb.elb_tmo with 
                | true,Some tm -> " * terminal" 
                | _,_ -> "" in
	        ( match pp_elements m xd sie elb.elb_es true false true true with  
                | None -> Some (None, "(unit"^tmt^") list")    
                | Some s -> Some (None, "("^s^ tmt^") list"))
            | Twf _ -> raise TwelfNotImplemented
            | Ascii _ | Tex _ | Lex _ | Yacc _ -> raise ThisCannotHappen )) in
      ( match m, vto with
      | _, None -> 
          None
      | Coq co, Some (Some v,t) when co.coq_names_in_rules && (not in_type) -> 
          Some ("("^v^":"^t^")")
      | Coq co, Some (None,t) when co.coq_names_in_rules && (not in_type) -> 
          Some ("(_:"^t^")")
      | Coq co, Some (v,t) when (not co.coq_names_in_rules) || in_type -> 
          Some t
      | _, Some (v,t) -> 
          Some t)
 
and pp_elements m xd sie es paren toplevel in_list in_type =
  match m with 
  | Ascii _ | Tex _ | Lex _ | Yacc _ ->
      Some (String.concat " " (Auxl.option_map (pp_element m xd sie in_type) es) )
  | Coq _ | Caml _ | Lem _ ->
      lemTODOmo m "10" (*really? *) (
      let ss = (Auxl.option_map (pp_element m xd sie in_type) es) in
      let separator = 
        if in_list then 
          ( match m with
          | Caml _ | Lem _ -> " * "
	  | Coq co when co.coq_expand_lists -> "_"
	  | Coq co when not (co.coq_expand_lists) -> "*"
          | _ -> "_" )
        else 
          ( match m with 
          | Coq co when co.coq_names_in_rules -> " "
          | _ -> " -> " ) in
      let s  = String.concat separator ss in  
      ( match List.length ss with 
      | 0 -> None 
      | 1 -> Some s
      | _ -> if paren then Some ("("^ s ^")") else Some s )
     )
  | Twf _ -> 
      let ss = (Auxl.option_map (pp_element m xd sie in_type) es) in
      let separator = if in_list then raise TwelfNotImplemented else " -> " in
      let s  = String.concat separator ss in  
      ( match List.length ss with 
      | 0 -> None 
      | 1 -> Some s
      | _ -> if paren then Some ("("^ s ^")") else Some s )
  | Isa _ -> 
      let ss = (Auxl.option_map (pp_element m xd sie in_type) es) in
      ( match ss with
      | [] -> None
      | _ -> 
           (if toplevel then 
             Some (String.concat " " (List.map (fun s -> "\""^s^"\"") ss) )
           else 
             (match paren,List.length ss with
             | false,_ | true,1 ->  Some (String.concat "*" ss)
             | true,_ ->  Some ("("^String.concat "*" ss^")"))))
  | Hol _ -> 
      let ss = (Auxl.option_map (pp_element m xd sie in_type) es) in
      ( match ss with
      | [] -> None
      | _ -> 
           (if toplevel then 
             Some (String.concat " => " (List.map (fun s -> ""^s^"") ss) )
           else 
             (match paren,List.length ss with
             | false,_ | true,1 ->  Some (String.concat "#" ss)
             | true,_ ->  Some ("("^String.concat "#" ss^")"))))

(* type nominalprod = ((metavarroot * metavar) list * element) list *)

and pp_nominal_prod m xd rnn rpw p =
  (* 1- convert p into a nominalprod *)
  let np = List.map (fun e -> ([],e)) p.prod_es in

  (* 2- for each bs, put the binding mv close to the bound nt *)
  let rec arrange np bs =
    match bs with
    | [] -> np
    | (Bind (MetaVarExp mv, nt)) :: bst ->
	let rnp =
	  Auxl.option_map
	    ( fun (bl,el) ->
	      match el with
	      | Lang_metavar (emvr,emv) -> 
		  if (Pervasives.compare mv emv = 0)
		  then None
		  else Some (bl,el)
	      | _ -> Some (bl,el) )
	    np in
	let unp = 
	  Auxl.option_map
	    ( fun (bl,el) ->
	      match el with
	      | Lang_nonterm (entr,ent) ->
		  if (Pervasives.compare nt ent = 0)
		  then 
		    let mvr = Auxl.primary_mvr_of_mvr xd (fst mv) in
		    Some ((Lang_metavar (mvr,(mvr,[])))::bl, el)
		  else Some (bl,el)
	      | _ -> Some (bl,el) )
	    rnp in 

	arrange unp bst
    | _ :: bst -> arrange np bst in

  let anp = arrange np p.prod_bs in

  (* 3- print the nominal prod *)
  let rec print np =
    match np with
    | [] -> []
    | (bl,el) :: npt -> 
	match pp_element m xd [] false el with
	| Some s -> 
	    let bls = Auxl.option_map (pp_element m xd [] false) bl in
	    let blss = String.concat "" (List.map (fun s -> "\\<guillemotleft>"^s^"\\<guillemotright>") bls) in
	    (blss^s) :: (print npt)
	| None -> print npt in

  Some (String.concat " " (p.prod_name :: (List.map (fun s -> "\""^s^"\"") (print anp)))
        ^ pp_com_es m xd p.prod_homs p.prod_es)

and apply_hom_order m xd p = (* returns an p.prod_es sorted according to the order hom *)
  try
    let oh = List.assoc "order" p.prod_homs in
    debug (p.prod_name^": "^String.concat " - " (List.map pp_plain_hom_spec_el oh));
    let ohi = Auxl.option_map (fun hse -> match hse with Hom_index i -> Some i | _ -> None) oh in
    let pf = List.filter (fun e -> match e with Lang_nonterm _ | Lang_metavar _ | Lang_list _ -> true | _ -> false) p.prod_es in
    List.map (fun i -> List.nth pf i) ohi
  with Not_found -> p.prod_es

and pp_prod m xd rnn rpw p = (* returns a string option *)
  let pp_com = pp_com_es m xd p.prod_homs p.prod_es in
  match m with 
  | Lex _ | Yacc _ -> Auxl.errorm m "pp_prod"
  | Ascii ao -> 
      let pn = 
	if ao.ppa_lift_cons_prefixes then 
          let lpnw = String.length rpw in
          let lpn  = String.length p.prod_name in
          String.sub p.prod_name lpnw (lpn-lpnw) 
	else
          p.prod_name in
      let pp_prod m'=
        let stnb = canonical_symterm_node_body_of_prod rnn p in
        let st = St_node(dummy_loc,stnb) in
        pp_symterm m' xd [] de_empty st 
      in
      Some
        ((pad2 60 
            (pp_prod_flavour m xd p.prod_flavour ^ " " 
	     ^ (pp_prod (Ascii{ao with ppa_colour=false})))
            (pp_prod_flavour m xd p.prod_flavour ^ " " 
	     ^ (pp_prod m )))
(*             (pp_prod_flavour m xd p.prod_flavour ^ " "  *)
(* 	     ^ Auxl.the (pp_elements    *)
(* 		          (Ascii{ao with ppa_colour=false}) xd [] p.prod_es true true false)) *)
(*             (pp_prod_flavour m xd p.prod_flavour ^ " "  *)
(* 	     ^ Auxl.the (pp_elements m xd [] p.prod_es true true false)) )  *)
         ^ " " 
         ^ pp_COLONCOLON ^ " " 
(*      ^ pad 1 (String.concat " " (List.map (pp_category m xd) p.prod_pcs)) *)
(*      ^ pp_categories_and_name m xd pcs pn *)
         ^ pn 
         ^ " " ^String.concat " " (List.map (pp_homomorphism m xd) p.prod_homs))
  | Isa io ->
      if p.prod_meta then
        None
      else if Auxl.prod_require_nominal m xd p 
      then pp_nominal_prod m xd rnn rpw p
      else
	(
        let datatype_clause = 
          match pp_elements m xd [] (apply_hom_order m xd p) (*p.prod_es*) false true false false with
          | None -> p.prod_name
          | Some s -> (p.prod_name ^ " "^s) in
        let fancy_syntax_clause = isa_fancy_syntax_clause_for_prod m xd io p in
        Some(datatype_clause ^ "  " ^ fancy_syntax_clause ^ pp_com)
       )
  | Hol ho ->
      if p.prod_meta then
        None
      else (
        match pp_elements m xd [] (apply_hom_order m xd p) (*p.prod_es*) false true false false with
        | None -> Some (p.prod_name ^ pp_com)
        | Some s -> Some (p.prod_name ^ " of " ^ s ^ pp_com) )
  | Coq co ->
      if p.prod_meta then
        None
      else
        ( match pp_elements m xd [] (apply_hom_order m xd p) (*p.prod_es*) false true false false with
        | None ->  Some (" | " ^ p.prod_name ^ " : " ^ pp_nontermroot_ty m xd rnn ^ pp_com)
        | Some s -> 
            if co.coq_names_in_rules 
            then Some (" | " ^ p.prod_name ^ " " ^ s ^ pp_com)
            else Some (" | " ^ p.prod_name ^ " : " ^ s ^ " -> " ^ pp_nontermroot_ty m xd rnn ^ pp_com) )
  | Twf _ ->
      if p.prod_meta then
        None
      else
        ( match pp_elements m xd [] (apply_hom_order m xd p) (*p.prod_es*) false true false false with
        | None ->  Some (p.prod_name ^ " : " ^ pp_nontermroot_ty m xd rnn^".")
        | Some s ->  Some (p.prod_name ^ " : " ^ s ^ " -> " ^ pp_nontermroot_ty m xd rnn^".") )
  | Caml _ ->
      if p.prod_meta then
        None
      else
        ( match pp_elements m xd [] (apply_hom_order m xd p) (*p.prod_es*) false true true false with
        | None ->  Some (String.capitalize p.prod_name ^ pp_com)
        | Some s ->  Some ((String.capitalize p.prod_name) ^ " of " ^ s ^ pp_com) )
  | Lem _ ->
      if p.prod_meta then
        None
      else
        ( match pp_elements m xd [] (apply_hom_order m xd p) (*p.prod_es*) false true true false with
        | None ->  Some (String.capitalize p.prod_name ^ pp_com)
        | Some s ->  Some ((String.capitalize p.prod_name) ^ " of " ^ s ^ pp_com) )

  | Tex xo -> 
      if not(xo.ppt_show_meta) && p.prod_meta && not(p.prod_sugar) then 
        None
      else
        Some
          (let pp_prod =
(* 	    (String.concat "\\ " (Auxl.option_map (pp_element m xd []) p.prod_es)) *)
            let stnb = canonical_symterm_node_body_of_prod rnn p in
            let st = St_node(dummy_loc,stnb) in
            pp_symterm m xd [] de_empty st 
          in
          let pp_meta_or_bindspec, pp_remaining_bindspecs = 
            if p.prod_sugar then " {\\textsf{S}}{}",[] 
            else if p.prod_meta then " {\\textsf{M}}{}",[] 
            else let pp_bss = pp_bindspec_list m xd [] de_empty p.prod_bs in
            match pp_bss with 
            | [] -> "{}{}",[]
            | hd::tl ->  "{}{"^hd^"}", tl in
          let pp_categories =
            if xo.ppt_show_categories then
              let categories =
                StringSet.fold (fun x l -> if x = "M" || x="S" then l else x::l)
                  (p.prod_categories) []
              in if categories = [] then "{}" else
              "{\\textsf{[" ^ String.concat " " categories ^ "]}}"
            else "{}" in
          let texlong = List.exists (function (hn,hs) -> hn="texlong") p.prod_homs in
          String.concat (pp_tex_PROD_NEWLINE_NAME m^"\n") 
            ( 
              (if not texlong then 
                [String.concat "" [ pp_tex_PROD_NAME m;
                                 "{|}";
                                 "{";pp_prod;"}";
                                 pp_meta_or_bindspec;
                                 pp_categories;
                                 "{";pp_com;"}";
                                  ]]
              else
                [String.concat "" [ pp_tex_LONG_PROD_NAME m;
                                    "{|}";
                                    "{";pp_prod;"}";
                                  ];
                 String.concat "" [ pp_tex_PROD_NAME m;
                                    "{}";
                                    "{}";
                                    pp_meta_or_bindspec;
                                    pp_categories;
                                    "{";pp_com;"}";
                                  ]])
              @
                (List.map (function pp_bs -> 
                  pp_tex_BINDSPEC_PROD_NAME m ^ "{}{}{}{" ^ pp_bs ^"}{}{}") pp_remaining_bindspecs))
                              )

and pp_internal_coq_buffer = ref "" (* FZ HACK *)

and pp_rule m xd r = (* returns a string option *)
  let pp_com = pp_com_strings m xd r.rule_homs [pp_nonterm_with_sie m xd [] (r.rule_ntr_name,[])] in
  let result : string option = 
  match m with 
  | Lex _ | Yacc _ -> Auxl.errorm m "pp_rule"
  | Ascii ao ->
      let pnw' = 
	if ao.ppa_lift_cons_prefixes 
	then r.rule_pn_wrapper
	else "''" in
      Some 
        ((String.concat " , " (List.map 
                                 (function ntr,homs->pp_nontermroot m xd ntr) 
                                 r.rule_ntr_names)) ^ " "
         ^ pp_COLONCOLON ^ " " ^ pnw' ^ " "
         ^ pp_CCE ^ " "
         ^ pp_homomorphism_list m xd r.rule_homs^"\n" ^ "  " 
         ^ String.concat 
             "  " 
             (List.map 
                (fun s -> s ^ "\n")
                (Auxl.option_map 
                   (pp_prod m xd r.rule_ntr_name r.rule_pn_wrapper) 
                   r.rule_ps)))
  | Isa _ ->
(* PS hack below to turn off printing of phantom rule bodies - please check! *)
    if r.rule_meta || r.rule_phantom  
      then None
      else 
        Some 
          ("\""^pp_nontermroot_ty m xd r.rule_ntr_name ^ "\" = "^pp_com^"\n   " 
           ^ String.concat " | " 
               (List.map 
                  (function s -> s^"\n") 
                  (Auxl.option_map 
		     (pp_prod m xd r.rule_ntr_name r.rule_pn_wrapper) 
                     r.rule_ps))
           ^ "")
  | Hol _ | Lem _| Caml _ ->
      if r.rule_meta || r.rule_phantom 
      then None
      else 
        (* horrible hack to remove the parens introduced around an auxparam-introduced type name and its arguments when used on the left of a definition, for Lem *)
        let strip_surrounding_parens s =
          if s.[0]='(' && s.[String.length s -1]=')' then String.sub s 1 (String.length s -2) else s in
        Some 
          (strip_surrounding_parens (pp_nontermroot_ty m xd r.rule_ntr_name) ^ " = "^pp_com^"\n" 
	   ^ (match m with Lem _ -> " | " | _ -> "   ")
           ^ String.concat " | " 
               (List.map 
                  (function s -> s^"\n") 
                  (Auxl.option_map 
		     (pp_prod m xd r.rule_ntr_name r.rule_pn_wrapper) 
                     r.rule_ps))
           ^ "")
  | Coq co -> 
      pp_internal_coq_buffer :=
        !pp_internal_coq_buffer ^
        coq_maybe_decide_equality m xd r.rule_homs (Ntr r.rule_ntr_name);
      if r.rule_meta || r.rule_phantom 
      then None
      else
        let universe = try pp_hom_spec m xd (List.assoc "coq-universe" r.rule_homs) with Not_found -> "Set" in
        Some 
          (pp_nontermroot_ty m xd r.rule_ntr_name ^ " : "^universe^ " := "^pp_com^"\n" 
           ^ String.concat "\n" 
               (Auxl.option_map 
		  (pp_prod m xd r.rule_ntr_name r.rule_pn_wrapper)
                  r.rule_ps))
  | Twf wo -> 
      if r.rule_meta || r.rule_phantom 
      then None
      else
        Some 
          (pp_nontermroot_ty m xd r.rule_ntr_name ^ " : type. \n\n" 
           ^ String.concat "" 
               (List.map 
                  (function s -> s^"\n") 
                  (Auxl.option_map 
		     (pp_prod m xd r.rule_ntr_name r.rule_pn_wrapper)
                     r.rule_ps))
           ^ "")
  | Tex xo ->
      if not(xo.ppt_show_meta) && r.rule_semi_meta then 
        None
      else
        Some
(* TODO: update the following to respect pp_tex_LONG_PROD_NAME (if necessary...) *)
          (Str.replace_first 
             (Str.regexp_string (pp_tex_PROD_NAME m))  
             (pp_tex_FIRST_PROD_NAME m) 
             ( "\\newcommand{"
               ^ tex_rule_name m r.rule_ntr_name
               ^ "}{\n"
	       ^ (String.concat (pp_tex_PROD_NEWLINE_NAME m^"\n") 
                    ( ( pp_tex_RULEHEAD_NAME m^"{"
	                ^ String.concat  "  ,\\ "
	                    (List.map (function ntr,homs->pp_nontermroot m xd ntr) r.rule_ntr_names)
	                ^ "}{::=}{" ^ pp_com ^ "}")
                      ::
	                (Auxl.option_map 
                           (pp_prod m xd r.rule_ntr_name r.rule_pn_wrapper)
                           r.rule_ps)))
(*            ^"[5.0mm]" *)
	       ^ "}\n"  ))
  in 
  match result with
  | Some s -> Some (if !Global_option.output_source_locations >= 2 then "\n"^pp_source_location m r.rule_loc  ^ s else s)
  | None -> None

and pp_rule_list m xd rs = 
  (* FZ why rs is a rule list instead of a rulename list? *)
  let ntrs_rs = List.map (fun r -> r.rule_ntr_name) rs in

  (* print_endline ("** "^(Auxl.hom_name_for_pp_mode m)^" ** pp_rule_list: "^(String.concat " " ntrs_rs));  *)

  let int_rule_list_dep m xd rs td md fd =
    let rule_groups = 	  
      let deps = Auxl.select_dep_ts m xd.xd_dep in
      (* find all dependency groups that mention a rule in rs *)
      List.filter
        (fun rg -> List.exists (fun ntr -> List.mem (Ntr ntr) rg) ntrs_rs)
        deps in

    (* print_endline (String.concat " -- " *)
    (*                  (List.map (fun rg -> (String.concat " " *)
    (*                                          (List.map pp_plain_nt_or_mv_root rg))) rule_groups)); *)

    String.concat "" 
      ( List.map 
	  ( fun b -> 
            match b with 
            (* either there is exactly one ntr in this block, with a hom, *)
            (* and we generate a type abbreviation *)
            | [Ntr ntr] 
              when (None<>Auxl.hom_spec_for_pp_mode m(Auxl.rule_of_ntr xd ntr).rule_homs 
                      & match m with Isa _ | Coq _ | Hol _ | Lem _ | Caml _ -> true | _ -> false) 
              ->
(* PS hack to turn off printing of phantom nonterms which would otherwise turn into type abbreviations.  Please check - maybe this should be before dependency analysis??? *)
                if (Auxl.rule_of_ntr xd ntr).rule_phantom then "" else 
		let hs = Auxl.the 
                    (Auxl.hom_spec_for_pp_mode m (Auxl.rule_of_ntr xd ntr).rule_homs) in
                ( match m with 
                | Isa _ -> 
                    "types "
                    ^ "\"" ^ pp_nontermroot_ty m xd ntr ^ "\" = \""
                    ^ pp_hom_spec m xd hs
                    ^ "\"\n"
                | Hol _ -> 
                    "val _ = type_abbrev(\""
                    ^ pp_nontermroot_ty m xd ntr ^ "\", ``:"
                    ^ pp_hom_spec m xd hs
                    ^ "``);\n"
                | Coq _ -> 
                    let universe = 
                      try pp_hom_spec m xd (List.assoc "coq-universe" (Auxl.rule_of_ntr xd ntr).rule_homs) 
                      with Not_found -> "Set" in
                    "\nDefinition "
                    ^ pp_nontermroot_ty m xd ntr ^ " : " ^ universe ^ " := "
                    ^ pp_hom_spec m xd hs
                    ^ ".\n"
                | Twf _ -> 
                    "\n%abbrev "
                    ^ pp_nontermroot_ty m xd ntr ^ " : type = "
                    ^ pp_hom_spec m xd hs
                    ^ ".\n"
                | Caml _ -> 
                    "\ntype\n"
                    ^ pp_nontermroot_ty m xd ntr ^ " = "
                    ^ pp_hom_spec m xd hs
                    ^ "\n\n"
                | Lem _ -> 
                    "\ntype "
                    ^ pp_nontermroot_ty m xd ntr ^ " = "
                    ^ pp_hom_spec m xd hs
                    ^ "\n\n"
                | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "int_rule_list_dep" )
            (* or not, in which case we generate an inductive type definition *)
            | b ->    
                let b = List.rev b in (* FZ this ensures that the output follows the source order *)
	        let def_string =
	          String.concat md 
		    ( Auxl.option_map 
		        ( fun nm -> 
		          ( match nm with
		          | Mvr mvr -> None
		          | Ntr ntr -> pp_rule m xd (Auxl.rule_of_ntr xd ntr) ))
		        b ) in
	        if (String.length def_string) = 0 then ""
	        else 
                  let tds = 
                    td ( Auxl.option_map 
		         ( fun nm -> 
		           ( match nm with
		           | Mvr mvr -> None
		           | Ntr ntr -> Some (Auxl.rule_of_ntr xd ntr) ))
		         b ) in
                      
                  tds ^ def_string ^ fd ^ "\n")
	  rule_groups)
  in

  match m with 
  | Ascii ao -> 
      if (Auxl.select_dep_ts m xd.xd_dep) = [] 
      then String.concat "\n" (Auxl.option_map (pp_rule m xd) rs) ^ "\n" 
      else int_rule_list_dep m xd rs (fun rs -> "\n") "\n" ""
  | Isa io ->
      int_rule_list_dep m xd rs 
        ( fun rs -> 
          if Auxl.rules_require_nominal m xd rs then "nominal_datatype " else "datatype ")
        "and " ""
  | Hol ho ->
      int_rule_list_dep m xd rs (fun rs -> "val _ = Hol_datatype ` \n") ";\n" "`;"
  | Coq co ->
      let def = int_rule_list_dep m xd rs (fun rs -> "\nInductive ") "\nwith " "." in
      let coq_equality_code = !pp_internal_coq_buffer in
      pp_internal_coq_buffer := "";
      def ^ coq_equality_code
  | Twf wo ->
      int_rule_list_dep m xd rs (fun rs -> "") "\n" ""
  | Caml oo ->
      int_rule_list_dep m xd rs (fun rs -> "\ntype \n") "\nand " ""
  | Lem lo ->
      int_rule_list_dep m xd rs (fun rs -> "\ntype ") "\nand " ""
  | Tex xo ->
      String.concat "\n" (Auxl.option_map (pp_rule m xd) rs) 
      ^ "\n" 
      ^ "\\newcommand{"^pp_tex_RULES_NAME m^"}{"
      ^ pp_tex_BEGIN_RULES m
      ^ String.concat (pp_tex_INTERRULE_NAME m ^"\n" )
          (Auxl.option_map 
             (fun r -> 
               if not(xo.ppt_show_meta) && r.rule_semi_meta then 
                 None
               else Some (tex_rule_name m r.rule_ntr_name))
             rs)
      ^ (match rs with []-> "" | _ -> pp_tex_AFTERLASTRULE_NAME m)
      ^ "\n"^pp_tex_END_RULES ^ "}\n\n"
  | Lex _ | Yacc _ ->
      String.concat "\n" (Auxl.option_map (pp_rule m xd) rs) 
 

and pp_ascii_subrule m xd sr = 
  pp_nontermroot m xd sr.sr_lower ^  " "
  ^ pp_LTCOLONCOLON ^" "
  ^ pp_nontermroot m xd sr.sr_upper^" "
  ^ pp_homomorphism_list m xd sr.sr_homs 

and pp_plain_pps pps = 
  String.concat " " (List.map (function (pn,pn') -> "("^pn^","^pn'^")") pps)

and pp_plain_subrule_data srd =
  "subrule data:\n"
  ^ "  srd_proper_subntr_data=["^String.concat "; " (List.map (function (ntr,ntrs)->"("^ntr^",["^String.concat ";" ntrs^"])") srd.srd_proper_subntr_data)^"]\n"
  ^ "  srd_subrule_graph = "^String.concat " " (List.map (function (ntr,ntr')->"("^ntr^","^ntr'^")") srd.srd_subrule_graph)^"\n"
  ^ "  srd_subrule_pn_promotion = \n"
  ^ String.concat "" 
      (List.map 
         (function (ntrl,(ntru,pps)) -> 
           "     "^ntrl^" |-> "^ntru^"  "
           ^ pp_plain_pps pps ^"\n")
      srd.srd_subrule_pn_promotion)

and pp_plain_ntlmvlr ntlmvlr = 
  match ntlmvlr with
  | Mvrlist mvrs -> "<"^String.concat "," (List.map pp_plain_metavarroot mvrs)^">"
  | Ntrlist ntrs -> "["^String.concat "," (List.map pp_plain_nontermroot ntrs)^"]"

and pp_plain_top_sort m xd =
  let s =
    String.concat "\n****\n" (
    List.map (fun rl ->
      String.concat " "
	(List.map (fun r -> pp_nt_or_mv_root error_opts xd r) rl))
      (Auxl.select_dep_ts m xd.xd_dep) )
  in "*** dependencies in the grammar:\n"^ s ^"\n"

and pp_plain_dep_graph m xd =
  "xd_dep_graph = [\n"
  ^ String.concat "" 
      (List.map 
         (function (ntmvr,ntmvrs) ->
           ""^ pp_plain_nt_or_mv_root ntmvr ^" |-> " 
           ^ String.concat "," (List.map pp_plain_nt_or_mv_root ntmvrs)
           ^ "\n")
         (Auxl.select_dep_graph m xd.xd_dep))
  ^"]\n"

(* note that we have to restrict this to rule_meta nodes to get meaningful results *)

(* note also that as the deps have been closed under transivity before, it's not what you thought *)

and pp_dot_dep_graph m xd =
  "digraph G {\n " 
  ^ String.concat "" 
      (Auxl.option_map
         (function (ntmvr,ntmvrs) ->
           match ntmvr with
           | Ntr ntr when not((Auxl.rule_of_ntr xd ntr).rule_meta) ->
               Some 
                 (pp_plain_nt_or_mv_root ntmvr ^";\n" )
           | _ -> None)
         (Auxl.select_dep_graph_nontran m xd.xd_dep))
  ^ "\n"
  ^ String.concat "" 
      (Auxl.option_map
         (function (ntmvr,ntmvrs) ->
           match ntmvr with
           | Ntr ntr when not((Auxl.rule_of_ntr xd ntr).rule_meta) ->
               Some (String.concat ""
                 (List.map
                    (function ntmvr' ->
                      ""^ pp_plain_nt_or_mv_root ntmvr
                      ^ " -> " ^ pp_plain_nt_or_mv_root ntmvr'
                      ^ ";\n" )
                    ntmvrs))
           | _ -> None)
         (Auxl.select_dep_graph_nontran m xd.xd_dep))
  ^"}\n"
      
(* and pp_plain_dep_graph m xd = *)
(*   "xd_dep_graph = [\n" *)
(*   ^ String.concat ""  *)
(*       (List.map  *)
(*          (function (ntlmvlr,ntlmvlrs) -> *)
(*            ""^ pp_plain_ntlmvlr ntlmvlr ^" |-> "  *)
(*            ^ String.concat "," (List.map pp_plain_ntlmvlr ntlmvlrs) *)
(*            ^ "\n") *)
(*          xd.xd_dep.xd_dep_graph) *)
(*   ^"]\n" *)

and pp_ascii_contextrule m xd cr = 
  pp_nontermroot m xd cr.cr_ntr ^ " "
  ^ pp_UNDERSCORECOLONCOLON ^ " "
  ^ pp_nontermroot m xd cr.cr_target ^ " "
  ^ pp_COLONCOLON ^ " "
  ^ pp_nontermroot m xd cr.cr_hole ^ " "
  ^ pp_homomorphism_list m xd cr.cr_homs 

and pp_ascii_subst m xd subst = 
  quote_ident subst.sb_name ^ " "
  ^ pp_nontermroot m xd subst.sb_this ^ " "
  ^ pp_nt_or_mv_root m xd subst.sb_that^ " "
  ^ pp_homomorphism_list m xd subst.sb_homs 

and pp_syntaxdefn m xd = 
  match m with
  | Ascii ao -> 
      String.concat "\n" (List.map (pp_metavardefn m xd) xd.xd_mds) 
      ^ pp_RULES^"\n"
      ^ pp_rule_list m xd xd.xd_rs ^ "\n" 
      ^ pp_SUBRULES^"\n"
      ^ String.concat "\n" (List.map (pp_ascii_subrule m xd) xd.xd_srs) ^"\n"
      ^ String.concat "\n" (List.map (pp_ascii_contextrule m xd) xd.xd_crs) ^"\n\n"
      ^ pp_SUBSTITUTIONS^"\n"
      ^ String.concat "\n" (List.map (pp_ascii_subst m xd) xd.xd_sbs) ^"\n"
      ^ (if ao.ppa_show_deps then
          (pp_plain_top_sort m xd ^ pp_plain_dep_graph m xd)
        else "")
  | Isa _ | Coq _ | Hol _ | Lem _ | Twf _ | Caml _ ->
      String.concat "" (List.map (pp_metavardefn m xd) xd.xd_mds) 
      ^ pp_rule_list m xd xd.xd_rs 
  | Tex _ ->
      "\\newcommand{"^pp_tex_METAVARS_NAME m^"}{\n"
      ^ pp_tex_BEGIN_METAVARS m  (*  "\\[\\begin{array}{l}\n" *)
      ^ String.concat "\n" (List.map (pp_metavardefn m xd) xd.xd_mds) 
      ^ "\n"^pp_tex_END_METAVARS ^"}\n\n"  (*  ^ "\\end{array}\\]\n" *)
      ^ pp_rule_list m xd xd.xd_rs
  | Lex _ | Yacc _ ->
      "<<TODO>>"


and pp_plain_mytoken tok = 
  match tok with
  | Tok_nonterm (l,nt) -> col_yellow ao_default (pp_plain_nonterm nt)
  | Tok_metavar (l,mv) -> col_red ao_default (pp_plain_metavar mv)
(*   | Tok_terminal (l,tm) -> col_green ao_default (pp_plain_terminal  tm) *)
(*   | Tok_dots (l,n) -> pp_plain_dots n *)
(*   | Tok_listform (l,s) -> col_magenta ao_default s *)
(*   | Tok_otherident (l,s) -> col_blue ao_default s *)
					     
and pp_plain_variable var = var

and pp_variable m xd mvrp var =
  match m with
  | Lex _ | Yacc _ -> Auxl.errorm m "pp_variable"
  | Ascii ao -> var
  | Isa _ -> 
      (match Auxl.hom_spec_for_hom_name 
          "isavar" 
          (Auxl.mvd_of_mvr xd mvrp).mvd_rep with
      | None -> var
      | Some hs -> String.concat "" (apply_hom_spec m xd hs [var]))
  | Hol _ -> 
      (match Auxl.hom_spec_for_hom_name 
          "holvar" 
          (Auxl.mvd_of_mvr xd mvrp).mvd_rep with
      | None -> var
      | Some hs -> String.concat "" (apply_hom_spec m xd hs [var]))
  | Lem _ -> 
      (match Auxl.hom_spec_for_hom_name 
          "lemvar" 
          (Auxl.mvd_of_mvr xd mvrp).mvd_rep with
      | None -> var
      | Some hs -> String.concat "" (apply_hom_spec m xd hs [var]))
  | Tex _ -> 
      (match Auxl.hom_spec_for_hom_name 
          "texvar" 
          (Auxl.mvd_of_mvr xd mvrp).mvd_rep with
      | None -> var
      | Some hs -> String.concat "" (apply_hom_spec m xd hs [var]))
  | Coq _ | Twf _ -> var  (* placeholder - ultimately may want some De Bruijning here *)        
  | Caml _ -> 
  (* placeholder - ultimately may want some De Bruijning here *)        
      (match Auxl.hom_spec_for_hom_name 
          "ocamlvar" 
          (Auxl.mvd_of_mvr xd mvrp).mvd_rep with
      | None -> var
      | Some hs -> String.concat "" (apply_hom_spec m xd hs [var]))


and pp_plain_symterm st : string = 
  match st with
  | St_node (l,stnb) -> "(St_node :"^stnb.st_rule_ntr_name^":"^stnb.st_prod_name^": "^pp_plain_symterm_node_body stnb ^")"
  | St_nonterm (l,ntrp,nt) -> "(St_nonterm "^pp_plain_nonterm nt^")"
  | St_nontermsub (l,ntrpl,ntrpt,nt) -> "(St_nontermsub "^pp_plain_nonterm nt^")"
  | St_uninterpreted (l,s) -> "(St_uninterpreted "^s^")"
            
and pp_plain_symterm_element ste : string =
  match ste with
  | Ste_st (l,st) -> "(Ste_st "^pp_plain_symterm st^")"
  | Ste_metavar (l,mvrp,mv) -> "(Ste_metavar "^pp_plain_metavar mv ^")"
  | Ste_var (l,mvrp,var) -> "(Ste_var "^pp_plain_variable var^")"
  | Ste_list (l,stlis) -> 
      "(Ste_list ["
      ^ String.concat "," (pp_plain_symterm_list_items stlis) 
      ^ "])"

and pp_plain_symterm_elements stes : string list =
  List.map pp_plain_symterm_element stes
  
and pp_plain_symterm_node_body stnb : string =
  String.concat " " (pp_plain_symterm_elements stnb.st_es)

and pp_plain_symterm_list_items stlis : string list = 
  List.map (pp_plain_symterm_list_item) stlis

and pp_plain_symterm_list_item stli : string =
  match stli with
  | Stli_single (l,stes) -> 
      "Stli_single "^String.concat " " (pp_plain_symterm_elements stes)
  | Stli_listform stlb -> 
      "Stli_listform "^String.concat " " (pp_plain_symterm_list_body stlb)

and pp_plain_symterm_list_body stlb : string list =
  pp_plain_bound stlb.stl_bound :: " : " ::
  pp_plain_symterm_elements stlb.stl_elements

and pp_symterm m xd sie de st : string = 
  debug ("pp_symterm entry: "^pp_plain_symterm st^"\n\n");
  match st with
  | St_node (l,stnb) when stnb.st_rule_ntr_name = "fancy_formula" -> pp_symterm_node_body_fancy_formula m xd sie de stnb 
  | St_node (l,stnb) -> pp_symterm_node_body m xd sie de stnb 
  | St_nonterm (l,ntrp,nt) -> pp_nonterm_with_de_with_sie m xd sie de nt
  | St_nontermsub (l,ntrpl,ntrpt,nt) -> pp_nonterm_with_de_with_sie m xd sie de nt
  | St_uninterpreted (l,s) -> 
      match m with
      | Tex xo -> 
          "\\texttt{"
          ^ (if xo.ppt_colour then "\\textcolor{red}{" else "")
          ^ "<<"^Auxl.pp_tex_escape s^">>"
          ^ (if xo.ppt_colour then "}" else "")
          ^ "}"
      | _ ->
          Printf.sprintf "(PARSE_ERROR \"%s\" \"%s\")"
            (Location.pp_loc l) (String.escaped s)

(* pp_symterm_element is never used.  Instead, pp_symterm_elements uses pp_symterm_elements_walk *)
(*  to walk over pairs of a list of production elements and a list of symterm elements, keeping *)
(*  track of which is associated with which *)
(* *)            
(* and pp_symterm_element m xd sie de ste : string = *)

(*   debug ("pp_symterm_element entry: "^pp_plain_symterm_element ste^"\n\n"); *)

(*   match ste with *)
(*   | Ste_st (l,st) -> pp_symterm m xd sie de st *)
(*   | Ste_metavar (l,mvrp,mv) -> pp_metavar_with_de_with_sie m xd sie de mv  *)
(*   | Ste_var (l,mvrp,var) -> pp_variable m xd mvrp var *)
(*   | Ste_list (l,stlis) ->  *)
(*       "(" *)
(*       ^ String.concat "," (pp_symterm_list_items m xd sie de None [] (\* <- ARGH! *\) stlis)  *)
(*       ^ ")" *)

and extract_nonterms_deep_ste_list slil =
  ( match slil with
  | [] -> []
  | Stli_single (_,stel)::tl -> (extract_nonterms_deep stel) @ (extract_nonterms_deep_ste_list tl)
  | Stli_listform _::tl -> 
      Auxl.warning "<<internal: extract_nonterms_deep_ste_list not implemented over listforms>>>";
      extract_nonterms_deep_ste_list tl )
  
and extract_nonterms_deep s =
  match s with
  | [] -> []
  | Ste_metavar (_,_,(mvr,i))::t -> (Mvr mvr,i) :: (extract_nonterms_deep t)
  | (Ste_st (_,St_nonterm (_,_,(ntr,i))))::t -> (Ntr ntr,i) :: (extract_nonterms_deep t)
  | (Ste_st (_,St_nontermsub (_,_,_,(ntr,i))))::t -> (Ntr ntr,i) :: (extract_nonterms_deep t)
  | (Ste_st (_,St_node (_,stnb)))::t -> (extract_nonterms_deep stnb.st_es) @ (extract_nonterms_deep t)
  | (Ste_list (_,slil))::t -> (extract_nonterms_deep_ste_list slil) @ (extract_nonterms_deep t)
  | h::t ->
      Auxl.warning
        ("internal: extract_nonterms_deep case failure\n "
         ^ (pp_plain_symterm_element h) ^ "\n\n"); (extract_nonterms_deep t)

and extract_nonterms s =
  match s with
  | [] -> []
  | (Ste_st (_,St_nonterm (_,_,nt)))::t -> nt :: (extract_nonterms t)
  | (Ste_st (_,St_nontermsub (_,_,_,nt)))::t -> nt :: (extract_nonterms t)
  | (Ste_st (_,St_node (_,stnb)))::t -> (stnb.st_rule_ntr_name,[]) :: (extract_nonterms t)
  (* | (Ste_st (_,St_node (_,stnb)))::t -> (extract_nonterms stnb.st_es) @ (extract_nonterms t)  *)
  | h::t ->
      Auxl.warning
        ("internal: extract_nonterms case failure\n "
         ^ (pp_plain_symterm_element h) ^ "\n\n"); (extract_nonterms t)

and pp_symterm_node_body_fancy_formula m xd sie de stnb : string =
  (* pull out the real symterm list *)
  let sts = Auxl.option_map (function ste -> match ste with Ste_st(_,st) -> Some st | _ -> Auxl.error "internal: non Ste_st found in pp_symterm_node_body_fancy_formula") stnb.st_es in
  let pp_sts = List.map (pp_symterm m xd sie de) sts in
  let strings = Str.full_split (Str.regexp_string "-ARG-") stnb.st_prod_name in
  let pp_string s = match m with
  | Tex _ -> "\\texttt{"^Auxl.pp_tex_escape s^"}"
  | _ -> s in
  let rec fold_in strings pp_sts = 
    match (strings,pp_sts) with
    | (Str.Text s)::strings',_ -> pp_string s ^ fold_in strings' pp_sts
    | (Str.Delim _)::strings',pp_st::pp_sts' -> pp_st ^ fold_in strings' pp_sts'
    | [],[] -> ""
    | _,_ -> ("internal fold_in") in
  fold_in strings pp_sts

(*  "{{ "^ stnb.st_prod_name ^ String.concat " " pp_sts ^ "}}" *)

and pp_symterm_node_body m xd sie de stnb : string =
  debug ("pp_symterm_node_body entry: "^pp_plain_symterm_node_body stnb^"\n\n");
  let promoted_pn = 
    try
      let ntrt,pps = List.assoc stnb.st_rule_ntr_name xd.xd_srd.srd_subrule_pn_promotion in
      try List.assoc stnb.st_prod_name pps with
        Not_found -> Auxl.error ("internal error: pp_symterm_node_body \""^stnb.st_prod_name^"\" Not_found in pps "^pp_plain_pps pps)
    with
      Not_found -> stnb.st_prod_name in 
  let p = Auxl.prod_of_prodname xd promoted_pn in
  let prod_es = p.prod_es in
  match Auxl.hom_spec_for_pp_mode m p.prod_homs with
  (* if there's a hom, use that *)
  | Some hses ->
      let pp_es = pp_symterm_elements m xd sie de false prod_es stnb.st_es in
      let xs = apply_hom_spec m xd hses pp_es in
(*      " {{ "^String.concat " " xs ^" }} " *)
      " "^String.concat " " xs ^" "

  (* otherwise, if there's not a hom, default to something *)
  | None -> 
      let include_terminals = 
        match m with
        | Ascii _ | Tex _ | Lex _ | Yacc _ -> true
        | Coq _ | Isa _ | Hol _ | Lem _ | Twf _  -> false
        | Caml oo -> oo.ppo_include_terminals in
      let pp_es' () = pp_symterm_elements' m xd sie de include_terminals prod_es stnb.st_es in
      let pp_es () = pp_symterm_elements m xd sie de include_terminals prod_es stnb.st_es in
      match m with
      | Lex _ | Yacc _ -> Auxl.errorm m "pp_symterm_node_body"
      | Ascii _  -> String.concat " " (pp_es())
      | Tex _ -> 
          ( match stnb.st_prod_name with
          | "formula_dots" -> String.concat " \\quad " (pp_es())
          | _ -> pp_tex_insert_spacing (pp_es'()))
      | Isa _ | Hol _ | Lem _ | Coq _ | Twf _ | Caml _ ->
          ( match stnb.st_prod_name with

          (* special case pp for proof assistant judgement forms *)
          | "formula_judgement" -> 
              ( match stnb.st_es with
              | [Ste_st(_,St_node(l,stnb'))] ->
                  ( match stnb'.st_es with
                  | [Ste_st(_,St_node(_,stnb''))] ->
                      let p'' = Auxl.prod_of_prodname xd stnb''.st_prod_name in
                      (match m with
                      | Isa io -> 
                          (match isa_fancy_syntax_hom_for_prod m xd io p'' with
                          | None -> 
                              pp_symterm_element_judge_isa_plain m xd sie de p'' stnb'' 
                          | Some(hs,arity,prec) -> 
                              pp_symterm_element_judge_isa_fancy m xd sie de hs p'' stnb'')
                      | Coq co -> 
                          pp_symterm_element_judge_coq_plain m xd sie de p'' stnb''
                      | Twf wo -> 
                          pp_symterm_element_judge_twf_plain m xd sie de p'' stnb''
                      | Hol ho -> 
                          pp_symterm_element_judge_hol_plain m xd sie de p'' stnb''
                      | Lem lo -> 
                          pp_symterm_element_judge_lem_plain m xd sie de p'' stnb''
                      | Ascii _ | Tex _ | Lex _ | Yacc _ -> raise ThisCannotHappen
                      | Caml _ -> Auxl.error "internal: Caml pp_symterm for proper symterms not supported"
                      )
                  | _ -> raise (Invalid_argument ("pp_symterm_node_body2: strange production in formula_judgement")))
              | _ -> raise (Invalid_argument ("pp_symterm_node_body3: strange production in formula judgement ")))

          (* special case pp for user_syntax productions *)
          | s when stnb.st_rule_ntr_name = "user_syntax" ->
              (* print_string ("<<"^s^" "^pp_plain_symterm_node_body stnb^">>\n");flush stdout;*)
              (match stnb.st_es with
              | [Ste_st(_,st)] ->
                  pp_symterm m xd sie de st
              | [Ste_metavar(_,_,mv)] ->
                  pp_metavar_with_de_with_sie m xd sie de mv
              | _ -> raise (Invalid_argument ("pp_symterm_node_body4: strange production in user_syntax "^ "["^String.concat ";" (List.map pp_plain_symterm_element stnb.st_es) ^"]")))
                
          (* hack: special case pp for formula dots, before we do general homs for productions with dot forms *) 
          | "formula_dots" -> 
	     
              (match m with
              | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "formula_dots"
              | Caml _ -> Auxl.error "internal: Caml pp_symterm for proper symterms not supported"
              | Isa io ->
                  (match isa_fancy_syntax_hom_for_prod m xd io p with
                  | None -> 
	              ( match stnb.st_es with
	              | [] -> stnb.st_prod_name
	              | _  -> 
(* Tobias *)
(*                           "(" *)
(*                           ^ (\*stnb.st_prod_name*\) "ALL x__ : set (" *)
(*                           ^ String.concat " " pp_es *)
(*                           ^ "). x__)" *)
                          
                          "("
                          ^ (*stnb.st_prod_name*) "List.list_all (% b . b)" ^ " "
                          ^ String.concat " " (pp_es())
                          ^ ")"
                       )

                  | Some(hs,arity,prec) -> 
                      "(" ^ String.concat "" 
                              (apply_hom_spec m xd hs (pp_es()))
                      ^ ")")
                    
              | Hol _ -> 
	          ( match stnb.st_es with
	          | [] -> stnb.st_prod_name
	          | _  -> 
                      "("
                      ^ "EVERY (\\ b . b)" ^ " "
                      ^ String.concat " " (pp_es())
                      ^ ")"
                   )
              | Lem _ -> 
	          ( match stnb.st_es with
	          | [] -> stnb.st_prod_name
	          | _  -> 
                      lemTODO "11" (
                      "("
                      ^ "List.all (fun b -> b)" ^ " "
                      ^ String.concat " " (pp_es())
                      ^ ")"
                     )
                   )
              | Coq co -> 
                  let dl = ("formula: "
                            ^(String.concat " -- "
                                (List.map pp_plain_symterm_element stnb.st_es))) in
		  debug dl;
                  ( match stnb.st_es with
                  | [ Ste_list (_,[ Stli_listform stlb ]) ] ->
                      ( match stlb.stl_elements with
                      | [ Ste_st (_,St_node (_,stnb)) ] ->
			  
			  let stnb =                       
			    if (String.compare stnb.st_prod_name "formula_judgement") = 0 
			    then (* now skip the formula_judgement and judgement_ *)
                              ( match stnb.st_es with 
                              | [ Ste_st (_,St_node (_,{ st_es = [ Ste_st (_,St_node (_,stnb)) ] })) ]  -> stnb
                              | _ -> raise ThisCannotHappen )
			    else 
			      let dl = ("formula *** : "
					^(String.concat " -- "
					    (List.map pp_plain_symterm_element stnb.st_es))) in
			      debug dl;
			      stnb   
			  in

			  let nt_stnb = pp_symterm_node_body m xd ((Si_var ("_",0))::sie) de stnb in  (* used *)

                          let de1i = de1_lookup (fst de) stlb.stl_bound in

			  let mvs_nts_collect = extract_nonterms_deep stnb.st_es in
			  let collected = 
			    Auxl.remove_duplicates (List.map  
 			      (pp_nt_or_mv_with_de_with_sie m xd ((Si_var ("_",0))::sie) de) mvs_nts_collect) in
			  let collected_without_toplevel = 
 			    let rec rem_list aq ls =
 			      (match ls with 
 			      | [] -> [] 
 			      | (v::tl) -> if List.mem v aq then rem_list aq tl else v::(rem_list aq tl)) in 
 			    rem_list !(co.coq_quantified_vars_from_de) collected in
			  
			  let s_collected_without_toplevel =
			    if List.length collected = 1 
			    then List.hd collected_without_toplevel 
			    else "(" ^  String.concat "," collected_without_toplevel ^ ")" in

                          let body = 
                            if co.coq_expand_lists then 
                              let types_collected =
                                List.map (pp_nt_or_mv_root m xd)
                                  (List.map
                                     (fun ((x,_),_) -> Auxl.promote_ntmvr xd (Auxl.primary_nt_or_mv_of_nt_or_mv xd x))
                                     de1i.de1_ntmvsns) in
                              let s_types_collected = String.concat "_" types_collected in
                              Printf.sprintf "(unmake_list_%s %s)" s_types_collected de1i.de1_compound_id
                            else de1i.de1_compound_id in
                          let arg = 
                            if String.contains de1i.de1_pattern ',' then
                              Printf.sprintf "(map (fun (pat_: %s) => match pat_ with %s => %s end) %s)"
                                de1i.de1_coq_type_of_pattern de1i.de1_pattern 
                                s_collected_without_toplevel body
                            else
                              Printf.sprintf "(map (fun (%s : %s) => %s) %s)"
                                de1i.de1_pattern de1i.de1_coq_type_of_pattern 
                                s_collected_without_toplevel body in

   			  "(forall " ^ String.concat " " collected_without_toplevel ^ ", "  
 			  ^ "In " 
			  ^ s_collected_without_toplevel ^ " "
			  ^ arg
   			  ^ " -> " ^ nt_stnb ^")" 

(*                          if co.coq_expand_lists  *)
(*			  then  *)
(*			    (* EXPAND LISTS *) *)
(*			  let mvs_nts_collect = Auxl.remove_duplicates (extract_nonterms_deep stnb.st_es) in *)
(*                            let collected =  *)
(*                              (List.map   *)
(*                                 (pp_nt_or_mv_with_de_with_sie m xd ((Si_var ("_",0))::sie) de) mvs_nts_collect) in *)
(*                            let s_collected = *)
(*                              if List.length collected = 1  *)
(*                              then List.hd collected *)
(*                                else "(" ^  String.concat "," collected ^ ")" in *)
(*                            let types_collected = *)
(*                              List.map (pp_nt_or_mv_root m xd)  *)
(*                                (List.map  *)
(*                                   (fun (x,_) -> Auxl.promote_ntmvr xd (Auxl.primary_nt_or_mv_of_nt_or_mv xd x))  *)
(*                                   mvs_nts_collect) in *)
(*                            let s_types_collected = String.concat "_" types_collected in *)
(*                            let s_var_types_collected = *)
(*                              String.concat " "  *)
(*                                (List.map2 (fun v t -> "("^v^":"^t^")") collected types_collected) in *)

(*			    let aux_rel_name =  (* FZ FIND BETTER NAME SCHEME *) *)
(*			      let rec aux stnb = *)
(*			        let stnbs = *)
(*			          Auxl.option_map *)
(*			            (fun ste -> match ste with Ste_st (_,St_node (_,stnb)) -> Some stnb | _ -> None) *)
(*			            stnb.st_es in *)
(*                                let sons = String.concat "_" (List.map aux stnbs) in *)
(*			        let tmp = stnb.st_prod_name ^(if List.length stnbs = 0 then "" else "_") ^sons in *)
(*			        Str.global_replace (Str.regexp_string "judgement_") ""  *)
(*			          (Str.global_replace (Str.regexp_string "formula_") "" tmp) in *)
(*			      (aux stnb) ^ "_list" in *)

(*			    if not (List.mem aux_rel_name !(co.coq_list_aux_defns.defined)) *)
(*			    then begin *)
(*                              let new_def =  *)
(*			        "\nwith "^aux_rel_name^" : list_"^s_types_collected^" -> Prop :=\n"  *)
(*			        ^ " | Nil_"^aux_rel_name^" : "^aux_rel_name^" Nil_list_"^s_types_collected^"\n" *)
(*                                ^ " | Cons_"^aux_rel_name^" : forall "^s_var_types_collected ^" (l':list_"^s_types_collected^"),\n"  *)
(*                                       (* FZ freshen l' *) *)
(*         		        ^ "      (" ^ nt_stnb  *)
(*			        ^ ") -> " ^ aux_rel_name ^" l' ->\n"  *)
(*                                ^ "      " ^ aux_rel_name ^" (Cons_list_" ^s_types_collected ^ " " ^ String.concat " " collected  ^" l')" *)
(*			      in *)
(*                              co.coq_list_aux_defns.defined := !(co.coq_list_aux_defns.defined) @ [aux_rel_name]; *)
(*                              co.coq_list_aux_defns.newly_defined :=  *)
(*                                !(co.coq_list_aux_defns.newly_defined) @ [new_def] *)
(*			    end; *)

(*			    (* generate the needed list types *) *)
(*			    if not (List.mem ("list_"^s_types_collected) !(co.coq_list_types)) *)
(*			    then begin (* cannot call create_list_rule because of recursive modules, so... *) *)
(*                              let id = "list_"^s_types_collected in *)
(*                              co.coq_list_types := id :: !(co.coq_list_types); *)
(*                              co.coq_list_rules_defns :=  *)
(*                                ( "Inductive\n" *)
(*                                  ^ id ^ " : Set :=\n" *)
(*                                  ^ "   Nil_" ^ id ^ " : " ^ id ^ "\n" *)
(*                                  ^ " | Cons_" ^ id ^ " : "  *)
(*                                  ^ (String.concat " -> " types_collected) ^ " -> " ^id ^ " -> " ^ id ^ ".\n\n" *)
(*                                  ^ (Auxl.make_aux_list_funcs xd types_collected id)) :: !(co.coq_list_rules_defns) *)
(*			    end; *)

(*                            let arg =  *)
(*                              if (String.compare de1i.de1_compound_id req) = 0 *)
(*                              then de1i.de1_compound_id *)
(*                              else  *)

(*				let ty_list = Str.split (Str.regexp "(\\|*\\|)") de1i.de1_coq_type_of_pattern in *)
(*				let var_list = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in *)

(*				"(make_list_" ^ s_types_collected ^ " " *)
(*				^ "(map_list_"  *)
(*				^ String.concat "_" ty_list  *)
(*				^ " (fun " *)
(*				^ String.concat " " (List.map2 (fun x t -> "(" ^ x ^ ":" ^t ^")") var_list ty_list) *)
(*				^ " => " ^ s_collected ^ ") "  *)
(*				^ de1i.de1_compound_id ^ ")" *)
(*				^ ")" *)
(*			    in *)
(*			    "(" ^ aux_rel_name ^ " " ^ arg ^ ")" *)
(* 			  else begin *)
(*			    (* NATIVE LISTS *) *)

(*			    let mvs_nts_collect = extract_nonterms_deep stnb.st_es in *)
(*			    let collected =  *)
(*			      Auxl.remove_duplicates (List.map   *)
(* 				(pp_nt_or_mv_with_de_with_sie m xd ((Si_var ("_",0))::sie) de) mvs_nts_collect) in *)
(*			    let collected_without_toplevel =  *)
(* 			      let rec rem_list aq ls = *)
(* 				(match ls with  *)
(* 				| [] -> []  *)
(* 				| (v::tl) -> if List.mem v aq then rem_list aq tl else v::(rem_list aq tl)) in  *)
(* 			      rem_list !(co.coq_quantified_vars_from_de) collected in *)
(*			     *)
(*			    let s_collected_without_toplevel = *)
(*			      if List.length collected = 1  *)
(*			      then List.hd collected_without_toplevel  *)
(*			      else "(" ^  String.concat "," collected_without_toplevel ^ ")" in *)

(*                            let arg =  *)
(*                              if (String.compare de1i.de1_compound_id req) = 0 *)
(*                              then de1i.de1_compound_id *)
(*                              else *)
(*				let ty_list = Str.split (Str.regexp "(\\|*\\|)") de1i.de1_coq_type_of_pattern in *)
(*				let var_list = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in *)
(*				( if List.length ty_list = 1 *)
(*				then "(map (fun (" ^ List.hd var_list ^":" ^ List.hd ty_list ^") "  *)
(*				else "(map (fun (pat_:" ^(String.concat "*" ty_list)  *)
(*				       ^") => match pat_ with (" ^ String.concat "," var_list ^ ")" ) *)
(*                                  ^ " => " ^ s_collected_without_toplevel *)
(*				  ^ ( if List.length ty_list = 1 then ") " else " end) " ) *)
(*                                  ^ de1i.de1_compound_id ^ ")" in  *)

(*   			    "(forall " ^ String.concat " " collected_without_toplevel ^ ", "   *)
(* 			    ^ "In "  *)
(*			    ^ s_collected_without_toplevel ^ " " *)
(*			    ^ arg *)
(*   			    ^ " -> " ^ nt_stnb ^")"  *)
(* 			  end *)




                      | _ -> " <<< multiple slti in formula_dots not implemented >>> ")
		  | _ -> " <<< invalid symterm in formula_dots >>> " ) 
              | Twf _ -> raise TwelfNotImplemented
              )
          
          (* normal case pp for proof assistant term forms *)
          | _ -> 
              (match m with
              | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_symterm_node_body"
              | Isa io ->
                  (match isa_fancy_syntax_hom_for_prod m xd io p with
                  | None -> 
	              ( match stnb.st_es with
	              | [] -> promoted_pn
	              | _  -> 
                          "("
                          ^ promoted_pn ^ " "
                          ^ String.concat " " (pp_es())
                          ^ ")"  )
                  | Some(hs,arity,prec) -> 
                      "("
                      ^ String.concat "" 
                          (apply_hom_spec m xd hs (pp_es()))
                      ^")")
              | Coq _ | Twf _ -> 
	          ( match stnb.st_es with
	          | [] -> promoted_pn
	          | _  -> 
		      "("
                      ^ promoted_pn^" "
                      ^ String.concat  " " (pp_es())
                      ^ ")"  )
              | Caml _ -> 
	          ( match stnb.st_es with
	          | [] -> (String.capitalize promoted_pn)
	          | _  ->
                      let pp_es = pp_es() in
		      "("
                      ^ (String.capitalize promoted_pn)^" "
                      ^ ( if List.length pp_es = 1 
                          then List.hd pp_es
                          else "("^String.concat  "," pp_es^")" )
                      ^ ")"  )
              | Lem _ -> 
	          ( match stnb.st_es with
	          | [] -> (String.capitalize promoted_pn)
	          | _  ->
                      let pp_es = pp_es() in
		      "("
                      ^ (String.capitalize promoted_pn)^" "
                      ^ ( if List.length pp_es = 1 
                          then List.hd pp_es
                          else String.concat  " " pp_es^"" )
                      ^ ")"  )
(*
              | Lem _ -> 
	          ( match stnb.st_es with
	          | [] -> promoted_pn
	          | _  -> 
                      "("
                      ^ promoted_pn ^ " "
                      ^ String.concat " " (pp_es())
                      ^ ")"  )
*)
              | Hol _ -> 
	          ( match stnb.st_es with
	          | [] -> promoted_pn
	          | _  -> 
                      "("
                      ^ promoted_pn ^ " "
                      ^ String.concat " " (pp_es())
                      ^ ")"  )
              ))

and pp_symterm_element_judge_isa_fancy m xd sie de hs p'' stnb''  =
  let pp_es'' = pp_symterm_elements m xd sie de false p''.prod_es stnb''.st_es in
  "("
  ^ String.concat "" (apply_hom_spec m xd hs pp_es'')
  ^")"

and pp_symterm_element_judge_isa_plain m xd sie de p'' stnb'' =
  match m with
  | Isa io when io.ppi_isa_inductive ->
      let pp_es'' = pp_symterm_elements m xd sie de false p''.prod_es stnb''.st_es in
      (stnb''.st_prod_name) 
      ^ " "
      ^ "(" ^ String.concat ") (" pp_es'' ^ ")"
  | Isa io when not io.ppi_isa_inductive ->
      let pp_es'' = pp_symterm_elements m xd sie de false p''.prod_es stnb''.st_es in
      " ( "
      ^ String.concat " , " pp_es''
      ^ " )"
      ^ (" : ") 
      ^ (stnb''.st_prod_name)
  | _ -> assert false

and pp_symterm_element_judge_coq_plain m xd sie de p'' stnb'' =
  let pp_es'' = pp_symterm_elements m xd sie de false p''.prod_es stnb''.st_es in
  stnb''.st_prod_name ^ " "
  ^ String.concat " " pp_es''

and pp_symterm_element_judge_hol_plain m xd sie de p'' stnb''  =
  let pp_es'' = pp_symterm_elements m xd sie de false p''.prod_es stnb''.st_es in
  " ( "
  ^ stnb''.st_prod_name ^ " "
  ^ String.concat  " " pp_es''
  ^ " )"

and pp_symterm_element_judge_lem_plain m xd sie de p'' stnb''  =
  let pp_es'' = pp_symterm_elements m xd sie de false p''.prod_es stnb''.st_es in
  lemTODO "12" (
(*  " (*( *) "*)
  stnb''.st_prod_name ^ " "
  ^ String.concat  " " pp_es''
(*  ^ "(* ) *)"*)
 )
and pp_symterm_element_judge_twf_plain m xd sie de p'' stnb'' =
  let pp_es'' = pp_symterm_elements m xd sie de false p''.prod_es stnb''.st_es in
  stnb''.st_prod_name ^ " "
  ^ String.concat " " pp_es''

and pp_symterm_elements m xd sie de include_terminals prod_es es : string list = 
  List.map fst (pp_symterm_elements' m xd sie de include_terminals prod_es es) 

and pp_symterm_elements' m xd sie de include_terminals prod_es es : (string * tex_token_category) list = 
  (* walk along a pair of an element list (from a grammar production)             *)
  (* and a symterm_element list (from a parsed term) in concert, pretty-printing  *)
  (* include terminals or not, as requested *)
  (* TODO: perhaps we should replace this by the more general hom mechanism, which,*)
  (*  when instantiated by the `identity hom' (not yet constructed) behaves like this *)
  debug ("pp_symterm_elements' entry:\nes= [" ^String.concat " ; " (List.map pp_plain_symterm_element es)^"]\nprod_es= ["^String.concat " ; "(List.map pp_plain_element prod_es)^"]\n\n");

  let lem_paren_hack m (s,tc) = (s,tc) in (*match m with Lem _ -> ("("^s^")",tc) | _ -> (s,tc) in*)
  let rec f prod_es es = 
  debug ("f entry:\nes= [" ^String.concat " ; " (List.map pp_plain_symterm_element es)^"]\nprod_es= ["^String.concat " ; "(List.map pp_plain_element prod_es)^"]\n\n");
    match prod_es, es with
    | [],[] -> []
    | Lang_terminal tm::prod_es', es -> 
        if include_terminals then (pp_terminal_unquoted m xd tm,classify_TTC_terminal tm) :: (f prod_es' es)
        else (f prod_es' es)
    | Lang_nonterm _ :: prod_es', Ste_st(_,St_nonterm (l,ntrp,nt))::es' -> 
        lem_paren_hack m (pp_nonterm_with_de_with_sie m xd sie de nt,TTC_nonterm_or_metavar) :: (f prod_es' es')
    | Lang_nonterm _ :: prod_es' , Ste_st(_,St_nontermsub (l,ntrpl,ntrpt,nt))::es' -> 
        lem_paren_hack m (pp_nonterm_with_de_with_sie m xd sie de nt,TTC_nonterm_or_metavar) :: (f prod_es' es')
    | Lang_nonterm _ :: prod_es', Ste_st(_,St_node (l,stnb))::es'  -> 
        lem_paren_hack m (pp_symterm_node_body m xd sie de stnb,TTC_nonterm_or_metavar) :: (f prod_es' es')
    | prod_es, Ste_st(_,St_uninterpreted(l,s)) :: es' ->
        (pp_uninterpreted m xd s,classify_TTC_terminal s) :: (f prod_es es')
    | Lang_metavar _ :: prod_es', Ste_metavar (l,mvrp,mv)::es'  -> 
        (pp_metavar_with_de_with_sie m xd sie de mv,TTC_nonterm_or_metavar) :: (f prod_es' es')
    | Lang_metavar _ :: prod_es', Ste_var (l,mvrp,var)::es'  -> 
        (pp_variable m xd mvrp var,TTC_nonterm_or_metavar) :: (f prod_es' es')
    | Lang_list elb :: prod_es',Ste_list(l,stlis)::es' -> 
        (pp_symterm_list_items m xd sie de elb.elb_tmo elb.elb_es stlis) @ (f prod_es' es')
    | Lang_option _ :: _, _ -> 
        raise (Invalid_argument "pp_symterm_elements' Lang_option not implemented")
    | Lang_sugaroption _ :: _, _ -> 
        raise (Invalid_argument "pp_symterm_elements' Lang_sugaroption not implemented")
    | _,_ ->
        raise (Invalid_argument ("pp_symterm_elements' inconsistent structure\nes=      " ^String.concat "  " (List.map pp_plain_symterm_element es)^"\nprod_es= "^String.concat "  "(List.map pp_plain_element prod_es)))
  in
  f prod_es es

            
and pp_symterm_list_items m xd sie (de :dotenv) tmopt prod_es stlis : (string * tex_token_category) list =
  debug("pp_symterm_list_items entry:\nstlis= [" ^String.concat " ; " (List.map pp_plain_symterm_list_item stlis)^"]\nprod_es= ["^String.concat " ; "(List.map pp_plain_element prod_es)^"]\n\n");
  let debug_string = "" (*  ("(* pp_symterm_list_items entry:\nstlis= [" ^String.concat " ; " (List.map pp_plain_symterm_list_item stlis)^"]\nprod_es= ["^String.concat " ; "(List.map pp_plain_element prod_es)^"] *)\n\n")*) in
  let elements_to_string ls =  (* FZ duplicated a few lines below *)
    let rec intern ls =
      ( match ls with
      | [] -> []
      | (Lang_nonterm(ntr,_))::t -> ntr :: (intern t)
      | (Lang_metavar(mvr,_))::t -> mvr :: (intern t)
      | (Lang_terminal _)::t -> intern t
      | _::t -> Auxl.warning "internal: elements_to_string never happen\n"; intern t )
    in (* List.rev *) (intern ls) in

  let include_terminals = 
    match m with
    | Ascii _ | Tex _ | Lex _ | Yacc _ -> true
    | Coq _ | Isa _ | Hol _ | Lem _ | Twf _  -> false
    | Caml oo -> oo.ppo_include_terminals in
  let tmopt' = 
    ( match tmopt with 
    | None -> []  
    | Some tm -> [ pp_terminal m xd tm,classify_TTC_terminal tm ] ) in  
  match stlis with 
  | [] -> (match m with
      | Ascii ao -> if ao.ppa_ugly then [col_magenta ao "[empty stlis]",TTC_dummy] else ["",TTC_dummy]
      | Tex _ -> ["\\,",TTC_space]
      | Isa _ -> ["[]",TTC_dummy]
      | Caml _ -> ["[]",TTC_dummy]
      | Lem _ -> ["[]",TTC_dummy]
      | Coq co -> 
         if co.coq_expand_lists then 
           ["Nil_list_"^(String.concat "_" (elements_to_string prod_es)),TTC_dummy ]
         else
           ["nil",TTC_dummy]
      | Hol _ -> ["NIL",TTC_dummy]
      | Twf _ -> raise TwelfNotImplemented
      | Lex _ | Yacc _ -> assert false)
  |  _ -> 
      match m with
      | Lex _ | Yacc _ -> assert false
      | Ascii _ | Tex _ ->
          let ss = 
            Auxl.list_concat tmopt'
              (List.map (pp_symterm_list_item m xd sie de tmopt include_terminals prod_es) stlis) in
          (match m with Ascii ao when  ao.ppa_ugly -> [col_magenta ao "[slb",TTC_dummy] @ ss @ [col_magenta ao "slb]",TTC_dummy]  | _ -> ss)
      | Isa _ | Caml _ | Coq _ | Hol _ | Lem _ | Twf _ -> 
          let pp_stlis = List.map (function xs->List.map fst xs)
              (List.map (pp_symterm_list_item m xd sie de tmopt include_terminals prod_es) stlis) in
          (List.map (function s -> (s,TTC_dummy)) (match m with
          | Isa _ -> 
              [ "("
                ^ String.concat " " 
                    (Auxl.list_concat [ "@" ]
                       pp_stlis)
                ^ ")"]
          | Hol _ -> 
              [ "("
                ^ String.concat " " 
                    (Auxl.list_concat [ "++" ]
                       pp_stlis) 
                ^ ")"]
          | Caml _ -> 
              [ "("
                ^ String.concat " " 
                    (Auxl.list_concat [ "@" ]
                       pp_stlis) 
                ^ ")"]
          | Lem _ -> 
              [ lemTODO "13" ("("
                ^ String.concat " " 
                    (Auxl.list_concat [ "++" ]
                       pp_stlis) 
                ^ ")")]
          | Coq co ->  (* FZ use Auxl.list_app_coq *)
	      let l = 
	        List.flatten 
	          pp_stlis in
              if List.length l > 1 
	      then 
	        let app,nil = 
	          if co.coq_expand_lists
	          then 
		    let t = (*Auxl.pp_coq_type_name*) (String.concat "_" (elements_to_string prod_es)) in
		    ("app_list_"^t, "Nil_list_"^t)
	          else
		    ("app", "nil") in
	        [ "(" 
	          ^ (List.fold_right (fun x s -> "("^app^" "^x^" "^s^")") l nil) 
	          ^ ")" ]
	      else [ List.hd l ]
          | Twf _ -> raise TwelfNotImplemented
          | Lex _ | Yacc _ | Tex _ | Ascii _ -> raise ThisCannotHappen)
          )

and pp_symterm_list_item m xd sie (de :dotenv) tmopt include_terminals prod_es stli : (string * tex_token_category) list =
  debug ("pp_symterm_list_item entry:\nstli= "^pp_plain_symterm_list_item stli^"\nprod_es= "^String.concat "  " (List.map pp_plain_element prod_es)^"\n\n");

  let elements_to_string ls =  (* FZ duplicated a few lines below *)
    let rec intern ls =
      ( match ls with
      | [] -> []
      | (Lang_nonterm(ntr,_))::t -> ntr :: (intern t)
      | (Lang_metavar(mvr,_))::t -> mvr :: (intern t)
      | (Lang_terminal _)::t -> intern t
      | _::t -> Auxl.warning "internal: elements_to_string never happen\n"; intern t )
    in (* List.rev *) (intern ls) in

  match stli with
  | Stli_single (l,stes) -> 
      let pp_es' = pp_symterm_elements' m xd sie de include_terminals prod_es stes in
      let pp_es = List.map fst pp_es' in
      (match m with
      | Ascii ao -> if ao.ppa_ugly then [col_magenta ao "[stli_single",TTC_dummy] @ pp_es' @ [col_magenta ao "stli_single]",TTC_dummy]  else pp_es'
      | Tex _ -> pp_es'
      | Caml _ | Isa _ | Hol _ | Lem _ -> 
          ["[(" ^ String.concat "," pp_es ^ ")]",TTC_dummy]
      | Coq co ->
          if co.coq_expand_lists then
	    let name = (String.concat "_" (elements_to_string prod_es)) in
	    ["(Cons_list_" ^ name ^ " " ^ String.concat " " pp_es ^ " Nil_list_" ^ name ^")",TTC_dummy]
          else
            if List.length pp_es = 1
	    then [ "(cons " ^ List.hd pp_es ^ " nil)",TTC_dummy]
	    else ["(cons " ^ "(" ^ String.concat "," pp_es ^ ") nil)",TTC_dummy]
      | Twf _ -> raise TwelfNotImplemented
      | Lex _ | Yacc _ -> raise ThisCannotHappen)
  | Stli_listform stlb -> 
      let pp = pp_symterm_list_body m xd sie de tmopt include_terminals prod_es stlb in
      match m with
      | Ascii ao -> if ao.ppa_ugly then [col_magenta ao "[stli_listform",TTC_dummy] @ pp @ [col_magenta ao "stli_listform]",TTC_dummy]  else pp
      | _ -> pp

and pp_symterm_list_body m xd sie (de :dotenv) tmopt include_terminals prod_es stlb : (string * tex_token_category) list =
  debug ("pp_symterm_list_body entry:\nstlb= ["^String.concat " ; " (pp_plain_symterm_list_body stlb)^"]\nprod_es= ["^String.concat " ; " (List.map pp_plain_element prod_es)^"]\n\n");
  let debug_string = "" in (*("pp_symterm_list_body entry:\nstlb= ["^String.concat " ; " (pp_plain_symterm_list_body stlb)^"]\nprod_es= ["^String.concat " ; " (List.map pp_plain_element prod_es)^"]\n\n") in*)
  match m with
  | Lex _ | Yacc _ -> raise ThisCannotHappen
  | Ascii ao ->
      let ss = 
      (match stlb.stl_bound with
      | Bound_dotform bd -> 
          let es = stlb.stl_elements in
          let tmopt' = 
            ( match tmopt with 
            | None -> []  
            | Some tm -> [ pp_terminal m xd tm,TTC_dummy] ) in  
          let dots = [pp_dots m xd bd.bd_length,TTC_dummy] in
          pp_symterm_elements' m xd (bd.bd_lower::sie) de include_terminals prod_es es
          @ tmopt' @ dots @ tmopt'  
          @ pp_symterm_elements' m xd (bd.bd_upper::sie) de include_terminals prod_es es
      | Bound_comp bc ->
          let es = stlb.stl_elements in
          ["</",TTC_dummy]
          @ pp_symterm_elements' m xd ((Si_var (bc.bc_variable,0))::sie) de include_terminals prod_es es
          @ ["//",TTC_dummy]
          @ [pp_metavarroot m xd bc.bc_variable,TTC_dummy]
          @ ["/>",TTC_dummy]
      | Bound_comp_u bcu ->
          let es = stlb.stl_elements in
          ["</",TTC_dummy]
          @ pp_symterm_elements' m xd ((Si_var (bcu.bcu_variable,0))::sie) de include_terminals prod_es es
          @ ["//",TTC_dummy]
          @ [pp_metavarroot m xd bcu.bcu_variable,TTC_dummy] 
          @ ["IN",TTC_dummy]
          @ [pp_suffix_item_with_sie m xd [] true bcu.bcu_upper,TTC_dummy] 
          @ ["/>",TTC_dummy]
      | Bound_comp_lu bclu ->
          let es = stlb.stl_elements in
          ["</",TTC_dummy]
          @ pp_symterm_elements' m xd ((Si_var (bclu.bclu_variable,0))::sie) de include_terminals prod_es es
          @ ["//",TTC_dummy]
          @ [pp_metavarroot m xd bclu.bclu_variable,TTC_dummy] 
          @ ["IN",TTC_dummy]
          @ [pp_suffix_item_with_sie m xd [] true bclu.bclu_lower,TTC_dummy] 
          @ [pp_dots m xd bclu.bclu_length,TTC_dummy] 
          @ [pp_suffix_item_with_sie m xd [] true bclu.bclu_upper,TTC_dummy] 
          @ ["/>",TTC_dummy]
      )
      in if ao.ppa_ugly then [col_magenta ao "[slb",TTC_dummy] @ ss @ [col_magenta ao "slb]",TTC_dummy]  else ss
  | Tex xo ->
      let es = stlb.stl_elements in
      (match stlb.stl_bound with
      | Bound_dotform bd -> 
          let tmopt' = 
            ( match tmopt with 
            | None -> []  
            | Some tm -> [ pp_terminal m xd tm,classify_TTC_terminal tm ] ) in  
          let dots = [pp_dots m xd bd.bd_length,TTC_dots] in
          pp_symterm_elements' m xd (bd.bd_lower::sie) de include_terminals prod_es es
          @ tmopt' @ dots @ tmopt'  
          @ pp_symterm_elements' m xd(bd.bd_upper::sie) de include_terminals prod_es es
      | Bound_comp bc ->
          [pp_tex_COMP_NAME m ^"{"
           ^ pp_tex_insert_spacing
               (pp_symterm_elements' m xd ((Si_var (bc.bc_variable,0))::sie) de include_terminals prod_es es)
           ^ "}{" ^ pp_metavarroot m xd bc.bc_variable ^ "}",TTC_comp]
      | Bound_comp_u bcu -> 
          [pp_tex_COMP_U_NAME m ^"{"
           ^ pp_tex_insert_spacing
               (pp_symterm_elements' m xd ((Si_var (bcu.bcu_variable,0))::sie) de include_terminals prod_es es)
           ^ "}{" ^ pp_metavarroot m xd bcu.bcu_variable 
           ^ "}{" ^ pp_suffix_item_with_sie m xd [] true bcu.bcu_upper
           ^ "}",TTC_comp]
      | Bound_comp_lu bclu -> 
          [pp_tex_COMP_LU_NAME m ^"{"
           ^ pp_tex_insert_spacing
               (pp_symterm_elements' m xd ((Si_var (bclu.bclu_variable,0))::sie) de include_terminals prod_es es)
           ^ "}{" ^ pp_metavarroot m xd bclu.bclu_variable 
           ^ "}{" ^ pp_suffix_item_with_sie  m xd [] true bclu.bclu_lower
           ^ "}{" ^ pp_dots m xd bclu.bclu_length
           ^ "}{" ^ pp_suffix_item_with_sie m xd [] true bclu.bclu_upper
           ^ "}",TTC_comp]
      )
        
  | Isa _ | Coq _ | Hol _ | Lem _ | Twf _ | Caml _ -> 
      (List.map (function s -> (s,TTC_dummy))
         (match m with
         | Ascii _ | Tex _ | Lex _ | Yacc _ ->  raise ThisCannotHappen
         | Isa _ | Coq _ | Hol _ | Lem _ | Twf _ | Caml _ -> 
      (* interim placeholder code - not remotely right *)
      (* FZ I hope that this comment is outdated *) 
      let es = stlb.stl_elements in
      let (de1,de2)=de in
      (* print_string ("[[["^pp_plain_dotenv de^"]]]");flush stdout; *)
(*       let bound = (* was (stlb.stl_lower,stlb.stl_upper) in *) *)
      let de1i =  de1_lookup de1 stlb.stl_bound in

      let pp_body = 
	let tmp = String.concat "," 
            (pp_symterm_elements m xd ((Si_var ("_",0))::sie) de include_terminals prod_es es) in
	if (List.length es) > 1 then "("^tmp^")" else tmp in
      (* hacky optimisation to remove identity maps *)
      (*let debug_string = debug_string ^ "\n de1i.de1_pattern= \""^de1i.de1_pattern^"\"  and pp_body = \""^pp_body^"\"\n" in*)
      if de1i.de1_pattern=pp_body then [ de1i.de1_compound_id ]
      else
	( match m with
        | Ascii _ | Tex _ | Lex _ | Yacc _ -> raise ThisCannotHappen
	| Isa _ ->
	    let var_pattern_list = (* from de1 *)
	      (List.map 
		 (function (ntmv,subntr_data) -> 
		   pp_nt_or_mv_with_sie m xd [Si_punct "_"] ntmv) de1i.de1_ntmvsns) in

	    let type_pattern_list = (* put into de1 *)
	      (List.map (function ((ntmv_root,_),subntr_data) -> 
 		(*Auxl.pp_coq_type_name*)
		  (pp_nt_or_mv_root m xd 
		     (Auxl.promote_ntmvr xd
			(Auxl.primary_nt_or_mv_of_nt_or_mv xd ntmv_root))))
		 de1i.de1_ntmvsns) in
	    let pattern = 
	      let tmp = 
		String.concat "," 
		  (List.map2 (fun v t -> "("^v^"::"^t^")") var_pattern_list type_pattern_list) in
	      if List.length var_pattern_list = 1 then tmp else "("^tmp^")" in

            [ "(List.map (%"^pattern^"."^pp_body^") "
              ^ de1i.de1_compound_id
	      ^ ")" ] (* FZ *)
        | Hol _ -> 
            ["(MAP (\\"^de1i.de1_pattern^" . "^pp_body^") "
             ^ de1i.de1_compound_id
	     ^ ")"]
        | Caml _ -> 
            ["(List.map (fun "^de1i.de1_pattern^" -> "^pp_body^") "
             ^ de1i.de1_compound_id
	     ^ ")"]
        | Lem _ -> 
            [lemTODO "14" ("(List.map (fun "^de1i.de1_pattern^" -> "^pp_body^") "
             ^ de1i.de1_compound_id
	     ^ ")")]
	| Coq co ->
            let convert_elements ls =
              let rec intern ls =
                ( match ls with
                | [] -> []
                | (Lang_nonterm(ntr,_))::t -> 
                    let r = Auxl.rule_of_ntr xd ntr in
                    let b = (List.exists (fun (h,_) -> String.compare h "coq" = 0) r.rule_homs) in
                    (Auxl.promote_ntr xd ntr,b) :: (intern t)
                | (Lang_metavar(mvr,_))::t -> (mvr,false) :: (intern t)
                | (Lang_terminal _)::t -> intern t
                | _::t -> Auxl.warning "internal: elements_to_string never happen\n"; intern t )
              in (* List.rev *) (intern ls) in

	    let ty_list = Str.split (Str.regexp "(\\|*\\|)") de1i.de1_coq_type_of_pattern in
	    let var_list = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in
	    let map_fun =
	      if co.coq_expand_lists
	      then "map_list_" ^ String.concat "_" ty_list 
		(* let na_list =  *)
		(*   List.map  *)
		(*     Auxl.pp_coq_type_name_inverse *)
		(*     ty_list in *)
		(* "map_list_" ^ Auxl.pp_coq_type_name (String.concat "_" na_list)  *)
	      else "map" in

            let header, footer =
              let (el,bl) = List.split (convert_elements prod_es) in
              if (not co.coq_expand_lists) || List.exists (fun x -> x) bl 
              then "",""
              else (
                let make_fun = 
	          "make_list_" 
                  ^ (*Auxl.pp_coq_type_name*) (String.concat "_" el) in
                "("^make_fun^" ", ")" ) in

	    let pat_fun,pat_fun_end = 
	      if co.coq_expand_lists 
	      then (String.concat " " (List.map2 (fun x y -> "("^x^":"^y^")") var_list ty_list), "")
	      else 
		if List.length var_list = 1 
		then "("^de1i.de1_pattern^":"^de1i.de1_coq_type_of_pattern^")", "" (* FZ FRESHEN pat_ *)
		else "(pat_:"^de1i.de1_coq_type_of_pattern^") => match pat_ with " ^ de1i.de1_pattern, " end "  in

	    [ header 
	      ^ "("^map_fun^" (fun "^pat_fun^" => "^pp_body^ pat_fun_end ^") " 
	      ^ de1i.de1_compound_id ^")" ^ footer ] 
        | Twf _ -> raise TwelfNotImplemented
         )))

(** isa fancy syntax stuff *)

(* most of this logically belongs in aux, but some needs to be in this mutual recursion *)

and vanilla_element e = 
  match e with
  | Lang_nonterm (_,_)
  | Lang_metavar _ 
  | Lang_terminal _ -> true
  | Lang_option _
  | Lang_sugaroption _
  | Lang_list _ -> false
and vanilla_elements es = List.for_all vanilla_element es

and arity_of_vanilla_elements es = match es with
| [] -> 0
| e::es' -> (match e with 
  | Lang_nonterm (_,_) 
  | Lang_metavar _ -> 1
  | Lang_terminal _ -> 0
  | Lang_option _
  | Lang_sugaroption _
  | Lang_list _ -> raise ThisCannotHappen)
      + arity_of_vanilla_elements es'

and interleave xs y = match xs with
| [] -> []
| [x] -> [x]
| x1::x2::xs -> x1::y::interleave (x2::xs) y 

and hom_of_vanilla_elements es = 
  let rec hom_of_vanilla_elements' es i = match es with
  | [] -> [] 
  | e::es' -> 
      match e with 
      | Lang_nonterm (_,_) 
      | Lang_metavar _ -> Hom_index i :: hom_of_vanilla_elements' es' (i+1)
      | Lang_terminal s -> Hom_terminal s :: hom_of_vanilla_elements' es' i
      | Lang_option _ 
      | Lang_sugaroption _ 
      | Lang_list _ -> raise ThisCannotHappen in
  interleave (hom_of_vanilla_elements' es 0) (Hom_string " ") 




(* we don't expect to be able to generate reasonable isa fancy syntax *)
(* for singleton nonterms/metavars or where we have adjacent nonterms/metavars *)
(* that aren't separated by a terminal.  Check this. *)
and terminal_separated_vanilla_elements es = match es with
| [] -> false
| [Lang_nonterm(_,_)]
| [Lang_metavar _] -> false
| [Lang_terminal _] -> true
| es ->
    let rec f last es = match es with
    | [] -> true
    | e::es -> match last,e with
      | None,(Lang_nonterm(_,_)|Lang_metavar _) -> f (Some false) es
      | None,(Lang_terminal _)                  -> f (Some true) es
      | Some false,(Lang_nonterm(_,_)| Lang_metavar _) -> false
      | Some true,(Lang_nonterm(_,_)| Lang_metavar _)  -> f (Some false) es
      | Some b,(Lang_terminal _) -> f (Some true) es
      | _,_ -> raise ThisCannotHappen
    in
    f None es

(* (\* we don't expect to be able to generate reasonable isa fancy syntax *\) *)
(* (\* for singleton nonterms/metavars.  Check this. *\) *)
(* let terminal_separated_vanilla_elements es = match es with *)
(* | [] -> false *)
(* | [Lang_nonterm(_,_)]  *)
(* | [Lang_metavar _] -> false *)
(* | [Lang_terminal _] -> true *)
(* | es -> true *)

and arity_of_homspec hs = 
  match hs with
  | [] -> 0
  | hse::hs' -> (match hse with 
    | Hom_string _ -> arity_of_homspec hs'
    | Hom_index i -> max (1+i) (arity_of_homspec hs')
    | Hom_terminal _ -> arity_of_homspec hs')


and isa_fancy_syntax_hom_for_prod m xd io p = 
  let hso = Auxl.hom_spec_for_hom_name "isasyn" p.prod_homs in
  let default_fancy_syntax_for_this_prod = 
    io.ppi_fancy_syntax 
      && vanilla_elements p.prod_es 
      && terminal_separated_vanilla_elements p.prod_es in
  let hsoprec = Auxl.hom_spec_for_hom_name "isaprec" p.prod_homs in
  let prec = match hsoprec with
  | None -> "50"
  | Some hs -> pp_hom_spec m xd hs in
  match hso,default_fancy_syntax_for_this_prod with
  | None,false -> 
      (* no hom *)
      None
  | None,true -> 
      (* default hom *) 
      let arity = arity_of_vanilla_elements p.prod_es in
      let hs = hom_of_vanilla_elements p.prod_es in
      Some (hs,arity,prec)
  | Some hs,_ -> 
      (* user override *)
      let arity = arity_of_homspec hs in
      Some(hs,arity,prec)


and isa_fancy_syntax_clause_for_prod m xd io p = 
  match isa_fancy_syntax_hom_for_prod m xd io p with
  | None -> ""
  | Some(hs,arity,prec) ->
      let rec list_make s i = if i=0 then [] else s::list_make s (i-1) in
      "(\""
      ^ String.concat "" (apply_hom_spec m xd hs (list_make "_" arity)) 
      ^ "\" "^ prec ^")" 
          
and isa_fancy_syntax_clause_for_defn m xd io dc_name dc_wrapper d = 

(* we generate things like this:

   inductive_set reduce :: "(t*t) set"
   and  "reduce'" :: "t => t =>  bool" ("_ ---> _" 50)
   where "(t1 ---> t2) ==  ( t1 , t2 ) : reduce"
*)

  let prod_name = dc_wrapper ^ d.d_name in
  let p = Auxl.prod_of_prodname xd prod_name in
  match isa_fancy_syntax_hom_for_prod m xd io p with
  | None -> None
  | Some(hs,arity,prec) ->
      let rec list_make s i = if i=0 then [] else s::list_make s (i-1) in

      let isa_syntax_type_of_defn : syntaxdefn -> defn -> string = 
        fun xd d ->  
          let ss = (Auxl.option_map (pp_element m xd [] false) p.prod_es) in
          String.concat "" (List.map (function s->s^" => ") ss) ^ " bool" in
      let isa_syntax_prod_name = prod_name^"'" in
      let syntax_part = 
        "  \""^isa_syntax_prod_name ^"\""
        ^ " :: " 
        ^ "\"" ^ isa_syntax_type_of_defn xd d ^"\" "
        ^ "(\""
        ^ String.concat "" (apply_hom_spec m xd hs (list_make "_" arity)) 
        ^ "\" "^prec^")" in
      
(* TODO proper freshening in the first case below *)
      let stnb = canonical_symterm_node_body_of_prod dc_name p in 
      let translations_part = 
        "  \"" ^ pp_symterm_element_judge_isa_fancy m xd [] de_empty hs p stnb   
        ^ " == "
        ^ pp_symterm_element_judge_isa_plain m xd [] de_empty p stnb  ^ "\"" in
      Some(syntax_part,translations_part)



and isa_fancy_syntax_clause_for_fundefn m xd io fdc_name fd = 
(* code duplication wrt the above *)
  let prod_name = fd.fd_pn_wrapper ^ fd.fd_name in
  let p = Auxl.prod_of_prodname xd prod_name in
  match isa_fancy_syntax_hom_for_prod m xd io p with
  | None -> None
  | Some(hs,arity,prec) ->
      let rec list_make s i = if i=0 then [] else s::list_make s (i-1) in

      let isa_syntax_type_of_fundefn : syntaxdefn -> fundefn -> string = 
        fun xd fd ->  
          let ss = (Auxl.option_map (pp_element m xd [] false) p.prod_es) in
          String.concat "" (List.map (function s->s^" => ") ss) ^ " bool" in
      let isa_syntax_prod_name = "_" ^ prod_name in
      let syntax_part = 
        "  \""^isa_syntax_prod_name ^"\""
        ^ " :: " 
        ^ "\"" ^ isa_syntax_type_of_fundefn xd fd ^"\" "
        ^ "(\""
        ^ String.concat "" (apply_hom_spec m xd hs (list_make "_" arity)) 
        ^ "\" "^prec^")" in
      
(* TODO proper freshening in the first case below *)
      let stnb = canonical_symterm_node_body_of_prod fdc_name p in 
      let translations_part = 
        "  \"" ^ pp_symterm_element_judge_isa_fancy m xd [] de_empty hs p stnb   ^ "\""
        ^ " \\<rightleftharpoons> "
        ^ "\""^ pp_symterm_element_judge_isa_plain m xd [] de_empty p stnb  ^ "\"" in
      Some(syntax_part,translations_part)



and de1_lookup de1 bound = 
  try List.assoc bound de1 with 
    Not_found -> 
      let de1_bogus = 
        { de1_ntmvsns = [];
          de1_compound_id = "<<< de1_lookup not found: bound "^pp_plain_bound bound^" >>>";
          de1_pattern =   "[[[ de1_lookup not found: in de "^pp_plain_dotenv1 de1^" ]]]";
          de1_coq_type_of_pattern = "<<< de1_lookup not found >>>";
          de1_hol_type_of_compound_id = "<<< de1_lookup not found >>>"; } in
      de1_bogus



   










       


(*  [ "<<< coq pp_symterm_list_body non-identity map not implemented >>> " ] ) *)

(* these are used when generating names for aux funcs over .. *)
let rec make_name_symterm m xd typ st =
  match st with
  | St_node (_,snb) -> make_name_elements m xd typ snb.st_es
  | St_nonterm (_,ntr,_) -> if typ then pp_nontermroot_ty m xd ntr else pp_nontermroot m xd ntr
  | St_nontermsub (_,l,t,(ntr,_)) -> 
      l^"-"^t
      ^if typ then pp_nontermroot_ty m xd ntr 
      else pp_nontermroot m xd ntr
  | St_uninterpreted (_,s) -> s
and make_name_element m xd typ e =
  match e with
  | Ste_st (_,st) -> make_name_symterm m xd typ st 
  | Ste_metavar (_,mvr,_) -> if typ then pp_metavarroot_ty m xd mvr else pp_metavarroot m xd mvr
  | Ste_var (_,mvr,_) -> (* mvr *) Auxl.error "internal: Ste_var in make_name_element"
  | Ste_list (_,stlil) -> Auxl.error "internal: Ste_list in make_name_element"
and make_name_elements m xd typ es = 
  let sep = if typ then "*" else "_" in
  let lst = List.map (make_name_element m xd typ) es in
  let body = String.concat sep (lst) in
  if (List.length lst) > 1 then
    if typ then "("^body^")" 
    else body  (* FZ need a proper separator for not typ *)
  else body 

let rec make_dep_symterm st =
  match st with
  | St_node (_,snb) -> make_dep_elements snb.st_es
  | St_nonterm (_,ntr,_) -> [ ntr ]
  | St_nontermsub (_,l,t,(ntr,_)) -> [ l^"-"^t^ntr ] (* FZ ASK *)
  | St_uninterpreted (_,s) -> [ s ] 
and make_dep_element e =
  match e with
  | Ste_st (_,st) -> make_dep_symterm st
  | Ste_metavar (_,mvr,_) -> [ mvr ]
  | Ste_var (_,mvr,_) -> [ mvr ]
  | Ste_list (_,stlil) -> Auxl.error "internal: Ste_list in make_dep_element"
and make_dep_elements es = 
  List.concat (List.map make_dep_element es) 


(* extract variables from a symterm - this should go in Aux *)

let extract_quantified_proof_assistant_vars m xd de1 de2 de3 =
  let coq_expand_list = 
    ( match m with
    | Coq co when co.coq_expand_lists -> true
    | _ -> false ) in
    
  let is_judgement_ntmv ntmv = match ntmv with
  | ((Ntr ntr),suff) -> 
      let r = Auxl.rule_of_ntr xd (Auxl.primary_ntr_of_ntr xd ntr) in
      r.rule_judgement
  | ((Mvr mvr),suff) -> false in
  
  Auxl.remove_duplicates 
    (List.map (function (_,de1i (*(ntmvsns,s,_,_,hol_type_var)*))-> 
      (* FZ put the coq_type computation inside de1 *)
      let coq_type_pp1 = 
	(List.map 
	   (function ((ntmv_root,_),subntr_data) -> 
 	     (*Auxl.pp_coq_type_name *)
	       (pp_nt_or_mv_root_ty m xd (* FZ *)
		  (Auxl.promote_ntmvr xd
		     (Auxl.primary_nt_or_mv_of_nt_or_mv xd ntmv_root))))
           de1i.de1_ntmvsns) in
      let tmp = 
	if coq_expand_list
	then String.concat "_" coq_type_pp1 
	else String.concat "*" coq_type_pp1 in
      let coq_type_var = 
	if coq_expand_list 
	then "list_" ^tmp 
	else "list " ^ (if (List.length coq_type_pp1) > 1 then "("^tmp^")" else tmp) in
      de1i.de1_compound_id,de1i.de1_hol_type_of_compound_id,(coq_type_var,Some tmp )) de1
     @ 
       List.map
	 (function (_,(_,i,_)) ->
	   ( match i with
	   | Si_var (s,_) ->   (* PS notes that this s originally shadowed what is now de1i.de1_compound_id, which is odd... *)
	       let t = 
		 pp_metavarroot_ty m xd 
		   (Auxl.primary_mvr_of_mvr xd s) in
	       (s,t,(t,None)) 
	   | Si_num s -> ("UNK: NUM "^s,"UNK_HTP",("UNK_CTP",None))
	   | Si_punct s -> ("UNK: PUNCT "^s,"UNK_HTP",("UNK_CTP",None))
	   | Si_index i -> ("UNK: PUNCT "^string_of_int i,"UNK_HTP",("UNK_CTP",None)) ))
(*  	   | _ -> ("UNK","UNK_HTP",("UNK_CTP",None)))) *)
	 de2
     @ 
       Auxl.option_map 
         (function (ntmv,_) -> 
           if not(is_judgement_ntmv ntmv) then 
	     let typ = 
               (*Auxl.pp_type_name m xd*)
	         (pp_nt_or_mv_root_ty m xd 
	            (Auxl.promote_ntmvr xd
		       (Auxl.primary_nt_or_mv_of_nt_or_mv xd (fst ntmv)))) in
             Some 
               ((pp_nt_or_mv_with_de_with_sie m xd [] de_empty ntmv),
		typ,(typ,None))
           else 
             None)
         de3)


let pp_pp_mode m = match m with 
  | Coq _ -> "Coq"
  | Isa _ -> "Isa"
  | Hol _ -> "Hol"
  | Lem _ -> "Lem"
  | Twf _ -> "Twf"
  | Ascii _ -> "Ascii" 
  | Tex _ -> "Tex"
  | Caml _ -> "Caml"
  | Lex _  -> "Lex"
  | Yacc _ -> "Yacc"

