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

exception TwelfNotImplemented;;

exception WorkInProgress;;

exception LemTODO;;

exception DE1 of string;;

open Location;;

(** ************************ *)
(** internal rep of systems  *)
(** ************************ *)

type loc = Location.t list (* l *)
let dummy_loc = []

module StringSet = Set.Make(String)
      
type prod_flavour = Bar  (* pf *) 
  (* for future extensions, eg, associativity annotations *)

type parsing_annotation_type =
  | LTEQ
  | Left
  | Right
  | Non

type terminal = string  (* tm *)

and langname = string  (* ln *)

and nonterm = nontermroot * suffix  (* nt *)
and nontermroot = string  (* ntr, or ntrp for primary *)

and metavar = metavarroot * suffix  (* mv *)
and metavarroot = string  (* mvr, or mvrp for primary *)
and metavardefn =  (* mvd *)
    { mvd_name : metavarroot;
      mvd_names : (metavarroot * homomorphism list) list;  (* includes the mvd_name *)
      mvd_rep : metavarrep;
      mvd_indexvar : bool;              (* invariant: not (mvd_indexvar /\ mvd_locally_nameless) *)
      mvd_locally_nameless : bool;      (* FZ: might just keep the hom *)
      mvd_phantom : bool;
      mvd_loc : loc }
and metavarrep = homomorphism list

and nt_or_mv = nt_or_mv_root * suffix  (* ntmv *)
and nt_or_mv_root =  (* ntmvr *)
  | Ntr of nontermroot 
  | Mvr of metavarroot
and ntl_or_mvl_root = 
  | Mvrlist of metavarroot list
  | Ntrlist of nontermroot list

and subntr_data = (nontermroot*nontermroot) option (* subntr_data, lower and top *)

and prodname = string  (* pn *)

and category = string  (* cat *)

and homomorphism = hom_name * hom_spec  (* hom, or (hn,hs) *)
and hom_name = string  (* hn *)
and hom_spec = hom_spec_el list  (* hs *)
and hom_spec_el =  (* hse *)
  | Hom_string of string
(*   | Hom_symterm of symterm   *)
  | Hom_index of int (* i *)
  | Hom_terminal of terminal
  | Hom_ln_free_index of (int list) * int      (* FZ keeping this separate from the main thing for now *)

and embedmorphism = loc * hom_name * embed_spec
and embed_spec = embed_spec_el list (* es *)
and embed_spec_el = (* ese *)
  | Embed_string of loc*string
  | Embed_inner of loc*string

and suffix = suffix_item list  (* suff *)
and suffixnum = string  (* suffn *)
and suffixvar = string  (* suffv *)
and suffix_item =  (* suffi *)
  | Si_num of suffixnum 
  | Si_punct of string (* of length 1 except when used for fancy sie printing*)
  | Si_var of suffixvar * int  (* the int is an offset, typically 0/-1/+1 *)
  | Si_index of int (* de bruijn index to the closest enclosing list form *)

and suffix_index_env = suffix_item list (* sie *) 
    (* invariant: just Si_num or Si_var *)

and bound =  (* b, bound *)
  | Bound_dotform of bound_dotform 
  | Bound_comp of bound_comp
  | Bound_comp_u of bound_comp_u
  | Bound_comp_lu of bound_comp_lu

and bound_dotform = (* bd *)
    { bd_lower : suffix_item;
      bd_upper : suffix_item;
      bd_length : int; (* the 0-,1- or 2-or-more dots *) } 

and bound_comp = (* bc *)
    { bc_variable : suffixvar }

and bound_comp_u = (* bcu *)
    { bcu_variable : suffixvar;
      bcu_upper : suffix_item}

and bound_comp_lu = (* bclu *)
    { bclu_variable : suffixvar;
      bclu_lower : suffix_item;
      bclu_upper : suffix_item;
      bclu_length : int}
      
and prod_env = (bound option) list (* pe *)

(* see comments in bounds.ml for what these mean *)
(* and dotenv1 = (bound * ((nt_or_mv*subntr_data) list *string * string * string * string)) list  (\* de1 *\) *)
(* and dotenv2 = (nt_or_mv * (suffix*suffix_item*bound)) list (\* de2 *\) *)

and dotenv1_item = (* de1i *)
  { de1_ntmvsns : (nt_or_mv*subntr_data) list;
    de1_compound_id : string;
    de1_pattern : string;
    de1_coq_type_of_pattern : string;
    de1_hol_type_of_compound_id : string;
  } 
and dotenv1 = (bound * dotenv1_item) list  (* de1 *)

and dotenv2 = (nt_or_mv * (suffix*suffix_item*bound)) list (* de2 *)

and dotenv3 = (nt_or_mv*subntr_data) list
and dotenv = dotenv1 * dotenv2 (* (de1,de2) as de *) 

and bindspec = (* bs *)
  | Bind of mse * nonterm
  | AuxFnDef of auxfn * mse
  | NamesEqual of mse * mse      (* not currently implemented *)
  | NamesDistinct of mse * mse   (* not currently implemented *)
  | AllNamesDistinct of mse      (* not currently implemented *)
and mse =  (* mse *) (* mse stands for `metavar set expression', but includes nonterms too *)
  | MetaVarExp of metavar 
  | NonTermExp of nonterm
  | MetaVarListExp of metavar * bound  
  | NonTermListExp of nonterm *  bound  
  | Aux of auxfn * nonterm
  | AuxList of auxfn * nonterm * bound 
  | Union of mse * mse
  | Empty
(* invariant: in the List forms, the nt or mv contains exactly one Si_index *)

and auxfn = string (* f *)

and mse_type_item = (* mse_tyi *)
  | Mse_ty_ntmvr of nt_or_mv_root
  | Mse_ty_aux of auxfn
  
and mse_type = mse_type_item list (* mse_ty *)

and auxfn_type = nontermroot list * nt_or_mv_root

and element = (* e *)
  | Lang_nonterm of nontermroot * nonterm  (* primary, as-written *)
  | Lang_metavar of metavarroot * metavar  (* primary, as-written *)
  | Lang_terminal of terminal
  | Lang_option of element list    (* not currently implemented *)
  | Lang_sugaroption of terminal   (* not currently implemented *)
  | Lang_list of element_list_body

and element_list_body = (* elb *)
    { elb_boundo : bound option;
      elb_tmo : terminal option;
      elb_es : element list ;} 
(*      elb_has_self_edge : bool  *)
      (* invariant: nested dot forms in productions are not supported, *)
      (* so elb_es contains only Lang_nonterm, Lang_metavar, Lang_terminal *)

and prod = (* p *)
    { prod_name : prodname;  
      prod_flavour : prod_flavour;
      prod_meta : bool;
      prod_sugar : bool;   
      prod_categories : StringSet.t;
      prod_es : element list;
      prod_homs : homomorphism list;
      prod_disambiguate : (string * string) option;
      prod_bs : bindspec list;
      prod_loc : loc }

(* The prod_sugar productions are a subset of the prod_meta productions *)
(* which should be _allowed_ by the concrete term parser.  In all other *)
(* respects they are treated simply as prod_meta productions.  Invariant: *)
(* if prod_sugar true then prod_meta also true *)
      
and rule =  (* r *)
    { rule_ntr_name : nontermroot; 
      rule_ntr_names : (nontermroot * homomorphism list) list;   
        (* includes rule_ntr_name as first item*)
      rule_pn_wrapper : string;
      rule_ps : prod list;
      rule_homs : homomorphism list;
      rule_meta : bool; 
        (* semi_meta OR rule occurs as srs_lower OR phantom *)
      rule_semi_meta : bool; 
        (* defnclass/judgement/formula/terminals/user_syntax *)
      rule_phantom : bool; 
        (* keeping phantom distinct from meta for now *)
      rule_judgement : bool; 
      rule_loc : loc }

and subrule =  (* sr *)
    { sr_lower : nontermroot; (* the primary one *)
      sr_upper : nontermroot; (* the primary one *)
      sr_top : nontermroot;   (* the primary one *)
      sr_homs : homomorphism list;
      sr_loc : loc }

and proper_subntr_data = (nontermroot * (nontermroot list)) list
   (* giving, for each primary ntr of a subrule, the list of all proper primary sub ntrs *)
and subrule_graph = (nontermroot * nontermroot) list 
   (* giving the edges of the transitive closure of <: *)
and subrule_pn_promotion = (nontermroot * (nontermroot * (prodname*prodname) list)) list
   (* for each subrule, the primary ntr mapped to the top ntr and the lower->top prodname mapping*)
and subrule_data = 
    { srd_proper_subntr_data : proper_subntr_data;
      srd_subrule_graph : subrule_graph;
      srd_subrule_pn_promotion : subrule_pn_promotion } (* srd *)

and contextrule =  (* cr *)
    { cr_ntr : nontermroot; (* the primary one *)
      cr_target : nontermroot; (* the primary one *)
      cr_hole : nontermroot;  (* the primary one *)
      cr_homs : homomorphism list;  (*dead code? *)
      cr_loc : loc }

and subst =  (* subst *)
    { sb_name : string;        (* "name this that foo" = {this/that}foo *)
      sb_this : nontermroot;   (* the primary one *)
      sb_that : nt_or_mv_root; (* the primary one *) 
      sb_multiple : bool;      (* false for single substitution *)
      sb_homs : homomorphism list;
      sb_loc : loc }
  (* this and that (if an ntr) must not be ntrs of subrules *)

and freevar =  (* fv *)
    { fv_name : string;        (* "name that " = free that's *)
      fv_this : nontermroot;   (* the primary one *)
      fv_that : nt_or_mv_root; (* the primary one *) 
      fv_homs : homomorphism list;
      fv_loc : loc }
  (* that (if an ntr) must not be an ntr of a subrule *)

and xd_dependencies = (* xddep *)
    { xd_dep_ts : nt_or_mv_root list list;
      xd_dep_graph : (nt_or_mv_root * (nt_or_mv_root list)) list;
      xd_dep_graph_nontran : (nt_or_mv_root * (nt_or_mv_root list)) list }
(*      xd_dep_graph : (ntl_or_mvl_root * (ntl_or_mvl_root list)) list } *)

and embed = (* embed *)
    embedmorphism 

and parsing_annotation = (prodname*parsing_annotation_type*prodname) (* pa *)

and parsing_annotations = (* pas *)
    { pa_data : parsing_annotation list; }

and backend = string

and structure_entry = (* stre *)
  | Struct_md of metavarroot 
  | Struct_rs of nontermroot list
  | Struct_srs of (nontermroot * nontermroot) list
  | Struct_crs of (nontermroot * nontermroot * nontermroot) list
  | Struct_axs of auxfn list
  | Struct_sbs of (string * nontermroot * nt_or_mv_root) list 
  | Struct_fvs of (string * nontermroot * nt_or_mv_root) list
  | Struct_embed of embed  
  | Struct_fun_or_defnclass of fundefnclassname

and structure = (string*structure_entry) list (* str *)

and syntaxdefn = (* xd *)  (* all the nt occurrences are fully resolved *)
    { xd_mds : metavardefn list;   
      xd_rs  : rule list; 
      xd_dep : (backend * xd_dependencies) list; 
      xd_srs : subrule list;           
      xd_srd : subrule_data;
      xd_crs : contextrule list;
      xd_axs : (auxfn * auxfn_type) list;
      xd_sbs : subst list;
      xd_fvs : freevar list;
      xd_embed_preamble : embed list;
      xd_embed : embed list;
      xd_isa_imports : string list;
      xd_pas : parsing_annotations }

and defnclassname = string  (* dcn *)
and defnname = string  (* dn *)
and defnrulename = string  (* drn *)

and defnclass =  (* dc *)
    { dc_name : defnclassname; 
         (* name to use for the grammar nontermroot, eg Jtype *)
      dc_homs : homomorphism list;
      dc_language_names : langname list; 
      dc_wrapper : string; (* prefix for individual judgement names       *)
      dc_defns : defn list; (* defns of each judgement *)
(*      dc_defns_dependencies - consistent with the term deps??? *)
                                 (* recursion structure explicit  *)
      dc_loc : loc }

and defn =  (* d *)
    { d_name : defnname;   (* eg Eet - the base for the proof asst reln name*)
      d_form : symterm;  (* eg E |- expr : typexpr *)
      d_wrapper : string;  (* prefix for individual rules, eg Eet_ *)
      d_rules : processed_semiraw_rule list;
      d_homs : homomorphism list;
      d_loc : loc }

and drule =  (* dr *)
    { drule_name : defnrulename;                (* eg Eet_value_name *)
      drule_categories : StringSet.t;
      drule_premises : (string option * symterm) list;
      drule_conclusion : symterm;
      drule_homs : homomorphism list;
      drule_loc : loc }

and processed_semiraw_rule = 
  | PSR_Rule of drule
  | PSR_Defncom of embed_spec

and fundefnclassname = string  (* fdcn *)
and fundefnname = string  (* fdn *)

and fundefnclass =  (* fdc *)
    { fdc_name : fundefnclassname; 
         (* name to use for the grammar nontermroot, eg Jtype *)
(*       fdc_language_names : langname list;  *)
(*       fdc_wrapper : string;  *)
      fdc_homs : homomorphism list;
      fdc_fundefns : fundefn list; (* defns of each judgement *)
(*      dc_defns_dependencies - consistent with the term deps??? *)
                                 (* recursion structure explicit  *)
      fdc_loc : loc }

and fundefn =  (* fd *)
    { fd_name : fundefnname;   (* the base for the proof asst fun name*)
      fd_form : symterm;  (* the syntactic form of the fully applied function *)
      fd_result : nontermroot;  (* the result type written by the user *)
      fd_result_type : nontermroot;  (* the primary nontermroot for that type *)
      fd_pn_wrapper : string;  (* the production name wrapper from the result-type rule *)
      fd_clauses : funclause list;
      fd_homs : homomorphism list;
      fd_loc : loc }

and funclause =  (* fc *)
    { fc_lhs : symterm;
      fc_rhs : symterm;
      fc_loc : loc }

and fun_or_reln_defnclass = (* frdc *)
  | FDC of fundefnclass
  | RDC of defnclass

and relationsdefn = fun_or_reln_defnclass list  (* rd *)
               
and systemdefn =  (* sd *)
    { syntax : syntaxdefn;
      relations : relationsdefn;
      structure : structure;
      sources : string}

(** ************************ *)
(** symbolic term processing *)
(** ************************ *)

(* representation of parsed symbolic terms *)

and mytoken =  (* tok *)
  | Tok_nonterm of loc * nonterm
  | Tok_metavar of loc * metavar
    (*   | Tok_terminal of loc * terminal *)
    (*   | Tok_dots of loc * int  *)
    (*   | Tok_listform of loc * string  *)
    (*   | Tok_otherident of loc * string *)
    (*   | Tok_whitespace of loc * string  (\* internal to varlex only *\) *)

and variable = string  (* var *)

and symterm =  (* st *)
  | St_node of loc * symterm_node_body  
  | St_nonterm of loc * nontermroot * nonterm
  | St_nontermsub of 
      loc * nontermroot (*lower*) * nontermroot (*top*) * nonterm
  | St_uninterpreted of loc * string 
          
and symterm_element =  (* ste *)
  | Ste_st of loc * symterm                                                 
  | Ste_metavar of loc * metavarroot * metavar
  | Ste_var of loc * metavarroot * variable
  | Ste_list of loc * symterm_list_item list     (* eg x1 , .. , xn    *)
(* TODO: could also have something like this ? *)
(*| Ste_listnonterm of loc * listnontermroot * listnonterm    (\* eg x_list or x_t'_list  *\) *)

and symterm_node_body =  (* stnb *)
    { st_rule_ntr_name : nontermroot;   
      st_prod_name : prodname;                          
      st_es : symterm_element list;
      st_loc : loc }
      
and symterm_list_item =  (* stli *)
  | Stli_single of loc * symterm_element list
  | Stli_listform of symterm_list_body

and symterm_list_body (* symterm_list *) =  (* stlb *)
    { stl_bound : bound ; 
      stl_elements : symterm_element list;  (* the repeated stuff *)  
        (* note that in a symterm there may be nested list forms *)
(* stl_indexed_things : nonterm list * metavar list; (\* the varying ones *\)*)
      stl_loc : loc } 



(* in a _concrete_ term:
- symterm is only St_node, not St_nonterm, St_nontermsub, or St_uninterpreted
- symterm_element is only Ste_st, Ste_var, or Ste_list, not Ste_metavar
- symterm_list_item is only Stli_single, not an Stli_listform
*)

(** ************************ *)
(** parsers                  *)
(** ************************ *)


(* We mostly use (char,symterm) parserS. A language produces a collection *)
(* of them, indexed by the nontermroot's naming their rules. *)
(* some of this structure could be hidden in term_parser.ml *)

type ('t,'v) parser = ('t list -> 'v -> unit) -> 't list -> unit

type made_parser = nontermroot -> bool -> string -> symterm list

exception My_parse_error of string


(** ************************ *)
(** auxiliary types of sets  *)
(** ************************ *)


module NtrSet = Set.Make(struct type t = nontermroot let compare = Pervasives.compare end);;
let ntrlistunion : NtrSet.t list -> NtrSet.t 
    = fun ntrss -> List.fold_left (fun ntrs ntrs' -> NtrSet.union ntrs ntrs') NtrSet.empty ntrss 
let ntrsetoflist : nontermroot list -> NtrSet.t 
    = fun ntrs -> List.fold_left (fun ntrs' ntr -> NtrSet.add ntr ntrs') NtrSet.empty ntrs

module NtrPairSet = Set.Make(struct type t = nontermroot*nontermroot let compare = Pervasives.compare end);;
let ntrpairlistunion : NtrPairSet.t list -> NtrPairSet.t 
    = fun ntrpairss -> List.fold_left (fun ntrpairs ntrpairs' -> NtrPairSet.union ntrpairs ntrpairs') NtrPairSet.empty ntrpairss 
let ntrpairsetoflist : (nontermroot*nontermroot) list -> NtrPairSet.t 
    = fun ntrpairs -> List.fold_left (fun ntrpairs' ntrpair -> NtrPairSet.add ntrpair ntrpairs') NtrPairSet.empty ntrpairs


module NtSet = Set.Make(struct type t = nontermroot * nonterm * prod_env let compare = Pervasives.compare end);;
let ntlistunion : NtSet.t list -> NtSet.t 
    = fun ntss -> List.fold_left (fun nts nts' -> NtSet.union nts nts') NtSet.empty ntss 
let ntsetoflist : (nontermroot * nonterm * prod_env) list -> NtSet.t 
    = fun nts -> List.fold_left (fun nts' nt -> NtSet.add nt nts') NtSet.empty nts 


module NtsubSet = Set.Make(struct type t = nontermroot * nontermroot * nonterm let compare = Pervasives.compare end);;
let ntsublistunion : NtsubSet.t list -> NtsubSet.t 
    = fun ntss -> List.fold_left (fun nts nts' -> NtsubSet.union nts nts') NtsubSet.empty ntss 
let ntsubsetoflist
    = fun ntsubs -> List.fold_left (fun ntsubs' ntsub -> NtsubSet.add ntsub ntsubs') NtsubSet.empty ntsubs 

module MvrSet = Set.Make(struct type t = metavarroot  let compare = Pervasives.compare end);;
let mvrlistunion : MvrSet.t list -> MvrSet.t 
    = fun mvrss -> List.fold_left (fun mvrs mvrs' -> MvrSet.union mvrs mvrs') MvrSet.empty mvrss 
let mvrsetoflist : metavarroot  list -> MvrSet.t 
    = fun mvrs -> List.fold_left (fun mvrs' mvr -> MvrSet.add mvr mvrs') MvrSet.empty mvrs 


module MvSet = Set.Make(struct type t =  metavarroot * metavar * prod_env let compare = Pervasives.compare end);;
let mvlistunion : MvSet.t list -> MvSet.t 
    = fun mvss -> List.fold_left (fun mvs mvs' -> MvSet.union mvs mvs') MvSet.empty mvss 
let mvsetoflist : (metavarroot * metavar * prod_env) list -> MvSet.t 
    = fun mvs -> List.fold_left (fun mvs' mv -> MvSet.add mv mvs') MvSet.empty mvs 


module TerminalSet = Set.Make(struct type t = terminal let compare = String.compare end);;
let terminallistunion : TerminalSet.t list -> TerminalSet.t 
    = fun tmss -> List.fold_left (fun tms tms' -> TerminalSet.union tms tms') TerminalSet.empty tmss
let terminalsetoflist : nontermroot list -> TerminalSet.t 
    = fun tms -> List.fold_left (fun tms' tm -> TerminalSet.add tm tms') TerminalSet.empty tms



(** ************************ *)
(** aux type for funcs gen   *)
(** ************************ *)

type footer = 
  | Footer_empty
  | Footer_isa_proj_lemma of string * string * string  
             (* projections, clauses of the lemma, def names *)
  | Footer_proof of string

type int_header = (string * string * string)
type int_func = 
    { r_fun_id : string;
      r_fun_dep : string list;
      r_fun_type : string;  
        (* type over which the function is recursive - used to decide what to collapse *)
      r_fun_header : int_header;
      r_fun_clauses : (string * string * string) list
	(* twelf prefix, lhs, rhs *)
    }
type int_funcs =
    { i_funcs : int_func list;
      i_funcs_proof : string option }

type int_funcs_collapsed = (string * string list * (int_header * string * footer)) list 

(** ************************ *)
(** raw rep of grammars      *)
(** ************************ *)
      
(* as produced by the ocamlyacc parser *)      

type raw_ident_desc = string  
and raw_ident = loc * raw_ident_desc

and raw_metavardefn = 
    { raw_mvd_name : string;
      raw_mvd_names : (string * raw_homomorphism list) list;
      raw_mvd_rep : raw_metavarrep;
      raw_mvd_indexvar : bool;        
      raw_mvd_loc : loc }
and raw_metavarrep = raw_homomorphism list

and raw_homomorphism = hom_name * raw_hom_spec * loc
and raw_hom_spec = raw_hom_spec_el list
and raw_hom_spec_el = 
  | Raw_hom_string of string
  | Raw_hom_blanks of string
(*   | Raw_hom_symterm of raw_element list  (* FZ or string ??? *) *)
  | Raw_hom_ident of raw_ident list
  | Raw_hom_ident_dots of loc * raw_ident list * int * raw_ident list
  | Raw_hom_ident_comp of loc * raw_ident list * raw_comp_bound


and raw_bindspec = 
  | Raw_Bind of loc * raw_mse * raw_ident
  | Raw_AuxFnDef of loc * raw_ident * raw_mse
  | Raw_NamesEqual of loc * raw_mse * raw_mse   (* not currently implemented *)
  | Raw_NamesDistinct of loc * raw_mse * raw_mse(* not currently implemented *)
  | Raw_AllNamesDistinct of loc * raw_mse       (* not currently implemented *)
and raw_mse = 
  | Raw_MVorNTExp of loc * raw_ident 
  | Raw_MVorNTListExp_dotform of loc * raw_ident * int * raw_ident
  | Raw_MVorNTListExp_comp of loc * raw_ident * raw_comp_bound
  | Raw_Aux of loc * raw_ident * raw_ident 
  | Raw_AuxList_dotform of loc * raw_ident * raw_ident * int * raw_ident 
  | Raw_AuxList_comp of loc * raw_ident * raw_ident * raw_comp_bound
  | Raw_Union of loc * raw_mse * raw_mse
  | Raw_Empty of loc

and raw_element = 
  | Raw_ident of loc * raw_ident
  | Raw_option of loc * raw_element list
  | Raw_list of loc * raw_element list   (* not currently implemented *)
  | Raw_nelist of loc * raw_element list (* not currently implemented *)
  | Raw_sugaroption of loc * raw_element (* not currently implemented *)
  | Raw_dots of loc * int   (* the int is the number of dots - 2 *)
  | Raw_comp of loc * raw_element list * raw_comp_bound * raw_ident option
(*   | Raw_comp of loc * raw_element list * raw_ident * raw_ident option *)
(*   | Raw_comp_u of loc * raw_element list * raw_ident * raw_ident * raw_ident option *)
(*   | Raw_comp_lu of loc * raw_element list * raw_ident * raw_ident * int * raw_ident * raw_ident option *)
  (* Raw_list and Raw_nelist are for EBNF lists, not dot forms *)

and raw_comp_bound = (* rcb *)
  | Raw_bound_comp of loc * raw_ident
  | Raw_bound_comp_u of loc * raw_ident * raw_ident
  | Raw_bound_comp_lu of loc * raw_ident * raw_ident * int * raw_ident

and semiraw_element =
  | Sr_el of element
  | Sr_dots of int (* the int is the number of dots - 2 *)

and raw_prod = 
    { raw_prod_name : string;  
      raw_prod_flavour : prod_flavour;
      raw_prod_categories : raw_ident list;
      raw_prod_es : raw_element list;
      raw_prod_homs : raw_homomorphism list;
      raw_prod_bs : raw_bindspec list;
      raw_prod_loc : loc }

and raw_rule = 
    { raw_rule_ntr_name : string; 
      raw_rule_ntr_names : (string * raw_homomorphism list) list; 
      raw_rule_pn_wrapper : string;
      raw_rule_ps : raw_prod list;
      raw_rule_homs : raw_homomorphism list;
      raw_rule_categories : string list;
      raw_rule_loc : loc }

and raw_subrule = 
    { raw_sr_lower : string;
      raw_sr_upper : string;
      raw_sr_homs : raw_homomorphism list;
      raw_sr_loc : loc }

and raw_contextrule =
    { raw_cr_ntr : nontermroot; (* the primary one *)
      raw_cr_target : nontermroot; (* the primary one *)
      raw_cr_hole : nontermroot;  (* the primary one *)
      raw_cr_homs : raw_homomorphism list;
      raw_cr_loc : loc }
      
and raw_subst = 
    { raw_sb_name : string;
      raw_sb_this : string;
      raw_sb_that : string;
      raw_sb_multiple : bool;
      raw_sb_homs : raw_homomorphism list;
      raw_sb_loc : loc }

and raw_freevar = 
    { raw_fv_name : string;
      raw_fv_this : string;
      raw_fv_that : string;
      raw_fv_homs : raw_homomorphism list;
      raw_fv_loc : loc }

and raw_embed = embedmorphism

and raw_hom_section_item = (* rhsi *)
    { raw_hsi_name : string;
      raw_hsi_bs : raw_bindspec list;
      raw_hsi_homs : raw_homomorphism list;
      raw_hsi_loc : loc}

and raw_hom_section = (* rhs *)
    { raw_hs_wrapper : string;
      raw_hs_hsis : raw_hom_section_item list;
      raw_hs_loc : loc }

and raw_parsing_annotations = (* pa *)
    { raw_pa_data : (string*parsing_annotation_type*string) list;
      raw_pa_loc : loc}

and raw_coq_section = (* rqs *)
    { raw_rqs_name : string;
      raw_rqs_begin : bool;  (* true for begin, false for end *)
      raw_rqs_loc : loc }

and raw_coq_variable = (* rqv *)
    { raw_rqv_name : string;
      raw_rqv_loc : loc }

and raw_item = (* ri *)
  | Raw_item_md of raw_metavardefn
  | Raw_item_rs of raw_rule list
  | Raw_item_dcs of raw_fun_or_reln_defnclass
  | Raw_item_srs of raw_subrule list
  | Raw_item_crs of raw_contextrule list
  | Raw_item_sbs of raw_subst list
  | Raw_item_fvs of raw_freevar list
  | Raw_item_embed of raw_embed list
  | Raw_item_pas of raw_parsing_annotations list
  | Raw_item_hs of raw_hom_section 
  | Raw_item_coq_section of raw_coq_section
  | Raw_item_coq_variable of raw_coq_variable
   
and raw_syntaxdefn = 
    { raw_sd_mds : raw_metavardefn list; 
      raw_sd_rs : raw_rule list;
      raw_sd_dcs : raw_fun_or_reln_defnclass list;
      raw_sd_srs : raw_subrule list;
      raw_sd_crs : raw_contextrule list;
      raw_sd_sbs : raw_subst list;
      raw_sd_fvs : raw_freevar list;
      raw_sd_embed : raw_embed list;
      raw_sd_pas : raw_parsing_annotations list;
      raw_sd_hss : raw_hom_section list;
      raw_sd_loc : loc }         (* FZ shall we keep loc here? *)
      
and raw_line = 
  | Raw_line of loc * string
  | Raw_lineline of loc * string * string
  | Raw_blankline of loc * string
  | Raw_commentline of loc * string

and semiraw_rule = 
    Lineless_rule of loc * (loc*string) list
  | Lined_rule of loc * (loc*string) list * (loc*string) * (loc*string) list
  | Defncom of loc * embed_spec

and raw_fun_or_reln_defnclass = (* rfrdc *)
  | Raw_FDC of raw_fundefnclass
  | Raw_RDC of raw_defnclass

and raw_defnclass = (* rdc *)
    { raw_dc_name : string;
(*      raw_dc_language_names : langname list; FZ unclear *)
      raw_dc_homs : raw_homomorphism list;
      raw_dc_wrapper : string;
      raw_dc_defns : raw_defn list;
      raw_dc_loc : loc }

and raw_defn = (* rd *)
    { raw_d_name : string;
      raw_d_es : raw_element list;
      raw_d_categories : raw_ident list;
      raw_d_wrapper : string;
      raw_d_body : (* raw_line list*) semiraw_rule list;
      raw_d_homs : raw_homomorphism list;
      raw_d_loc : loc }

and raw_fundefnclass =  (* rfdc *)
    { raw_fdc_name : string;
(*       fdc_language_names : langname list;  *)
(*       raw_fdc_wrapper : string;  *)
      raw_fdc_homs : raw_homomorphism list;
      raw_fdc_fundefns : raw_fundefn list; 
      raw_fdc_loc : loc }

and raw_fundefn =  (* rfd *)
    { raw_fd_name : string;
      raw_fd_es : raw_element list;
      raw_fd_result : raw_ident; 
      raw_fd_result_type : nontermroot;
      raw_fd_pn_wrapper : string;   
      raw_fd_clauses : raw_funclause list;
      raw_fd_homs : raw_homomorphism list;
      raw_fd_loc : loc }

and raw_funclause = loc * string

type raw_extra_homs = (string * (raw_bindspec list * raw_homomorphism list))
      
type raw_drule_line_annot = 
    { dla_name : string;
      dla_categories : raw_ident list;
      dla_homs : raw_homomorphism list}

let empty_raw_sd = 
  { raw_sd_mds = []; raw_sd_rs = []; raw_sd_dcs = []; 
    raw_sd_srs = []; raw_sd_crs = []; raw_sd_sbs = []; raw_sd_fvs = [];
    raw_sd_embed = []; raw_sd_hss = [];
    raw_sd_pas = [];
    raw_sd_loc = dummy_loc } 



        
   
(* raw representation of tex input files *)

type raw_unfiltered =
    Raw_uf_string of string
  | Raw_uf_embedded of Lexing.position * string list 


(** ************************ *)
(** pp modes and options     *)
(** ************************ *)

type coq_aux_defns = 
    { defined : string list ref; 
      newly_defined : string list ref }
and pp_coq_opts = 
    { coq_expand_lists : bool;
      coq_quantified_vars_from_de : string list ref;
      coq_non_local_hyp_defn : string ref;
      coq_non_local_hyp_defn_vars : (string*(string option)) list ref;
      coq_list_types : string list ref;        (* FZ add more structure? *)
      coq_list_aux_funcs : string ref option;
      coq_list_aux_defns : coq_aux_defns;
      coq_library : (string * string list) ref;
      coq_locally_nameless : bool ref;
      coq_lngen : bool;
      coq_use_filter_fn : bool;
      coq_names_in_rules : bool } (* co *)
and pp_isa_opts = 
    { ppi_isa_primrec : bool;
      ppi_isa_inductive : bool;
      ppi_fancy_syntax : bool; 
      ppi_generate_lemmas : bool;
      isa_library : (string * string list) ref } (* io *)
and pp_hol_opts = 
    { hol_library : (string * string list) ref } (* io *)
and pp_lem_opts = 
    { lem_library : (string * string list) ref } (* lo *)
and pp_twf_opts = 
    { twf_current_defn : string ref;
      twf_library : (string * string list) ref } (* wo *)
and pp_ascii_opts = 
    { ppa_colour : bool; 
      ppa_ugly : bool; 
      ppa_lift_cons_prefixes : bool; 
      ppa_show_deps : bool; 
      ppa_show_defns : bool } (* ao *)
and pp_tex_opts = 
    { ppt_colour : bool;
      ppt_show_meta : bool;
      ppt_show_categories : bool;
      ppt_wrap : bool;
      ppt_name_prefix : string }  (* xo *)
and pp_caml_opts = 
    { ppo_include_terminals : bool;
      caml_library : (string * string list) ref } (* oo *) 
type pp_lex_opts = unit (* lo *)
type pp_yacc_opts = unit (* yo *)

type pp_mode =  (* m *)
  | Coq of pp_coq_opts
  | Isa of pp_isa_opts
  | Hol of pp_hol_opts
  | Lem of pp_lem_opts
  | Twf of pp_twf_opts
  | Ascii of pp_ascii_opts
  | Tex of pp_tex_opts
  | Caml of pp_caml_opts
  | Lex  of pp_lex_opts
  | Yacc of pp_yacc_opts

let pp_ascii_opts_default =
  Ascii { ppa_colour = true;
	  ppa_ugly = false;
	  ppa_lift_cons_prefixes = false;
	  ppa_show_deps = false;
	  ppa_show_defns = true }

let ao_default =
  { ppa_colour = true;
    ppa_ugly = false;
    ppa_lift_cons_prefixes = false;
    ppa_show_deps = false;
    ppa_show_defns = true }
    
let error_opts =
  Ascii { ppa_colour = false;
	  ppa_lift_cons_prefixes = true;
	  ppa_ugly = false;
	  ppa_show_deps = false;
	  ppa_show_defns = true }


(** ************************ *)
(** miscellaneous stuff      *)
(** ************************ *)


let root_of (x,y) = x

let de_empty = [],[]

type 'a optionprime = 
  | OP_None
  | OP_Some of 'a
  | OP_Many of 'a list


type cd_env =  (* c *)
    { ident_lexer : string -> Lexing.position -> mytoken optionprime ;
      primary_mvr_of_mvr : metavarroot -> metavarroot ;
      primary_ntr_of_ntr : nontermroot -> nontermroot ;
      all_indexvar_synonyms : metavarroot list;
    }

type hom_usage = (* hu *)
  | Hu_root
  | Hu_metavar
  | Hu_rule
  | Hu_rule_meta
  | Hu_prod
  | Hu_prod_tm
  | Hu_drule
  | Hu_defn
  | Hu_defnclass
  | Hu_fundefn
  | Hu_fundefnclass
  | Hu_embed
  | Hu_deadcode
  | Hu_subrule
  | Hu_subst
  | Hu_freevar

type tex_token_category =
  | TTC_terminal_alpha
  | TTC_terminal_symb
  | TTC_nonterm_or_metavar
  | TTC_space
  | TTC_dots
  | TTC_comp
  | TTC_dummy

(* dummy types *)

let empty_dependencies = 
    { xd_dep_ts = [];
      xd_dep_graph = [];
      xd_dep_graph_nontran = [] ; }

type file_argument =
  | In 
  | Out 



(** ************************ *)
(** lem debug    *)
(** ************************ *)

let lem_debug = ref false
let lemTODO s1 s2 = if !lem_debug then "(* lemTODO "^s1^"*) "^s2 else s2
let lemTODOm m s1 s2 = match m with Lem _ -> lemTODO s1 s2 | _ -> s2
let lemTODOmo m s1 s2o = match s2o with None -> None | Some s2 -> Some (lemTODOm m s1 s2) 

