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
exception RepeatedBinder of string

(* MOVE TO AUXL *)

let find_split s (l:rule list) = 
  let rec find_split_int l r =
    match l with
    | [] -> failwith ("internal: find-split not found: "^s)
    | h::t -> 
	if ((String.compare s h.rule_ntr_name) = 0)
	then ((List.rev r),h, t)
	else find_split_int t (h::r)
  in find_split_int l []

let ntmvrlist_to_ntrlist ntmvrl = 
  Auxl.option_map 
    (fun ntmvr -> match ntmvr with | Ntr ntr -> Some ntr | _ -> None) 
    ntmvrl 

(* check that this has not already been implemented *)
let rec collect_mv_in_mse mse =
  match mse with
  | MetaVarExp mv -> [mv]
  | Union (mse1,mse2) -> (collect_mv_in_mse mse1) @ (collect_mv_in_mse mse2) 
  | _ -> Auxl.warning "internal: collect ln bindspec not implemented\n"; [] 

(* LIBRARY *)

let ln_debug s = if false then print_endline s

let ln_update_dependencies xd m =
  let ln_transformed_deps = Dependency.compute_dependencies xd m in
  { xd with
    xd_dep = [ (m, ln_transformed_deps); ("ascii", ln_transformed_deps) ] }   (* FZ for ascii should not we compute the deps wrt Ascii? *)

(* true if the rule definition defines a type in the theorem prouver p output *)
let defined_rule m r =
  (not (r.rule_meta)) && (Auxl.hom_spec_for_pp_mode m r.rule_homs = None)

(* names of generated functions *)
let open_name xd (b:bool) (ntr:nontermroot) (wrt_ntr:nontermroot) = 
  let pntr = Auxl.promote_ntr xd ntr in
  let pwrt_ntr = Auxl.promote_ntr xd wrt_ntr in
  "open_"^pntr^"_wrt_"^pwrt_ntr^(if b then "_rec" else "")

let arity_name f ntr = 
  "arity_"^f^"_"^ntr

(* collect the mvr that require a ln representation *)
let ln_mvrs (xd:syntaxdefn) : metavarroot list =
  List.map 
    (fun mvd -> mvd.mvd_name)
    (List.filter (fun mvd -> mvd.mvd_locally_nameless) xd.xd_mds)

(* collect the binders of a production *)
let binders p = 
  List.concat 
    (Auxl.option_map
       ( fun bs -> 
	 (* print_endline (Grammar_pp.pp_plain_bindspec bs); *)
	 match bs with
	 | Bind (MetaVarExp mv,_) -> Some [mv]
	 | AuxFnDef (_,mse) -> Some (collect_mv_in_mse mse)
	 | Bind _ -> Auxl.warning "internal: binders not implemented - 1\n"; None
	 | _ -> None )
       p.prod_bs)

let binders_for_nt p nt = 
  List.concat 
    (Auxl.option_map
       ( fun bs -> 
	 (* print_endline (Grammar_pp.pp_plain_bindspec bs); *)
	 match bs with
	 | Bind (MetaVarExp mv,nt1) when compare nt nt1 = 0 -> Some [mv]
	 | Bind (MetaVarExp mv,nt1) when not (compare nt nt1 = 0) -> None
	 | Bind _ -> Auxl.warning "internal: binders not implemented - 2\n"; None
	 | _ -> None )
       p.prod_bs)

(* a mv is bindable if it is alone on a production, requires a ln representation, and is not used in an auxfn *)
let is_bindable xd mv p = 
  (* when this function is invoked, we already know that mv is in a singleton production *)
  (* so check that: *)
  (* - mv has a locally nameless representation *)
  (* - mv is not mentioned in an auxfn *)
  let bndrs = binders p in
  let mvd = Auxl.mvd_of_mvr xd (Auxl.primary_mvr_of_mvr xd (fst mv)) in
  mvd.mvd_locally_nameless && not(List.mem mv bndrs)

(* for a ln mvr, record the rules where it has been splitted *)
let rules_with_bindable_mvr (xd:syntaxdefn) (mvr:metavarroot) : rule list =
  if not((Auxl.mvd_of_mvr xd mvr).mvd_locally_nameless) then Auxl.error ("internal: rules_with_bindable_mvr: "^mvr^" does not have a ln repr.\n");
  List.filter
    (fun r -> 
      (not r.rule_meta) && 
      List.exists (fun p -> 
	match p.prod_es with 
	| [Lang_metavar (mvr1,mv1)] when is_bindable xd mv1 p -> if String.compare mvr mvr1 = 0 then true else false
	| _ -> false) r.rule_ps)
    xd.xd_rs

let all_rules_with_bindable_mvr (xd:syntaxdefn) : (metavarroot * nontermroot) list =
  List.concat 
    (Auxl.option_map
       (fun mvr ->
	 match (rules_with_bindable_mvr xd mvr) with
	 | [] -> None
	 | _::_ as rs -> Some (List.map (fun r -> (mvr,r.rule_ntr_name)) rs))
       (ln_mvrs xd))

(* given an ntr, does it depend on a rule where mvr was splitted? *)
let depend_on_splitted (m:pp_mode) (xd:syntaxdefn) (ntr:nontermroot) (mvr:metavarroot) =
  List.exists
    (fun ntr ->
      let r = Auxl.rule_of_ntr xd ntr in
      List.exists 	
	(fun p -> 
	  match p.prod_es with 
	  | [Lang_metavar (mvr1,mv1)] when is_bindable xd mv1 p -> if String.compare mvr mvr1 = 0 then true else false 
	  | _ -> false) 
	r.rule_ps)
    (ntmvrlist_to_ntrlist (List.assoc (Ntr ntr) (Auxl.select_dep_graph m xd.xd_dep)))

(* true if the terms defined by ntr are always locally closed *)
let always_locally_closed m xd ntr =
  let mvs = ln_mvrs xd in
  not (List.exists (fun mvr -> depend_on_splitted m xd ntr mvr) mvs)

(* true if mvr might be bound by an aufn *)
let bound_by_auxfn xd mvr =
  List.exists
    (fun (_,(_,ntmvr)) -> match ntmvr with | Mvr mvr1 -> String.compare mvr mvr1 = 0 | _ -> false )
    xd.xd_axs

  
  
(* for each ln mvr, record all the rules that have a dependency on a rule where the mvr was splitted *)
(* let bindable_dependency_mvr (m:pp_mode) (xd:syntaxdefn) (mvr:metavarroot) : rule list = *)
(*   let rs = List.map (fun r -> r.rule_ntr_name) (rules_with_bindable_mvr xd mvr) in  *)
(*   List.filter  *)
(*     (fun r ->  *)
(*       defined_rule m r *)
(* 	&& List.exists (fun rname -> (List.mem (Ntr rname) (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep)))) rs) *)
(*     xd.xd_rs *)

(* let bindable_dependency_rule (m:pp_mode) (xd:syntaxdefn) (ntr:nontermroot) : rule list = *)
(*   List.filter *)
(*     (fun r ->  *)
(*       defined_rule m r *)
(* 	&& List.mem (Ntr ntr) (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep))) *)
(*     xd.xd_rs *)

(* for each rule, return all the rules that depend on it *)
(* let all_bindable_dependency (m:pp_mode) (xd:syntaxdefn) : (nontermroot * nontermroot list) list = *)
(*   List.map  *)
(*     (fun ntr -> (ntr, List.map (fun r -> r.rule_ntr_name) (bindable_dependency_rule m xd ntr))) *)
(*     (List.map snd (all_rules_with_bindable_mvr xd)) *)

(* SINGLE-BINDER CHECK *)
let check_single_binder xd =
  (* -for each production, verify that there are no auxfns defined and at most one bind annotation *)
  let check_production p = 
    let one_bind = ref false in
    List.iter (fun bs ->
      match bs with
      | AuxFnDef _ -> 
	  Auxl.warning "locally-nameless: auxfns are not supported by the locally-nameless backend\n"
      | Bind (NonTermExp _,_) -> 
	  Auxl.warning "locally-nameless: bindspec binding a nonterminal are not supported by the locally-nameless backend\n"
      | Bind (MetaVarListExp _,_) ->
	  Auxl.warning "locally-nameless: bindspec binding a list of metavars are not supported by the locally-nameless backend\n"
      | Bind (NonTermListExp _,_) ->
	  Auxl.warning "locally-nameless: bindspec binding a list of nonterminals are not supported by the locally-nameless backend\n"
      | Bind (MetaVarExp mv,_) ->
          (* check if mv has a locally nameless representation *)
          let mvd = Auxl.mvd_of_mvr xd (Auxl.primary_mvr_of_mvr xd (fst mv)) in
          if mvd.mvd_locally_nameless then
	    if !one_bind
	    then 
	      Auxl.warning "locally-nameless: multiple bind declaration on the same production are not supported by the locally-nameless backend\n"
	    else one_bind := true
          else ()
      | _ -> ())
      p.prod_bs
  in
  List.iter (fun r -> List.iter (fun p -> check_production p) r.rule_ps) xd.xd_rs

(* SYNTAXDEFN TRANSFORMATION *) 

(* A metavar element mv of a production of a rule for ntr is _bindable_ if *)
(* (a) it is a singleton production, and *)
(* (b) there are some ntr' and ntr'' such that ntr' depends on ntr and *)
(*      the ntr'' rule contains a production with a (+ bind mv' in nt' +) *)
(*      where mv' and mv have the same root and nt' has root ntr'. *)

(* A metavar element mv of a production is a _binder_ if the production *)
(*  has a (+ bind mv in nt +). *)

(* To generate penn locally nameless (PLN) types we can do a syntaxdefn *)
(* translation and then generate the current fully concrete (FC) *)
(* representation.  The translation: *)

(* - fixes a proof assistant type of index *)
(* - splits all productions pn that consist of a bindable mv, into a *)
(*    "bound_"^pn carrying an index and a "free_"^pn carrying the *)
(*    metavar type the user specified *)
(* - erases all binder elements if these require a locally-nameless representation *)

(* given a production, a binder is:  *)
(* - a mv for which there is a bind mv in nt bindspec in the current production *)
(* - a mv collected by a auxfn defined for the prod *)
(* let is_binder xd (p:prod) (e:element) = *)
(*   match e with *)
(*   | Lang_metavar (_,mv) -> List.mem mv (binders p) *)
(*   | _ -> false *)

let is_ln_binder xd (p:prod) (e:element) =
  match e with
  | Lang_metavar (mvr,mv) -> 
      let is_ln = 
        try (* hack, as here xd is not entirely consistent, e.g. nat *)
          let mvd = Auxl.mvd_of_mvr xd mvr in
          mvd.mvd_locally_nameless 
        with Not_found -> false in
      is_ln && List.mem mv (binders p) 
  | _ -> false

let ln_transform_rule (m:pp_mode) (xd:syntaxdefn) (r:rule) : rule =
  (* 1: split productions defining bindable metavars *)
  let splitted_bindable_prods =
    List.flatten
      ( List.map
	  ( fun p -> 
	    match p.prod_es with
	    | [Lang_metavar (mvr,mv)] when is_bindable xd mv p -> 
                (* TODO: fix homs and bs *)
		[ { prod_name = p.prod_name^"_b";  
		    prod_flavour = p.prod_flavour;
		    prod_meta = p.prod_meta;
		    prod_sugar = p.prod_sugar;
		    prod_categories = p.prod_categories;
		    prod_es = 
		      if bound_by_auxfn xd mvr
		      then [ Lang_metavar ("nat",("nat",[Si_num "1"])); Lang_metavar ("nat",("nat",[Si_num "2"])) ]
		      else [ Lang_metavar ("nat",("nat",[])) ];
		    prod_homs = ("coq-ln_splitted",[Hom_string mvr])::p.prod_homs;  
                    prod_disambiguate = None;
		    prod_bs = [];                                                   
		    prod_loc = p.prod_loc };
		  { prod_name = p.prod_name^"_f";  
		    prod_flavour = p.prod_flavour;
		    prod_meta = p.prod_meta;
		    prod_sugar = p.prod_sugar;
		    prod_categories = p.prod_categories;
		    prod_es = p.prod_es;
		    prod_homs = p.prod_homs;                           
                    prod_disambiguate = None;
		    prod_bs = [];                                      
		    prod_loc = p.prod_loc } ] 
	    | _ -> [p] )
	  r.rule_ps ) in
  (* 2: erase all binder elements *)
  let erased_binder_prods =
    List.map 
      ( fun p ->
	{ p with prod_es = List.filter (fun es -> not(is_ln_binder xd p es)) p.prod_es } )
      splitted_bindable_prods in 
  (* 3: add the open metaproductions *)

  let open_prods =
    let make_prod_open r wrt =
      { prod_name = r.rule_pn_wrapper^"open_wrt_"^wrt;  
	prod_flavour = Bar;
	prod_meta = true;
	prod_sugar = false;
	prod_categories = StringSet.empty;
	prod_es = [ Lang_terminal (open_name xd false r.rule_ntr_name wrt);
		    Lang_nonterm (wrt,(wrt,[]));
		    Lang_nonterm (r.rule_ntr_name,(r.rule_ntr_name,[])) ];
	prod_homs = [ ( "coq",
			[ Hom_string "(";
			  Hom_string (open_name xd false r.rule_ntr_name wrt); 
			  Hom_index 0;
			  Hom_index 1;
			  Hom_string ")" ] ) ];
	prod_disambiguate = None;
        prod_bs = [];
	prod_loc = dummy_loc } in

    (* open r wrt all reachable r' that have a ln spliited mvr *)
    if defined_rule m r then
      let accessible_rules = ntmvrlist_to_ntrlist (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep)) in
      let all_bindable_rules = List.map snd (all_rules_with_bindable_mvr xd) in
      let rule_wrt_to_open = List.filter (fun r -> List.mem r all_bindable_rules) accessible_rules in
      ln_debug ("rule = "^r.rule_ntr_name^"; is meta = "^(string_of_bool r.rule_meta) ^"; bind_dep = "^(String.concat " , " rule_wrt_to_open));
      List.map (fun rd -> make_prod_open r rd) rule_wrt_to_open 
    else [] in
      
  let final_prods = erased_binder_prods@open_prods in

  (* 5: build the ln_transformed rule *)
  { r with
    rule_ps = final_prods }
  
(* add all lc_* productions. *)
(* TODO: respect the convention that mutually recursive productions are defined in the same rule *)

let ln_add_lc_judgment m xd =
  let def_lc_rule ntr =   
    { rule_ntr_name = "def_lc"^"_"^ntr;
      rule_ntr_names = [ ("def_lc"^"_"^ntr,[]) ];
      rule_pn_wrapper = "lc_";
      rule_ps = [
      { prod_name = "lc_"^ntr; (* 1 *)
	prod_flavour = Bar;
	prod_meta = false;
	prod_sugar = false;
	prod_categories = StringSet.empty;
	prod_es = [Lang_terminal ("lc_"^ntr); Lang_nonterm (ntr, (ntr,[])) ];
	prod_homs = [];
	prod_disambiguate = None;
        prod_bs = [];
	prod_loc = dummy_loc } ];
      rule_homs = [];
      rule_meta = true;    
      rule_semi_meta = false;
      rule_phantom = false;
      rule_judgement = false;  (* FZ what is this for? *)
      rule_loc = dummy_loc } in
  let lcs_prod_judgement_rule ntr = 
    { prod_name = "judgement_def_lc_"^ntr;
      prod_flavour = Bar;
      prod_meta = false;
      prod_sugar = false;
      prod_categories = StringSet.empty;
      prod_es = [Lang_nonterm ("def_lc_"^ntr, ("def_lc_"^ntr,[])) ];
      prod_homs = [];
      prod_disambiguate = None;
      prod_bs = [];
      prod_loc = dummy_loc } in
  let rs = List.filter (defined_rule m) xd.xd_rs  in 
  let (r1,j,r2) = find_split "judgement" xd.xd_rs in 
  let def_lc_rules = List.map def_lc_rule (List.map (fun r -> r.rule_ntr_name) rs) in
  let lcs_prod_judgement_rules = 
    List.map lcs_prod_judgement_rule (List.map (fun r -> r.rule_ntr_name) rs) in
(*  ln_update_dependencies *)
    { xd with
      xd_rs = r1 
              @ [ {j with rule_ps = lcs_prod_judgement_rules @ (j.rule_ps)}] 
              @ def_lc_rules  @ r2;
	xd_dep = [] } 
(*    (Auxl.hom_name_for_pp_mode m)  *)

(* some useful symterms about var sets *)
let st_var_set_vars : symterm_element = Ste_st (dummy_loc, St_node 
    (dummy_loc, 
     {st_rule_ntr_name = "var_sets";
      st_prod_name = "var_sets_vars";
      st_es = [Ste_metavar (dummy_loc, "vars", ("L",[]))];
      st_loc = dummy_loc;
    }))

let rec st_var_set_union mvrs : symterm_element = 
  match mvrs with
  | [] -> st_var_set_vars
  | mvr::mvrs ->
      let st_mvrs = st_var_set_union mvrs in
      Ste_st (dummy_loc, St_node 
		(dummy_loc, 
		 {st_rule_ntr_name = "var_sets";
		  st_prod_name = "var_sets_union";
		  st_es = [st_mvrs; mvr];
		  st_loc = dummy_loc;
		}))

(* extend the formula rule with productions for confinite quantification *)
let ln_add_cofinite_formula m xd mvrs =
  let cofinite_prod mvr =
    { prod_name = "formula_cofinite_formula_"^mvr;
      prod_flavour = Bar;
      prod_meta = false;
      prod_sugar = false;
      prod_categories = StringSet.empty;
      prod_es = [ Lang_terminal "cofin";
(*		  Lang_metavar ("vars", ("L",[]));      *)
		  Lang_nonterm ("var_sets",("var_sets",[]));
		  Lang_metavar (mvr, (mvr,[]));        
		  Lang_nonterm ("formula",("formula",[])) ];
      prod_homs = [ ("coq", [ Hom_string "(";
			      Hom_string "forall";
			      Hom_index 1;
			      Hom_string ",";
			      Hom_index 1;
			      Hom_string ("\\notin");
			      Hom_index 0;
			      Hom_string ("->");
			      Hom_index 2;
			      Hom_string (")")] ) ];
      prod_disambiguate = None;
      prod_bs = [];
      prod_loc = dummy_loc } in

  let cofinite_prods = List.map cofinite_prod mvrs in
  let (r1,f,r2) = find_split "formula" xd.xd_rs in  
  
  { xd with
    xd_rs = r1 @ [ { f with rule_ps = f.rule_ps @ cofinite_prods } ] @ r2 }

let ln_add_universal_formula m xd mvrs =
  let cofinite_prod mvr =
    { prod_name = "formula_universal_formula_"^mvr;
      prod_flavour = Bar;
      prod_meta = false;
      prod_sugar = false;
      prod_categories = StringSet.empty;
      prod_es = [ Lang_terminal "univ";
		  Lang_metavar (mvr, (mvr,[]));        
		  Lang_nonterm ("formula",("formula",[])) ];
      prod_homs = [ ("coq", [ Hom_string "(";
			      Hom_string "forall";
			      Hom_index 0;
			      Hom_string ",";
			      Hom_index 1;
			      Hom_string (")")] ) ];
      prod_disambiguate = None;
      prod_bs = [];
      prod_loc = dummy_loc } in

  let cofinite_prods = List.map cofinite_prod mvrs in
  let (r1,f,r2) = find_split "formula" xd.xd_rs in  
  
  { xd with
    xd_rs = r1 @ [ { f with rule_ps = f.rule_ps @ cofinite_prods } ] @ r2 }

let ln_transform_syntaxdefn (m:pp_mode) (xd:syntaxdefn) : syntaxdefn =
  (* 0- check that the xd does not hit not-implemented features *)
  check_single_binder xd;
  (* 1- add phantom definitions for nat and vars *)
  let ln_transformed_mvs = 
    ( (* this guarantees that there is always a phantom mvd named "var", 
         used by the phantom production var_sets *)
      if not(List.exists (fun mvd -> String.compare mvd.mvd_name "var" = 0) xd.xd_mds)
      then 
	[ { mvd_name = "var"; 
	    mvd_names = [ ("var",[]) ];
	    mvd_rep = [("coq",[Hom_string "var"]) ];
	    mvd_indexvar = false;
	    mvd_locally_nameless = false;
	    mvd_phantom = true;
	    mvd_loc = dummy_loc } ]
      else [] ) 
    @
    ( { mvd_name = "nat"; 
	mvd_names = [ ("nat",[]) ];
	mvd_rep = [("coq",[Hom_string "nat"]) ];
	mvd_indexvar = false;
	mvd_locally_nameless = false;
	mvd_phantom = true;
	mvd_loc = dummy_loc }
      :: 
	{ mvd_name = "vars"; 
	  mvd_names = [ ("vars",[]); ("L",[]) ];
	  mvd_rep = [("coq",[Hom_string "vars"]) ];
	  mvd_indexvar = false;
	  mvd_locally_nameless = false;
	  mvd_phantom = true;
	  mvd_loc = dummy_loc }
      :: xd.xd_mds ) in
  let ln_var_sets = 
    { rule_ntr_name = "var_sets"; 
      rule_ntr_names = ["var_sets",[]];
      rule_pn_wrapper = "var_sets_";
      rule_ps = 
      [ { prod_name = "var_sets_vars";
	  prod_flavour = Bar;
	  prod_meta = false;
	  prod_sugar = false;
	  prod_categories = StringSet.empty;
	  prod_es = [ Lang_metavar ("vars",("vars",[])) ];
	  prod_homs = [ ("coq", [ Hom_index 0 ]) ];
          prod_disambiguate = None;
	  prod_bs = [];
	  prod_loc = dummy_loc };
	{ prod_name = "var_sets_union";
	  prod_flavour = Bar;
	  prod_meta = false;
	  prod_sugar = false;
	  prod_categories = StringSet.empty;
	  prod_es = [ Lang_nonterm ("var_sets",("var_sets",[])); 
		      Lang_terminal "union"; 
		      Lang_metavar ("var",("var",[])) ];
	  prod_homs = [ ("coq", [ Hom_index 0; Hom_string "\\u {{"; Hom_index 1; Hom_string "}}" ]) ];
          prod_disambiguate = None;
	  prod_bs = [];
	  prod_loc = dummy_loc }
      ];
      rule_homs = [];
      rule_meta = true;
      rule_semi_meta = true;
      rule_phantom = true;
      rule_judgement = false; 
      rule_loc = dummy_loc 

    } in
  (* 2- split productions of bindable elements, add open productions to each rule *)
  let ln_transformed_rules = List.map (ln_transform_rule m xd) xd.xd_rs in
  let xd = 
    { xd with 
      xd_mds = ln_transformed_mvs;
      xd_rs = ln_var_sets::ln_transformed_rules; 
      xd_dep = [] } in
  (* 3- extend the syntax definition *)
  (* 3a- add the "lc" predicate to the judgements *)
  let xd = ln_add_lc_judgment m xd in
  (* 3b- add cofinite quantification to formulas *)
  let ln_mvrs = 
    List.map (fun mvd -> mvd.mvd_name) (List.filter (fun mvd -> mvd.mvd_locally_nameless) xd.xd_mds) in
  let xd = 
    let xd' = ln_add_cofinite_formula m xd ln_mvrs in
    if Auxl.is_lngen m
    then ln_add_universal_formula m xd' ln_mvrs
    else xd' in

  
  (* 4- update the dependencies *)
(*  print_endline (Grammar_pp.pp_syntaxdefn error_opts xd); *)
  let xd = ln_update_dependencies xd (Auxl.hom_name_for_pp_mode m) in

  ln_debug "*****************************";
  ln_debug "*** transformed syntaxdef ***";
  ln_debug "*****************************";
  ln_debug (Grammar_pp.pp_syntaxdefn error_opts xd); 
  xd



(* ******************************************************************** *)
(* open                                                                 *)
(* ******************************************************************** *)

let rec pp_open_symterm_element m xd mvr wrt s unshifted_nonterms ov sie de (ste:symterm_element) = 
  match ste with
  | Ste_st(_,st) -> 
      (pp_open_symterm m xd mvr wrt s unshifted_nonterms ov sie de st)
  | Ste_metavar (l,mvrp,mv) -> 
      let mv_s = Grammar_pp.pp_metavar_with_de_with_sie m xd sie de mv in
      ( mv_s, [] )
  | Ste_var (l,mvrp,var) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
  | Ste_list (l,stlis) -> 
      ( match stlis with 
      | [Stli_listform stlb] -> 
	  pp_open_symterm_list_body 
	    m xd mvr wrt s unshifted_nonterms ov sie de stlb
      | _-> 
	  raise ThisCannotHappen (*never occurs in a canonical symterm_element*) )

and pp_open_symterm m xd mvr wrt s unshifted_nonterms ov sie de (st:symterm) =
  match st with
  | St_node (l,stnb) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)
  | St_nonterm (l,ntrp,nt) ->
      let nt_s = Grammar_pp.pp_nonterm_with_de_with_sie m xd sie de nt in
      if depend_on_splitted m xd ntrp mvr 
      then 
	let id_call = open_name xd true ntrp wrt in
	let sk = 
	  if List.mem nt unshifted_nonterms 
	  then " (S k) "
	  else " k " in 
	( "(" ^  id_call ^ sk ^ ov ^ " " ^ nt_s ^")", [ id_call ] )
      else
	( nt_s, [] )
  | St_nontermsub (l,ntrpl,ntrpt,nt)  -> 
      raise ThisCannotHappen  (* never occurs in a canonical symterm_element *)
  | St_uninterpreted (p,s) -> 
      raise ThisCannotHappen (* never occurs in a canonical symterm_element *)

and pp_open_symterm_list_body m xd mvr wrt s unshifted_nonterms ov sie de stlb =
  let (de1,de2)=de in
  let de1i = Grammar_pp.de1_lookup de1 stlb.stl_bound in

  let pp_body_tmp, list_funcs = 
    List.split
      (List.map 
	 (pp_open_symterm_element m xd mvr wrt s unshifted_nonterms ov ((Si_var ("_",0))::sie) de)
	 stlb.stl_elements) in
  
  let pp_body = 
    let tmp = String.concat "," pp_body_tmp in
    if (List.length stlb.stl_elements) > 1 then "("^tmp^")" else tmp in

  match m with
  | Coq co when not co.coq_expand_lists ->
      let l = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in
      if List.length l = 1 then	
        ( "(map (fun ("^de1i.de1_pattern^":" ^ de1i.de1_coq_type_of_pattern ^ ") => "^pp_body^") "
          ^ de1i.de1_compound_id
          ^ ")", List.concat list_funcs )
      else
        ( "(map (fun (pat_:" ^ de1i.de1_coq_type_of_pattern ^ ") => match pat_ with " (* FZ freshen pat_ *)
	  ^ de1i.de1_pattern^" => " ^pp_body^" end) "  
          ^ de1i.de1_compound_id
          ^ ")", List.concat list_funcs )
  | _ -> ("<<internal: only Coq + native lists supported>>",[])



(* mvr : the mvr with respect to we are opening - is bindable in rule wrt *)
(* ov : variable used to abstract mvr *)
let pp_open_prod m xd mvr wrt (ov:string) (rule_ntr_name:nontermroot) (p:prod) : nontermroot list * (string * string * string) * int_func list =

  let lhs_stnb = Grammar_pp.canonical_symterm_node_body_of_prod rule_ntr_name p in
  let lhs_st = St_node(dummy_loc,lhs_stnb) in
  let sie = [] in
  let ((de1,de2) as de,de3,pptbe) = Bounds.bound_extraction m xd dummy_loc [lhs_st] in
  (* print_endline ("lhs**"^(Grammar_pp.pp_plain_symterm lhs_st)); FZ *)
  let lhs = Grammar_pp.pp_symterm m xd sie de lhs_st in
  
  (* we distinguish the case of the prod that splits mvr *)
  let splits = 
    try 
      match List.assoc "coq-ln_splitted" p.prod_homs with
      | [(Hom_string mvr1)] -> String.compare mvr mvr1 = 0
      | _ -> false 
    with Not_found -> false in

  let (rhs,deps) = 
    if splits
    then (
      (* we distinguish the case auxfns from the simpler one *)
      match lhs_stnb.st_es with
      | [ Ste_metavar (_,mvr,mv) ] ->
	  let s = lhs_stnb.st_prod_name in
	  let mv_s = Grammar_pp.pp_metavar_with_de_with_sie m xd sie de mv in
          if Auxl.is_lngen m then
            ( "\n      match lt_eq_lt_dec " ^ mv_s ^ " k with\n"
              ^ "        | inleft (left _) => " ^ s ^ " " ^ mv_s ^ "\n"
              ^ "        | inleft (right _) => " ^ ov ^ "\n"
              ^ "        | inright _ => " ^ s ^ " (" ^ mv_s ^ " - 1)\n"
              ^ "      end" , [] )
          else
            ( "if (k === "^mv_s^") then "^ov^" else (" ^ s^ " "^mv_s^")" , [] )
      | [ Ste_metavar (_,mvr1,mv1); Ste_metavar (_,mvr2,mv2); ] ->
	  let s = lhs_stnb.st_prod_name in
	  let mv1_s = Grammar_pp.pp_metavar_with_de_with_sie m xd sie de mv1 in
	  let mv2_s = Grammar_pp.pp_metavar_with_de_with_sie m xd sie de mv2 in
	  ( "if (k === "^mv1_s^") then (List.nth "^mv2_s^" "^ov^" "^"("^p.prod_name^" 0 0)"^") else (" ^ s^ " "^mv1_s^" "^mv2_s^")" , [] )
      | _ -> Auxl.error "internal: weird lhs_stnb in pp_open_prod\n" )
      
    else (
      let unshifted_nonterms = 
	Auxl.option_map
	  ( fun bs -> 
	    match bs with 
	    | Bind (MetaVarExp (mvr1,_),nt) -> 
		let mvr1 = Auxl.primary_mvr_of_mvr xd mvr1 in
		if (String.compare mvr mvr1 = 0) then Some nt else None
	    | _ -> None )
	  p.prod_bs in
      let pp_body, deps = 
	(fun (body,deps) -> (String.concat " " body, List.concat deps))
	  (List.split
	     (List.map 
		(pp_open_symterm_element m xd mvr wrt (lhs_stnb.st_prod_name) unshifted_nonterms ov ((Si_var ("_",0))::sie) de) 
		lhs_stnb.st_es)) in
      (lhs_stnb.st_prod_name ^ " " ^ pp_body, deps)) in
    
  (deps,("",lhs,rhs),[])

let pp_open_rule m xd (r:rule) (wrt:nontermroot) (mvr:metavarroot)  : int_func list =
  (* invariant: mvr must be bindable in wrt *)
  ln_debug ("open_rule, rule = "^r.rule_ntr_name^"*** wrt = "^wrt^"*** mvr = "^mvr); 

  let nts_used = Context_pp.nts_used_in_lhss m xd r in
  let rule_var_1 = Auxl.fresh_nt nts_used (Auxl.secondary_ntr xd wrt, []) in 
  let rule_var_2 = Auxl.fresh_nt (rule_var_1::nts_used) (Auxl.secondary_ntr xd r.rule_ntr_name, []) in

  let prods = List.filter (fun p -> not p.prod_meta) r.rule_ps in
  let open_prods = 
    List.map (pp_open_prod m xd mvr wrt (Grammar_pp.pp_nonterm m xd rule_var_1) r.rule_ntr_name) prods in

  let clauses = List.map (fun (_,s,_) -> s) open_prods in
  let funcs = List.flatten (List.map (fun (_,_,f) -> f) open_prods) in
  let dep = List.flatten (List.map (fun (d,_,_) -> d) open_prods) in

  let id_rec = open_name xd true r.rule_ntr_name wrt in
  let id = open_name xd false r.rule_ntr_name wrt in

  let header =
    ( id_rec
      ^ " (k:nat)"         (* FZ freshen k *)
      ^ " (" ^ Grammar_pp.pp_nonterm m xd rule_var_1
      ^ ":" ^ (if bound_by_auxfn xd mvr then "list " else "") ^ Grammar_pp.pp_nontermroot_ty m xd wrt 
      ^ ") (" ^ Grammar_pp.pp_nonterm m xd rule_var_2
      ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name 
      ^ ") "
      ^ (if List.mem id_rec dep then "{struct "^Grammar_pp.pp_nonterm m xd rule_var_2^"}" else "") ,
      "",
      ": " ^ Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name 
      ^ " :=\n  match " ^ Grammar_pp.pp_nonterm m xd rule_var_2 ^ " with\n" ) in
  let added_deps = List.map (fun x -> x.r_fun_id) funcs in

  { r_fun_id = id_rec;
    r_fun_dep = dep @ added_deps;
    r_fun_type = r.rule_ntr_name;
    r_fun_header = header;
    r_fun_clauses = clauses } :: 
  { r_fun_id = id;
    r_fun_dep = [ id_rec ];
    r_fun_type = r.rule_ntr_name;
    r_fun_header = 
      ( id ^" "^ Grammar_pp.pp_nonterm m xd rule_var_1 
         ^" "^ Grammar_pp.pp_nonterm m xd rule_var_2
         ^" := " ^ id_rec ^" 0 "^ Grammar_pp.pp_nonterm m xd rule_var_2
         ^" "^ Grammar_pp.pp_nonterm m xd rule_var_1,
         "", "");
    r_fun_clauses = [] }
  :: funcs

let pp_open m xd : int_funcs_collapsed =
  match m with
  | Coq _ ->
      (* collect all the pairs mvr - rule such that mvr was splitted in rule *)
      let all_bindable_mvr_rule = all_rules_with_bindable_mvr xd in
      (* for each rule r, if r depends on a rule ntr with a splitted mvr, generate open r wrt ntr *)
      let ifuncs =
	List.concat (List.map 
	  (fun r ->
	    if defined_rule m r then 
	      let accessible_rules = ntmvrlist_to_ntrlist (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep)) in
	      List.concat (Auxl.option_map 
		(fun (mvr,ntr) -> 
		  if List.mem ntr accessible_rules
		  then Some (pp_open_rule m xd r ntr mvr)
		  else None)
		all_bindable_mvr_rule)
	    else [])
	  xd.xd_rs) in

      Dependency.collapse m xd 
	{ i_funcs = ifuncs;
	  i_funcs_proof = None }

  | _ -> Auxl.warning "internal: pp_open implemented only for Coq\n"; []

(* ******************************************************************** *)
(* lc (locally closed)                                                  *)
(* ******************************************************************** *)

(* Here xd already knows of the judgments "lc": we build them and pp *)

let required_ntc m xd ntc =
  let required_ntr xd ntr = 
    (* version 0.10.17 did not need this primary/promotion, FZ is suspicious *)
    let ntr = Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd ntr) in
    let splitted_nt xd ntr = 
      let r = Auxl.rule_of_ntr xd ntr in 
      List.exists 
	(fun p -> match p.prod_es with [Lang_metavar (_,mv)] when is_bindable xd mv p -> true | _ -> false) 
	r.rule_ps in
    (splitted_nt xd ntr) (* it contains a splitted mvr *)
  ||                     (* or an nt accessible in the dep graph contains a splitted mvr *)
    (List.exists 
       (splitted_nt xd)
       (ntmvrlist_to_ntrlist
	  (List.assoc (Ntr ntr) (Auxl.select_dep_graph m xd.xd_dep) )))
  in
  List.exists 
    (required_ntr xd)
    (ntmvrlist_to_ntrlist ntc) 

let pp_lcs fd m xd : unit =     
  (* now build the definition of the term relation *)
  let build_term_call xd ntr st = 
    (* TODO wrap with formula_judgement *)
    let ntr = Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd ntr) in
    St_node (dummy_loc,
	     { st_rule_ntr_name = "def_lc_"^ntr;
	       st_prod_name = "lc"^"_"^ntr;   (* 1 *)
	       st_es = [ Ste_st (dummy_loc, st) ];
	       st_loc = dummy_loc } ) in

  let make_premises r p = 
    ln_debug("lcs, making premises for rule "^r.rule_ntr_name^", production "^p.prod_name);
    (* the tricky part here is to understand if we have to cofinite quantify something *)

    (* build a canonical symterm for the production, to extract the nonterms: ntss *)
    let stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in
    let st = St_node(dummy_loc,stnb) in

    let x = Bounds.nt_or_mv_of_symterms [st] in 
    ln_debug ("** st: "^Grammar_pp.pp_plain_symterm st^"\n ** bd: "
	      ^ (String.concat " -*- " 
		   (List.map 
		      (fun ((ntmv,_),bo) -> Grammar_pp.pp_plain_nt_or_mv ntmv ^ " :: " ^ 
			match bo with None -> "None" | Some b -> "Some "^Grammar_pp.pp_plain_bound b) x)));

    let ntss_nobounds =
      Auxl.option_map (fun (((ntmvr,s),_),bo) -> match ntmvr,bo with (Ntr ntr, None) -> Some (ntr,s) | _ -> None ) x in
    let ntss_bounds = 
      Auxl.option_map (fun (((ntmvr,s),_),bo) -> match ntmvr,bo with (Ntr ntr, Some b) -> Some ((ntr,s),b) | _ -> None ) x in

    (* for each nonterm... *)
    let premises_nobounds = 
      Auxl.option_map 
	(function (ntr,s) -> 
	  let ntrp = Auxl.primary_ntr_of_ntr xd ntr in

	  let mvs = binders_for_nt p (ntr,s) in (* compute the set of mv that bind in nt *)

	  ln_debug 
	    ("lcs, rule "^r.rule_ntr_name^", binders in prod "
	     ^ p.prod_name^ " for ntr "^ntr ^ " = "^String.concat " , " (List.map Grammar_pp.pp_plain_metavar mvs));

	  if List.length mvs > 1 then Auxl.error "locally_nameless - not implemented: several mvs bind the same nt\n";

	  if List.length mvs = 1 
	      (* build premise with cofinite quantification *)
	  then
	    let r = Auxl.rule_of_ntr_nonprimary xd ntr in
	    let st_prod_name_s = 
	      try
		let p = List.find
		    ( fun p ->
		      match p.prod_es with
		      | [ Lang_metavar (mv2,_) ] ->
			  if (Auxl.primary_mvr_of_mvr xd (fst (List.hd mvs))) = mv2 then true else false
		      | _ -> false )
		    (List.concat 
		       (List.map 
			  (fun ntr -> let r = Auxl.rule_of_ntr xd ntr in r.rule_ps)
			  (ntmvrlist_to_ntrlist (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep)))))
		in
		p.prod_name
	      with Not_found -> 
		Auxl.error ("internal: lns, make_premises, cannot find singleton production for "
			    ^ (fst (List.hd mvs)) ^ " starting from rule " ^ r.rule_ntr_name ^ "\n")
	    in
	    let st_rule_name_s = 
	      let r = List.find
		  (fun r ->
		    List.exists
		      ( fun p ->
			match p.prod_es with
			| [ Lang_metavar (mv2,_) ] -> if (Auxl.primary_mvr_of_mvr xd (fst (List.hd mvs))) = mv2 then true else false
			| _ -> false )
		      r.rule_ps)
		  (List.map  (* list of rules accessible *)
		     (fun ntr -> Auxl.rule_of_ntr xd ntr)
		     (ntmvrlist_to_ntrlist (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep))))
	      in r.rule_ntr_name
	    in
	    Some (
	    St_node (dummy_loc,
		     { st_rule_ntr_name = "formula";
		       st_prod_name = 
                       if Auxl.is_lngen m 
                       then  "formula_universal_formula_"^(Auxl.primary_mvr_of_mvr xd (fst (List.hd mvs)))
                       else "formula_cofinite_formula_"^(Auxl.primary_mvr_of_mvr xd (fst (List.hd mvs)));
		       st_es = 
                       ( if Auxl.is_lngen m 
                       then []
                       else [ st_var_set_vars ] )
                       @ 
		       [ (* Ste_metavar (dummy_loc, "vars", ("L",[]));  st_var_set_vars - now included above *)
			 Ste_var (dummy_loc, fst (List.hd mvs), Grammar_pp.pp_plain_metavar (List.hd mvs));
			 Ste_st 
			   (dummy_loc, 
			    St_node 
			      (dummy_loc,
			       { st_rule_ntr_name = "formula";
				 st_prod_name = "formula_judgement";
				 st_es = 
				 [ Ste_st 
				     (dummy_loc,
				      St_node
					(dummy_loc,
					 { st_rule_ntr_name = "judgement";
					   st_prod_name = "def_lc_"^ntrp;
					   st_es =
					   [ Ste_st
					       (dummy_loc,
						St_node
						  (dummy_loc,
						   { st_rule_ntr_name = "def_lc_"^ntrp;
						     st_prod_name = "lc_"^ntrp;
						     st_es = [ Ste_st 
								 (dummy_loc, 
								  St_node 
								    (dummy_loc, 
								     { st_rule_ntr_name = ntr;
								       st_prod_name = ((Auxl.rule_of_ntr xd ntrp).rule_pn_wrapper)^"open_wrt_"^st_rule_name_s; (* FZFZ *)
								       st_es = 
								       [ Ste_st (dummy_loc, St_nonterm (dummy_loc, ntr, (ntr,s)));
									 Ste_st (dummy_loc,
										 St_node 
										   (dummy_loc,
										    { st_rule_ntr_name = st_rule_name_s; (* WRONG *)
										      st_prod_name = st_prod_name_s;
										      st_es = [ Ste_var (dummy_loc, fst (List.hd mvs), 
													 Grammar_pp.pp_plain_metavar (List.hd mvs)) ];
										      st_loc = dummy_loc }))
								       ];
								       st_loc = dummy_loc })) ];
						     st_loc = dummy_loc })) ];
					   st_loc = dummy_loc })) ];
				 st_loc = dummy_loc })) ];
		       st_loc = dummy_loc }) )
	  else 
	    (* decide if a call to lc_ntr is needed *)
	    if always_locally_closed m xd (Auxl.primary_ntr_of_ntr xd ntr)
	    then None
	    else Some (build_term_call xd ntr (St_nonterm (dummy_loc, ntr, (ntr,s))) ) )
	ntss_nobounds in

    let premises_bounds =
      Auxl.option_map
	(fun ((ntr,s),b) ->
	  if always_locally_closed m xd (Auxl.primary_ntr_of_ntr xd ntr)
	  then None
	  else
	    Some
	      (St_node (dummy_loc,
			{ st_rule_ntr_name = "formula";
			  st_prod_name = "formula_dots"; (* FZ ensure that it exists *)
			  st_es =
			  [ Ste_list (dummy_loc,
				      [ Stli_listform
					  { stl_bound = b;
					    stl_elements = [Ste_st (dummy_loc,
								    (build_term_call xd ntr (St_nonterm (dummy_loc, ntr, (ntr,s)))))];
					    stl_loc = dummy_loc }
				      ])];
			  st_loc = dummy_loc } ))) 
	ntss_bounds in


(* (\* (build_term_call xd ntr (St_nonterm (dummy_loc, ntr, (ntr,[])))) )*\) *)
(*  	ntss_bounds in  *)

    premises_nobounds @ premises_bounds in

  let lcs_drule_from_prod r p =
    try 
      let _ = List.assoc "coq-ln_splitted" p.prod_homs 
      in None
    with Not_found -> 
      let premises = make_premises r p in

      let conclusion = 
	let stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in
	build_term_call xd r.rule_ntr_name (St_node(dummy_loc,stnb)) in
      
      Some (PSR_Rule
	      { drule_name = "lc"^"_"^p.prod_name;
		drule_categories = StringSet.empty;
		drule_premises = List.map (fun st -> None,st) premises; (*HNAMING *)
		drule_conclusion = conclusion;
		drule_homs = [];
		drule_loc = dummy_loc }) in

  let lcs_defn_from_rule r =
    let ntr = r.rule_ntr_name in 
    let rules = 
      Auxl.option_map 
	(lcs_drule_from_prod r) 
	(List.filter (fun p -> not p.prod_meta) r.rule_ps) in
    { d_name = "lc"^"_"^ntr;  (* 1 *)
      d_form = build_term_call xd ntr (St_nonterm (dummy_loc, ntr,(ntr,[])));  
      d_wrapper = "lc_";
      d_rules = rules; 
      d_homs = [];
      d_loc = dummy_loc } in

  let lcs_defnclasses =
    Auxl.option_map 
      (fun ntcl ->
	let rules =
	  (List.filter 
	     (fun r -> (not r.rule_meta) && (Auxl.hom_spec_for_pp_mode m r.rule_homs = None)) 
	     (List.map 
		(Auxl.rule_of_ntr xd) 
		(ntmvrlist_to_ntrlist ntcl))) in
	match rules with
	| [] -> None
	| _ ->
	    Some (RDC { dc_name = "LC_"^(String.concat "_" (List.map (fun r -> r.rule_ntr_name) rules));
                        dc_homs = [];  (* TODO: should we inherit any coq-universe from elsewhere?*)
			dc_language_names = [];
			dc_wrapper = "";
			dc_defns = List.map lcs_defn_from_rule rules;
			dc_loc = dummy_loc }))
      (List.filter (required_ntc m xd) (Auxl.select_dep_ts m xd.xd_dep))

 in

  let lookup = Term_parser.make_parser xd in
  
  Defns.pp_fun_or_reln_defnclass_list fd m xd lookup lcs_defnclasses

(* ******************************************************************** *)
(* arity                                                                *)
(* ******************************************************************** *)

let pp_arity_prod m xd_transformed f ntr p =
  let lhs_stnb = Grammar_pp.canonical_symterm_node_body_of_prod ntr p in 
  let lhs_st = St_node(dummy_loc,lhs_stnb) in
  let ((de1,de2) as de,de3,pptbe) = Bounds.bound_extraction m xd_transformed dummy_loc [lhs_st]  in
  let lhs = Grammar_pp.pp_symterm m xd_transformed [] de lhs_st in

  let mse = (* invariant: there exists exactly one mse *)
    List.hd 
      (Auxl.option_map
	 ( fun bs -> 
	   match bs with
	   | AuxFnDef (f',mse) when String.compare f f' = 0 -> Some mse
	   | _ -> None )
	 p.prod_bs) in
  let rec mse_to_rhs mse =
    match mse with
    | Empty -> 
	"0",[]
    | MetaVarExp mv -> 
	"1",[] (* FZ is this correct in the general case? *)
    | Union (mse1,mse2) -> 
	let (c1,d1) = mse_to_rhs mse1 in let (c2,d2) = mse_to_rhs mse1 in  "("^c1 ^") + ("^c2^")", d1@d2
    | Aux (f1,nt1) -> 
	let name = arity_name f1 (Auxl.promote_ntr xd_transformed (Auxl.primary_ntr_of_ntr xd_transformed (fst nt1))) in
	name ^ " " ^ Grammar_pp.pp_nonterm m xd_transformed nt1,
	[name]
  in
  let (rhs,deps) = mse_to_rhs mse in

  ("",lhs,rhs), deps
  

let pp_arity_clause m xd xd_transformed f ntr ntmvr =
  
  let id = arity_name f ntr in

  let header = 
    ( match m with
    | Coq _ ->         
	let nts_used = Context_pp.nts_used_in_lhss m xd (Auxl.rule_of_ntr xd ntr) in
        let fresh_var_ntr = Auxl.secondary_ntr xd ntr  in
	let pat_var  = Auxl.fresh_nt nts_used (fresh_var_ntr,[]) in
	( id
	  ^ " (" ^ Grammar_pp.pp_nonterm m xd pat_var 
	  ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd ntr ^ ")", 
          "", 
          " : nat :=\n" 
	  ^ "  match " ^ Grammar_pp.pp_nonterm m xd pat_var ^ " with\n")
    | _ -> assert false ) in

  let clauses_deps = 
    List.map 
      (pp_arity_prod m xd_transformed f ntr)
      (List.filter 
         (function p -> not p.prod_meta) 
         (Auxl.rule_of_ntr xd_transformed ntr).rule_ps) in
  let clauses, deps =  let c,d = List.split clauses_deps in c, List.flatten d in 

  { r_fun_id = id;
    r_fun_dep = deps;
    r_fun_type = ntr;
    r_fun_header = header;
    r_fun_clauses = clauses }

let pp_arities m xd xd_transformed =
  (* for each auxfn *)
  ln_debug "auxfn infos:";
  List.iter
    (fun (f,(ntrs,ntmvr)) ->
      ln_debug ("name: "^f);
      ln_debug ("from: "^(String.concat " , " ntrs));
      ln_debug ("to  : "^Grammar_pp.pp_plain_nt_or_mv_root ntmvr))
    xd.xd_axs;
  (* ****** *)
  let pp_arity (f,(ntrs,ntmvr)) =
    List.map 
      (fun ntr -> pp_arity_clause m xd xd_transformed f ntr ntmvr)  (* FZ go only auxfns with target with a ln repr *)
      ntrs in 
  Dependency.collapse m xd 
    { i_funcs = (List.concat (List.map pp_arity xd.xd_axs));
      i_funcs_proof = None }


(* ******************************************************************** *)
(* free vars                                                            *)
(* ******************************************************************** *)

let pp_freevars m xd =
  let erase_binders r =
    { r with
      rule_ps = List.map (fun p -> { p with prod_bs = [] } ) r.rule_ps } in
  let erased_rules = List.map erase_binders xd.xd_rs in
  let xd_erased = 
    { xd with 
      xd_rs = erased_rules } in
  Substs_pp.pp_freevars m xd_erased

(* ******************************************************************** *)
(* substitutions                                                        *)
(* ******************************************************************** *)

let pp_substs m xd =
  let erase_binders r =
    { r with
      rule_ps = List.map (fun p -> { p with prod_bs = [] } ) r.rule_ps } in
  let erased_rules = List.map erase_binders xd.xd_rs in
  let xd_erased = 
    { xd with 
      xd_rs = erased_rules } in
  Substs_pp.pp_substs m xd_erased


(* ******************************************************************** *)
(* DEFNS                                                                *)
(* ******************************************************************** *)

let opening_vars = ref []      (* FZ replace with functional version? *)

let build_open_symterm m xd open_wrt st =
  opening_vars := Auxl.remove_duplicates (open_wrt @ !opening_vars);
  let ntr = 
    match st with
    | St_nonterm (_,ntr,_) -> Auxl.primary_ntr_of_ntr xd ntr
    | St_nontermsub (_,_,ntr,_) -> Auxl.primary_ntr_of_ntr xd ntr
    | _ -> Auxl.error "internal: build_open_symterm, not a nonterm\n" in
  let r = Auxl.rule_of_ntr xd ntr in
  let find_var_prod mv =
    let mv1 = 
      match mv with
      | Ste_metavar (_,mv1,_) -> mv1
      | Ste_var (_,mv1,_) -> mv1
      | _ -> Auxl.error "internal: find_var_prod ln not ste_metavar\n" in
    let p = List.find
	( fun p ->
	  match p.prod_es with
	  | [ Lang_metavar (mv2,_) ] -> if mv1 = mv2 then true else false
	  | _ -> false )
	(List.concat  (* copied from 537 *)
	   (List.map 
	      (fun ntr -> let r = Auxl.rule_of_ntr xd ntr in r.rule_ps)
	      (ntmvrlist_to_ntrlist (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep)))))
    in p.prod_name 
  in
  let find_var_rule mv =
    let mv1 = 
      match mv with
      | Ste_metavar (_,mv1,_) -> mv1
      | Ste_var (_,mv1,_) -> mv1
      | _ -> Auxl.error "internal: find_var_prod ln not ste_metavar\n" in

    let r = List.find
	(fun r ->
	  List.exists
	    ( fun p ->
	      match p.prod_es with
	      | [ Lang_metavar (mv2,_) ] -> if mv1 = mv2 then true else false
	      | _ -> false )
	    r.rule_ps)
	(List.map  (* list of rules accessible *)
	   (fun ntr -> Auxl.rule_of_ntr xd ntr)
	   (ntmvrlist_to_ntrlist (List.assoc (Ntr r.rule_ntr_name) (Auxl.select_dep_graph m xd.xd_dep))))
    in ln_debug ("find_var_rule: "^r.rule_ntr_name); r.rule_ntr_name
  in
  let rev_open_wrt = List.rev open_wrt in
  let rec internal wrt st =
    match wrt with
    | [] -> st
    | mv::tl ->
	let prefix = 
	  let r = Auxl.rule_of_ntr xd ntr in
	  r.rule_pn_wrapper in 
	let open_st =  
	  St_node ( dummy_loc,
		    { st_rule_ntr_name = ntr;
		      st_prod_name = prefix^"open_wrt_"^(find_var_rule mv); 
		      st_es = [ 
		        Ste_st (dummy_loc, st);
			Ste_st (dummy_loc,
				St_node (dummy_loc,
					 { st_rule_ntr_name = ntr;
					   st_prod_name = (find_var_prod mv)^"_f"; 
					   st_es = [ mv ];
					   st_loc = dummy_loc })) ];
		      st_loc = dummy_loc } ) in
	internal tl open_st in
  internal rev_open_wrt st

let rec find_occurrence_nt nt els o =
  match els with
  | (Lang_nonterm (_,nt1)::tl) -> 
      if nt = nt1 then o else find_occurrence_nt nt tl (o+1) 
  | (Lang_metavar (_,_)::tl) -> find_occurrence_nt nt tl (o+1) 
  | _::tl -> find_occurrence_nt nt tl o
  | [] -> raise Not_found

let rec find_occurrence_mv els c mv =     (* merge with nt *)
  match els with
  | (Lang_metavar (_,mv1)::tl) -> if mv = mv1 then c else find_occurrence_mv tl (c+1) mv
  | (Lang_nonterm (_,nt1)::tl) -> find_occurrence_mv tl (c+1) mv
  | _::tl -> find_occurrence_mv tl c mv
  | [] -> raise Not_found

let occ_stes stnb =       (* move to auxl  *)
  let c = ref 0 in
  List.map 
    (fun ste -> c := !c +1; (ste,!c))
    stnb.st_es 

let ln_add_lc_premise m xd nts_premises nts_conclusion =
  (* for each nonterm mentioned in the conclusion but not in the premises add a "lc" test *)
  (* ...but ignore nonterms which are defined by a hom *)

  let nts_lc = 
    let nts_lc_dupl = List.filter (fun (nt,_) -> not (List.mem nt (List.map fst nts_premises))) nts_conclusion in
    let nts_lc_dupl_filt = 
      List.filter 
	( fun ((ntr,_),_) -> 
	  let r = Auxl.rule_of_ntr xd (Auxl.primary_ntr_of_ntr xd ntr) in
	  match	Auxl.hom_spec_for_hom_name (Auxl.hom_name_for_pp_mode m) r.rule_homs with
	  | None -> true
	  | Some _ -> false )
	nts_lc_dupl 

    in 
    let rec internal l =
      match l with 
      | [] -> []
      | (nt, Some st)::tl -> 
	  let tl = List.filter (fun (nt1,st1) -> not ((nt = nt1))) tl in (nt, Some st)::(internal tl)
      | (nt, None)::tl -> 
	  let tmp = List.filter (fun (nt1,_) -> nt=nt1) tl in
	  if List.exists (fun (_,st) -> match st with | None -> false | Some _ -> true) tmp then internal tl else (nt,None)::(internal tl) 
    in
    (* before returning check if it lc_ntc is really required *)
    List.filter (fun ((nt,_),_) -> required_ntc m xd [Ntr nt]) (internal nts_lc_dupl_filt) in

(*   print_endline ("#########"^(String.concat " " (List.map (fun (nt,b) -> *)
(*     Grammar_pp.pp_plain_nonterm nt ^ " " ^ (match b with None -> "none" | Some st -> Grammar_pp.pp_plain_symterm st)) *)
(* 						   nts_lc))); *)

  let build_premise xd (nt,st_bind) =
    let st =
    St_node 
	(dummy_loc,
	 { st_rule_ntr_name = "formula";
	   st_prod_name = "formula_judgement";
	   st_es = [ Ste_st 
		       (dummy_loc, 
			St_node 
			  (dummy_loc,
			   { st_rule_ntr_name = "judgement";
			     st_prod_name = ("judgement_def_lc_"^(Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd (fst nt))));
			     st_es = [ (Ste_st 
					  (dummy_loc, 
					   St_node
					     (dummy_loc,
					      { st_rule_ntr_name = "def_lc_"^(Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd (fst nt)));
						st_prod_name = "lc_"^(Auxl.promote_ntr xd (Auxl.primary_ntr_of_ntr xd (fst nt)));
						st_es = [ (Ste_st (dummy_loc, 
								   (match st_bind with
								   | None -> St_nonterm (dummy_loc,(fst nt),nt)
								   | Some st_bind -> st_bind ))) ];
						st_loc = dummy_loc }))) ];
			     st_loc = dummy_loc })) ]; 
	   st_loc = dummy_loc }) in
(*    print_endline ("$$$$"^(Grammar_pp.pp_plain_symterm st));  *)
    st
  in
  List.map (build_premise xd) nts_lc

(* (ln_transform_symterm xd stl) returns symterms valid in (ln_transform_syntaxdefn xd) *)
let ln_transform_symterms (m:pp_mode) (xd:syntaxdefn) (stlp:(string option * symterm) list) (stlc:symterm) (* : symterm list * symterm *) =
  (* 1- functions to erase all binders, update names of productions - done at the end *)
  let rec remove_binders_symterm xd st =
    match st with
    | St_node (l,stnb) -> St_node (l,remove_binders_symterm_node_body xd stnb)
    | St_nonterm (l,ntrp,nt) -> St_nonterm (l,ntrp,nt)
    | St_nontermsub (l,ntrpl,ntrpt,nt) -> St_nontermsub (l,ntrpl,ntrpt,nt)
    | St_uninterpreted (l,s) -> St_uninterpreted (l,s) 
  and remove_binders_symterm_node_body xd stnb =
    try
      let p = Auxl.prod_of_prodname ~warn:false xd stnb.st_prod_name in
      let prod_name_t = (* FZ see splitted_bindable_prods *)
	match p.prod_es with
	| [Lang_metavar (mvr,mv)] when is_bindable xd mv p -> p.prod_name^"_f"  
	| _ -> p.prod_name in

      let binder_mvs_prod =  (* these metavars bind in the prod: discover the occurrencies *)
	binders p in

      let binder_mvs_occurrences = (* list of occurrencies *)
	List.map (find_occurrence_mv p.prod_es 1) binder_mvs_prod in
      let st_es_t = 
	  Auxl.option_map (remove_binders_symterm_element xd binder_mvs_occurrences) (occ_stes stnb) in
      { stnb with st_prod_name = prod_name_t; st_es = st_es_t }
    with Not_found ->
      (* this happens when going over an "open" or "formula_cofinite" production, which *)
      (* does not yet belong to xd: both have no binders *)
      { stnb with st_es = Auxl.option_map (remove_binders_symterm_element xd []) (occ_stes stnb) }

  and remove_binders_symterm_element xd mvs_occurrences ste =
    match ste with
    | (Ste_st (l,st),_) -> Some (Ste_st (l,remove_binders_symterm xd st))
    | (Ste_metavar (l,mvrp,mv),o) ->
	if List.mem o mvs_occurrences 
	then None
	else Some (Ste_metavar (l,mvrp,mv))
    | (Ste_var (l,mvrp,var),o) -> 	
	if List.mem o mvs_occurrences 
	then None
	else Some (Ste_var (l,mvrp,var))
    | (Ste_list (l,stlis),_) -> 
	(* Auxl.warning "internal: remove_binders_symterm_element ste_list not implemented\n"; *)
	Some (Ste_list (l,stlis)) (* FZ *)
  in

  (* 2- open each nt wrt the longest binder sequence found *)
 
  (* 2a collect binders sequences for each nonterminal *)

  let rec collect_binders_symterm xd current_binding_mvs bind_st st =
    match st with
    | St_node (l,stnb) -> 
	let p = Auxl.prod_of_prodname xd stnb.st_prod_name in
	let bss = 
	  Auxl.option_map
	    ( fun bs -> 
	      match bs with
	      | Bind (MetaVarExp mv, nt) -> 
		  let mvo = List.nth stnb.st_es (find_occurrence_mv p.prod_es 0 mv) in
		  let o = find_occurrence_nt nt p.prod_es 1 in
		  Some (mvo,nt,o,(St_node (l,stnb)))     
	      | _ -> None )
	    p.prod_bs in

(* 	print_endline ("&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& "^p.prod_name); *)
(* 	print_endline (String.concat " ** "  *)
(* 			 (List.map (fun (mv,nt,o) ->  *)
(* 			   (Grammar_pp.pp_plain_metavar mv) ^" , "  *)
(* 			   ^ (Grammar_pp.pp_plain_nonterm nt) ^" , "  *)
(* 			   ^ (string_of_int o)) *)
(*			    bss)); *)

	List.concat      
	  ( List.map 
	      ( fun (ste,o) ->
		let extra_binders =
		  List.map (fun (mv,_,_,_) -> mv)
		    (List.filter (fun (_,_,o1,_) -> o = o1) bss) in
		let st_binder = 
		  ( match bind_st with
		  | Some st -> Some st
		  | None -> 
		      let bndrs = List.filter (fun (_,_,o1,_) -> o = o1) bss in
		      ( match bndrs with 
		      | [] -> None
		      | h::_ -> let b = ((fun (_,_,_,st) -> st) h) in Some b))
		in
		( collect_binders_symterm_element xd (current_binding_mvs@extra_binders) st_binder ste ) )
	      (occ_stes stnb) )    

    | St_nonterm (l,ntrp,nt) -> 
	[(nt,current_binding_mvs, bind_st)]
    | St_nontermsub (l,ntrpl,ntrpt,nt) -> 
	[(nt,current_binding_mvs,bind_st)]
    | St_uninterpreted (l,s) -> 
	[]
  and collect_binders_symterm_element xd current_binding_mvs bind_st ste =
    match ste with
    | Ste_st (l,st) -> collect_binders_symterm xd current_binding_mvs bind_st st
    | Ste_metavar (l,mvrp,mv) -> []
    | Ste_var (l,mvrp,var) -> []
    | Ste_list (l,stlis) -> []
(*	Auxl.warning ("internal: collect_binders_symterm_element ste_list not implemented\n"); []  FZ *)
  in

  (* TODO fix quantification - requires collapse hypothesis *)
  

(*   print_endline "************* ln_transform_symterms **************"; *)
(*   print_endline ""; *)
(*   print_endline ((String.concat "\n\n" (List.map Grammar_pp.pp_plain_symterm stlp)) *)
(* 		^ "\n\n" ^ (Grammar_pp.pp_plain_symterm stlc)); *)

  let nt_bound_p = List.concat (List.map (fun st -> collect_binders_symterm xd [] None st) (List.map snd stlp)) in
  let nt_bound_c = collect_binders_symterm xd [] None stlc in
  let nt_bound = nt_bound_p @ nt_bound_c in

(*   print_endline ("** "^(String.concat "\n** "  *)
(* 			 (List.map  *)
(* 			    (fun (nt,bvars) ->  *)
(* 			      (Grammar_pp.pp_plain_nonterm nt) ^ " : " ^ *)
(* 			      (String.concat ", " *)
(* 				 (List.map Grammar_pp.pp_plain_metavar bvars))) *)
(* 			    nt_bound))); *)

  (* now for each nt, find the longest sequence of binders *)
  let nt_longest = 
    let rec find_longest nt_bound nt_longest =
      match nt_bound with
      | [] -> nt_longest
      | (nt,bvars,_)::tl -> 
	  try 
	    let longest = List.assoc nt nt_longest in
	    if List.length bvars > List.length longest      (* add error check here *)
	    then find_longest tl ((nt,bvars)::(List.remove_assoc nt nt_longest))
	    else find_longest tl nt_longest
	  with Not_found -> find_longest tl ((nt,bvars)::nt_longest) in
    find_longest nt_bound [] in

  let nt_longest = 
    List.map
      ( fun (nt,stel) -> 
	(nt,
	 List.map 
	   ( fun ste ->
	     match ste with
	     | Ste_metavar (_,mvr,mv) -> (ste,(Ste_var (dummy_loc,mvr, ((*"TX_"^*)(Grammar_pp.pp_plain_metavar mv)))))
	     | _ -> Auxl.error "internal: nt_longest" )
	   stel ))
      nt_longest in

(*   print_endline "*** longest binder sequence for each nonterm"; *)
(*   print_endline ("** "^(String.concat "\n** "  *)
(* 			 (List.map  *)
(* 			    (fun (nt,bvars) ->  *)
(* 			      (Grammar_pp.pp_plain_nonterm nt) ^ " : " ^ *)
(* 			      (String.concat ", " *)
(* 				 (List.map Grammar_pp.pp_plain_symterm_element bvars))) *)
(* 			    nt_longest))); *)

  (* now open the nonterms - variant of collect, return the symterm and the set of opening metavariables *)

  let rec open_nonterm_symterm m xd current_binding st =
    match st with
    | St_node (l,stnb) -> 
(* 	print_endline "STNB**************************************************"; *)
(* 	print_endline (Grammar_pp.pp_plain_symterm_node_body stnb); *)
	
	let p = Auxl.prod_of_prodname xd stnb.st_prod_name in
	let bss = (* variables binding nts + nts occurrences - look at bindspecs *)
	  Auxl.option_map
	    ( fun bs -> 
	      match bs with
	      | Bind (MetaVarExp mv, nt) -> 
		  let mvo = List.nth stnb.st_es (find_occurrence_mv p.prod_es 0 mv) in
		  let o = find_occurrence_nt nt p.prod_es 1 in
		  Some (mvo,nt,o) 
	      | _ -> None )
	    p.prod_bs in
	let nbss = (* nts that should not be opened wrt variables - look at homs *)
	  try
	    let h = List.assoc "coq" p.prod_homs in
	    Auxl.option_map
	      ( fun hse -> match hse with
	      | Hom_ln_free_index (fvis, nti) -> Some ((nti+1), (List.map (List.nth stnb.st_es) fvis))
	      | _ -> None )
	      h
	  with Not_found -> [] in
(* 	print_endline ("** nbss:"  *)
(* 		       ^ String.concat " " (List.concat (List.map (fun (nti,l) ->  *)
(* 			 (string_of_int nti) :: " - " :: (List.map Grammar_pp.pp_plain_symterm_element l)) nbss))); *)
	St_node ( l, { stnb with
		       st_es = 
		       ( List.map 
			   ( fun (ste,o) ->
			     let extra_binders =
			       Auxl.option_map (fun (mvo,_,o1) -> if o = o1 then Some mvo else None) bss in
			     let removed_binders =
			       List.concat (Auxl.option_map (fun (o1,fvis) -> if o = o1 then Some fvis else None) nbss) in
			     
(* 			     print_endline "NBE**************************************************"; *)
(* 			     print_endline (Grammar_pp.pp_plain_symterm_element ste); *)
(* 			     print_endline ("extra: "^String.concat " " (List.map Grammar_pp.pp_plain_symterm_element extra_binders)); *)
(* 			     print_endline ("current: "^String.concat " " (List.map Grammar_pp.pp_plain_symterm_element current_binding)); *)
(* 			     print_endline ("removed: "^String.concat " " (List.map Grammar_pp.pp_plain_symterm_element removed_binders)); *)

			     let current_str = List.map Grammar_pp.pp_plain_symterm_element current_binding in
			     List.iter
			       (fun str -> if List.mem str current_str 
			       then Auxl.error ("locally-nameless: a rule definition contains a repeated binder: "^str^";\n  try alpha-converting one of the occurrences.\n"))
			       (List.map Grammar_pp.pp_plain_symterm_element extra_binders);
			       
			       let binders = 
(* 				 print_endline ("removed = " ^ String.concat " " (List.map Grammar_pp.pp_plain_symterm_element removed_binders)); *)
(* 				 print_endline ("current = " ^ String.concat " " (List.map Grammar_pp.pp_plain_symterm_element current_binding)); *)
(* 				 print_endline ("extra   = " ^ String.concat " " (List.map Grammar_pp.pp_plain_symterm_element extra_binders)); *)
				 
				 removed_binders @ current_binding @ extra_binders in
			       
			       ( open_nonterm_symterm_element m xd binders ste ) )
			   (occ_stes stnb) ) } )
    | St_nonterm (l,ntrp,nt) -> 
	let longest = List.assoc nt nt_longest in
	let open_wrt = List.map snd (List.filter (fun (mv,_) -> not (List.mem mv current_binding)) longest) in
	
(* 	print_endline ("nonterm: "^(Grammar_pp.pp_plain_nonterm nt) *)
(* (\*		       ^" longest: " ^(String.concat " " (List.map Grammar_pp.pp_plain_symterm_element longest)) *\) *)
(* 		       ^" current: " ^(String.concat " " (List.map Grammar_pp.pp_plain_symterm_element current_binding)) *)
(* 		       ^" open: " ^(String.concat " " (List.map Grammar_pp.pp_plain_symterm_element open_wrt))); *)
	build_open_symterm m xd open_wrt (St_nonterm (l,ntrp,nt))

    | St_nontermsub (l,ntrpl,ntrpt,nt) -> 
	let longest = List.assoc nt nt_longest in
	let open_wrt = List.map snd (List.filter (fun (mv,_) -> not(List.mem mv current_binding)) longest) in
	build_open_symterm m xd open_wrt (St_nontermsub (l,ntrpl,ntrpt,nt)) (* TODO *)      
    | St_uninterpreted (l,s) -> 
	St_uninterpreted (l,s)
  and open_nonterm_symterm_element m xd current_binding ste =
    match ste with
    | Ste_st (l,st) -> 
	Ste_st (l,open_nonterm_symterm m xd current_binding st)
    | Ste_metavar (l,mvrp,mv) -> 
	let opening_mvs = List.concat (List.map snd nt_longest) in
	if List.mem (Ste_metavar (l,mvrp,mv)) (List.map fst opening_mvs)
	then (Ste_var (dummy_loc,mvrp, ((*"TX_"^*)(Grammar_pp.pp_plain_metavar mv))))
	else (Ste_metavar (l,mvrp,mv))
    | Ste_var (l,mvrp,var) -> Ste_var (l,mvrp,var)
    | Ste_list (l,stlis) -> 
	(* Auxl.warning ("internal: open_nonterm_symterm_element ste_list not implemented\n"); *) 
	Ste_list (l,stlis)
  in

  let open_nonterm m xd st =
    opening_vars := [];
    let nst = open_nonterm_symterm m xd [] st in
    (nst, !opening_vars) in

  (* simplest case: cofinite quantification for each hypothesis - no merge FZ FIXME *)
  let cofinite_quantify (st,mvs) =
(*     print_endline "COFINITE QUANTIFY"; *)
(*     print_endline (Grammar_pp.pp_plain_symterm st); *)
(*     print_endline (String.concat " " (List.map Grammar_pp.pp_plain_symterm_element mvs)); *)
    let mvsr = List.rev mvs in
    let rec internal mvsr st =
      match mvsr with
      | [] -> st
      | mv::tl ->
	  let mvr = match mv with Ste_metavar (_,mvr,_) -> mvr | Ste_var (_,mvr,_) -> mvr | _ -> Auxl.error "internal: cofinite quantify not metavar" in
	  let cq_st =
	    St_node ( dummy_loc,
		      { st_rule_ntr_name = "formula";
			st_prod_name = "formula_cofinite_formula_"^mvr;
			st_es = [ (* Ste_metavar (dummy_loc, "vars", ("L",[])); *) st_var_set_union tl;
				  mv;
				  Ste_st (dummy_loc, st) ];
			st_loc = dummy_loc } ) in
	  internal tl cq_st in
    internal mvsr st in

  (* *** all together *)
  let opened_p = List.map (fun (hn,st) -> (hn, open_nonterm m xd st)) stlp in
  let opened_c = open_nonterm m xd stlc in 

  let quantified_p = List.map (fun (hn,st) -> (hn, cofinite_quantify st)) opened_p in
  let quantified_c = cofinite_quantify opened_c in           (* FZ TODO *)

  let stlp_t = List.map (fun (hn,st) -> (hn, remove_binders_symterm xd st)) quantified_p in
  let stlc_t = remove_binders_symterm xd quantified_c in
  let nt_bound_p =
    Auxl.remove_duplicates 
      (List.map (fun (nt,_,sto) -> match sto with None -> (nt,None) | Some st -> (nt,Some (remove_binders_symterm xd st))) nt_bound_p) in
  let nt_bound_c = 
    Auxl.remove_duplicates 
      (List.map (fun (nt,_,sto) -> match sto with None -> (nt,None) | Some st -> (nt,Some (remove_binders_symterm xd st))) nt_bound_c) in


(*   print_endline "+++++++++++++ ln_transformed_symterms ------------"; *)
(*   print_endline (Grammar_pp.pp_syntaxdefn error_opts xd); *)

(*   print_endline ""; *)
(*   print_endline ((String.concat "\n\n" (List.map Grammar_pp.pp_plain_symterm stlp_t)) *)
(* 		^ "\n\n" ^ (Grammar_pp.pp_plain_symterm stlc_t)); *)

  ((stlp_t,stlc_t),(nt_bound_p,nt_bound_c))

let ln_transform_drule m xd dr =
  let (non_fancy_premises, fancy_premises) =
    List.partition ( fun (hn,st) ->
      match st with
      | St_node (l,stnb) when (String.compare stnb.st_rule_ntr_name "fancy_formula" = 0) -> false
      | _ -> true ) dr.drule_premises in

  let ((t_symterms_p,t_symterm_c) ,(nt_bound_p,nt_bound_c)) = 
    ln_transform_symterms m xd non_fancy_premises dr.drule_conclusion in

  let extra_premises =
    ln_add_lc_premise m xd nt_bound_p nt_bound_c in
  { dr with
    drule_premises = fancy_premises @ List.map (fun st -> None,st) (extra_premises) @ t_symterms_p;
    drule_conclusion = t_symterm_c }
   
let ln_transform_defn m xd d =
  { d with
    d_rules = 
    List.map 
      (fun psr -> match psr with 
      | PSR_Rule dr -> PSR_Rule (ln_transform_drule m xd dr)
      | PSR_Defncom _ -> Auxl.error "internal: ln transform defncom not implemented" )
      d.d_rules }

let ln_transform_reln_defnclass m xd dc =
  { dc with 
    dc_defns = List.map (fun d -> ln_transform_defn m xd d) dc.dc_defns }

let ln_transform_fun_or_reln_defnclass_list 
    m (xd:syntaxdefn) (frdcs:fun_or_reln_defnclass list) : fun_or_reln_defnclass list =
  List.map 
    ( fun frdc -> match frdc with
    | FDC fdc -> Auxl.error "internal: fdc transform not implemented" 
    | RDC dc -> RDC (ln_transform_reln_defnclass m xd dc)
    ) frdcs







(* ****************************************************** *)
(* infrastructure                                         *)
(* ****************************************************** *)

let index_list l = 
  let c = ref 0 in
  List.map 
    (fun ste -> c := !c +1; (ste,!c))
    l

let ln_infrastructure m xd rd =
  (* ** body *)
  
  (* for each nonterm that has a lc predicate, define a body predicate *)
  (* build these by hand, without going through the general function mechanism *)
  (* TODO: fix computation of x *)
  let body_rules =
    List.concat 
      (List.map 
	 (fun ntcl ->
	   let rules =
	  (List.filter 
	     (fun r -> (not r.rule_meta) && (Auxl.hom_spec_for_pp_mode m r.rule_homs = None)) 
	     (List.map 
		(Auxl.rule_of_ntr xd) 
		(ntmvrlist_to_ntrlist ntcl))) in
	rules)
      (List.filter (required_ntc m xd) (Auxl.select_dep_ts m xd.xd_dep)))
  in
(*
  let make_body r =
    let t = try fst (List.hd (List.tl r.rule_ntr_names)) with _ -> r.rule_ntr_name in
    "Definition body_"^r.rule_ntr_name^" "
    ^ t
    ^ " :=\n  exists L, forall x, x \\notin L -> lc_"^r.rule_ntr_name
    ^ " (open_"^r.rule_ntr_name^"_wrt_term "^t ^" (term_var_f x)).\n" in   (* FZ TODO *)
  let body = String.concat "\n" (List.map make_body body_rules) in 
*)


  (* ** pick fresh *)

  (* this should recompute all the names of the generated fv functions - not sure it is correct *)
(*
  let fv_function_names m xd =
    let fv_function_name_s m xd fv =
      (fun i -> List.map (fun i -> i.r_fun_id) i.i_funcs)
	(Substs_pp.pp_foo_with_dependencies m xd 
	   (Substs_pp.freevar_manifestly_needed fv) 
	   (fun m xd domain r -> 
	     [ { r_fun_id = Auxl.fv_name fv.fv_name r.rule_ntr_name;
		 r_fun_dep = [];
		 r_fun_type = ""; 
		 r_fun_header = ("","","");
		 r_fun_clauses = [] } ] ))
    in

    List.concat (List.map (fv_function_name_s m xd) xd.xd_fvs) in
  let gather_fv (x,i) = 
    ( "D"^(string_of_int i),
      "  let D"^(string_of_int i)^" := gather_vars_with (fun x => "^x^" x) in\n" ) in

  let (g_fv_def, g_fv) = List.split (List.map gather_fv (index_list (fv_function_names m xd))) in

  let pick_fresh =
    "\nLtac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : env => dom x) in\n"
  ^ String.concat "" g_fv 
  ^ "  constr:(A \\u B \\u C"
  ^(if List.length g_fv_def = 0 then ")." else " \\u "^String.concat " \\u " g_fv_def^").")
  ^"

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Tactic Notation \"apply_fresh\" constr(T) \"as\" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation \"apply_fresh\" \"*\" constr(T) \"as\" ident(x) :=
  apply_fresh T as x; auto*.\n" in
*)
  
  (* ** hints *)
  let hints_rel = 
    List.concat (
    Auxl.option_map 
      (fun rd -> 
	match rd with
	| FDC _ -> None
	| RDC dc -> Some (List.map (fun d -> d.d_name) dc.dc_defns))
      rd) in
  let hints_lc = List.map (fun r -> "lc_"^r.rule_ntr_name) body_rules in
  let hints = 
    let h = hints_rel @ hints_lc in
    if List.length h = 0 
    then ""
    else "Hint Constructors "^(String.concat " " h)^".\n" in

  (* ** all together *)
  "\n(** infrastructure *)\n" 
(*   ^ "\n(\* additional definitions *\)\n\n" *)
(*   ^ body  *)
(*   ^ "\n(\* instanciation of tactics *\)\n" *)
(*   ^ pick_fresh ^"\n" *)
  ^ hints ^"\n"


(* ATTIC *)

(*       let rs =  *)
(* 	List.filter  *)
(* 	  ( fun r -> (not r.rule_meta) && (Auxl.hom_spec_for_pp_mode m r.rule_homs = None) )  *)
(* 	  xd.xd_rs  in  *)
(*       String.concat "\n" (List.map (pp_lcs_rule m xd) rs) *)

(*   let fake_raw_defn_list =  *)
(*     [ { raw_d_name = "t3_"; *)
(* 	raw_d_es : raw_element list; *)
(* 	raw_d_categories = []; *)
(* 	raw_d_wrapper =  "t4_"; *)
(* 	raw_d_body : semiraw_rule list; *)
(* 	raw_d_homs = []; *)
(* 	raw_d_loc = dummy_loc } ] in *)

(*   let fake_raw_defnclass = *)
(*     [ { raw_dc_name = "t1_"; *)
(* 	raw_dc_wrapper = "t2_"; *)
(* 	raw_dc_defns = fake_raw_defn_list; *)
(* 	raw_dc_loc = dummy_loc } ] in *)

(*   let lookup = Term_parser.make_parser xd in *)



(* let pp_lcs_prod m xd r p : string = *)
(*   let cst_stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in *)
(*   let cst_st = St_node(dummy_loc,cst_stnb) in *)
(*   let sie = [] in *)
(*   let ((de1,de2) as de,de3,pptbe) = Bounds.bound_extraction m xd dummy_loc [cst_st] in *)
(*   let cst = Grammar_pp.pp_symterm m xd sie de cst_st in *)

(*   let conclusion = "term_"^r.rule_ntr_name ^ " "^cst in  *)

(*   " | term_"^p.prod_name^" : " ^ conclusion *)

(* let pp_lcs_rule m xd r : string = *)
(*   let prods = List.filter (fun p -> not p.prod_meta) r.rule_ps in *)

(*   "Inductive term_"^r.rule_ntr_name^" : "^r.rule_ntr_name^" -> Prop :=\n" *)
(*   ^ String.concat "\n" (List.map (pp_lcs_prod m xd r) prods) *)





(* 		   (Auxl.option_map *)
(* 		      (fun psr -> match psr with PSR_Rule dr -> Some dr.drule_name | _ -> None)) *)
(* 		     d.d_rules) *)


  

(* compilation strategy for auxfn *)
(* - revise the split procedure: bvar does not have type nat but nat -> nat *)
(* - generate all the ntr definitions, splitting variables  *)
(*     (if a auxfn is defined, then the variable might bind something) *)
(* - for each ntr which has a auxfn defined, define a ntr_auxfn_arity function *)
(* - open functions must work with lists and nat -> nat bvars *)
(* - fresh now takes a list...  modify lc and symterms compilations to invoke arity *)

(* Questions: 

   Arthur defines only bgvar for patterns.  Can we assume that if a
   variable has a auxfn defined on it will never be in non-binding
   position? *)

