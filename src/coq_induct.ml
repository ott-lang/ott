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

open Types;;

(* identify the nontermroots that include list types *)
let need_induction m xd r =  
  let rec_rules = 
    List.find 
      (fun l -> List.mem (Ntr r.rule_ntr_name) l) 
      (Auxl.select_dep_ts m xd.xd_dep) in
  let rec uses_list_nt p =
    let element_uses_list_nt e = 
      match e with
      | Lang_list elb -> 
	  List.exists 
	    (fun e -> 
	      match e with 
	      | Lang_nonterm (ntr,_) -> List.mem (Ntr ntr) rec_rules
	      | _ -> false)
	    elb.elb_es
      | Lang_option _ | Lang_sugaroption _ -> 
	  Auxl.error "interal: option types not implemented in pp_induction\n"
      | Lang_nonterm (_,_) | Lang_metavar (_,_) | Lang_terminal _ -> false
    in List.exists element_uses_list_nt p.prod_es in
  (not r.rule_meta) && (List.exists uses_list_nt r.rule_ps)

let rules_needing_induction m xd rs : nontermroot list list = 
  (* ** returns the groups of mutually recursive rules that need 
        an ott-generated induction principle *)

  let rules = List.filter (need_induction m xd) rs in

  let groups = 
    Auxl.remove_duplicates 
      (List.map 
	 (fun r -> 
	   Auxl.option_map
	     (fun ntmvr -> 
	       ( match ntmvr with
	       | Ntr ntr -> Some ntr
	       | Mvr _ -> None ))
	     (List.find 
		(fun l -> List.mem (Ntr r.rule_ntr_name) l) 
		(Auxl.select_dep_ts m xd.xd_dep)))
	 rules) in
  
  (* remove groups for which a nonterm has a rule hom *)
  List.filter
    (fun g -> List.for_all 
	(fun ntr -> 
	  let r = Auxl.rule_of_ntr xd ntr in
	  match (Auxl.hom_spec_for_hom_name "coq" r.rule_homs) with
	    Some _ -> false | None -> true)
	g)
    groups

(* ** generate the induction principle for a set of rules *)
let generate_induction m xd ntr_set =
  let rule_set =
    List.map (fun ntr -> Auxl.rule_of_ntr xd ntr) ntr_set in

  (* ** Name for the induction principle ** *)
  let ip_name = (String.concat "_" ntr_set) ^ "_rect" 
  in

  (* ** Variables ** *)
  (* need a Variable decl for each inductive type appearing in any rule *)

  let rec used_in_tuple e : (string*string*string option) list =
    ( match e with
    | Lang_nonterm (ntr_primary,_) -> 
	let ntr = Auxl.promote_ntr xd ntr_primary in
	[ (ntr, ntr, None) ]
    | Lang_metavar (mvr_primary,_) -> 
	[ (mvr_primary,mvr_primary,None) ] 
    | _ -> [] ) in
  
  let rec inductive_types_used_in_element e : (string*string*(string option)) list = 
    ( match e with
    | Lang_nonterm (ntr_primary,_) -> 
	let ntr = Auxl.promote_ntr xd ntr_primary in
	if List.mem ntr (List.map (fun r -> r.rule_ntr_name) rule_set) 
	then [ (ntr, ntr, None) ]
	else []
    | Lang_metavar (mvr_primary,_) -> 
	[]
    | Lang_terminal _ -> []
    | Lang_option es -> [ "","<<<option unimplemented>>>",None ] 
    | Lang_sugaroption es -> []
    | Lang_list elb -> 
	let l = List.flatten (List.map used_in_tuple elb.elb_es) in
	if List.exists (fun (n,_,_) -> List.mem n (List.map (fun r -> r.rule_ntr_name) rule_set)) l 
	then
	  ( match List.length l with
	  | 0 -> []
	  | 1 -> [ "list_"^((fun (x,_,_) -> x) (List.hd l)), 
		   "list "^((fun (_,x,_) -> x) (List.hd l)), 
		   Some ((fun (_,x,_) -> x) (List.hd l)) ]
	  | _ -> [ "list_" ^ String.concat "_" (List.map (fun (x,_,_) -> x) l), 
		   "list (" ^ String.concat "*" (List.map (fun (_,x,_) -> x) l) ^")",
		   Some (String.concat "*" (List.map (fun (_,x,_) -> x) l)) ] )
	else [] )
  in
  let inductive_types_used_in_prod p =
    if p.prod_meta 
    then []
    else 
      Auxl.remove_duplicates 
	(List.flatten (List.map inductive_types_used_in_element p.prod_es)) in
  let inductive_types_used_in_rule r =
    Auxl.remove_duplicates 
      (List.flatten (List.map inductive_types_used_in_prod r.rule_ps)) in

  let pre_declarations =
    Auxl.remove_duplicates
      ( (List.map 
	   (fun r -> (r.rule_ntr_name, (Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name), None))
	   rule_set)
	@
	  (List.flatten 
	     (List.map
		(fun r -> inductive_types_used_in_rule r)
		rule_set))) in

  let variables_assoc =
    List.map
      (fun (n,s,_) -> (s,"P_"^n))
      pre_declarations in
  let list_types_used =
    Auxl.option_map
      (fun (_,_,l) -> l)
      pre_declarations in
  
  let variables_declaration = 
    "Variables\n  "
    ^ String.concat "\n  "
	(List.map
	   (fun (n,s,_) -> "(P_"^n^" : " ^ s ^" -> Prop)")
	   pre_declarations)
    ^ ".\n"
  in

  (* ** Hypothesis ** *)
  let make_hypothesis r p =
    let conc_stnb = 
      Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in 
    let conc_st = St_node(dummy_loc,conc_stnb) in
    let ((de1,de2) as de,de3,pptbe) =
      Bounds.bound_extraction m xd dummy_loc [conc_st]  in
    let conc_st = Grammar_pp.pp_symterm m xd [] de conc_st in
    
    let var_list = 	
      Grammar_pp.extract_quantified_proof_assistant_vars m xd de1 de2 de3 in

    let hyp =
      String.concat ""
	(List.map
	   (fun (v,_,(t,_)) -> 
	     "forall (" ^ v ^":"^t^"), " 
	     ^ (try List.assoc t variables_assoc ^" "^v^" -> " with Not_found -> ""))
	   var_list) in
    (* build conclusion *)
    let v = Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name in
    let conc = 
      (try List.assoc v variables_assoc with Not_found -> "<<<"^v^">>>") ^ " "
      ^ conc_st in
    hyp ^ conc in
  let hypothesis_used_in_rule r =
    Auxl.option_map 
      (fun p -> 
	if p.prod_meta then None
	else Some (Grammar_pp.pp_prodname m xd p.prod_name, 
		   make_hypothesis r p) ) 
      r.rule_ps in  
  let hypothesis_from_rules = 
    String.concat "\n  "
      (List.flatten
	 (List.map
	    (fun r ->
	      (List.map 
		 (fun (n,s) -> "(H_"^n^" : " ^ s ^")")
		 (hypothesis_used_in_rule r)))
	    rule_set)) in

  let make_index = (* move to aux ? *)
    let is = ref [] in
    let intr s =
      try
 	let ix = List.assoc s !is in
 	ix := !ix + 1;
 	!ix
      with Not_found -> begin
 	let ix = ref 0 in
 	is := ((s,ix)::!is);
 	!ix end in
    fun s -> intr s in

  let hypothesis_from_list_types = 
    String.concat "\n"
      (List.map 
	 (fun t -> 
	   let types = Str.split (Str.regexp "(\\|*\\|)") t in (* FZ *)
	   let vars_types = List.map (fun t -> (t^(string_of_int(make_index t)), t)) types in
	   let n = String.concat "_" types in
	   let xl,tl = n^"_l", "list "^(if List.length types = 1 then t else "("^t^")") in
	   "  (H_list_"^n^"_nil : P_list_"^n^" nil)\n"
	   ^ "  (H_list_"^n^"_cons : " 
	   ^ (String.concat "" 
		(List.map 
		   (fun (v,t) -> 
		     "forall ("^v^":"^t^"), " 
		     ^ (try List.assoc t variables_assoc ^" "^v^" -> " with Not_found -> ""))
		   vars_types))
	   ^ "forall ("^xl^":" ^tl^"), "
	   ^ (try List.assoc tl variables_assoc ^" "^xl^" -> " with Not_found -> "")
	   ^ (try List.assoc tl variables_assoc ^" (cons "
	     ^ (if List.length types = 1 
	     then fst (List.hd vars_types) 
	     else "("^(String.concat "," (List.map fst vars_types))^")")
	     ^" "^xl^")" with Not_found -> "<<>>" )
	   ^")" )  
	 list_types_used)
  in
  
  let hypothesis_declaration = 
    "Hypothesis\n  "
    ^ hypothesis_from_rules ^"\n"
    ^ hypothesis_from_list_types
    ^ ".\n" 
  in

  (* ** Fixpoint ** *)
  let function_int = 
    List.map 
      (fun r ->
	let name = Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name in
	let ind_ip = List.assoc name variables_assoc in
	let clauses = 
	  List.map
	    (fun p -> 
	      (* synthesize lhs *)
	      let lhs_stnb = 
		Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in 
	      let lhs_st = St_node(dummy_loc,lhs_stnb) in
	      let ((de1,de2) as de,de3,pptbe) 
		  = Bounds.bound_extraction m xd dummy_loc [lhs_st]  in
	      let lhs = Grammar_pp.pp_symterm m xd [] de lhs_st in
	      (* extract quantified vars *)
	      let var_list = Grammar_pp.extract_quantified_proof_assistant_vars m xd de1 de2 de3 in
	      (* generate induction calls *)
	      let var_list_ext =
		Auxl.option_map (fun x -> x)
		  (List.flatten 
		     (List.map 
			(fun (v,_,(t,l)) -> 
			  [ Some v; 
			    ( match l with
			    | Some lt ->
				let types = Str.split (Str.regexp "(\\|*\\|)") lt in (* FZ *)
				let vars_types = List.map (fun t -> (t^(string_of_int(make_index t)), t)) types in
				if List.exists 
				    (fun t -> List.mem t (List.map (fun r -> r.rule_ntr_name) rule_set))
				    types 
				then
				  (* list recursion *)
				  let name_l = v^"_ott_ind" in
				  let n = String.concat "_" types in
				  let l_arg = n^"_l" in

(* 				    print_endline ("*** "^t^ "\n "  *)
(* 						   ^(String.concat "\n * "  *)
(* 						       (List.map (fun (v,t) -> v^"="^t) variables_assoc))); *)

				  Some
				    ( "(((fix "^name_l^" ("^l_arg^":"^t^") : " 
				      ^ (List.assoc t variables_assoc) ^ " "^l_arg^" := "  (* FZ freshen xl *)
				      ^ "match "^l_arg^" as x return "^(List.assoc t variables_assoc) ^ " x with "
				      ^ "nil => H_list_"^n^"_nil" 
				      ^ ( " | cons "
					  ^ (if List.length types = 1 
					  then fst (List.hd vars_types) 
					  else "("^(String.concat "," (List.map fst vars_types))^")") 
					  ^ " xl" ^ " =>" ) 
				      ^ " H_list_"^n^"_cons " 
				      ^ (String.concat " " 
					   (List.map 
					      (fun (v,t) ->
						v 
						^ (if List.mem t (List.map (fun r -> r.rule_ntr_name) rule_set)
						then "("^t^"_ott_ind "^v^")" 
						else " "))
					      vars_types))
(*						" x "  ^ (try "("^n^"_ott_ind x) " with Not_found -> "") ) *)

				      ^ "xl ("^name_l^" xl) "
				      ^ "end)) "^v^")"
				     )
				else None
			    | None ->
				(* nonterm recursion *)
				if List.mem t (List.map (fun r -> r.rule_ntr_name) rule_set)
				then Some ("("^t^"_ott_ind "^v^")")
				else None ) ])
			var_list)) in

	      let rhs = "H_" ^ p.prod_name ^ " " ^ String.concat " " var_list_ext in

	      (* all together *)
	      ("", lhs, rhs)
	    )
	    (List.filter (fun p -> not p.prod_meta) r.rule_ps) in

	{ r_fun_id = name ^ "_ott_ind";
	  r_fun_dep = (List.map 
			 (fun r -> (Grammar_pp.pp_nontermroot_ty m xd r.rule_ntr_name) ^ "_ott_ind") 
			 rule_set);
	  r_fun_type = name;
	  r_fun_header = (name ^ "_ott_ind (n:"^r.rule_ntr_name^") : " ^ ind_ip ^ " " ^ "n :=\n",
			  "", 
			  "  match n as x return "^ind_ip^" x with\n"); (* FZ freshen n x *)
	  r_fun_clauses = clauses
	})
      rule_set in

  let function_definition = 
    Dependency.compute m xd 
      (Dependency.collapse m xd 
	 { i_funcs = function_int;
	   i_funcs_proof = None }) in

  (* ** all together ** *)
  "Section " ^ ip_name ^ ".\n\n"
  ^ variables_declaration ^ "\n"
  ^ hypothesis_declaration ^ "\n"
  ^ function_definition 
  ^ "End " ^ ip_name ^ ".\n"

(* ** All together ** *)
let pp_induction m xd rs =
  String.concat "\n\n" (List.map (generate_induction m xd) (rules_needing_induction m xd rs))
