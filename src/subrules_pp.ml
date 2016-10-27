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


exception ThisCannotHappen;;

open Location;;
open Types;;
(* open Lexicalgoo;; *)

(* find all the primary nonterminal roots of a language that have
non-free definitions, ie the smallest set of ntrs that contains those
that either:

- occur on the left of a <:: relation
- have a production that mentions a non-free ntr

and for each, pair it with the ntr of the free Isabelle type that
we're carving out a predicate of 
*)

let non_free_ntrs : pp_mode -> syntaxdefn -> subrule list -> (nontermroot * nontermroot) list =
  fun m xd srs ->
      
    let rs = List.filter (function r -> (not r.rule_meta)&& (Auxl.hom_spec_for_pp_mode m r.rule_homs = None)) xd.xd_rs  in 
    
    let mentions : (nontermroot * NtrSet.t) list =
      List.map 
        (function r -> r.rule_ntr_name, Auxl.primary_ntrs_used_in_rule xd false None false r) 
        rs in
      
    (* the closure function that we want a fixed point of *)
    let f : NtrSet.t -> NtrSet.t =
      fun ntrs0 ->
        let non_free = 
          Auxl.option_map 
            (function (ntr,ntrs) -> 
              if NtrSet.is_empty (NtrSet.inter ntrs0 ntrs) then None 
              else Some ntr) 
            mentions in
        NtrSet.union ntrs0 (ntrsetoflist non_free) in

    (* the fixed point starting from the left side of xd.xd_srs *)
    let ntrs0 = ntrsetoflist 
        (List.map (function sr -> sr.sr_lower) srs) in
    
    let rec fixedpoint : (NtrSet.t -> NtrSet.t) -> NtrSet.t -> NtrSet.t =
      fun f x ->
        let x' = f x in
        if NtrSet.equal x x' then x' else f x' in
    
    (* all the non_free ntrs that are _not_ on the left of a <:: *)
    let non_ntrs0_non_free_ntrs' = NtrSet.diff (fixedpoint f ntrs0) ntrs0 in
    
    (* ... paired with themselves *)
    let non_ntrs0_non_free_ntrs = 
      List.map 
        (function x->x,x) 
        (NtrSet.elements non_ntrs0_non_free_ntrs') in
    
    (* all the non_free ntrs that are on the left of a <::, paired with the thing at the top *)
    let ntrs0_non_free_ntrs = 
      List.map 
        (function sr -> sr.sr_lower,sr.sr_top (*sr.sr_upper*)) 
        srs in
    
    ntrs0_non_free_ntrs @ non_ntrs0_non_free_ntrs
        
let debug xd (nt,ntl,(_,s)) =
  Auxl.debug ("*** " ^ (Grammar_pp.pp_nontermroot_ty error_opts xd nt) ^ "\n");
  Auxl.debug ("* " ^ (String.concat ", " (List.map (Grammar_pp.pp_nontermroot_ty error_opts xd) ntl)) ^ "\n");
  Auxl.debug s;
  Auxl.debug "\n"


let pp_subrules m xd srs : int_funcs_collapsed =

  (*pp_source_locations m (List.map (function sr -> sr.sr_loc) srs);*)
  let non_free_ntrs = non_free_ntrs m xd srs in
  
  (* used to add suffixes when splitting functions over the same list type in a production *)
  let list_split_inprod_counter = ref [] in 

  (* remark: these functions assume the arguments are in fact in the sub
     relationship *)

  let rec pp_subelement = 
    fun sie de isa_list_name_flag pu srl sru el eu -> match el,eu with
      Lang_nonterm (ntrpl,ntl), Lang_nonterm (ntrpu,ntu) -> 
        (* TODO: THIS IS PROBABLY WRONG WRONG WRONG *)
(*         if  (ntrpl=ntrpu) then  *)
(*           try  *)
(*             let ntr_upper = List.assoc ntrpl non_free_ntrs in *)
(*             [ "(" ^ (Auxl.pp_is ntrpl (Auxl.promote_ntr xd ntrpu)) ^ " "  *)
(*               ^ Grammar_pp.pp_nonterm_with_sie m xd sie ntu  *)
(* 	      ^ ")"], [Auxl.pp_is ntrpl (Auxl.promote_ntr xd ntrpu)], [] *)
(*           with Not_found -> [],[],[] *)
(*         else if  *)
(*           List.exists  *)
(*             (function sr -> sr.sr_lower=ntrpl && sr.sr_upper=ntrpu)  *)
(*             xd.xd_srs  *)
(*         then  *)
(*           [ "(" ^ (Auxl.pp_is ntrpl (Auxl.promote_ntr xd ntrpu)) ^ " "  *)
(*             ^ Grammar_pp.pp_nonterm_with_sie m xd sie ntu ^")"],  *)
(*           [Auxl.pp_is ntrpl (Auxl.promote_ntr xd ntrpu)], [] *)
(*         else [],[],[] *)

        (try
          let ntr_upper = List.assoc ntrpl non_free_ntrs in
          [ "(" ^ (Auxl.pp_is ntrpl ntr_upper) ^ " " 
            ^ Grammar_pp.pp_nonterm_with_sie m xd sie ntu 
	    ^ ")"], [Auxl.pp_is ntrpl ntr_upper], []
        with Not_found -> [],[],[])

    | Lang_metavar _, Lang_metavar _ -> [],[],[]
    | Lang_terminal _, Lang_terminal _ -> [],[],[]
    | Lang_option els', Lang_option eus' -> pp_subelements sie de isa_list_name_flag pu els' eus' srl sru
    | Lang_sugaroption tml', Lang_sugaroption tmu' -> [],[],[]
    | Lang_list elbl, Lang_list elbu -> 

        (* we depend here on multiple list constructs within a *)
        (* single production having different bounds - which should be *)
        (* checked, but probably isn't yet... *)

        let (de1,de2)=de in
        let bound = 
          (match elbl.elb_boundo with 
          | Some bound -> bound
          | None -> failwith "null bounds in pp_subelement")  in
        let de1i = Grammar_pp.de1_lookup de1 bound in
        let conjuncts, deps, funcs = 
          pp_subelements ((Si_var ("_",0))::sie) de isa_list_name_flag pu elbl.elb_es elbu.elb_es srl sru in
        let conjuncted_conjuncts = 
	  if conjuncts = [] then Auxl.pp_true m false
	  else 
	    String.concat (Auxl.pp_and m false) conjuncts in
        ( match m with 
        | Isa io when io.ppi_isa_primrec ->
	    let typ = 
	      Auxl.the (Grammar_pp.pp_elements 
	       	 m xd  ((Si_punct "_")::sie) elbu.elb_es true false true true) ^ " list" in
	    let args = 
	      String.concat "_" 
		(List.map (fun (x,y) -> 
		  Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_punct "")::sie) x) de1i.de1_ntmvsns) in
	    let post_name =  (* promoted args *)
	      String.concat "_" 
		(List.map (fun ((r,s),y) -> Grammar_pp.pp_nt_or_mv_root m xd (Auxl.promote_ntmvr xd r))
(*		  Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_punct "")::sie)  *)
(*		  ((Auxl.promote_ntmvr xd r), s))  *)
		   de1i.de1_ntmvsns) in
           
	    let split_suffix = 
	      let pre_split_suffix = 
		if isa_list_name_flag then "_"^pu.prod_name else "" in
	      let counter_suffix = 
		try 
		  let c_p = List.assoc (typ^pre_split_suffix) !list_split_inprod_counter in
		  c_p := !c_p + 1;
		  string_of_int (!c_p)
		with Not_found -> (
		  list_split_inprod_counter := ((typ^pre_split_suffix),ref 0)::!list_split_inprod_counter;
		  "" )
	      in
	      pre_split_suffix ^ counter_suffix in

	    let id = (Auxl.pp_is srl post_name) ^ "_list" ^ split_suffix in  

	    let (rhs_sc,tuple_aux_fun, list_deps) =
	      if List.length de1i.de1_ntmvsns = 1 
	      then conjuncted_conjuncts, [], deps 
	      else (* build an aux funcs over the tuple *)
                begin
                  let list_names = 
                    (List.map (fun ((r,s),y) -> 
		      Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_punct "")::sie) 
		        ((Auxl.promote_ntmvr xd r), s)) 
		       de1i.de1_ntmvsns) in
                  let list_patterns = 
		    (List.map (fun (x,y) -> 
		      Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_punct "")::sie) x) de1i.de1_ntmvsns) in
(*                     Str.split (Str.regexp "(\\|,\\|)") pp_pattern in *)
                  let list_types = 
                    Str.split (Str.regexp "(\\|*\\|)")
	              (Auxl.the (Grammar_pp.pp_elements 
	       	                  m xd  ((Si_punct "_")::sie) elbu.elb_es true false true true)) 
                  in

                  let rec make_tuple_func l_names l_patterns l_types elbl_es elbu_es =  

                    let name = 
		      Auxl.pp_is srl ((List.hd l_types) ^ "_" ^ (String.concat "_" (List.tl l_types))) ^ split_suffix in

                    if List.length l_names = 2 
                    then 	
	              let typ = "(" ^ String.concat "*" l_types ^ ")" in 
                      let lhs = "(" ^ String.concat "," 
					(List.map 
					   (fun s -> Auxl.hide_isa_trailing_underscore m (s^"_")) 
					   l_patterns) ^ ")" in
                      let rhs, deps =
                        let conjuncts, deps, funcs = 
                          pp_subelements ((Si_var ("_",0))::sie) de isa_list_name_flag pu elbl_es elbu_es srl sru in
	                if conjuncts = [] 
                        then "True", deps
	                else 
			  if List.length conjuncts = 1 
			  then (List.hd conjuncts), deps
			  else ("(" ^ String.concat " & " conjuncts^")", deps) in

                      "(" ^ name ^ " " ^ Auxl.hide_isa_trailing_underscore m (args ^ "_")^")",
		      [ { r_fun_id = name;
		          r_fun_dep = deps;
		          r_fun_type = typ^split_suffix;
		          r_fun_header = (name ^ " :: \"" ^ typ ^ " => bool\"\n","","");
		          r_fun_clauses = [ "", lhs, rhs ] } ], 
		      [ name ]
                        
                    else
                      let typ = "(" ^ (List.hd l_types) ^ "*(" ^ String.concat "*" (List.tl l_types) ^ "))" in 
                      let dep_lhs = Auxl.hide_isa_trailing_underscore m ((String.concat "_" (List.tl l_patterns))^"_") in

                      let lhs = 
			"(" 
			^ Auxl.hide_isa_trailing_underscore m ((List.hd l_patterns)^"_") 
			^ "," ^ dep_lhs ^ ")" in
                      let (r,f,d) = make_tuple_func 
                          (List.tl l_names) (List.tl l_patterns) (List.tl l_types) 
                          (Auxl.skip_nt_mv elbl_es) (Auxl.skip_nt_mv elbu_es) in
                      let dep_name = 
			(Auxl.pp_is srl (String.concat "_" (List.tl l_types))) ^ split_suffix in

                      let rhs,deps =
                        let rec_call = 
                          let c,d,f = 
                            pp_subelement ((Si_var ("_",0))::sie) de isa_list_name_flag pu srl sru (Auxl.head_nt_mv elbl_es) (Auxl.head_nt_mv elbu_es) in
                          if c = [] 
                          then ""
                          else (String.concat " & " c) ^ " & " (* c has at most length one *) in
                        rec_call ^ "("^dep_name ^" "^dep_lhs^")", (dep_name::d)
                      in

                      "(" ^ name ^ " " ^ (Auxl.hide_isa_trailing_underscore m (args ^ "_")) ^")", 
		      ( { r_fun_id = name;
		          r_fun_dep = deps;
		          r_fun_type = typ^split_suffix;
		          r_fun_header = (name ^ " :: \"" ^ typ ^ " => bool\"\n","","");
		          r_fun_clauses = [ "", lhs, rhs ] } :: f ),  
		      [ name ]
	          in
                  make_tuple_func list_names list_patterns list_types elbl.elb_es elbu.elb_es
                end
	    in
	    [ id ^ " " ^ de1i.de1_compound_id ],
	    id::deps,  
	    { r_fun_id = id;
	      r_fun_dep = id :: list_deps;
	      r_fun_type = typ^split_suffix;
	      r_fun_header = (id ^ " :: \"" ^ typ ^ " => bool\"\n","","");
	      r_fun_clauses = 
	      [ ("", "Nil", "True" );
		("", "("^Auxl.hide_isa_trailing_underscore m (args^"_")^"#"^Auxl.hide_isa_trailing_underscore m (de1i.de1_compound_id^"_")^")", 
		 "("^rhs_sc
		 ^ " & " ^ "(" ^ id ^" " ^ Auxl.hide_isa_trailing_underscore m(de1i.de1_compound_id ^"_")^"))"  ) ] } :: tuple_aux_fun 
        | Isa io when not io.ppi_isa_primrec ->
	    [ "(list_all (% "^de1i.de1_pattern^ " . "^conjuncted_conjuncts ^") "
	      ^ de1i.de1_compound_id
	      ^ ")"], deps, []
        | Hol _ ->
            [ "(EVERY (\\"^de1i.de1_pattern^". "^conjuncted_conjuncts^") "
	      ^ de1i.de1_compound_id
	      ^ ")"], deps, []
        | Caml _ ->
            [ "(List.for_all (fun "^de1i.de1_pattern^" -> "^conjuncted_conjuncts^") "
	      ^ de1i.de1_compound_id
	      ^ ")"], deps, []
        | Lem _ ->
            [ lemTODO "15" (" (List.all (fun "^de1i.de1_pattern^" -> "^conjuncted_conjuncts^") "
	      ^ de1i.de1_compound_id
	      ^ ")")], deps, []
	| Coq co when not co.coq_expand_lists ->
	    let e = 
	      if List.length (Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern) = 1
	      then 
		"(forall_list (fun ("^de1i.de1_pattern^":"^de1i.de1_coq_type_of_pattern^") => "^conjuncted_conjuncts^") "
		^ de1i.de1_compound_id
		^ ")"
	      else
		"(forall_list (fun (pat_:"^de1i.de1_coq_type_of_pattern^") => match pat_ with "^de1i.de1_pattern^" => " ^conjuncted_conjuncts^" end) "
		^ de1i.de1_compound_id
		^ ")"
	    in
            [e], deps, []

        | Coq co when co.coq_expand_lists ->
	    let ty_list = Str.split (Str.regexp "(\\|*\\|)") de1i.de1_coq_type_of_pattern in
	    let var_list = Str.split (Str.regexp "(\\|,\\|)") de1i.de1_pattern in

	    let suf = "list_" ^ (String.concat "_" ty_list) in

	    let typ = (*Auxl.pp_coq_type_name*) suf in

	    let args = 
	      String.concat "_" 
		(List.map (fun (x,y) -> 
		  Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_punct "")::sie) x) de1i.de1_ntmvsns) in
	    let post_name =  (* promoted args *)
	      String.concat "_" 
		(List.map (fun ((r,s),y) -> 
		  Grammar_pp.pp_nt_or_mv_with_sie m xd ((Si_punct "")::sie) 
		    ((Auxl.promote_ntmvr xd r), s)) 
		   de1i.de1_ntmvsns) in
            let name = (Auxl.pp_is srl post_name) in
	    let id = name ^ "_list" in  

	    let header = 	
	      ( id ^ " (l:" ^ typ ^ ")", 
		"", 
		" : Prop :=\n" 
		^ "  match l with\n" )  
	    in

	    [ id ^ " " ^ de1i.de1_compound_id ],
	    id::deps,  
	    [ { r_fun_id = id;
		r_fun_dep = id :: deps (* list_deps *);
		r_fun_type = typ;
		r_fun_header = header;
		r_fun_clauses = 
		[ ("", "Nil_"^suf, "True" );
		  ("", "Cons_"^suf^ " " ^ (String.concat " " var_list)^" "^de1i.de1_compound_id^"_", 
		   conjuncted_conjuncts
		   ^ " /\\ " ^ "(" ^ id ^" " ^ de1i.de1_compound_id ^"_)" ) ] } ] (* :: tuple_aux_fun *)
        | Twf _ ->
            [ " %{ TWELF NOT IMPLEMENTED }%"], deps, []
        | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_subelement"

 )
    | _,_ -> raise (Invalid_argument "pp_subelement")
	  
  and pp_subelements : suffix_index_env -> dotenv -> bool -> prod -> element list -> element list -> nontermroot -> nontermroot -> string list * nontermroot list * int_func list
      = fun sie de isa_list_name_flag pu els eus srl sru -> 
	(fun (a,b,c) -> (List.flatten a), (List.flatten b), (List.flatten c))
	  (Auxl.split3 (List.map2 (pp_subelement sie de isa_list_name_flag pu srl sru) els eus)) in
  
  let pp_subprod : dotenv -> bool -> prod -> prod -> nontermroot -> nontermroot -> string list * nontermroot list * int_func list
      = fun de isa_list_name_flag pl pu srl sru -> 
	list_split_inprod_counter := [];
	pp_subelements [] de isa_list_name_flag pu pl.prod_es pu.prod_es srl sru in
  
  let pp_subrule : nontermroot -> nontermroot -> int_func list =
    fun srl sru ->
      
      let rl = Auxl.rule_of_ntr xd srl in
      let ru = Auxl.rule_of_ntr xd sru in
      
      let dep = ref [] in
      let funcs = ref [] in

      let isa_list_name_flag = Auxl.compute_isa_list_name_flag ru in
(*      print_endline ("************* "^srl^" "^sru^" "^(string_of_bool isa_list_name_flag)); *)

      let clauses = 
        (* iterate over each production of ru, for each finding all the productions of rl 
           that are subprods of it; disregard all productions with the meta flag set *)
        (List.flatten (List.map
	   (function pu -> 
	     (* pls set of prod in rl that "match" pu *)
             let pls = List.filter 
                 (function pl->Grammar_typecheck.subprod xd.xd_srd.srd_subrule_graph pl pu)
                 rl.rule_ps in
             let pls = List.filter 
                 (function p -> not (p.prod_meta))
                 pls in
	     
             (* construct a case of is_sru as a disjunction over these different pls possibilities *)
	     
             (* the lhs is constructed by synthesising a *)
             (*  canonical symterm from the production and then pping that *)
             let lhs_stnb = 
               Grammar_pp.canonical_symterm_node_body_of_prod sru pu in 
             let lhs_st = St_node(dummy_loc,lhs_stnb) in
             let ((de1,de2) as de,de3,pptbe) 
                 = Bounds.bound_extraction m xd dummy_loc [lhs_st] in

             let lhs = Grammar_pp.pp_symterm m xd [] de lhs_st in
	     
             let rhss =
               List.map 
                 (function pl -> (
		   let conjuncts,deps,new_funcs = (pp_subprod de isa_list_name_flag pl pu srl sru) in 
                   (* FZ: I pass around srl and sru to easily build the list functions for isa *)
                   (* FZ: not sure this is really needed though *)
		   dep := deps @ !dep;
		   funcs := !funcs @ new_funcs;
                   match m with 
                   | Coq _ | Hol _ | Lem _| Isa _ | Caml _ -> 
		       if conjuncts = [] 
                       then Auxl.pp_true m false
		       else String.concat (Auxl.pp_and m false) conjuncts
                   | Twf _ -> String.concat "" (List.map (function s -> " <- "^s) conjuncts)
                   | Lex _ | Yacc _ | Tex _ | Ascii _ -> Auxl.errorm m "pp_subrule"
                  ))
                 pls in

             match m with 
             | Coq _ | Hol _ | Lem _ | Isa _ | Caml _ -> 
                 let rhs = 
                   if rhss = [] 
                   then Auxl.pp_false m false
	           else if List.length rhss = 1 then "("^(List.hd rhss)^")"
                   else String.concat (Auxl.pp_or m false) (List.map (fun s -> "("^s^")") rhss)
                 in
	         
	         [("", lhs, rhs)]
             | Twf _ -> 
		 let pfx = pu.prod_name in 
                 List.map (fun rhs -> (pfx, lhs,rhs)) rhss
             | Ascii _ | Tex _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_subrule"
           )
	   (List.filter (function p->not (p.prod_meta)) ru.rule_ps))) in
      
      let srln = Grammar_pp.pp_nontermroot_ty m xd srl in
      let srlu = Grammar_pp.pp_nontermroot_ty m xd sru in
   
      let header =
	( match m with 
	| Isa _ -> 
	    ( Auxl.pp_is srl sru ^ " :: \"" 
	      ^ Grammar_pp.pp_nontermroot_ty m xd sru
	      ^ " => bool\"\n", "","")
        | Hol _ -> ("","","")
	| Lem _ (* -> ("","","") *)
	| Caml _ -> 
            let nts_used = Context_pp.nts_used_in_lhss m xd ru in
(*	    let nts_used = Auxl.nts_used_in_rule ru in *)
            let fresh_var_ntr = Auxl.secondary_ntr xd sru in
	    let fresh_var = Auxl.fresh_nt nts_used (fresh_var_ntr,[]) in 
	    ( Auxl.pp_is srl sru 
              ^ lemTODOm m "16" " (" ^ Grammar_pp.pp_nonterm m xd fresh_var 
              ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd sru ^ ")",
              "",
              " : bool =\n"
	      ^ "  match " ^ Grammar_pp.pp_nonterm m xd fresh_var ^ " with\n" )
	| Coq co -> 
            let nts_used = Context_pp.nts_used_in_lhss m xd ru in
(*	    let nts_used = Auxl.nts_used_in_rule ru in *)
            let fresh_var_ntr = Auxl.secondary_ntr xd sru in
	    let fresh_var = Auxl.fresh_nt nts_used (fresh_var_ntr,[]) in (* FZ Substs_pp *)
	    ( Auxl.pp_is srl sru 
              ^ " (" ^ Grammar_pp.pp_nonterm m xd fresh_var 
              ^ ":" ^ Grammar_pp.pp_nontermroot_ty m xd sru ^ ")",
              "",
              " : " 
	      ^ (if co.coq_expand_lists then "Prop :=\n" else "bool :=\n")
	      ^ "  match " ^ Grammar_pp.pp_nonterm m xd fresh_var ^ " with\n" ) 
        | Twf _ -> 
	    ( Auxl.pp_is srl sru ^ " : " 
	      ^ Grammar_pp.pp_nontermroot_ty m xd sru
	      ^ " -> type.\n", "","")
        | Tex _ | Ascii _ | Lex _ | Yacc _ -> Auxl.error "pp_subprod"
         ) in


(*
      let match_end =
	( match m with 
	| Lem _ -> Some "end" 
	| Isa _| Hol _ 
	| Caml _ | Coq _ 
        | Twf _ 
        | Tex _ | Ascii _ | Lex _ | Yacc _ -> None
         ) in
*)
      
      let id = Auxl.pp_is srl sru in
      
      { r_fun_id = id;
	r_fun_dep = !dep;
	r_fun_type = sru;
	r_fun_header = header;
	r_fun_clauses = clauses } :: !funcs in
 
  Dependency.collapse m xd
    { i_funcs = (List.concat 
		   (List.map
		      ( function ntr_lower,ntr_upper -> pp_subrule ntr_lower ntr_upper )
		      non_free_ntrs));
      i_funcs_proof = None }

