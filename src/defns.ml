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

exception NotImplementedYet;;

exception Rule_parse_error of string

open Types;;
open Location;;

let rec iter_nosep f l =
  match l with [] -> () | x::l -> let _ = f x in iter_nosep f l

let rec iter_sep f (s:string) l =
  match l with [] -> () | x::l -> if f "" x then iter_nosep (f s) l else iter_sep f s l

let iter_asep fd s f l = match l with
  | [] -> () 
  | x::l -> f x; List.iter (fun x -> output_string fd s; f x) l

(* library functions *) 

(*
let pp_list_all_coq =
    "Definition list_all (A:Set) (p:A->Prop) :=\n"
  ^ "  fix list_all (l:list A) : Prop :=\n"
  ^ "  match l with\n"
  ^ "  | nil => True\n"
  ^ "  | cons a l' => p a /\\ list_all l'\n"
  ^ "  end.\n"
  ^ "Implicit Arguments list_all.\n\n"
 
let pp_list_all m = match m with 
  | Coq co -> Auxl.add_to_lib co.coq_library "list_all" pp_list_all_coq
  | _ -> Auxl.errorm m "pp_list_all"
*)

let rn_formula="formula"

(** ******************************** *)
(** pretty printing of definitions   *)
(** ******************************** *)

let pp_subntr (m: pp_mode) (xd: syntaxdefn): (nontermroot * nontermroot * nonterm) -> string = 
    function (ntrl,ntru,(ntr',suff)) ->
      let s = 
	Auxl.pp_is ntrl ntru ^ " " 
	^ Auxl.hide_isa_trailing_underscore m
	    (( match m with Twf _ -> String.uppercase ntr' 
	    | Coq _ | Isa _ | Hol _ | Lem _ -> ntr'
	    | Caml _ | Tex _ | Ascii _ | Lex _ | Yacc _ -> raise Auxl.ThisCannotHappen )
	     ^ Grammar_pp.pp_suffix_with_sie m xd Bounds.sie_project suff)
      in ( match m with
      | Coq co when not co.coq_expand_lists -> "Is_true ("^s^")"
      | _ -> s )
          
let pp_listsubntr : pp_mode -> syntaxdefn -> ((nontermroot * nontermroot * nonterm) list * string * string * string) list -> string list =
  fun m xd listsubntrs -> 
    let clauses = 
      List.flatten
        (List.map 
           (function (subntrs,pp_squished_vars,pp_pattern,coq_type_pattern) ->
             List.map
               (function subntr ->
                 match m with
                 | Ascii _ | Tex _ | Caml _ | Twf _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_listsubntr"
                 | Isa _ -> 
(* Tobias says: should use  "ALL x : set xs. P x" rather than "list_all P xs", so...: *)
(* TODO: choose a better internal name than x__ *)
                     "List.list_all "
                     ^ "(%"^pp_pattern^". "^pp_subntr m xd subntr^") "
                     ^ pp_squished_vars
                         
(*                            "(ALL x__ : set "^pp_squished_vars *)
(*                            ^ ".  let "^pp_pattern^"=x__ in " *)
(*                            ^ pp_subntr m xd subntr^")" *)
                              
                 | Hol _ -> 
                     "EVERY "
                     ^ "(\\"^pp_pattern^". "^pp_subntr m xd subntr^") "
                     ^ pp_squished_vars

                 | Lem _ -> 
                     lemTODO "1" "List.all "
                     ^ "(fun "^pp_pattern^" -> "^pp_subntr m xd subntr^") "
                     ^ pp_squished_vars

                 | Coq co -> 
	             let ty_list = Str.split (Str.regexp "(\\|*\\|)") coq_type_pattern in
	             if String.contains coq_type_pattern '*' 
 	             then begin
                       "(Forall (fun (tmp_:"^coq_type_pattern^") => match tmp_ with "
		       ^ pp_pattern ^ " => "
		       ^ pp_subntr m xd subntr ^ " end) "
		       ^ ( if co.coq_expand_lists 
		           then "(unmake_list_"^(String.concat "_" ty_list)^" "^ pp_squished_vars^")"
		           else pp_squished_vars )
		       ^ ")"
	             end else begin
	               "(Forall (fun ("^pp_pattern^":"^coq_type_pattern^") => "  (* FZ too many parentheses *)
		       ^ pp_subntr m xd subntr ^ ") "
		       ^ ( if co.coq_expand_lists 
		           then "(unmake_list_"^(String.concat "_" ty_list)^" "^ pp_squished_vars^")"
		           else pp_squished_vars )
		       ^ ")"
	             end)
               subntrs)
           listsubntrs) in
    clauses

(* this function collapses (e1:term) (e2:term) into (e1 e2:term) *)
(* it is used when pp Coq forall quantifications in definitions *)
let rec collapse_quantifications l =
  let rec collapse_none l = match l with 
    | [] -> []
    | (v,None)::tl -> ([v],None)::(collapse_none tl) 
    | (v,Some t)::tl -> collapse_some [v] t tl
  and collapse_some b t l = match l with 
    | [] -> [(b, Some t)]
    | (v, None)::tl -> (b,Some t)::([v],None)::(collapse_none tl) 
    | (v, Some t1)::tl -> 
        if String.compare t t1 = 0 
        then collapse_some (b@[v]) t1 tl
        else (b,Some t)::(collapse_some [v] t1 tl) 
  in 
  collapse_none l


let pp_drule fd (m:pp_mode) (xd:syntaxdefn) (dr:drule) : unit =
(*   print_endline ("&*"^dr.drule_name); *)
(*   print_endline (String.concat "\n" (List.map Grammar_pp.pp_plain_symterm dr.drule_premises));  *)
(*   print_endline (Grammar_pp.pp_plain_symterm dr.drule_conclusion);  *)

  if !Global_option.output_source_locations >=1 then Printf.fprintf fd "\n%s" (Grammar_pp.pp_source_location m dr.drule_loc);

  let (((de1:dotenv1),de2) as de,de3,pptbe) = 
    Bounds.bound_extraction m xd dr.drule_loc (dr.drule_conclusion::List.map snd dr.drule_premises) in

  (* FZ hack to get the right quantification when pp formula_dots in Coq using native lists *)
  ( match m with
  | Coq co when not co.coq_expand_lists ->
      co.coq_quantified_vars_from_de := 
	List.map (fun (x,_,_) -> x)
	  (Grammar_pp.extract_quantified_proof_assistant_vars m xd de1 de2 de3);
  | _ -> () );
  
  (* print_endline ("rule: " ^dr.drule_name); *)

  let ppd_premises = 
    match m with
    | Coq _ ->
        (Auxl.option_map 
           (fun (hn,p) -> 
             match hn with 
             | Some hn ->
                 Some ("("^hn^": "^(Grammar_pp.pp_symterm m xd [] de p)^")")
             | None -> None)
           dr.drule_premises,
         Auxl.option_map 
           (fun (hn,p) -> 
             match hn with 
             | None ->
                 Some (Grammar_pp.pp_symterm m xd [] de p)
             | Some _ -> None)
           dr.drule_premises)
    | _ ->
        ([], List.map (fun (hn,p) -> Grammar_pp.pp_symterm m xd [] de p)
      (* print_endline (Grammar_pp.pp_plain_symterm p); *)
           dr.drule_premises) in

  let ppd_conclusion = 
    (* print_endline (Grammar_pp.pp_plain_symterm dr.drule_conclusion); *)
    Grammar_pp.pp_symterm m xd [] de dr.drule_conclusion in
  match m with
  | Ascii ao ->
      (* first find out the width, without colorization *)
      let m0 = Ascii {ao with ppa_colour=false } in
      let ppd_premises0 = List.map 
          (Grammar_pp.pp_symterm m0 xd [] de) 
          (List.map snd dr.drule_premises) in
      let ppd_conclusion0
          = Grammar_pp.pp_symterm m0 xd [] de dr.drule_conclusion in
      let length = List.fold_left max 0 
          (List.map String.length (ppd_conclusion0::ppd_premises0)) in
      (* now really pp *)
      let line = 
        (String.make length '-' ) ^ " " 
        ^ Grammar_pp.pp_COLONCOLON ^ dr.drule_name in
      output_string fd pptbe;
      List.iter (fun x -> output_string fd x; output_string fd "\n") (snd ppd_premises);
      output_string fd line;
      output_string fd "\n";
      output_string fd ppd_conclusion;
      output_string fd "\n"
  | Tex _ ->                                  
      let pp_com = 
        (match Auxl.hom_spec_for_hom_name "com" dr.drule_homs
        with
        | None -> ""
        | Some hs ->
            "\\text{"
            ^ String.concat "" (Grammar_pp.apply_hom_spec m xd hs [])
            ^ "}") in
      Printf.fprintf fd "\\newcommand{%s}[1]{%s[#1]{%%\n"
        (Grammar_pp.tex_drule_name m dr.drule_name)
        (Grammar_pp.pp_tex_DRULE_NAME m);
      List.iter
        (fun p-> Printf.fprintf fd "%s{%s}%%\n" (Grammar_pp.pp_tex_PREMISE_NAME m) p)
        (snd ppd_premises);
      output_string fd "}{\n";
      output_string fd ppd_conclusion;
      Printf.fprintf fd "}{%%\n{%s{%s}}{%s}%%\n}}\n"
        (Grammar_pp.pp_tex_DRULE_NAME_NAME m)
        (Auxl.pp_tex_escape dr.drule_name)
        pp_com
  | Isa _ | Hol _ | Lem _ | Coq _ | Twf _ ->
      let non_free_ntrs = Subrules_pp.non_free_ntrs m xd xd.xd_srs in

      (* find all the nonterms used at non-free types *)
      let subntrs_of_ntmvsns : (nt_or_mv*subntr_data) list -> (nontermroot * nontermroot * nonterm) list = 
        function ntmvsns ->
          Auxl.option_map 
            (function x -> match x with
            | (Ntr ntr,suffix),None -> 
                (try  
                  let ntr_upper = List.assoc ntr non_free_ntrs in
                  Some (ntr,ntr_upper,(ntr,suffix))
                with
                  Not_found -> None)
            | (Ntr ntr,suffix),Some(ntrl,ntru) -> Some (ntrl,ntru,(ntr,suffix))
            | (Mvr mvr,suffix),_ -> None) 
            ntmvsns in

      (* first the non-list nonterms used at non-free types*)
      let nonlist_subntrs = subntrs_of_ntmvsns de3 in

      (* and second the list nonterms used at non-free types *)
      let list_subntrs :((nontermroot * nontermroot * nonterm) list * string * string * string) list = 
        List.map  
          (function (bound,de1i (*(ntmvsns,pp_squished_vars,pp_pattern,coq_type_pattern,hol_type_var)*)) ->
            subntrs_of_ntmvsns de1i.de1_ntmvsns,de1i.de1_compound_id,de1i.de1_pattern,de1i.de1_coq_type_of_pattern)
          de1 in

      let ppd_subntrs = 
        List.map (pp_subntr m xd) nonlist_subntrs 
        @ pp_listsubntr m xd list_subntrs in

      (* collect all the isa/coq/hol variables that should be quantified *)
      (* for this clause *)

      let quantified_proof_assistant_vars = 
	Grammar_pp.extract_quantified_proof_assistant_vars m xd de1 de2 de3 in

      (* calculate list length constraints *)
      (*   There are several different things we could do here: *)
      (*   -a- For a proof assistant list arising from ott list forms with bounds that      *)
      (*        include an upper bound and (perhaps implicitly) a lower bound               *)
      (*        (i.e. Bound_dotform, Bound_comp_u, or Bound_comp_lu, but not Bound_comp),   *)
      (*        say 1..n, we could add a premise that the length of the proof assistant list*)
      (*        is n.                                                                       *)
      (*    -a.2-  It might be a nice optimisation to only include that premise if the n    *)
      (*        is also mentioned elsewhere in the drule.                                   *)
      (*   -b- For a proof assistant list arising from ott list forms with bounds that      *)
      (*        have a number of dots (i.e. Bound_dotform or Bound_comp_lu), say 1....n,    *)
      (*        we could add a premise that the length of the proof assistant list is >= 2. *)
      (*   -c- We could record in each Ste_list any dot length constraint from the ott      *)
      (*        source grammar, then add up the length constraints from the                 *)
      (*        symterm_list_items comprising the Ste_list, see if a non-trivial additional *)
      (*        constraint is required to make the Ste_list of length at least that in the  *)
      (*        grammar, and, if so, add that as a premise.                                 *)
      (*   -d- For each projection index, eg ti, we could add a constraint that i is < the  *)
      (*        length of the proof assistant list.                                         *)
      (*  *)
      (* Below is code to do -a-, fine for isa & hol, but not enough for Coq as there       *)
      (*  we need to add quantifiers for the vars that occur only in bounds                 *)
(*         let list_vars_with_bounds = List.map (function (b,(_,compound_ident,_,_,_)) -> compound_ident,b) de1 in *)
(*         let si_subtract si_lower si_upper = match si_lower,si_upper with *)
(*         | Si_num s, Si_var (suffv,n) ->  *)
(*             let n' = n + 1 - int_of_string s in *)
(*             if n'=0 then suffv else (match m with *)
(*             | Isa _ -> "("^suffv^"+("^string_of_int n'^"::nat))" *)
(*             | Hol _ -> "("^suffv^"+"^string_of_int n'^")" *)
(*             | Coq _ -> "("^suffv^"+"^string_of_int n'^")") *)
(*         | _,_ -> failwith ("internal error: surprising suffixes in si_subtract: "^Grammar_pp.pp_plain_suffix_item si_lower^" and "^Grammar_pp.pp_plain_suffix_item si_lower) in *)
(*         let lengths b = match b with *)
(*         | Bound_dotform bd -> Some (si_subtract bd.bd_lower bd.bd_upper), Some bd.bd_length *)
(*         | Bound_comp bc -> None,None *)
(*         | Bound_comp_u bcu -> Some (si_subtract (Si_num "0") bcu.bcu_upper), None *)
(*         | Bound_comp_lu bclu -> Some (si_subtract bclu.bclu_lower bclu.bclu_upper), Some bclu.bclu_length in *)
(*         let list_length_constraints = Auxl.option_map (function  (b,(_,compound_ident,_,coq_type_pattern,_)) ->  *)
(*           match lengths b with *)
(*           | Some s, _ ->  *)
(*               Some ((match m with *)
(*               | Isa _ -> "length" *)
(*               | Hol _ -> "LENGTH" *)
(*               | Coq _ ->  *)
(*                   let ty_list = Str.split (Str.regexp "(\\|*\\|)") coq_type_pattern in *)
(*                   "length_list_"^(String.concat "_" ty_list) *)
(*                   (\* "[[TODO: insert appropriate Coq list length function for the compound_ident, built from the coq_type_pattern, here ]]" *\)) *)
(*               ^ " " ^ compound_ident^" = "^s) *)
(*           | None,_ -> None) de1 in *)

(*         let ppd_premises = ppd_premises @ list_length_constraints in *)
      
      ( match m with
      | Isa io ->
          Printf.fprintf fd "%sI: \"" dr.drule_name;
          if (snd ppd_premises)<>[] || ppd_subntrs<>[] then begin
            output_string fd "\\<lbrakk>";
            iter_asep fd " ;\n" (output_string fd)          
	      (ppd_subntrs @ snd ppd_premises);
            output_string fd "\\<rbrakk> \\<Longrightarrow>\n";
          end;
          output_string fd ppd_conclusion;
          output_string fd "\"\n"
      | Hol _ ->
          Printf.fprintf fd "( (* %s *) " dr.drule_name; 
          (match quantified_proof_assistant_vars with
           | [] -> ()
           | _ ->
              output_string fd "!";
              List.iter (fun (var,ty,_) -> Printf.fprintf fd " (%s:%s)" var ty)
	        quantified_proof_assistant_vars;
              output_string fd " . ");
          Printf.fprintf fd "(clause_name \"%s\")" dr.drule_name;
          if (snd ppd_premises)<>[] || ppd_subntrs<>[] then begin
            output_string fd " /\\\n(";
	    iter_asep fd " /\\\n"
              (fun s -> output_string fd "("; output_string fd s; output_string fd ")") 
              (ppd_subntrs @ snd ppd_premises);
	    output_string fd ")\n"
          end; 
          output_string fd " ==> \n(";
          output_string fd ppd_conclusion; 
          output_string fd "))\n\n"

      | Lem _ ->
          Printf.fprintf fd "%s%s%s: " 
            (lemTODO "2" "") 
            "" (*("(*"^Location.pp_loc dr.drule_loc^"*)")*)
            dr.drule_name; 
(* Lem currrently requires a forall even if there are no quantified variables,
   and a "true ==>" if there are no premises *)
(*
          (match quantified_proof_assistant_vars with
           | [] -> ()
           | _ ->
*)
              output_string fd "forall";
              List.iter (fun (var,ty,_) -> Printf.fprintf fd " %s" (lemTODO "A" var))
	        quantified_proof_assistant_vars;
(*              List.iter (fun (var,ty,_) -> Printf.fprintf fd " (%s:%s)" var ty)
	        quantified_proof_assistant_vars;*)
              output_string fd " .\n";
(*
);
*)
          (*Printf.fprintf fd "(clause_name \"%s\")" dr.drule_name;*)
          if (snd ppd_premises)<>[] || ppd_subntrs<>[] then
	    begin
              (* output_string fd " &&\n(";*)
	      iter_asep fd " &&\n"
		(fun s -> output_string fd "("; output_string fd s; output_string fd ")") 
		(ppd_subntrs @ snd ppd_premises);
	      output_string fd "\n"
            end
	  else
	    output_string fd "true\n"; 
          output_string fd " ==> \n";
          output_string fd ppd_conclusion; 
          output_string fd "\n\n"

      | Coq co -> 
	  let rec remove_dupl l = match l with
	    | [] -> []
	    | (v,t)::tl -> 
		if List.exists (fun (x,_)->x=v) tl
		then remove_dupl tl
		else (v,t)::(remove_dupl tl) in

	  let nlh, nlhv = !(co.coq_non_local_hyp_defn), !(co.coq_non_local_hyp_defn_vars) in
	  co.coq_non_local_hyp_defn := "";
	  co.coq_non_local_hyp_defn_vars := [];
	  
	  let qpavt_list =
	    let vtl = (List.map (fun (x,_,(t,_)) -> (x,Some t)) quantified_proof_assistant_vars) @ nlhv in
            let vtlr = if co.coq_expand_lists then remove_dupl vtl else Auxl.remove_duplicates vtl in
	    (* Arthur insists that for locally nameless it is important to have the (L:vars) quantifications at the beginning *)
	    let (t1,t2) = List.partition (fun (v,t) -> match t with Some t1 -> String.compare t1 "vars" = 0 | None -> false) vtlr in
	    collapse_quantifications (t1@t2)
	  in
	  
 	  Printf.fprintf fd "\n | %s : " dr.drule_name;
	  if qpavt_list <> [] || fst ppd_premises <> [] then begin
            output_string fd "forall";
            List.iter (fun (vs,t) ->
              begin match t with
              | Some t -> output_string fd " ("; 
                          iter_asep fd " " (output_string fd) vs;
                          output_string fd ":";
                          output_string fd t;
                          output_char fd ')'
              | None -> output_char fd ' '; output_string fd (List.hd vs)
              end) qpavt_list;
            List.iter (fun x -> output_string fd "\n     "; output_string fd x) (fst ppd_premises);
            output_string fd ","
          end;
          output_string fd "\n     ";
          output_string fd nlh; 
	  List.iter (fun x -> output_string fd x; output_string fd " ->\n     ") 
            (ppd_subntrs @ snd ppd_premises);
	  output_string fd ppd_conclusion

      | Twf wo ->
          let pr_premise x = output_string fd " <- "; output_string fd x in
          Printf.fprintf fd "%s/%s: " !(wo.twf_current_defn) dr.drule_name;
	  output_string fd ppd_conclusion;
          List.iter pr_premise ppd_subntrs;
          List.iter pr_premise (snd ppd_premises);
          output_string fd ".\n"

      | Tex _ | Ascii _ | Caml _ | Lex _ | Yacc _ -> raise Auxl.ThisCannotHappen 
       )
  | Caml _ | Lex _ | Yacc _ ->
      Auxl.errorm m "defns not implemented"

let pp_processed_semiraw_rule fd (m:pp_mode) (xd:syntaxdefn) (s: string) (psr:processed_semiraw_rule) =
  match psr with
  | PSR_Rule dr -> output_string fd s; pp_drule fd m xd dr; true
  | PSR_Defncom _ -> false

let pp_defn fd (m:pp_mode) (xd:syntaxdefn) lookup (defnclass_wrapper:string) (universe:string) (d:defn) =
  match m with
  | Ascii _ ->
      output_string fd Grammar_pp.pp_DEFN;
      output_string fd "\n";
      output_string fd (Grammar_pp.pp_symterm m xd [] de_empty d.d_form);
      output_string fd Grammar_pp.pp_COLONCOLON;
      output_string fd " ";
      output_string fd d.d_wrapper;
      output_string fd " ";
      output_string fd Grammar_pp.pp_BY;
      output_string fd "\n\n";
      iter_nosep (fun psr -> pp_processed_semiraw_rule fd m xd "" psr) d.d_rules;
      output_string fd "\n\n"
  | Isa io ->
      Printf.fprintf fd "(* defn %s *)\n\n" d.d_name;
      ( match (Grammar_pp.isa_fancy_syntax_clause_for_defn m xd io "foo" defnclass_wrapper d) with
        | None -> ()
	| Some _ -> output_string fd "| " );
      iter_sep (pp_processed_semiraw_rule fd m xd) "\n| " d.d_rules
  | Hol _ ->
      Printf.fprintf fd "(* defn %s *)\n\n" d.d_name;
      iter_sep (pp_processed_semiraw_rule fd m xd) "/\\ " d.d_rules
  | Lem _ ->
      Printf.fprintf fd "(* defn %s *)\n\n" d.d_name;
      iter_sep (pp_processed_semiraw_rule fd m xd) "and\n" d.d_rules
  | Coq co -> (* FZ factor this code ? *)

      let prod_name = defnclass_wrapper ^ d.d_name in

      let type_defn = 
        let es = (Auxl.prod_of_prodname xd prod_name).prod_es in
        let ss = (Auxl.option_map (Grammar_pp.pp_element m xd [] true) es) in
        match ss with
        | [] -> universe^" :="
        | [s] -> s ^ " -> "^universe^" :="      
        | _ -> String.concat " -> " ss ^ " -> " ^ universe^" :=" in        
      Printf.fprintf fd "%s%s : %s    (* defn %s *)" defnclass_wrapper d.d_name type_defn d.d_name;
      iter_nosep (fun psr -> pp_processed_semiraw_rule fd m xd "" psr) d.d_rules
  | Twf wo ->
      wo.twf_current_defn := d.d_name;
      Printf.fprintf fd "%%%% defn %s\n\n" d.d_name;
      iter_nosep (fun psr -> pp_processed_semiraw_rule fd m xd "" psr) d.d_rules

  | Tex xo ->
      let prod_name = (defnclass_wrapper^d.d_name) in
      let p = Auxl.prod_of_prodname xd prod_name in
      let es = p.prod_es in 
      let pp_com = Grammar_pp.pp_com_es m xd d.d_homs es  in
      Printf.fprintf fd "%%%% defn %s\n" d.d_name;
      iter_sep (pp_processed_semiraw_rule fd m xd) "\n\n" d.d_rules;
      Printf.fprintf fd "\n\\newcommand{%s}[1]{\\begin{%s}[#1]{$%s$}{%s}\n"
        (Grammar_pp.tex_defn_name m defnclass_wrapper d.d_name)
        (Grammar_pp.pp_tex_DEFN_BLOCK_NAME m)
        (Grammar_pp.pp_symterm m xd [] de_empty d.d_form)
        pp_com;
      List.iter (function
        | PSR_Rule dr -> 
            Printf.fprintf fd "%s{%s{}"
              (Grammar_pp.pp_tex_USE_DRULE_NAME m)
              (Grammar_pp.tex_drule_name m dr.drule_name);
            if (xo.ppt_show_categories &&
               not (StringSet.is_empty dr.drule_categories)) then begin
              output_string fd "\\quad\\textsf{[";
              StringSet.iter (fun x -> output_string fd x; output_string fd " ")
                dr.drule_categories;
              output_string fd "]}"
            end;
            output_string fd "}\n"
        | PSR_Defncom es -> Embed_pp.pp_embed_spec fd m xd lookup es)
        d.d_rules;
      Printf.fprintf fd "\\end{%s}}\n\n" (Grammar_pp.pp_tex_DEFN_BLOCK_NAME m)
  | Caml _ | Lex _ | Yacc _ -> Auxl.errorm m "pp_defn"

            
let pp_defnclass fd (m:pp_mode) (xd:syntaxdefn) lookup (dc:defnclass) =
  let universe = try Grammar_pp.pp_hom_spec m xd (List.assoc "coq-universe" dc.dc_homs) with Not_found -> "Prop" in
  let isa_type_of_defn (m: pp_mode) (xd: syntaxdefn) (d: defn) : string = 
      (* seems simplest to find the type associated with the production that
         we added to the language for this defn, rather than build a type
         directly from the defn. Though (now wrappers are working properly)
         that does mean we need to pass them in. *)
      let prod_name = dc.dc_wrapper ^ d.d_name in
      let es = (Auxl.prod_of_prodname xd prod_name).prod_es in
      let ss = (Auxl.option_map (Grammar_pp.pp_element m xd [] true) es) in
      let ss = match ss with [] -> ["unit"] | _ -> ss in
      match m with 
        | Isa io when io.ppi_isa_inductive -> String.concat " \\<Rightarrow> " ss ^" \\<Rightarrow> bool"  
        | Isa io when not io.ppi_isa_inductive -> "("^String.concat "*" ss ^") set" 
        | _ -> failwith "internal: isa_type_of_defn: cannot happen" in
  let lem_type_of_defn (m: pp_mode) (xd: syntaxdefn) (d: defn) : string = 
    let prod_name = dc.dc_wrapper ^ d.d_name in
    let es = (Auxl.prod_of_prodname xd prod_name).prod_es in
    let ss = (Auxl.option_map (Grammar_pp.pp_element m xd [] true) es) in
    let ss = match ss with [] -> ["unit"] | _ -> ss in
    lemTODO "25" "" ^ String.concat " -> " ss ^" -> bool" in


  match m with
  | Ascii _ -> 
      output_string fd Grammar_pp.pp_DEFNCLASS;
      output_string fd "\n";
      output_string fd dc.dc_name;
      output_string fd " ";
      output_string fd Grammar_pp.pp_COLONCOLON;
      output_string fd " ";
      output_string fd dc.dc_wrapper;
      output_string fd " ";
      output_string fd Grammar_pp.pp_CCE;
      output_string fd "\n\n";
      List.iter (fun d -> pp_defn fd m xd lookup dc.dc_wrapper universe d) dc.dc_defns

  | Isa io ->
      let fancy_syntax_clauses = 
        Auxl.option_map
	  (Grammar_pp.isa_fancy_syntax_clause_for_defn m xd io dc.dc_name dc.dc_wrapper)
	  dc.dc_defns in
      Printf.fprintf fd "(* defns %s *)\n%s " dc.dc_name 
        (if io.ppi_isa_inductive then "inductive" else "inductive_set");
      iter_asep fd "\n and "
        (fun d -> Printf.fprintf fd "%s%s :: \"%s\"" dc.dc_wrapper d.d_name
                    (isa_type_of_defn m xd d))
         dc.dc_defns; 
      ( match fancy_syntax_clauses with
        | [] -> ()
        | fscs -> output_string fd "\nand ";
                  List.iter (fun x -> output_string fd (fst x)) fscs);
      output_string fd "\nwhere\n";
      ( match fancy_syntax_clauses with
        | [] -> ()
        | fscs -> List.iter (fun x -> output_string fd (snd x)) fscs);
      iter_asep fd "\n| " (fun d -> pp_defn fd m xd lookup dc.dc_wrapper universe d) dc.dc_defns

  | Hol ho -> 
      Printf.fprintf fd "(* defns %s *)\n\nval (%s_rules, %s_ind, %s_cases) = Hol_reln`\n"
        dc.dc_name dc.dc_name dc.dc_name dc.dc_name;
      iter_asep fd "/\\" (fun d -> pp_defn fd m xd lookup dc.dc_wrapper universe d) dc.dc_defns;
      output_string fd "`;\n"

  | Lem lo -> 
      Printf.fprintf fd "%s(* defns %s *)\nindreln\n" 
        (lemTODO "3" "")
        dc.dc_name;
      let lem_wcf_of_defn m xd d = 
	try 
	  let hs = List.assoc "lemwcf" d.d_homs in
	  let pp_hom_spec hs =
	    String.concat "" (List.map Grammar_pp.pp_pseudo_hom_spec_el hs) in
	  " "^pp_hom_spec hs
	with
	  Not_found -> "" in
      iter_asep fd "\n and "
        (fun d -> Printf.fprintf fd "[%s%s : %s%s]\n" dc.dc_wrapper d.d_name
                    (lem_type_of_defn m xd d)
                    (lem_wcf_of_defn m xd d))
         dc.dc_defns; 
      iter_asep fd "\nand\n" (fun d -> pp_defn fd m xd lookup dc.dc_wrapper universe d) dc.dc_defns;
      output_string fd "\n"

  | Coq co -> 
      co.coq_list_aux_defns.newly_defined := [];
      Printf.fprintf fd "\n(* defns %s *)\nInductive " dc.dc_name;
      iter_asep fd "\nwith "
        (fun d -> pp_defn fd m xd lookup dc.dc_wrapper universe d)
	dc.dc_defns;
      List.iter (output_string fd) !(co.coq_list_aux_defns.newly_defined);
      output_string fd ".\n"

  | Twf wo -> 
      let twf_type_of_defn : syntaxdefn -> defn -> string = 
        fun xd d ->  
        (* follows isa case here *)
          let prod_name = dc.dc_wrapper ^ d.d_name in
          let es = (Auxl.prod_of_prodname xd prod_name).prod_es in
          let ss = (Auxl.option_map (Grammar_pp.pp_element m xd [] true) es) in
          match ss with
          | [] -> "unit"  (* FZ CHECK THIS *)
          | [s] -> s      
          | _ -> String.concat " -> " ss in
      
      Printf.fprintf fd "%%%% defns %s\n\n" dc.dc_name;
      List.iter
        (fun d -> Printf.fprintf fd "%s%s : %s -> type.\n" dc.dc_wrapper d.d_name
                    (twf_type_of_defn xd d))
         dc.dc_defns; 
      List.iter (fun d -> pp_defn fd m xd lookup dc.dc_wrapper universe d) dc.dc_defns

  | Caml _ | Lex _ | Yacc _ -> ()

  | Tex _ ->
      Printf.fprintf fd "%% defns %s\n" dc.dc_name;
      List.iter (fun d -> pp_defn fd m xd lookup dc.dc_wrapper universe d) dc.dc_defns;
      Printf.fprintf fd "\n\\newcommand{%s}{\n" (Grammar_pp.tex_defnclass_name m dc.dc_name);
      List.iter (fun d -> output_string fd (Grammar_pp.tex_defn_name m dc.dc_wrapper d.d_name);
                          output_string fd "{}") dc.dc_defns;
      output_string fd "}\n\n"

(**********************************************)
(* pp of fundefns                             *)
(**********************************************)

let pp_funclause (m:pp_mode) (xd:syntaxdefn) (fc:funclause) : string =
  let (((de1:dotenv1),de2) as de,de3,pptbe) = 
    Bounds.bound_extraction m xd fc.fc_loc [fc.fc_lhs;fc.fc_rhs] in
  let ppd_lhs = Grammar_pp.pp_symterm m xd [] de fc.fc_lhs in
  let ppd_rhs = Grammar_pp.pp_symterm m xd [] de fc.fc_rhs in
  match m with
  | Ascii ao ->
      ppd_lhs ^ " === " ^ ppd_rhs ^ "\n"
  | Tex _ ->                                  
      Grammar_pp.pp_tex_FUNCLAUSE_NAME m^"{"^ppd_lhs^"}"^"{"^ppd_rhs^"}%\n"
  | Isa _ | Hol _ | Lem _ | Coq _ | Caml _ | Twf _ | Lex _ | Yacc _ -> 
      Auxl.errorm m "pp_funclause"

let rec insert_commas l =
  match l with
  | [] -> []
  | h::[] -> h::[]
  | h::t -> h::(Hom_string ",")::(insert_commas t)

let pp_symterm_node_lhs m xd sie de st = 
  match st with
  | St_node (_,stnb) -> 
      let promoted_pn = 
	try
	  let ntrt,pps = List.assoc stnb.st_rule_ntr_name xd.xd_srd.srd_subrule_pn_promotion in
	  try List.assoc stnb.st_prod_name pps with Not_found -> Auxl.int_error ("ppd_lhs")
	with Not_found -> stnb.st_prod_name in 
      let p = Auxl.prod_of_prodname xd promoted_pn in
      let prod_es = p.prod_es in
      let pes = Grammar_pp.pp_symterm_elements m xd [] de false prod_es stnb.st_es in
      let hom = 
        try List.assoc "order" p.prod_homs
        with Not_found -> Auxl.int_error "pp_symterm_node_lhs" in
      let hom =
	match m with
	| Coq _ | Caml _ | Lem _ (* LemTODO4: really? *) -> (insert_commas hom)
	| Hol _ | Isa _  -> hom
	| Twf _ | Ascii _ | Tex _ | Lex _ | Yacc _ -> raise Auxl.ThisCannotHappen
      in String.concat " " (Grammar_pp.apply_hom_spec m xd hom pes)

  | _ -> Auxl.int_error "pp_symterm_node_lhs"

let fundefn_to_int_func (m:pp_mode) (xd:syntaxdefn) (deps:string list) (fd:fundefn) : int_func option =
  let header =
    match m with
    | Hol _ -> Some ("","","")
    | Lem _ -> raise LemTODO (*LemTODO5*)
    | Coq _ -> 
	let prod_name = fd.fd_pn_wrapper^ fd.fd_name in
	let result_type_name = Grammar_pp.pp_nontermroot_ty m xd fd.fd_result_type in
        let prod_es = Grammar_pp.apply_hom_order m xd (Auxl.prod_of_prodname xd prod_name) in

	let struct_on = 
	  match Auxl.hom_spec_for_hom_name "coq-struct" fd.fd_homs with
	  | Some ([Hom_index i]) -> "{struct x" ^ string_of_int (i+1) ^ "} "
	  | Some _ -> 
	      Auxl.warning "malformed coq-struct homomorphism"; 
	      "{struct <<<malformed term in coq-struct hom>>>}"
	  | None -> "" in

	let (type_defn,match_string) =
          let ss = (Auxl.option_map (Grammar_pp.pp_element m xd [] true) prod_es) in

          match ss with
          | [] -> (" :=","")      (* FZ THIS IS PROBABLY WRONG *)
          | _ -> 
	      let i = ref 0 in
	      let v = 
		String.concat " "
		  (List.map (fun s -> "(x"^(i := !i+1; string_of_int !i)^":"^s^")") ss) in
	      i := 0;
              let ms = 
		"  match "
		^ String.concat "," (List.map (fun _ -> i := !i+1; "x"^string_of_int !i) ss)
		^ " with\n" in
	      (v,ms) 
	in
	Some ( fd.fd_name ^ " " ^ type_defn ^ " "^struct_on^": " ^ result_type_name ^ ":=\n",
	  "",
	  match_string)
    | Isa _ ->
	let isa_type_of_fundefn : syntaxdefn -> fundefn -> string =
          fun xd fd ->
            (* seems simplest to find the type associated with the
               production that we added to the language for this defn,
               rather than build a type directly from the defn. Though
               (now wrappers are working properly) that does mean we
               need to pass them in. *) 

	    let result_type_name = Grammar_pp.pp_nontermroot_ty m xd fd.fd_result_type in
            let prod_name = fd.fd_pn_wrapper ^ fd.fd_name in
            let es = Grammar_pp.apply_hom_order m xd (Auxl.prod_of_prodname xd prod_name) in
            let ss = (Auxl.option_map (Grammar_pp.pp_element m xd [] true) es)in
            (match ss with
            | [] -> "unit"
            | _ -> String.concat " => " ss) ^ " => " ^ result_type_name in

	let h1 = fd.fd_name ^ " :: \"" ^ isa_type_of_fundefn xd fd ^"\"\n" in
	Some (h1,"","")

(*         (let fancy_syntax_clauses = *)
(*           Auxl.option_map *)
(* 	    (Grammar_pp.isa_fancy_syntax_clause_for_fundefn m xd io fdc.fdc_name) *)
(* 	    fdc.fdc_fundefns in *)
(*         match fancy_syntax_clauses with *)
(*         | [] -> "" *)
(*         | fscs -> *)
(*             "syntax\n" *)
(*             ^ String.concat "\n" (List.map fst fscs) *)
(*             ^ "\n\ntranslations\n" *)
(*             ^ String.concat "\n" (List.map snd fscs) *)
(*             ^ "\n\n") *)
(*       ^ "inductive " *)
(*       ^ (String.concat *)
(*            " " *)
(*            (List.map (function fd ->  fd.fd_name) fdc.fdc_fundefns)) *)
(*       ^ "\nintros\n\n" *)
    | Caml _ ->
      if String.compare fd.fd_result_type "formula" = 0 then None else
	let prod_name = fd.fd_pn_wrapper^ fd.fd_name in
	let result_type_name = Grammar_pp.pp_nontermroot_ty m xd fd.fd_result_type in
        let prod_es = Grammar_pp.apply_hom_order m xd (Auxl.prod_of_prodname xd prod_name) in

	let (type_defn,match_string) =
          let ss = (Auxl.option_map (Grammar_pp.pp_element m xd [] true) prod_es) in

          match ss with
          | [] -> (" =","")  
          | _ -> 
	      let i = ref 0 in
	      let v = 
		String.concat " "
		  (List.map (fun s -> "(x"^(i := !i+1; string_of_int !i)^":"^s^")") ss) in
	      i := 0;
              let ms = 
		"  match "
		^ String.concat "," (List.map (fun _ -> i := !i+1; "x"^string_of_int !i) ss)
		^ " with\n" in
	      (v,ms) 
	in
	Some ( fd.fd_name ^ " " ^ type_defn ^ ": " ^ result_type_name ^ "=\n", "", match_string)
    | Tex _ | Ascii _ | Twf _ | Lex _ | Yacc _ -> raise Auxl.ThisCannotHappen 

  in
  match header with None -> None | Some header -> 
  let clauses =
    List.map 
      (fun fc ->
	let (((de1:dotenv1),de2) as de,de3,pptbe) = 
	  Bounds.bound_extraction m xd fc.fc_loc [fc.fc_lhs;fc.fc_rhs] in
	let ppd_lhs = pp_symterm_node_lhs m xd [] de fc.fc_lhs in
	let ppd_rhs = Grammar_pp.pp_symterm m xd [] de fc.fc_rhs in
	("", ppd_lhs, ppd_rhs))
      fd.fd_clauses in

  Some { r_fun_id = fd.fd_name;
    r_fun_dep = deps;
    r_fun_type = "TODO";  
    r_fun_header = header;
    r_fun_clauses = clauses
  }

let pp_fundefn (m:pp_mode) (xd:syntaxdefn) lookup (fd:fundefn) : string =
  match m with
  | Ascii _ ->
      Grammar_pp.pp_FUNDEFN ^"\n"
      ^ Grammar_pp.pp_symterm m xd [] de_empty fd.fd_form
      ^ Grammar_pp.pp_COLONCOLON ^" "^fd.fd_result^" "
      ^ Grammar_pp.pp_COLONCOLON ^" "^fd.fd_name^" "
(*      ^ Grammar_pp.pp_COLONCOLON ^" "^fd.fd_pn_wrapper^" " *)
      ^ Grammar_pp.pp_BY
      ^ "\n\n"
      ^ String.concat "\n" (List.map (pp_funclause m xd) fd.fd_clauses)

  | Tex xo ->
      let prod_name = (fd.fd_pn_wrapper^fd.fd_name) in
      let p = Auxl.prod_of_prodname xd prod_name in
      let es = p.prod_es in 
      let pp_com = Grammar_pp.pp_com_es m xd fd.fd_homs es  in
      "% fundefn "^fd.fd_name^"\n"
      ^ "\n\\newcommand{"^Grammar_pp.tex_fundefn_name m fd.fd_name^"}[1]{"
      ^ "\\begin{"^Grammar_pp.pp_tex_FUNDEFN_BLOCK_NAME m ^"}[#1]{$" 
      ^ Grammar_pp.pp_symterm m xd [] de_empty fd.fd_form 
      ^ "$}{"
      ^ pp_com
      ^ "}\n"
      ^ String.concat "" 
          (List.map (pp_funclause m xd) fd.fd_clauses)
      ^ "\\end{"^Grammar_pp.pp_tex_FUNDEFN_BLOCK_NAME m ^"}" 
      ^ "}\n\n"

  | Isa _ | Hol _ | Lem _ | Coq _ | Twf _ | Caml _ | Lex _ | Yacc _ -> 
      Auxl.errorm m "pp_fundefn"

let pp_fundefnclass (m:pp_mode) (xd:syntaxdefn) lookup (fdc:fundefnclass) : string =
  match m with
  | Ascii _ -> 
      Grammar_pp.pp_FUNDEFNCLASS ^"\n"
      ^ fdc.fdc_name ^" "
      ^ Grammar_pp.pp_CCE^"\n\n"
      ^ String.concat "\n\n" (List.map (pp_fundefn m xd lookup) fdc.fdc_fundefns)

  | Tex _ ->
      "% fundefns "^fdc.fdc_name^"\n"
      ^ (String.concat 
           "\n"
           (List.map (pp_fundefn m xd lookup) fdc.fdc_fundefns))
      ^ "\n"
      ^ "\\newcommand{"^Grammar_pp.tex_fundefnclass_name m fdc.fdc_name^"}{\n"
      ^ (String.concat 
           "\n" 
           (List.map (function fd -> Grammar_pp.tex_fundefn_name m fd.fd_name^"{}") fdc.fdc_fundefns))
      ^ "}\n\n"
 
  | Isa _ | Coq _ | Hol _ | Lem _ | Caml _ ->
      let proof = 
	let pp_proof h =
	  ( match h with 
	  | Some ([Hom_string s]) -> Some s
	  | None -> None
	  | _ -> Auxl.warning "malformed isa-proof/hol-proof hom"; Some "<<<malformed isa-proof/hol-proof hom>>>" ) in 
	( match m with
	| Coq _ | Caml _ | Lem _ -> None
	| Isa _ -> pp_proof (Auxl.hom_spec_for_hom_name "isa-proof" fdc.fdc_homs) 
	| Hol _ -> pp_proof (Auxl.hom_spec_for_hom_name "hol-proof" fdc.fdc_homs)
	| _ -> raise Auxl.ThisCannotHappen ) in
      let deps = List.map (fun fd -> fd.fd_name) fdc.fdc_fundefns in
      let int_funcs = 
	{ i_funcs = Auxl.option_map (fundefn_to_int_func m xd deps) fdc.fdc_fundefns;
	  i_funcs_proof = proof } in
      let int_funcs_collapsed = Dependency.collapse m xd int_funcs in
      Auxl.print_with_comment m "\n" ("funs "^fdc.fdc_name) 
	(Dependency.compute m xd int_funcs_collapsed)

  | Twf _ -> Auxl.warning "internal: fundefnclass not implemented for Twelf"; ""
  | Lex _ | Yacc _ -> ""



 (* ************************************************ *)

let pp_fun_or_reln_defnclass fd m xd lookup frdc = match frdc with
| FDC fdc -> output_string fd (pp_fundefnclass m xd lookup fdc)
| RDC dc -> pp_defnclass fd m xd lookup dc

let pp_auxiliary_list_rules fd m xd frdcs = match m with
  | Coq co when co.coq_expand_lists ->

    let b = Buffer.create 120 in
 
    let list_types_drule dr = 
      let (((de1:dotenv1),_),_,_) =
        Bounds.bound_extraction m xd dr.drule_loc
          (dr.drule_conclusion::List.map snd dr.drule_premises) in
      List.iter (fun (_,de1i) ->
        Buffer.clear b;
        Buffer.add_string b "list";
        let ntmvrl =
          List.map (fun ((ntmvr,_),_) ->
            let ntmvr = 
              Auxl.promote_ntmvr xd
                (Auxl.primary_nt_or_mv_of_nt_or_mv xd ntmvr) in
            Buffer.add_char b '_';
            Buffer.add_string b (Grammar_pp.pp_nt_or_mv_root m xd ntmvr);
            ntmvr) de1i.de1_ntmvsns in
        let s = Buffer.contents b in
        if not (List.mem s !(co.coq_list_types)) then begin
          Transform.pp_list_rule fd xd ntmvrl;
          co.coq_list_types := s :: !(co.coq_list_types)
        end) de1 in
  
      List.iter
        (function 
         | RDC dc ->
             List.iter (fun d ->
               List.iter (function
                  | PSR_Rule dr -> list_types_drule dr
                  | PSR_Defncom _ -> ()) d.d_rules) dc.dc_defns
         | FDC _ -> ()) frdcs

  | _ -> ()

let pp_fun_or_reln_defnclass_list
  (fd : out_channel) (m: pp_mode) (xd: syntaxdefn)
  (lookup: made_parser) (frdcs: fun_or_reln_defnclass list) =
      match m with
      | Ascii _ | Isa _ | Hol _ | Lem _ | Caml _ -> 
	  output_string fd "(** definitions *)\n";
          List.iter (fun frdc -> pp_fun_or_reln_defnclass fd m xd lookup frdc) frdcs
      | Twf _ -> 
	  output_string fd "%%% definitions %%%\n\n";
          List.iter (fun frdc -> pp_fun_or_reln_defnclass fd m xd lookup frdc) frdcs
      | Coq co ->
          pp_auxiliary_list_rules fd m xd frdcs;
	  output_string fd "(** definitions *)\n";
          List.iter (fun frdc -> pp_fun_or_reln_defnclass fd m xd lookup frdc) frdcs;
      | Tex _ -> 
          output_string fd "% defnss\n";
          List.iter (fun frdc -> pp_fun_or_reln_defnclass fd m xd lookup frdc) frdcs;
          Printf.fprintf fd "\\newcommand{%s}{\n" (Grammar_pp.pp_tex_DEFNSS_NAME m);
          List.iter (function
                       | FDC fdc -> Printf.fprintf fd "%s\n" (Grammar_pp.tex_fundefnclass_name m fdc.fdc_name)
                       | RDC dc -> Printf.fprintf fd "%s\n" (Grammar_pp.tex_defnclass_name m dc.dc_name)) frdcs;
          output_string fd "}\n\n"
      | Lex _ | Yacc _ -> () 


(** *********************** *)
(** processing of raw defns *)
(** *********************** *)


let fakesucc = let n=ref 0 in function () -> n:= !n+1; 
  Auxl.string_of_char_list
    (List.map 
       (function c -> char_of_int (int_of_char c + 49)) 
       (Auxl.char_list_of_string 
          (let s0=string_of_int !n in
          (String.make (6-String.length s0) '0' ^ s0))))


let process_semiraw_rule (m: pp_mode) (xd: syntaxdefn) (lookup: made_parser)
    (defnclass_wrapper: string) (defn_wrapper: string) (prod_name: string) 
	(sr: semiraw_rule): processed_semiraw_rule option =
  match sr with
      Lined_rule(l0,lss1,ls,lss2) ->

        let (l,s)=ls in 
        let lexbuf = Lexing.from_string s in
        let annot : raw_drule_line_annot = try
          Grammar_parser.drule_line_annot (Grammar_lexer.my_lexer true Grammar_lexer.metalang)  lexbuf 
        with 
        |  Parsing.Parse_error | My_parse_error _ ->
            raise (Rule_parse_error ("bad annotation in \""^s^"\" at "^Location.pp_loc l))
        |  e ->
            (print_string ("exception in parsing \""^s^"\" at "^Location.pp_loc l^"\n");
             flush stdout;
             raise e) in
        (* let categories = List.map del c in *)

(*         let rule_name_parse s =  *)
(* (\*          let srev = String.copy s in  *\) *)
(*           let srev = Auxl.string_rev s in *)
(*           let re = Str.regexp " *\\(\\[\\[\\([a-z]\\|[A-Z]\\|[0-9]\\|_\\)*\\([a-z]\\|[A-Z]\\):\\]\\]\\)?\\(.*\\\)" in *)
(*           if not(Str.string_match re srev 0) then  *)
(*             (None,s)  *)
(*           else *)
(*             let hn = Some (Auxl.string_rev (Str.matched_group 1 srev)) in *)
(*             let s' = Auxl.string_rev (Str.matched_group 4 srev) in *)
(*             (hn,s')  *)
(*         in *)

        let rule_name_parse s =
          let is_letter c =
            let cc = Char.code (Char.lowercase c) in
            cc >= 97 && cc <= 122 in
          
          let is_num_or_letter c =
            let cc = Char.code (Char.lowercase c) in
            (cc >= 97 && cc <= 122) || (cc >= 48 && cc <= 57) in
          
          let is_space c =
            c = ' ' in
          
          let rec scan f i =
            if i <= 0 then 0 else
            if f(s.[i]) then scan f (i-1) else i in
          
          let skip_right_spaces = scan is_space in
          
          let skip_num_or_letter = scan is_num_or_letter in
          
          let rightmost_char_index = skip_right_spaces ((String.length s)-1) in

          
          if rightmost_char_index = 0 
             || s.[rightmost_char_index] != ']' 
             || s.[rightmost_char_index-1] != ']'
          then (s,None)
          else
            
            let leftmost_char_index = (skip_num_or_letter (rightmost_char_index-2)) + 1 in
            
            if s.[leftmost_char_index-3] != '[' 
              || s.[leftmost_char_index-2] != '[' 
              || s.[leftmost_char_index-1] != ':' 
              || not (is_letter s.[leftmost_char_index])
            then (s,None)
            else (String.sub s 0 (leftmost_char_index-3), 
                  Some (String.sub s (leftmost_char_index) 
                          ((rightmost_char_index-2) - leftmost_char_index + 1)))
        in

        let fancy_parse (l, s) = 
          let (s,hn) = rule_name_parse s in
          let re = Str.regexp " *{{ *\\(.*\\)}} *" in
          if not(Str.string_match re s 0) then 
            (hn,Term_parser.just_one_parse xd lookup rn_formula false l s )
          else 
            let s' = Str.matched_group 1 s in

            let lexbuf = Lexing.from_string s' in
            (*lexbuf.Lexing.lex_curr_p <- 
              { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = src_filename};*)
            let unfiltered_string = try
              Grammar_parser.unfiltered_spec_el_list (Grammar_lexer.my_lexer true Grammar_lexer.filter) lexbuf
            with 
              Parsing.Parse_error ->
                Auxl.error ("unfiltered premise "^s^" cannot be parsed\n") in
            let collapsed_string = Auxl.collapse_embed_spec_el_list unfiltered_string in 
            (*let filtered_string = Embed_pp.pp_embed_spec m xd lookup collapsed_string in*)
            (* walk over collapsed_string, building a new string (with -ARG- replacing each [[.]]) and a list of symterms (one for each [[.]]) *)
            let rec walk es acc_s acc_sts n =
              match es with
              | [] -> (acc_s,acc_sts)
              | Embed_string(l'',s'')::es' -> walk es' (acc_s^s'') acc_sts n 
              | Embed_inner(l'',s'')::es' -> 
                  (* print_string ("TRYING TO JUSTONEPARSE "^s''^"\n"); *)
                  let st = Term_parser.just_one_parse xd lookup "user_syntax" false l'' s'' in
                  walk es' (acc_s^"-ARG-" (*^string_of_int n*) ) (acc_sts@[st]) (n+1) in
            let (embedding_string,sts) = walk collapsed_string "" [] 0 in

            (*let sts_debug = String.concat " " (List.map (Grammar_pp.pp_plain_symterm) sts) in*)
            (* print_string ("REALLY FOUND {{"^embedding_string^"  "^sts_debug^"}}\n"); *)

            let st = St_node(l,{st_rule_ntr_name = "fancy_formula";
                                st_prod_name = embedding_string;
                                st_es = List.map (function st -> Ste_st(l,st)) sts;
                                st_loc = l}) in
            (* print_string ("CONSTRUCTED "^Grammar_pp.pp_plain_symterm st^"\n"); *)
            (hn,st) in



        let premises = List.map fancy_parse lss1 in
        let conclusion =
          match lss2 with
          | [] -> raise (Rule_parse_error ("rule with no conclusion at " ^ Location.pp_loc l))
          | [(l,s)] -> Term_parser.just_one_parse ~transform:(Term_parser.defn_transform prod_name) xd lookup rn_formula false l s
          | _ -> raise (Rule_parse_error ("rule with multiple conclusions at " ^ Location.pp_loc l))
        in
        let c = Term_parser.cd_env_of_syntaxdefn xd in
        let dr = {drule_name = defnclass_wrapper^defn_wrapper^annot.dla_name;
                  drule_categories =
                  List.fold_left (fun s (_,c) -> StringSet.add c s)
                    StringSet.empty annot.dla_categories;
                  drule_premises = premises (*List.map (fun st -> None,st) premises*);  (* HNAMING *)
                  drule_conclusion = conclusion;
                  drule_homs = List.map (Grammar_typecheck.cd_hom Hu_drule c []) annot.dla_homs ;
                  drule_loc = l0} in
        (* print_string (pp_ascii_drule xd dr^"\n\n"); *)
        Some (PSR_Rule dr)

	  (* hacky test harness code for now*)
    | Lineless_rule (l0,lss) -> 
        (match lss with
        | [] -> None
        | _ -> let dr = {drule_name = "fake" ^ fakesucc ();
                         drule_categories = StringSet.singleton "F";
                         drule_premises = [];
                         drule_conclusion = (Term_parser.just_one_parse xd lookup rn_formula false) l0 (String.concat " " (List.map snd lss));
                         drule_homs = [];  
                         drule_loc = l0} in
          Some(PSR_Rule dr))
    | Defncom (l0,es) ->
        Some(PSR_Defncom es)

let process_raw_defn : pp_mode -> syntaxdefn -> made_parser -> string -> string -> raw_defn -> defn
    = fun m xd lookup defnclass_name defnclass_wrapper rd -> 

      let prod_name = (defnclass_wrapper^rd.raw_d_name) in
      let p = Auxl.prod_of_prodname xd prod_name in
      let es = p.prod_es in 
      (match m with Ascii ao when ao.ppa_show_defns -> 
        print_string (rd.raw_d_name^" ");flush stdout 
      | _ -> ());
      let c = Term_parser.cd_env_of_syntaxdefn xd in
      { d_name=rd.raw_d_name;
        d_form= 
          St_node(dummy_loc, { st_rule_ntr_name=defnclass_name;
                               st_prod_name= prod_name ;
                               st_es = Auxl.option_map Grammar_pp.canonical_symterm_element_of_element es;
                               st_loc = rd.raw_d_loc }) ;
        d_wrapper= rd.raw_d_wrapper;
        d_rules= Auxl.option_map
          (process_semiraw_rule m xd lookup defnclass_wrapper rd.raw_d_wrapper prod_name) 
          rd.raw_d_body;
        d_homs =  List.map (Grammar_typecheck.cd_hom Hu_defn c es) rd.raw_d_homs;
        d_loc = dummy_loc} 

let process_raw_defnclass : pp_mode -> syntaxdefn -> made_parser -> raw_defnclass -> defnclass
    = fun m xd lookup rdc -> 
      let c = Term_parser.cd_env_of_syntaxdefn xd in
      {dc_name=rdc.raw_dc_name;
       dc_homs =  List.map (Grammar_typecheck.cd_hom Hu_defnclass c []) rdc.raw_dc_homs;
       dc_language_names = []; (* TODO *)
       dc_wrapper = rdc.raw_dc_wrapper;
       dc_defns = List.map 
         (process_raw_defn m xd lookup rdc.raw_dc_name rdc.raw_dc_wrapper) rdc.raw_dc_defns;
       dc_loc = dummy_loc} 

(* ******************** *)

let process_raw_funclause 
  (m: pp_mode) (xd: syntaxdefn) (lookup: made_parser) 
  (fundefnclass_name: string) (pn_wrapper: string) (fundefn_name: string)
  (result_type: nontermroot) = function ((l,s) : raw_funclause) ->
(*
      print_string ("funclause prodname = "^prodname^"\n");flush stdout;
      print_string ("s = "^s^"\n");flush stdout;
      let fundefnclassname = "FUNTODO" in
*)
      let st = Term_parser.just_one_parse xd lookup fundefnclass_name false l s in
      
      match st with
      | (St_node(_,{st_es=es })) -> 
          let e,es' = 
            (let rev_es = List.rev es in
            match rev_es with
            | e::es' -> e, List.rev es'
            | _ -> failwith "process_raw_funclause internal error - empty list ") in
          (* synthesise a symterm node for the meta production of the term grammar *)
          let lhs = St_node(dummy_loc, { st_rule_ntr_name=result_type;
                                         st_prod_name= pn_wrapper^fundefn_name;
                                         st_es = es';
                                         st_loc = dummy_loc }) in
          let rhs = 
	    match e with 
	    | Ste_st(_,st) -> st 
	    | _ -> Auxl.error "process_raw_funclause internal error - bad rhs" in
(*       print_string ("lhs symterm: "^ Grammar_pp.pp_plain_symterm lhs ^ "\n");flush stdout;  *)
(*       print_string ("rhs symterm: "^ Grammar_pp.pp_plain_symterm rhs ^ "\n");flush stdout;  *)

          { fc_lhs = lhs; fc_rhs = rhs; fc_loc = l }
      | _ -> 
	  Auxl.warning ("process_raw_funclause lost symterm: "
			^ Grammar_pp.pp_plain_symterm st ^ "\n"); 
          let lhs = St_uninterpreted(l, "error") in
          let rhs = St_uninterpreted(l, Grammar_pp.pp_plain_symterm st) in 
	  { fc_lhs = lhs; fc_rhs = rhs; fc_loc = l }
          
let process_raw_fundefn : pp_mode -> syntaxdefn -> made_parser -> string -> raw_fundefn -> fundefn
    = fun m xd lookup fundefnclass_name rfd -> 

      let prod_name = (rfd.raw_fd_pn_wrapper^rfd.raw_fd_name) in
      let p = Auxl.prod_of_prodname xd prod_name in
      let es = p.prod_es in 
(*       (match m with Ascii ao when ao.ppa_show_defns ->  *)
(*         print_string (rfd.raw_fd_name^" ");flush stdout  *)
(*       | _ -> ()); *)
      (*print_string ("process_raw_fundefn prod_name = "^prod_name^"***"^(String.concat "" (List.map Grammar_pp.pp_plain_element es))^"***\n");flush stdout;  *)
      let c = Term_parser.cd_env_of_syntaxdefn xd in
      let fd_result = snd rfd.raw_fd_result in
      let fd_result_type = rfd.raw_fd_result_type in
      { fd_name=rfd.raw_fd_name;
        fd_form=
          St_node(dummy_loc, { st_rule_ntr_name=fd_result_type;
                               st_prod_name= prod_name ;
                               st_es = Auxl.option_map Grammar_pp.canonical_symterm_element_of_element es;
                               st_loc = rfd.raw_fd_loc }) ;
        fd_result = fd_result; 
        fd_result_type = fd_result_type; 
        fd_pn_wrapper = rfd.raw_fd_pn_wrapper;
        fd_clauses = List.map
          (process_raw_funclause m xd lookup fundefnclass_name rfd.raw_fd_pn_wrapper rfd.raw_fd_name fd_result_type) 
          rfd.raw_fd_clauses;
        fd_homs =  List.map (Grammar_typecheck.cd_hom Hu_fundefn c es) rfd.raw_fd_homs;
        fd_loc = dummy_loc} 

let process_raw_fundefnclass : pp_mode -> syntaxdefn -> made_parser -> raw_fundefnclass -> fundefnclass
    = fun m xd lookup rfdc -> 
      let c = Term_parser.cd_env_of_syntaxdefn xd in
      { fdc_name=rfdc.raw_fdc_name;
        fdc_homs =  List.map (Grammar_typecheck.cd_hom Hu_fundefnclass c []) rfdc.raw_fdc_homs;
	fdc_fundefns = List.map 
          (process_raw_fundefn m xd lookup rfdc.raw_fdc_name) rfdc.raw_fdc_fundefns;
	fdc_loc = dummy_loc} 

(* **************** *)        

let process_raw_defnclasss : pp_mode -> syntaxdefn -> made_parser -> raw_fun_or_reln_defnclass list -> fun_or_reln_defnclass list 
    = fun m xd lookup rdcs ->
      let dcs = List.map (function rfrdc -> 
        let frdc = 
          match rfrdc with
          | Raw_FDC rfdc -> FDC (process_raw_fundefnclass m xd lookup rfdc)
          | Raw_RDC rdc -> RDC (process_raw_defnclass m xd lookup rdc) in
        (match m with 
        | Ascii ao when ao.ppa_show_defns -> 
            pp_fun_or_reln_defnclass stdout m xd lookup frdc
        | _ -> ());
        flush stdout;
        frdc
                         ) rdcs in
      
(*      print_string (let m = pp_syntaxdefn_opts_default in String.concat "\n" (List.map (function dc -> pp_ascii_defnclass m xd dc (* ^pp_isa_defnclass m xd dc*)) dcs)); *)
      dcs
	(* raise NotImplementedYet *)


(** ***************** *)
(** goodness counting *)
(** ***************** *)

(* check that a symterm has no uninterpreted elements *)
let rec no_uninterpreted_symterm st 
    = match st with
    | St_node (l,stnb) -> no_uninterpreted_symterm_node_body stnb
    | St_nonterm (l,ntrp,nt)  -> true
    | St_nontermsub (l,ntrpl,ntrpt,nt)  -> true
    | St_uninterpreted (l,s) -> false
and no_uninterpreted_symterm_element e 
    = match e with
    | Ste_st (l,st) -> no_uninterpreted_symterm st
    | Ste_metavar (l,mvrp,mb) -> true
    | Ste_var (l,mvrp,var) -> true
    | Ste_list (l,stlis) -> List.for_all no_uninterpreted_symterm_list_item stlis
and no_uninterpreted_symterm_list_item stli 
    = match stli with
    | Stli_single(l,stes) -> 
        List.for_all no_uninterpreted_symterm_element stes
    | Stli_listform stlb ->
        no_uninterpreted_symterm_list_body stlb
and no_uninterpreted_symterm_node_body stnb
    = List.for_all no_uninterpreted_symterm_element stnb.st_es
and no_uninterpreted_symterm_list_body stlb
    = List.for_all no_uninterpreted_symterm_element stlb.stl_elements
    
(* count the number of rules that do not / do have uninterpreted elements *)
let sum_pairs xys = 
  List.fold_left (function (x,y) -> function (x',y') -> (x+x',y+y')) (0,0) xys 

let count_good_clauses_drule : drule -> int*int
    = fun dr -> 
      let sts = dr.drule_conclusion::List.map snd dr.drule_premises in
      let n_all = List.length sts in
      let n_good = 
	List.length ((List.filter no_uninterpreted_symterm) sts) in
      (n_good, n_all-n_good)

let count_good_clauses_psr : processed_semiraw_rule -> int*int
    = fun psr -> match psr with
    | PSR_Rule dr -> count_good_clauses_drule dr
    | PSR_Defncom _ -> (0,0)

let count_good_clauses_defn : defn -> int*int
    = fun d -> 
      sum_pairs (List.map count_good_clauses_psr d.d_rules)

let count_good_clauses_defnclass : defnclass -> int*int
    = fun dc ->
      sum_pairs (List.map count_good_clauses_defn dc.dc_defns)

let count_good_clauses_defnclasses : defnclass list-> int*int
    = fun dcs ->
      sum_pairs (List.map count_good_clauses_defnclass dcs)

let count_good_drule : drule -> int*int
    = fun dr -> 
      let (n_good,n_bad) = count_good_clauses_drule dr in 
      if n_bad=0 then (1,0) else (0,1)                            
let count_good_psr : processed_semiraw_rule -> int*int
    = fun psr ->
      match psr with
      | PSR_Rule dr -> count_good_drule dr
      | PSR_Defncom es -> (0,0)
let count_good_defn : defn -> int*int
    = fun d -> 
      sum_pairs (List.map count_good_psr d.d_rules)
let count_good_defnclass : defnclass -> int*int
    = fun dc ->
      sum_pairs (List.map count_good_defn dc.dc_defns)
let count_good_defnclasses : defnclass list-> int*int
    = fun dcs ->
      sum_pairs (List.map count_good_defnclass dcs)

let pp_counts sd = 
  let defnclasses = Auxl.option_map (fun frdc -> match frdc with RDC dc -> Some dc | FDC _ -> None) sd.relations in
  let (good,bad) = count_good_defnclasses defnclasses in
  let (good',bad') = count_good_clauses_defnclasses defnclasses in
  bad <> 0 || bad' <> 0,
  if good+bad = 0 then "" else
  ("Definition rules:        "
  ^string_of_int good ^" good    "
  ^string_of_int bad^" bad\n"
  ^ "Definition rule clauses: "
  ^string_of_int good'^" good    "
  ^string_of_int bad'^" bad\n")
                         




