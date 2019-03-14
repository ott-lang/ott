(* 

   A different approach to auxifying grammar rules *and* definitions: we auxify as a rewrite
   on the non-raw grammar and definitions.
 *)
open Types
open Grammar_rewrite

let auxify_prod p = { p with prod_es = (Lang_nonterm ("loc",("loc", [])) :: p.prod_es ) }


let do_auxify xd ntr_name =
  let rule = Auxl.rule_of_ntr_nonprimary xd ntr_name in
  match Auxl.hom_spec_for_hom_name "aux"   rule.rule_homs with
  | Some _ -> true
  | _ -> false
                      
let auxify_rule r = match (Auxl.hom_spec_for_hom_name "aux" r.rule_homs) with
                        | Some aux_hom -> { r with rule_ps = List.map auxify_prod r.rule_ps }
                        | None -> r

let auxify_st xd st = match st with
  | St_node (loc,stnb) when do_auxify xd stnb.st_rule_ntr_name ->
     Printf.eprintf "auxify_st \n";
     let new_ste = Ste_st(loc,St_nonterm(loc, "loc",("loc",[]))) in
     St_node(loc, { stnb with st_es = new_ste :: stnb.st_es })
  | _ -> st
                          
let auxify_drule xd ( dr : drule ) : drule =
  Printf.eprintf "auxify_drule\n";
  (*  print_endline (Grammar_pp.pp_symterm Isa_rules_rewrite.m_ascii xd [] de_empty dr.drule_conclusion);*)
  print_endline (Grammar_pp.pp_plain_symterm dr.drule_conclusion);
  let new_conc = map_st { id_mf with f_st = auxify_st xd } dr.drule_conclusion  in
  print_endline (Grammar_pp.pp_plain_symterm new_conc);
  { dr with drule_conclusion = new_conc;
            drule_premises = List.map (fun (os,st,hs) -> (os, map_st { id_mf with f_st = auxify_st xd } st, hs)) dr.drule_premises
  }

let auxify (sd : systemdefn ) : systemdefn = { sd with
                                               syntax = { sd.syntax with xd_rs = List.map auxify_rule sd.syntax.xd_rs };
                                               relations = map_rel (auxify_drule sd.syntax) sd.relations
                                             }

  
