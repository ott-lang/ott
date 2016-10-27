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

exception Cannot_parse_fake_rhs

(* *** compute the nts and mvs used in the symterms used for the lhs's of a rule *** *)

(* this is called also from substs_pp and subrules_pp - should be moved to auxl if we had recursive modules *)
let sts_for_lhss m xd r = 
  List.map 
    (function p ->
      let lhs_stnb = 
        Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in
      let lhs_st = St_node(dummy_loc,lhs_stnb) in
      lhs_st) 
    r.rule_ps 

let nts_used_in_lhss m xd r = 
  Auxl.nts_of_symterms (sts_for_lhss m xd r)

let mvs_used_in_lhss m xd r = 
  Auxl.mvs_of_symterms (sts_for_lhss m xd r)

(* *** pp of the fake rhs *** *)

(* this function builds the string containing the fake rhs *)
let fake_rhs m xd (hole:nonterm) (r:rule) (p:prod) =
  let rhs_stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in
  let rhs_st = St_node(dummy_loc,rhs_stnb) in
  let fake_rhs_with_hole = Grammar_pp.pp_symterm error_opts xd [] de_empty rhs_st in

  (* FZ instead of regexp we should directly print the string with the fake_hole_var in it *)
  let rgx = Str.regexp_string (Str.quote "__") in
  let fake_hole_var = Grammar_pp.pp_nonterm m xd hole in
  Str.replace_first rgx fake_hole_var fake_rhs_with_hole 

(* this function does the fake_rhs pretty printing and subsequent parsing *)
(* it is used both by grammar typecheck, to verify the subgrammar inclusion *)
(* and by pp_prod_context below, to build the rhs *)

let context_app_rhs m xd lookup (hole:nonterm) (target:nontermroot) (r:rule) (p:prod) : bool * string option =
  try
    let fake_rhs = fake_rhs m xd hole r p in 
(*    print_endline ("*** fr:"^fake_rhs); *)
    (*parse the fake rhs*)
    let sts = Term_parser.parse_complete lookup target false fake_rhs in 
    let sts_e = 
      match List.length sts with
      | 0 -> raise Cannot_parse_fake_rhs 
             (* Auxl.error ("internal: cannot parse context fake rhs: "^ fake_rhs ^"\n") *)
      | 1 -> 
	( match m with
	| Caml _ -> Auxl.capitalize_prodnames_in_symterm (List.hd sts)
	| _ -> List.hd sts )
      | _ -> Auxl.warning ("internal: multiple parses context fake rhs: "^fake_rhs^"\n"); List.hd sts in
    let sie = [] in
    let ((de1,de2) as de,de3,pptbe) = Bounds.bound_extraction m xd dummy_loc [sts_e]  in
    (true, Some (Grammar_pp.pp_symterm m xd sie de sts_e))
  with Cannot_parse_fake_rhs -> (false, None)

(* *** all together *** *)

let pp_prod_context m xd lookup (hole:nonterm) (target:nontermroot) (r:rule) (p:prod) =
  (* compute the lhs *)
  let lhs_stnb = Grammar_pp.canonical_symterm_node_body_of_prod r.rule_ntr_name p in
  let lhs_st = St_node(dummy_loc,lhs_stnb) in
  let sie = [] in
  let ((de1,de2) as de,de3,pptbe) = Bounds.bound_extraction m xd dummy_loc [lhs_st]  in
  let lhs_pat = Grammar_pp.pp_symterm m xd sie de lhs_st in
  let lhs = 
    ( match m with
    | Coq _ | Caml _ -> lhs_pat 
    | Isa _ | Hol _ | Lem _ | Twf _ -> lhs_pat ^ " " ^ Grammar_pp.pp_nonterm m xd hole
    | Lex _ | Yacc _ | Tex _ | Ascii _ -> assert false) in
  (* compute the rhs *)
  let rhs = Auxl.the (snd (context_app_rhs m xd lookup hole target r p)) in
  (* all together *)
  (p.prod_name, lhs, rhs)

let pp_rule_context m xd lookup cr : int_func =
  let e_rule = Auxl.rule_of_ntr xd cr.cr_ntr in
  let nts_used = ref (nts_used_in_lhss m xd e_rule) in     
  let ctx = Auxl.fresh_nt !nts_used (cr.cr_ntr,[]) in
  let ctx_var = Grammar_pp.pp_nonterm m xd ctx in
  nts_used := ctx::!nts_used; 

  let fake_hole = (Auxl.fresh_nt !nts_used (cr.cr_hole,[])) in 
  let fake_hole_var = Grammar_pp.pp_nonterm m xd fake_hole in

  let clauses = List.map (pp_prod_context m xd lookup fake_hole cr.cr_target e_rule) e_rule.rule_ps in

  let id = Auxl.context_name cr.cr_ntr cr.cr_hole in
  let header = 
    ( match m with
    | Coq _ ->
	( id 
	  ^ " ("^ctx_var^":"^ Grammar_pp.pp_nontermroot_ty m xd cr.cr_ntr 
	  ^ ") ("^fake_hole_var^":"^ Grammar_pp.pp_nontermroot_ty m xd cr.cr_hole ^")",
	  "",
	  " : " ^ (Grammar_pp.pp_nontermroot_ty m xd cr.cr_target) ^ " :=\n  match "^ctx_var^" with\n")
    | Isa _ ->
	( id ^ " :: \"" 
	  ^ Grammar_pp.pp_nontermroot_ty m xd cr.cr_ntr ^ " => " 
	  ^ Grammar_pp.pp_nontermroot_ty m xd cr.cr_hole ^ " => " 
	  ^ Grammar_pp.pp_nontermroot_ty m xd cr.cr_target ^ "\"\n", "", "")
    | Hol _ -> ("","","")
    | Lem _ -> raise LemTODO (* LemTODO23*)
    | Caml _ ->
	( id 
	  ^ " ("^ctx_var^":"^ Grammar_pp.pp_nontermroot_ty m xd cr.cr_ntr 
	  ^ ") ("^fake_hole_var^":"^ Grammar_pp.pp_nontermroot_ty m xd cr.cr_hole ^")",
	  "",
	  " : " ^ (Grammar_pp.pp_nontermroot_ty m xd cr.cr_target) ^ " =\n  match "^ctx_var^" with\n")
    | Twf _ -> Auxl.errorm m "pp_rule_context"
    | Lex _ | Yacc _ | Tex _ | Ascii _ -> assert false
    ) in

  { r_fun_id = id;
    r_fun_dep = [];
    r_fun_type = cr.cr_ntr;
    r_fun_header = header;
    r_fun_clauses = clauses }

let pp_context m xd lookup crs = 
  Dependency.collapse m xd 
    { i_funcs = (List.map (pp_rule_context m xd lookup) crs);
      i_funcs_proof = None }




