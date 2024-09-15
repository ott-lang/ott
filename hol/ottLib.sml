(**************************************************************************)
(*                               ottLib                                   *)
(*                                                                        *)
(*        Scott Owens, Computer Laboratory, University of Cambridge       *)
(*                                                                        *)
(*  Copyright 2006                                                        *)
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

structure ottLib :> ottLib = struct

infix THEN

open numSyntax listSyntax pairSyntax listTheory HolKernel bossLib boolLib Defn; 
open ottTheory;

fun inst_filter_size tm =
  case total (PART_MATCH (fst o dest_leq) filter_size) tm of
    NONE => 
      if is_comb tm then 
        let val (f, args) = strip_comb tm in
          inst_filter_size f @ List.concat (List.map inst_filter_size args)
        end
      else
        []
  | SOME thm => [thm];

fun APPLY_FILTER_SIZE (assums, g) =
  case inst_filter_size g of
    [] => ALL_TAC (assums, g)
  | l => (MAP_EVERY STRIP_ASSUME_TAC l) (assums, g);

fun find_list t =
  if is_var t then
    t
  else if is_map t then
    find_list (snd (dest_map t))
  else
    t;

fun PAIR_CASES_TAC (a, g) = 
  case total dest_prod (type_of (fst (dest_forall g))) of
    NONE => ALL_TAC (a, g)
  | SOME _ => Cases (a, g);


fun MEM_IND_TAC mem =
let val (arg1, arg2) = dest_mem mem
    val lst = find_list arg2
in
  PAT_ASSUM mem (fn ma => REPEAT (POP_ASSUM MP_TAC) THEN MP_TAC ma) THEN
  SPEC_TAC (lst, genvar (type_of lst)) THEN 
  HO_MATCH_MP_TAC list_induction THEN STRIP_TAC THENL 
  [ALL_TAC, STRIP_TAC THEN STRIP_TAC THEN PAIR_CASES_TAC] THEN
  SRW_TAC [] [] THEN 
  CONV_TAC TotalDefn.TC_SIMP_CONV THEN 
  SRW_TAC [] [] THEN
  RES_TAC THEN
  DECIDE_TAC THEN NO_TAC
end;

fun ONE_TERM_TAC measure =
  WF_REL_TAC `^measure` THEN
  CONV_TAC TotalDefn.TC_SIMP_CONV THEN  
  SRW_TAC [] [] THEN
  APPLY_FILTER_SIZE THEN 
  TRY (ASSUM_LIST (MAP_FIRST MEM_IND_TAC o List.filter is_mem o List.map concl))
  THEN
  RES_TAC THEN DECIDE_TAC THEN NO_TAC;

fun TERM_TAC defn = (MAP_FIRST ONE_TERM_TAC (TotalDefn.guessR defn));

fun ottDefine name tq =
      let val defn = Hol_defn name tq in
        if not (null (tcs_of defn)) then 
          fst (tstore_defn (defn, TERM_TAC defn)) 
        else
          (save_defn defn;
           LIST_CONJ (eqns_of defn))
      end;

(* Adapted from THENL *)
fun mapshape [] _ _ =  []
  | mapshape (n1::nums) (f1::funcs) args =
     let val (f1_args,args') = split_after n1 args
     in f1 f1_args :: mapshape nums funcs args'
     end;

fun mk_branch_name (consts, TAC) =
((fn (assums, g) => 
    let val (cn, goal_name) = (dest_comb o hd o strip_conj o fst o dest_imp o snd o strip_forall) g in
       same_const ``clause_name`` cn andalso
       List.exists (fn tm => term_eq goal_name tm) consts
    end),
 TAC);

fun mk_branch (consts, TAC) =
((fn (assums, g) => List.exists (fn const => can (find_term (can (match_term const))) g) consts),
 TAC);

fun THENcases (rws:thm list) (tac1:tactic) (branches:((term list * term -> bool) * tactic) list) : tactic =
fn g =>
let val tac2 = SIMP_TAC (srw_ss()) rws;
    fun apply_branch subgoal =
      case List.find (fn (pred, T) => pred subgoal) branches of
        NONE => tac2 subgoal
      | SOME (pred, T) =>
          (case (tac2 THEN T) subgoal of
             ([], vf) => let val th = vf [] in ([], fn [] => th) end
           | x => x);
    val (gl, vf) = tac1 g;
    val (G,V,lengths) =
      itlist (fn goal => fn (G,V,lengths) =>
                let val (goals, vfun) = apply_branch goal in
                  (goals@G, vfun::V, length goals::lengths)
                end)
             gl
             ([],[],[]);
in
  case G of
    [] => ([], let val th = vf (map (fn f => f[]) V) in fn [] => th end)
  | _  => (G, (vf o mapshape lengths V))
end
handle e as HOL_ERR _ => raise (wrap_exn "Tactical" "THENcases" e);

fun RULE_INDUCT_TAC (ind:thm) (rws:thm list) (spec:(term list * tactic) list) : tactic =
  THENcases rws (HO_MATCH_MP_TAC ind THEN REPEAT CONJ_TAC) (List.map mk_branch_name spec);

fun INDUCT_TAC (ind:thm) (rws:thm list) (spec:(term list * tactic) list) : tactic =
  THENcases rws (HO_MATCH_MP_TAC ind THEN REPEAT CONJ_TAC) (List.map mk_branch spec);

fun get_terms f =
  List.map (hd o snd o strip_comb o hd o snd o strip_comb o concl o SPEC_ALL) (CONJUNCTS f)

fun structural_cases datatype_thms arg cases thm =
  let fun helper (terms, thm) =
        let val thm1 = LIST_CONJ (List.map (fn qt => (GEN_ALL o SPEC qt o funpow arg Q.ID_SPEC) thm) terms)
        in SIMP_RULE bool_ss datatype_thms thm1 end
  in
    LIST_CONJ (ListPair.map helper (cases, CONJUNCTS thm))
  end;


end
