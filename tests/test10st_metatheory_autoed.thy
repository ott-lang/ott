theory test10st_metatheory = "test10st_snapshot_out":

(* Tom Ridge, Peter Sewell  Fri Aug 25 16:18:06 BST 2006

Proof of type preservation and progress for the test10st simply typed lambda calculus.
This is a cleaned-up version, using more automation. *)

lemma weakening_on_the_left:
  "(G0,t,T):GtT  ==> (! G . (G0@G,t,T):GtT)"
  apply(rule_tac GtT.induct)
  apply(force intro:GtT.intros)+
  done

lemma weakening_from_empty:
  "([],t,T):GtT --> (G,t,T):GtT"
  by(force dest:weakening_on_the_left)

lemma de_shadow: "! G t T. (G, t, T) : GtT --> (! x T1 G0 G1 Tv. G = G1 @ (x, T1) # G0 @ [(x, Tv)] --> (G1 @ (x, T1) # G0, t, T) : GtT)"
  apply(intro allI)  apply(rule) 
  apply(erule GtT.induct)
   apply(intro allI impI, elim exE conjE) 
   apply(rule GtT_value_nameI) 
   apply(simp) apply(clarify)
   apply(rule_tac x=G1a in exI) apply(simp) apply(rule_tac x="butlast G2" in exI) apply(case_tac G2 rule: rev_cases) apply(simp) apply(simp)
 
   apply(force intro:GtT_applyI)

   apply(intro allI impI)
   apply(rule GtT_lambdaI)
   apply(simp) apply(clarify)
   apply(drule_tac x=T1a in spec) apply(drule_tac x=G0 in spec) apply(drule_tac x="(x1,T1)#G1" in spec) apply(simp)
  done

lemma de_shadow': "(! t T x T1 G0 G1 Tv. (G1 @ (x, T1) # G0 @ [(x, Tv)], t, T) : GtT --> (G1 @ (x, T1) # G0, t, T) : GtT)"
  by (force elim:de_shadow [rule_format])

lemma substitution : 
  "(G,t,T):GtT
  --> 
  (!v x Tv G0. (
  G = G0 @[(x,Tv)]) 
  & x ~: set (map fst G0) 
  & ([],v,Tv):GtT 
  -->
  ((G0,tsubst_t v x t, T) : GtT))
  "
  apply(intro impI)
  apply(erule GtT.induct)
   apply(intro allI impI)
   apply(elim exE conjE)
   apply(simp)
   apply(intro conjI impI)
    apply(simp)
    apply(subgoal_tac "filter (%(x,y).x=xa) (G1 @ (xa, T) # G2) = filter (%(x,y).x=xa) (G0 @ [(xa, Tv)])")
    apply(simp (no_asm_use) add: List.filter_append)
    apply(subgoal_tac "[(x, y):G1. x = xa] = [] &[(x, y):G0. x = xa] = [] ") prefer 2 
    apply(force intro: filter_False)
    apply(simp) apply(erule weakening_from_empty [ rule_format]) 
    apply(simp)
   
    apply(rule GtT_value_nameI) apply(rule_tac x=G1 in exI) apply(rule_tac x="butlast G2" in exI) apply(case_tac G2 rule: rev_cases) apply(simp) apply(simp)
   
   apply(force intro: GtT_applyI)

     (* lambda case *)
   apply(intro allI impI) apply(elim exE conjE)
   apply(simp) apply(intro conjI impI)
   
      (* x1=x *)
    apply(rule GtT_lambdaI) apply(simp) 
    using de_shadow' apply(simp) apply(drule_tac x=t in spec) apply(drule_tac x=T in spec) apply(drule_tac x=x in spec)apply(drule_tac x=T1 in spec) apply(drule_tac x=G0 in spec) apply(drule_tac x="[]" in spec) apply(force)

      (* x1~=x *)
    apply(force intro: GtT_lambdaI)
  done

theorem type_preservation: "(G,t,T):GtT --> (!t'. G=[] & (t,t'):E --> (G,t',T):GtT)" 
  apply(rule impI);
  apply(erule_tac GtT.induct);

     (* vars don't reduce *)
   apply(force elim:E.cases)

     (* apps might reduce *)
   apply(intro allI impI)
   apply(elim conjE)
   apply(simp)
   apply(erule_tac E.cases)
   
    apply(force elim:GtT.cases intro:substitution [rule_format])

    apply(force elim:GtT.GtT_applyI)
   
    apply(force elim:GtT.GtT_applyI)

     (* lambdas don't reduce *)
   apply(force elim:E.cases)
  done


(* a variable of any type in the empty env can't exist *)
lemma empty_env_vars: "([],t_Var x,T) : GtT ==> False"
  by (force elim:GtT.cases) 

(* a term of function type in the empty env must be a lambda *)
lemma empty_env_canonical_functions: "([],t,Arr T1 T2) : GtT ==> is_v t ==> (? x t1'. t = t_Lam x t1')"
  by (force elim:GtT.cases)

theorem progress: "(G,t,T) : GtT --> G = [] & ~ (is_v t) --> (? t'. (t,t') : E)"
  apply(rule, erule GtT.induct)

   (* t_Var *)
   apply(force dest: empty_env_vars)
   
   (* App *)
   apply(simp) apply(rule)

   apply(rename_tac t1 t2)
   apply(case_tac "is_v t1")
    (* is_v t1 *)
    apply(case_tac "is_v t2")
     (* is_v t1, is_v t2 use AX_APP *)
     apply(force elim:E.ax_appI dest:empty_env_canonical_functions)

     (* is_v t1, ~ is_v t2 reduce t2 *)
     apply(force elim:E.ctx_app_argI) 

    (* ~ is_v t1 *)
    apply(force elim:E.ctx_app_funI)

    (* Lam *)
    apply(force)
  done

  
