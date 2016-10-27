(* by Scott Owens *)

(*load "stlcTheory";*)

open HolKernel boolLib bossLib test10stTheory IndDefLib IndDefRules listTheory optionTheory relationTheory;

val _ = new_theory "test10st_metatheory";

val list_minus_thm = Q.prove (
`!l x. ~(MEM x (list_minus l [x])) /\
       (!x'. ~(x' = x) /\ MEM x' l ==> MEM x' (list_minus l [x])) /\
       (!x'. MEM x' (list_minus l [x]) ==> MEM x' l)`,
Induct THEN RW_TAC list_ss [list_minus_def] THEN METIS_TAC []);

val datatype_thms = [T_11, T_distinct, t_11, t_distinct];

val lookup_def = Define `
(lookup [] x = NONE) /\
(lookup ((x',Ty)::G) x = if x' = x then SOME Ty else lookup G x)`;

val lookup_thm = Q.prove (
`!G x Ty. (lookup G x = SOME Ty) = (?G1 G2. (G = G1++(x, Ty)::G2) /\ ~(MEM x (MAP FST G1)))`,
recInduct (fetch "-" "lookup_ind") THEN RW_TAC list_ss [lookup_def] THEN EQ_TAC THEN RW_TAC list_ss []
THENL [
  METIS_TAC [MEM, APPEND, MAP],
  Cases_on `G1` THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [],
  Q.EXISTS_TAC `(x',Ty)::G1` THEN RW_TAC list_ss [],
  Cases_on `G1` THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []
]);

val GtT_rules = SIMP_RULE bool_ss [GSYM lookup_thm] GtT_rules;
val GtT_ind = SIMP_RULE bool_ss [GSYM lookup_thm] GtT_ind;
val GtT_cases = SIMP_RULE bool_ss [GSYM lookup_thm] GtT_cases;

fun structural_cases arg cases thm =
  let fun helper (terms, thm) =
        let val thm1 = LIST_CONJ (List.map (fn qt => (GEN_ALL o SPEC qt o funpow arg Q.ID_SPEC) thm) terms)
        in SIMP_RULE list_ss datatype_thms thm1 end
  in
    LIST_CONJ (ListPair.map helper (cases, CONJUNCTS thm))
  end;

fun get_terms f =
  List.map (hd o snd o strip_comb o hd o snd o strip_comb o concl o SPEC_ALL) (CONJUNCTS f)

val terms = get_terms is_v_of_t_def;

val reduce_fun = structural_cases 0 [terms] reduce_cases;
val GtT_fun = structural_cases 1 [terms] GtT_cases;

val GtT_sind = IndDefLib.derive_strong_induction (GtT_rules, GtT_ind);
val reduce_sind = IndDefLib.derive_strong_induction (reduce_rules, reduce_ind);

fun RI thm = RULE_INDUCT_THEN thm STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

val canon_val_lem = Q.prove (
`!t Ty G. is_v_of_t t /\ (?T1 T2. GtT G t (T_arrow T1 T2)) ==> ?x t'. t = t_Lam x t'`,
Induct THEN RW_TAC list_ss [GtT_fun, is_v_of_t_def]);

val progress_thm = Q.prove (
`!G t Ty. GtT G t Ty ==> (G = []) ==> is_v_of_t t \/ ?t'. reduce t t'`,
RI GtT_sind THEN IMP_RES_TAC canon_val_lem THEN RW_TAC list_ss [reduce_fun, GtT_fun, is_v_of_t_def] THEN
METIS_TAC [lookup_def, NOT_SOME_NONE, is_v_of_t_def]);

val context_lem = Q.prove (
`!G t Ty. GtT G t Ty ==> 
   !G'. (!x. MEM x (fv_t t) ==> (lookup G x = lookup G' x)) ==>
        GtT G' t Ty`,
RI GtT_sind THEN RW_TAC list_ss [GtT_fun, fv_t_def] THEN METIS_TAC [list_minus_thm, lookup_def]);

val fv_lem = Q.prove(
`!G t Ty. GtT G t Ty ==> !x. MEM x (fv_t t) ==> ?Ty'. lookup G x = SOME Ty'`,
RI GtT_sind THEN RW_TAC list_ss [fv_t_def, lookup_def] THEN
  METIS_TAC [lookup_def, list_minus_thm]);

val weakening_lem = Q.prove(
`!G t Ty. GtT G t Ty ==>
   !G'. (!x T1. (lookup G x = SOME T1) ==> (lookup G' x = SOME T1)) ==>
        GtT G' t Ty`,
METIS_TAC [context_lem, fv_lem]);

val subst_lem = Q.prove (
`!G t Ty. GtT G t Ty ==>
   !x T1 t'. (lookup G x = SOME T1) /\ GtT [] t' T1 ==> GtT G (tsubst_t t' x t) Ty`,
RI GtT_sind THEN RW_TAC list_ss [tsubst_t_def, GtT_fun, lookup_def] THEN
METIS_TAC [weakening_lem, NOT_SOME_NONE, lookup_def, SOME_11]);

val subst_fv_lem = Q.prove(
`!t t' x. ~(MEM x (fv_t t')) ==> ~(MEM x (fv_t (tsubst_t t' x t)))`,
Induct THEN RW_TAC list_ss [tsubst_t_def, fv_t_def] THEN METIS_TAC [list_minus_thm]);

val preservation_thm = Q.prove(
`!t t'. reduce t t' ==> !Ty. GtT [] t Ty ==> GtT [] t' Ty`,
RI reduce_sind THEN RW_TAC list_ss [GtT_fun] THEN 
METIS_TAC [fv_lem, NOT_SOME_NONE, context_lem, subst_fv_lem, lookup_def, subst_lem]);

val soundness_thm = Q.store_thm("soundness_thm",
`!t t'. (RTC reduce) t t' ==> !Ty. GtT [] t Ty ==> is_v_of_t t' \/ ?t''. reduce t' t''`,
HO_MATCH_MP_TAC RTC_INDUCT THEN RW_TAC list_ss [] THEN METIS_TAC [preservation_thm, progress_thm]);

val val_reduce_lem = Q.prove (
`!t t'. is_v_of_t t ==> ~(reduce t t')`,
Induct THEN RW_TAC list_ss [is_v_of_t_def, reduce_fun]);

val determinacy_thm = Q.store_thm("determinacy_thm",
`!t t1' t2'. reduce t t1' /\ reduce t t2' ==> (t1' = t2')`,
Induct THEN RW_TAC list_ss [reduce_fun, is_v_of_t_def] THEN
   METIS_TAC [val_reduce_lem, reduce_fun, is_v_of_t_def]);

val _ = export_theory();
