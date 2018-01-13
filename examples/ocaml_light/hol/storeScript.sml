open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory shiftTheory environmentTheory validTheory;
open weakenTheory shiftTheory remv_tyvarTheory type_substsTheory;

val _ = Parse.hide "S";

val _ = new_theory "store";

val store_typing_thm = Q.store_thm ("store_typing_thm",
`!E st E'. JTstore E st E' ==> !l. (MEM (name_l l) (MAP domEB E') =
           ?v. (list_assoc l st = SOME v) /\ is_value_of_expr v)`,
RULE_INDUCT_TAC JTstore_ind [list_assoc_def, domEB_def] [] THEN METIS_TAC []);

val empty_type_sub_inst_any_thm = Q.prove (
`!E t src_t. JTinst_any E t src_t ==> !S'. JTinst_any E t (substs_typevar_typexpr S' src_t)`,
RULE_INDUCT_TAC JTinst_any_ind [JTinst_any_fun, substs_typevar_typexpr_def]
[([``"JTinst_any_tuple"``, ``"JTinst_any_ctor"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\x. (FST x, substs_typevar_typexpr S' (SND x))) t_t'_list` THEN
      SRW_TAC [] [MAP_MAP, ETA_THM, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM])]);

val empty_type_sub_pat_thm = Q.prove (
`!S E pm t E'. JTpat S E pm t E' ==> (S = []) ==> !S'. JTpat S' E pm t E'`,
RULE_INDUCT_TAC JTpat_ind [JTpat_fun]
[([``"JTpat_typed"``],
  SRW_TAC [] [substs_tv_empty_thm] THEN METIS_TAC [empty_type_sub_inst_any_thm]),
 ([``"JTpat_construct"``, ``"JTpat_tuple"``, ``"JTpat_record"``],
  SRW_TAC [] [EVERY_MEM] THEN METIS_TAC []),
 ([``"JTpat_construct_any"``, ``"JTpat_cons"``, ``"JTpat_or"``],
  METIS_TAC [])]);

val empty_type_sub_thm = Q.prove (
`(!S E e t. JTe S E e t ==> (S = []) ==> !S'. JTe S' E e t) /\
 (!S E p t t'. JTpat_matching S E p t t' ==> (S = []) ==> !S'. JTpat_matching S' E p t t') /\
 (!S E lb E'. JTlet_binding S E lb E' ==> (S = []) ==> !S'. JTlet_binding S' E lb E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==> (S = []) ==> !S'. JTletrec_binding S' E lrbs E')`,
RULE_INDUCT_TAC JTe_sind [JTe_fun, shiftTsig_def]
[([``"JTe_typed"``], 
   SRW_TAC [] [substs_tv_empty_thm] THEN METIS_TAC [empty_type_sub_inst_any_thm]), 
 ([``"JTe_tuple"``, ``"JTe_construct"``, ``"JTe_record_constr"``, ``"JTe_record_with"``,
   ``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [EVERY_MEM] THEN METIS_TAC []),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [EVERY_MEM] THEN METIS_TAC [empty_type_sub_pat_thm]), 
 ([``"JTlet_binding_poly"``],
  METIS_TAC [empty_type_sub_pat_thm])] 
THEN
METIS_TAC []);

val store_dom_thm = Q.prove (
`!E st E'. JTstore E st E' ==> (MAP (\x. name_l (FST x)) st = MAP domEB E')`,
RULE_INDUCT_TAC JTstore_ind [domEB_def]
[]);

local

val lem1 = Q.prove (
`!E1 st E2. JTstore E1 st E2 ==> !l v. (list_assoc l st = SOME v) ==>
            ?t. (!S. JTe S E1 v t) /\ (lookup E2 (name_l l) = SOME (EB_l l t))`,
RULE_INDUCT_TAC JTstore_ind [list_assoc_def] [] THEN
SRW_TAC [] [COND_EXPAND_EQ, lookup_def, shiftEB_add_thm, domEB_def] THEN METIS_TAC [empty_type_sub_thm]);

val lem2 = Q.prove (
`!E l. type_env E ==> ~MEM (name_l l) (MAP domEB E)`,
Induct THEN SRW_TAC [] [type_env_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss()) [type_env_def, domEB_def]);

val lem3 = Q.prove (
`!E st E'. JTstore E st E' ==> (!v. ~(list_assoc l st = SOME v)) ==> ~MEM (name_l l) (MAP domEB E')`,
RULE_INDUCT_TAC JTstore_ind [list_assoc_def, domEB_def]
[] THEN SRW_TAC [] []);

val lem4 = (SIMP_RULE list_ss [] o GEN_ALL o
            Q.SPECL [`[EB]`, `E`, `[]`, `v`, `t`, `[]`] o GEN_ALL o
            SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM])
           (hd (CONJUNCTS weak_not_tv_thm));

val lem5 = SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] (Q.prove (
`!E st E'. JTstore E st E' ==> !l t. Eok (EB_l l t::E) ==> JTstore (EB_l l t::E) st E'`,
RULE_INDUCT_TAC JTstore_ind [JTstore_fun]
[([``"JTstore_map"``],
  SRW_TAC [] [] THEN MATCH_MP_TAC lem4 THEN
      FULL_SIMP_TAC (srw_ss()) [domEB_def, MEM_MAP, Eok_def])]));

val lem6 = SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] (Q.prove (
`!E st E'. JTstore E st E' ==> !st1 st2 l v v' t. (st = st1++[(l, v')]++st2) /\ is_value_of_expr v /\
           JTe [] E v t /\ (lookup E' (name_l l) = SOME (EB_l l t)) /\ ~MEM l (MAP FST st1)  ==>
           JTstore E (st1++[(l, v)]++st2) E'`,
RULE_INDUCT_TAC JTstore_sind []
[] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [lookup_def, domEB_def, COND_EXPAND_EQ, shiftEB_add_thm] THEN
SRW_TAC [] [] THEN Cases_on `st1` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [JTstore_fun] THEN
FULL_SIMP_TAC list_ss [FST]));

val lem7 = Q.prove (
`!E' E1 l t. (lookup (E' ++ E1) (name_l l) = SOME (EB_l l t)) /\ type_env E1 ==> 
             (lookup E' (name_l l) = SOME (EB_l l t))`,
SRW_TAC [] [lookup_append_thm] THEN Cases_on `lookup E' (name_l l)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC lookup_dom_thm THEN METIS_TAC [lem2]);

val lem8 = Q.prove (
`!st'. DISJOINT (remove_vn_tv (MAP (\x. name_l (FST x)) st')) (remove_vn_tv [name_l l]) ==> 
       ~MEM l (MAP FST st')`,
SRW_TAC [] [DISJOINT_MEM, EVERY_MEM] THEN POP_ASSUM (ASSUME_TAC o Q.SPEC `name_l l`) THEN
FULL_SIMP_TAC (srw_ss()) [remove_vn_tv_thm, MEM_MAP]);

in

val store_in_thm = Q.store_thm ("store_in_thm",
`!st L st'. JRstore st L st' ==> !E' E1 E2. type_env E1 /\ JTstore (E'++E1) st E' ==> 
            !S. JTLin S (E'++E1) L`,
RULE_INDUCT_TAC JRstore_ind [JTLin_cases]
[([``"JRstore_lookup"``],
  SRW_TAC [] [lookup_append_thm] THEN METIS_TAC [lem1, option_case_def]),
 ([``"JRstore_alloc"``],
  SRW_TAC [] [lem2] THEN METIS_TAC [lem3])]);

val store_out_thm = Q.store_thm ("store_out_thm",
`!st L st'. JRstore st L st' ==> !E' E'' E1 E2 E7 S. JTstore (E'++E1) st E' /\ JTLout S (E'++E1) L E7 /\
            type_env E1 ==> 
            JTstore (E7++E'++E1) st' (E7++E')`,
RULE_INDUCT_TAC JRstore_ind [JTLout_cases]
[([``"JRstore_alloc"``],
  SRW_TAC [] [JTstore_fun] THEN SRW_TAC [] [value_remv_tyvar_thm] THENL
      [MATCH_MP_TAC lem5 THEN SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_thm, lem2, lem3],
       MATCH_MP_TAC lem4 THEN SRW_TAC [] [Eok_def, domEB_def, remv_tyvar_fv_thm] THEN
           METIS_TAC [remv_tyvar_thm, MEM_MAP, name_distinct, ok_thm, lem2, lem3]]),
 ([``"JRstore_assign"``],
  SRW_TAC [] [] THEN SRW_TAC [] [] THEN MATCH_MP_TAC lem6 THEN MAP_EVERY Q.EXISTS_TAC [`expr`, `t`] THEN
      SRW_TAC [] [value_remv_tyvar_thm, lookup_append_thm] THENL
      [METIS_TAC [remv_tyvar_thm],
       METIS_TAC [lem7],
       IMP_RES_TAC store_dom_thm THEN 
           `ALL_DISTINCT (remove_vn_tv (MAP domEB (E'++E1)))` 
                               by METIS_TAC [Eok_dom_thm, ok_thm, ok_ok_thm] THEN
           FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, remove_vn_tv_APPEND] THEN
           `ALL_DISTINCT (remove_vn_tv (MAP (\x. name_l (FST x)) st' ++ [name_l l] ++ 
                                        MAP (\x. name_l (FST x)) st))`
                               by METIS_TAC [] THEN 
           FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, remove_vn_tv_APPEND] THEN
           METIS_TAC [lem8]])]);
end;

local

val lem1 = Q.prove (
`!E. type_env E ==> ~MEM EB_tv E`,
Induct THEN SRW_TAC [] [type_env_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss ()) [type_env_def]);

val lem2 = Q.prove (
`!E. type_env E /\ MEM n (MAP domEB E) ==> ~?vn. n = name_vn vn`,
Induct THEN SRW_TAC [] [type_env_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss ()) [type_env_def, domEB_def]);

in

val type_env_store_weak_thm = Q.store_thm ("type_env_store_weak_thm",
`!E st E'. JTstore E st E' ==> !E1 E2 E3. (E = E1++E3) /\ type_env E2 /\ Eok (E1++E2++E3) ==> 
           JTstore (E1++E2++E3) st E'`,
RULE_INDUCT_TAC JTstore_ind [JTstore_fun]
[([``"JTstore_map"``],
  SRW_TAC [] [] THEN 
      MATCH_MP_TAC ((SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] o hd o CONJUNCTS)
                    weak_not_tv_thm) THEN 
      SRW_TAC [] [lem1] THEN METIS_TAC [lem2, MEM_MAP])]);
end;


val _ = export_theory ();
