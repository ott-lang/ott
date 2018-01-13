open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory;
open ottLib caml_typedefTheory;
open utilTheory basicTheory environmentTheory shiftTheory;

val _ = new_theory "strengthen";

val _ = Parse.hide "S";

val value_env_teq_str_thm = Q.store_thm ("value_env_teq_str_thm",
`!E t1 t2. JTeq E t1 t2 ==> (E=E1++E2++E3) /\ value_env E2 ==> JTeq (E1++E3) t1 t2`,
RULE_INDUCT_TAC JTeq_ind []
[([``"JTeq_refl"``], METIS_TAC [value_env_ok_str_thm, JTeq_rules]),
 ([``"JTeq_sym"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_trans"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_arrow"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_tuple"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 3 DISJ2_TAC THEN
      METIS_TAC []),
 ([``"JTeq_constr"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 4 DISJ2_TAC THEN
      METIS_TAC [value_env_ok_str_thm]),
 ([``"JTeq_expand"``],
  SRW_TAC [] [] THEN SRW_TAC [] [Once JTeq_cases, MAP_MAP] THEN NTAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
      IMP_RES_TAC value_env_lookup_str_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN METIS_TAC [value_env_ok_str_thm])]);

val value_env_inst_str_thm = Q.store_thm ("value_env_inst_str_thm",
`!E1 E2 E3 t ts. value_env E2 /\ JTinst (E1++E2++E3) t ts ==> JTinst (E1++E3) t ts`,
SRW_TAC [] [JTinst_cases, EVERY_MEM] THEN METIS_TAC [value_env_ok_str_thm]);

val value_env_inst_named_str_thm = Q.store_thm ("value_env_inst_named_str_thm",
`!E1 E2 E3 t tpo t'. value_env E2 /\ JTinst_named (E1++E2++E3) t tpo t' ==> JTinst_named (E1++E3) t tpo t'`,
SRW_TAC [] [JTinst_named_cases, EVERY_MEM] THEN METIS_TAC [value_env_ok_str_thm]);

val value_env_constr_p_str_thm = Q.store_thm ("value_env_constr_p_str_thm",
`!E1 E2 E3 c ts t. value_env E2 /\ JTconstr_p (E1++E2++E3) c ts t ==> JTconstr_p (E1++E3) c ts t`,
SRW_TAC [] [JTconstr_p_cases] THEN
METIS_TAC [value_env_ok_str_thm, value_env_lookup_str_thm, value_env_inst_named_str_thm]);

val value_env_constr_c_str_thm = Q.store_thm ("value_env_constr_c_str_thm",
`!E1 E2 E3 c t. value_env E2 /\ JTconstr_c (E1++E2++E3) c t ==> JTconstr_c (E1++E3) c t`,
SRW_TAC [] [JTconstr_c_cases] THEN
METIS_TAC [value_env_ok_str_thm, value_env_lookup_str_thm, value_env_inst_named_str_thm, EVERY_MEM]);

val value_env_field_str_thm = Q.store_thm ("value_env_field_str_thm",
`!E1 E2 E3 c ts t. value_env E2 /\ JTfield (E1++E2++E3) c ts t ==> JTfield (E1++E3) c ts t`,
SRW_TAC [] [JTfield_cases] THEN
METIS_TAC [value_env_ok_str_thm, value_env_lookup_str_thm, value_env_inst_named_str_thm]);

val value_env_const_str_thm = Q.store_thm ("value_env_const_str_thm",
`!E1 E2 E3 c t. value_env E2 /\ JTconst (E1++E2++E3) c t ==> JTconst (E1++E3) c t`,
SRW_TAC [] [JTconst_cases] THEN
METIS_TAC [value_env_ok_str_thm, value_env_constr_c_str_thm]);

val value_env_inst_any_thm = Q.store_thm ("value_env_inst_any_thm",
`!E t t'. JTinst_any E t t' ==> !E1 E2 E3. (E = E1++E2++E3) /\ value_env E2 ==> JTinst_any (E1++E3) t t'`,
RULE_INDUCT_TAC JTinst_any_ind [JTinst_any_fun, EVERY_MEM] [] THEN
METIS_TAC [value_env_ok_str_thm]);

val value_env_pat_str_thm = SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM] ( Q.prove (
`!S E p t E'. JTpat S E p t E' ==> !E1 E2 E3. (E = E1++E2++E3) /\ value_env E2 ==> JTpat S (E1++E3) p t E'`,
RULE_INDUCT_TAC JTpat_ind [JTpat_fun] [] THEN 
SRW_TAC [ARITH_ss] [] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
METIS_TAC [value_env_ok_str_thm, value_env_const_str_thm, value_env_constr_p_str_thm,
           value_env_field_str_thm, value_env_inst_any_thm, value_env_teq_str_thm]));

val _ = save_thm ("value_env_pat_str_thm", value_env_pat_str_thm);

val value_env_uprim_str_thm = Q.store_thm ("value_env_uprim_str_thm",
`!E1 E2 E3 u t. value_env E2 /\ JTuprim (E1++E2++E3) u t ==> JTuprim (E1++E3) u t`,
SRW_TAC [] [JTuprim_cases] THEN METIS_TAC [value_env_ok_str_thm]);

val value_env_bprim_str_thm = Q.store_thm ("value_env_bprim_str_thm",
`!E1 E2 E3 u t. value_env E2 /\ JTbprim (E1++E2++E3) u t ==> JTbprim (E1++E3) u t`,
SRW_TAC [] [JTbprim_cases] THEN METIS_TAC [value_env_ok_str_thm]);

val value_env_val_name_str_thm = Q.store_thm ("value_env_val_name_str_thm",
`!E1 E2 E3 vn t. value_env E2 /\ (!x. MEM x (MAP domEB E2) ==> MEM x (MAP domEB E1)) /\ 
                JTvalue_name (E1++E2++E3) vn t ==>
                JTvalue_name (E1++E3) vn t`,
SRW_TAC [] [JTvalue_name_cases, lookup_append_thm] THEN
Cases_on `lookup E1 (name_vn vn)` THEN FULL_SIMP_TAC list_ss [] THENL
[Cases_on `lookup E2 (name_vn vn)` THEN FULL_SIMP_TAC list_ss [num_tv_append_thm] THEN SRW_TAC [] [] THEN
        METIS_TAC [value_env_inst_str_thm, lookup_dom_thm, value_env_num_tv_thm, ADD_0],
 METIS_TAC [value_env_inst_str_thm]]);

val value_env_str_thm = 
SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM] ( Q.prove (
`(!S E e t. JTe S E e t ==> !E1. (E = E1++E2++E3) /\ value_env E2 /\
          (!x. MEM x (MAP domEB E2) ==> MEM x (MAP domEB E1)) ==>
          JTe S (E1++E3) e t) /\
 (!S E pm t E'. JTpat_matching S E pm t E' ==> !E1. (E = E1++E2++E3) /\ value_env E2 /\ 
              (!x. MEM x (MAP domEB E2) ==> MEM x (MAP domEB E1)) ==>
              JTpat_matching S (E1++E3) pm t E') /\
 (!S E lb E'. JTlet_binding S E lb E' ==> !E1. (E = E1++E2++E3) /\ value_env E2 /\
            (!x. MEM x (MAP domEB E2) ==> MEM x (MAP domEB E1)) ==>
            JTlet_binding S (E1++E3) lb E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==> !E1. (E = E1++E2++E3) /\ value_env E2 /\
              (!x. MEM x (MAP domEB E2) ==> MEM x (MAP domEB E1)) ==>
              JTletrec_binding S (E1++E3) lrbs E')`,
RULE_INDUCT_TAC JTe_ind [JTe_fun]
[([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_ident"``, ``"JTe_constant"``, ``"JTe_record_proj"``,
   ``"JTe_typed"``],
  METIS_TAC [value_env_uprim_str_thm, value_env_bprim_str_thm, value_env_const_str_thm, value_env_teq_str_thm,
             value_env_val_name_str_thm, value_env_field_str_thm, value_env_inst_any_thm]),
 ([``"JTe_tuple"``, ``"JTe_construct"``, ``"JTe_record_constr"``, ``"JTe_record_with"``, ``"JTe_apply"``],
  FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [value_env_constr_p_str_thm, value_env_lookup_str_thm, value_env_field_str_thm,
                   value_env_teq_str_thm]),
 ([``"JTe_cons"``, ``"JTe_match"``, ``"JTe_and"``, ``"JTe_or"``, ``"JTe_while"``, ``"JTe_function"``],
  METIS_TAC [value_env_teq_str_thm]),
 ([``"JTe_for"``, ``"JTe_let_poly"``, ``"JTe_letrec"``, ``"JTe_let_mono"``], 
  SRW_TAC [] [shiftt_def] THEN FULL_SIMP_TAC std_ss [APPEND_11, GSYM APPEND, APPEND_ASSOC] THEN
        FULL_SIMP_TAC list_ss [] THEN METIS_TAC [value_env_teq_str_thm]),
 ([``"JTe_assert"``, ``"JTe_assertfalse"``], METIS_TAC [value_env_ok_str_thm, value_env_teq_str_thm]),
 ([``"JTe_location"``], METIS_TAC [value_env_ok_str_thm, value_env_lookup_str_thm, value_env_teq_str_thm]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [ARITH_ss] [] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
            METIS_TAC [value_env_pat_str_thm, MEM_APPEND, MAP_APPEND]),
 ([``"JTlet_binding_poly"``], METIS_TAC [value_env_pat_str_thm]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        Q.EXISTS_TAC `value_name_pattern_matching_t_t'_list` THEN SRW_TAC [] [] THEN
        METIS_TAC [MEM_APPEND, MAP_APPEND, value_env_ok_str_thm])]));

val _ = save_thm ("value_env_str_thm", value_env_str_thm);

val _ = export_theory ();
