open bossLib HolKernel boolLib combinTheory listTheory rich_listTheory optionTheory pairTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory shiftTheory basicTheory environmentTheory shiftTheory type_substsTheory;

val _ = new_theory "valid";

local

val lem1 = Q.prove (
`!EB E. Eok (EB::E) ==> EBok E EB`,
Cases_on `EB` THEN SRW_TAC [] [EBok_def, Eok_def] THENL
[Cases_on `t`,
 Cases_on `t` THEN Cases_on `t0` THEN Cases_on `l` THEN Cases_on `t1`,
 Cases_on `t`,
 Cases_on `t`] THEN
FULL_SIMP_TAC list_ss [EBok_def, Eok_def, EVERY_MEM] THEN METIS_TAC []);


val lem2 = Q.prove (
`!EB E. Eok (EB::E) ==> EBok (EB::E) EB`,
SRW_TAC [] [] THEN Cases_on `EB = EB_tv` THEN SRW_TAC [] [Eok_def, EBok_def] THEN
METIS_TAC [lem1, weak_EBok_thm, APPEND, MEM]);

in

val lookup_ok_thm = Q.store_thm ("lookup_ok_thm",
`!E name EB. Eok E /\ (lookup E name = SOME EB) ==> EBok E EB`,
Induct THEN SRW_TAC [] [lookup_def, shiftEB_add_thm] THENL
[METIS_TAC [lem2],
 `EBok E EB2` by METIS_TAC [APPEND, ok_ok_thm] THEN Cases_on `h` THEN 
     FULL_SIMP_TAC list_ss [domEB_def, name_distinct] THEN 
     METIS_TAC [weak_one_tv_EBok_thm, APPEND, shiftE_def, num_tv_def],
 METIS_TAC [APPEND, ok_ok_thm, weak_EBok_thm, domEB_def, MEM]]);

end;


local

val lem1 = Q.prove (
`!l1 l2. MEM (a,b) l1 /\ (MAP FST l1 = MAP FST l2) ==> ?c. MEM (a,c) l2`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN
SRW_TAC [] [] THEN METIS_TAC []);

in

val tvar_subst_ok_lem = Q.store_thm ("tvar_subst_ok_lem",
`!v_t_list t v_t_list'. EVERY (\v_t. tkind E (SND v_t)) (REVERSE v_t_list) /\
                        (MAP FST v_t_list = MAP FST v_t_list') /\
                        tkind E (substs_typevar_typexpr v_t_list' t) ==>
                        tkind E (substs_typevar_typexpr v_t_list t)`,
recInduct substs_typevar_typexpr_ind THEN
SRW_TAC [] [EVERY_MAP, substs_typevar_typexpr_def, Eok_def, EVERY_MEM] THEN1
(Cases_on `list_assoc typevar sub` THEN SRW_TAC [] [Eok_def] THEN IMP_RES_TAC list_assoc_mem THEN
      IMP_RES_TAC list_assoc_not_mem THENL
      [Cases_on `list_assoc typevar v_t_list'` THEN FULL_SIMP_TAC list_ss [Eok_def] THEN
               IMP_RES_TAC list_assoc_mem THEN METIS_TAC [lem1],
       METIS_TAC [SND]])
THEN METIS_TAC []);

end;


val teq_ok_thm = Q.store_thm ("teq_ok_thm",
`!E t1 t2. JTeq E t1 t2 ==> tkind E t1 /\ tkind E t2`,
RULE_INDUCT_TAC JTeq_ind [Eok_def, EVERY_CONJ, EVERY_MAP]
[([``"JTeq_expand"``], 
   SRW_TAC [] [] THENL
   [MATCH_MP_TAC tvar_subst_ok_lem  THEN
        SRW_TAC [] [EVERY_REVERSE, EVERY_MAP, MAP_MAP] THEN IMP_RES_TAC lookup_ok_thm THEN 
        FULL_SIMP_TAC (srw_ss()) [EBok_def, Eok_def, MAP_MAP, tp_to_tv_def] THEN
        Q.EXISTS_TAC `MAP (\z. (SND z, TE_constr [] TC_unit)) t_typevar_list` THEN 
        SRW_TAC [] [MAP_MAP],
    CCONTR_TAC THEN FULL_SIMP_TAC (srw_ss()) [o_DEF] THEN
        IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def,
        Eok_def, MAP_MAP, tp_to_tv_def]])]);

val inst_named_ok_thm = Q.store_thm ("inst_named_ok_thm",
`!E t tps t'. JTinst_named E t (TPS_nary tps) t' ==> tkind E t /\ ntsok E tps t'`,
SRW_TAC [] [JTinst_named_cases] THEN
FULL_SIMP_TAC list_ss [Eok_def, MAP_MAP, GSYM MAP_REVERSE, tp_to_tv_def] THEN
MATCH_MP_TAC tvar_subst_ok_lem THEN Q.EXISTS_TAC `MAP (\z. (FST z,TE_constr [] TC_unit)) typevar_t_list` THEN
SRW_TAC [] [EVERY_REVERSE, MAP_MAP] THEN METIS_TAC []);

val idxsub_ok_lem = Q.store_thm ("idxsub_ok_lem",
`!t_list t E. EVERY (tkind E) t_list /\ tkind (EB_tv::E) t ==> tkind E (idxsub t_list t)`,
HO_MATCH_MP_TAC idxsub_ind THEN 
SRW_TAC [] [idxsub_def, Eok_def, EVERY_MAP, EVERY_MEM, idx_bound_def,
            GSYM arithmeticTheory.ADD1] THEN1 METIS_TAC [MEM_EL] THEN
Cases_on `tcn` THEN FULL_SIMP_TAC list_ss [Eok_def] THEN Cases_on `Eok E` THEN 
FULL_SIMP_TAC list_ss [lookup_def, domEB_def, name_distinct] THEN 
Cases_on `lookup E (name_tcn t')` THEN FULL_SIMP_TAC list_ss [] THEN
IMP_RES_TAC lookup_name_thm THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC list_ss [shiftEB_def, environment_binding_case_def]);

val inst_ok_thm = Q.store_thm ("inst_ok_thm",
`!E t ts. JTinst E t ts ==> tkind E t /\ tsok E ts`,
SRW_TAC [] [JTinst_cases] THEN
FULL_SIMP_TAC list_ss [Eok_def, MAP_MAP, GSYM MAP_REVERSE, tp_to_tv_def] THEN
METIS_TAC [idxsub_ok_lem]);

val prim_vn_constr_c_ok_thm = Q.store_thm ("prim_vn_constr_c_ok_thm",
`(!E unary_prim t. JTuprim E unary_prim t ==> tkind E t) /\
 (!E binary_prim t. JTbprim E binary_prim t ==> tkind E t) /\
 (!E vp t. JTvalue_name E vp t ==> tkind E t) /\
 (!E constr t. JTconstr_c E constr t ==> tkind E t)`,
SRW_TAC [] [JTuprim_cases, JTbprim_cases, JTconstr_c_cases, JTvalue_name_cases] THEN
SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_ok_thm, inst_ok_thm]);

val const_ok_thm = Q.store_thm ("const_ok_thm",
`(!E const t. JTconst E const t ==> tkind E t)`,
SRW_TAC [] [JTconst_cases] THEN
SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_ok_thm, prim_vn_constr_c_ok_thm]);

val field_constr_p_ok_thm = Q.store_thm ("field_constr_p_ok_thm",
`(!E fn t1 t2. JTfield E fn t1 t2 ==> tkind E t1 /\ tkind E t2) /\
 (!E constr tlist t. JTconstr_p E constr tlist t ==> EVERY (tkind E) tlist /\ tkind E t)`,
SRW_TAC [] [JTfield_cases, JTconstr_p_cases] THEN
IMP_RES_TAC inst_named_ok_thm THEN
FULL_SIMP_TAC list_ss [Eok_def, EVERY_MAP] THEN
METIS_TAC [ok_ok_thm]);

val pat_ok_thm = Q.store_thm ("pat_ok_thm",
`!S E pat t E'. JTpat S E pat t E' ==> tkind E t`,
RULE_INDUCT_TAC JTpat_ind [Eok_def, EVERY_MAP, EVERY_CONJ, ELIM_UNCURRY, domEB_def]
[([``"JTpat_record"``], Cases_on `field_name_pattern_E_t_list` THEN FULL_SIMP_TAC list_ss [] THEN
                  METIS_TAC [field_constr_p_ok_thm])]
THEN
METIS_TAC [ok_ok_thm, prim_vn_constr_c_ok_thm, const_ok_thm, field_constr_p_ok_thm]);

local

val lem1 = Q.prove (
`!vn ts. ~(EB_vn vn ts = EB_tv)`, FULL_SIMP_TAC list_ss [environment_binding_distinct]);

val lem2 = Q.prove (
`!E t k.  tkind E t ==> tkind (EB_tv::E) (shiftt 0 1 t)`,
METIS_TAC [weak_one_tv_ok_thm, APPEND, shiftE_def, num_tv_def]);

val lem3 = Q.prove (
`!E1 E2. value_env E1 ==> tkind E2 t /\ Eok (E1++E2) ==> tkind (E1++E2) t`,
Induct THEN SRW_TAC [] [value_env_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC list_ss [value_env_def] THEN `Eok (E1++E2)` by METIS_TAC [ok_ok_thm, APPEND] THEN
METIS_TAC [lem1, weak_ok_thm, APPEND, MEM]);

val lem4 = Q.prove (
`!E2 E1 E3. value_env E2 ==> tsok (E1++E3) ts /\ Eok (E1++E2++E3) ==> tsok (E1++E2++E3) ts`,
Induct THEN SRW_TAC [] [value_env_def] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [value_env_def] THEN 
`Eok (E1++E2++E3)` by METIS_TAC [value_env_ok_str_thm, value_env_def, APPEND, APPEND_ASSOC] THEN
METIS_TAC [lem1, weak_ok_thm, APPEND, APPEND_ASSOC, MEM]);

val lem5 = Q.prove (
`!l. EVERY value_env l ==> value_env (FLAT l)`,
Induct THEN SRW_TAC [] [value_env_def, value_env_append_thm]);

val lem6 = Q.prove (
`!l. Eok E /\ EVERY (\x. Eok (x ++ E)) l /\ EVERY value_env l ==> Eok (FLAT l ++ E)`,
Induct THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN Induct_on `h` THEN
SRW_TAC [] [] THEN Cases_on `h'` THEN FULL_SIMP_TAC list_ss [value_env_def, Eok_def] THEN
METIS_TAC [ok_ok_thm, lem4, lem5]);

in

val pat_ok_thm2 = Q.store_thm ("pat_ok_thm2",
`!S E pat t E'. JTpat S E pat t E' ==> Eok (E'++E)`,
RULE_INDUCT_TAC JTpat_sind [Eok_def, EVERY_MAP, EVERY_CONJ, ELIM_UNCURRY, domEB_def]
[([``"JTpat_var"``], METIS_TAC [lem2]),
 ([``"JTpat_any"``, ``"JTpat_constant"``, ``"JTpat_construct_any"``],
  METIS_TAC [ok_ok_thm, const_ok_thm, field_constr_p_ok_thm]),
 ([``"JTpat_alias"``], METIS_TAC [lem2, lem3, pat_env_lem, APPEND, pat_ok_thm]),
 ([``"JTpat_construct"``],
  SRW_TAC [] [] THEN MATCH_MP_TAC lem6 THEN SRW_TAC [] [EVERY_REVERSE, EVERY_MAP] THEN1
          METIS_TAC [field_constr_p_ok_thm, ok_ok_thm] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
          METIS_TAC [pat_env_lem]),
 ([``"JTpat_tuple"``],
  SRW_TAC [] [] THEN MATCH_MP_TAC lem6 THEN SRW_TAC [] [EVERY_REVERSE, EVERY_MAP] THENL
          [Cases_on `pattern_t_E_list` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC [pat_ok_thm, ok_ok_thm],
           FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [pat_env_lem]]),
 ([``"JTpat_record"``],
  SRW_TAC [] [] THEN MATCH_MP_TAC lem6 THEN SRW_TAC [] [EVERY_REVERSE, EVERY_MAP] THENL
          [Cases_on `field_name_pattern_E_t_list` THEN FULL_SIMP_TAC list_ss [] THEN
                   METIS_TAC [field_constr_p_ok_thm, ok_ok_thm],
           FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [pat_env_lem]]),
 ([``"JTpat_cons"``],
  SRW_TAC [] [] THEN MATCH_MP_TAC (SIMP_RULE list_ss [] (Q.SPEC `[E''; E']` lem6)) THEN
          METIS_TAC [pat_env_lem, ok_ok_thm])]);

end;

local

val lem1 = Q.prove (
`!l f g. value_env (MAP (\z. EB_vn (f z) (g z)) l)`,
Induct THEN SRW_TAC [] [value_env_def]);

in

val ok_thm = Q.prove (
`(!S E e t. JTe S E e t ==> tkind E t) /\
 (!S E pm t1 t2. JTpat_matching S E pm t1 t2 ==> tkind E t1 /\ tkind E t2) /\
 (!S E lb E'. JTlet_binding S E lb E' ==> T) /\
 (!S E lrb E'. JTletrec_binding S E lrb E' ==> T)`,
RULE_INDUCT_TAC JTe_ind [Eok_def, EVERY_MAP]
[([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_ident"``, ``"JTe_constant"``, ``"JTe_construct"``, 
   ``"JTe_record_proj"``, ``"JTe_tuple"``, ``"JTe_cons"``, ``"JTe_and"``, ``"JTe_or"``, ``"JTe_while"``,
   ``"JTe_for"``, ``"JTe_assert"``, ``"JTe_location"``, ``"JTe_record_with"``, ``"JTe_function"``], 
  METIS_TAC [prim_vn_constr_c_ok_thm, const_ok_thm, field_constr_p_ok_thm, pat_ok_thm, teq_ok_thm]),
 ([``"JTe_record_constr"``],
    SRW_TAC [] [] THEN METIS_TAC [teq_ok_thm]),
    (*
    Cases_on `field_name_e_t_list` THEN FULL_SIMP_TAC list_ss [] THEN IMP_RES_TAC field_constr_p_ok_thm THEN
    FULL_SIMP_TAC list_ss [Eok_def, COND_EXPAND_EQ] THEN
    Cases_on `lookup E (name_tcn typeconstr_name)` THEN FULL_SIMP_TAC list_ss [option_case_def] THEN
    IMP_RES_TAC lookup_name_thm THEN
    FULL_SIMP_TAC list_ss [environment_binding_case_def, environment_binding_distinct,
                           environment_binding_11] THEN METIS_TAC [ok_ok_thm]),
                           *)
 ([``"JTe_let_mono"``, ``"JTe_let_poly"``, ``"JTe_letrec"``],
    METIS_TAC [lem1, value_env_ok_str_thm, APPEND, MAP_REVERSE]),
 ([``"JTpat_matching_pm"``], Cases_on `pattern_e_E_list` THEN FULL_SIMP_TAC list_ss [] THEN
    METIS_TAC [pat_ok_thm, pat_env_lem, value_env_ok_str_thm, APPEND])]);

val _ = save_thm ("ok_thm", ok_thm);

end;


val _ = export_theory ();

