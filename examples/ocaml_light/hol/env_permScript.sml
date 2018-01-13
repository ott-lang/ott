open bossLib HolKernel boolLib listTheory optionTheory rich_listTheory sortingTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory shiftTheory environmentTheory;

val OPTION_MAP_ID = Q.prove (
`!Op. OPTION_MAP (\x. x) Op = Op`,
Cases THEN SRW_TAC [] []);

val _ = new_theory "env_perm";

val idx_bound_append_thm = Q.store_thm ("idx_bound_append_thm",
`!E1 E2 idx. idx_bound (E1++E2) idx = idx_bound E1 idx \/ idx_bound E2 (idx - num_tv E1)`,
Induct THEN SRW_TAC [] [idx_bound_def, num_tv_def] THEN Cases_on `h` THEN
SRW_TAC [] [idx_bound_def, num_tv_def] THEN Cases_on `idx` THEN
SRW_TAC [ARITH_ss] [idx_bound_def, num_tv_def, arithmeticTheory.ADD1]);

val idx_env_thm = Q.store_thm ("idx_env_thm",
`!E idx. value_env E \/ type_env E \/ store_env E ==> ~(idx_bound E idx)`,
Induct THEN SRW_TAC [] [value_env_def, type_env_def, store_env_def, idx_bound_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC list_ss [value_env_def, type_env_def, store_env_def, idx_bound_def]);

val type_env_lookup_lem = Q.store_thm ("type_env_lookup_lem",
`!E. type_env E ==>
            (!x. lookup E (name_l x) = NONE) /\
            (!x. lookup E (name_vn x) = NONE) /\
            (!x. lookup E name_tv = NONE)`,
Induct THEN SRW_TAC [] [lookup_def, type_env_def, domEB_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC list_ss [type_env_def, domEB_def, name_distinct]);

val type_env_num_tv_thm = Q.prove (
`!E. type_env E ==> (num_tv E = 0)`,
Induct THEN SRW_TAC [] [num_tv_def, type_env_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC list_ss [num_tv_def, type_env_def]);

val lookup_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 EB name. type_env E2 /\ store_env E3 /\
          (lookup (E1++E2++E3++E4) name = SOME EB) ==> (lookup (E1++E3++E2++E4) name = SOME EB)`,
SRW_TAC [] [lookup_append_thm] THEN
Cases_on `lookup E1 name` THEN FULL_SIMP_TAC list_ss [option_case_def] THEN
Cases_on `lookup E2 name` THEN FULL_SIMP_TAC list_ss [option_case_def] THEN
Cases_on `lookup E3 name` THEN FULL_SIMP_TAC list_ss [option_case_def, num_tv_append_thm] THEN
IMP_RES_TAC type_env_num_tv_thm THEN IMP_RES_TAC value_env_num_tv_thm THEN FULL_SIMP_TAC list_ss [] THEN
Cases_on `name` THEN IMP_RES_TAC store_env_lookup_lem THEN FULL_SIMP_TAC list_ss [] THEN
METIS_TAC [NOT_SOME_NONE, type_env_lookup_lem]);

val idx_bound_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 idx. type_env E2 /\ store_env E3 /\ idx_bound (E1 ++ E2 ++ E3 ++ E4) idx ==>
                   idx_bound (E1 ++ E3 ++ E2 ++ E4) idx`,
SRW_TAC [ARITH_ss] [idx_bound_append_thm, idx_env_thm, num_tv_append_thm] THEN
METIS_TAC [idx_env_thm]);

local

val lem1 = Q.prove (
`!E1 E2 E3 t. tkind (E1++E3) t /\ Eok (E1++E2++E3) /\ store_env E1 /\ type_env E2 ==> tkind (E1++E2++E3) t`,
Induct THEN SRW_TAC [] [] THENL
[IMP_RES_TAC tkind_weak_thm THEN IMP_RES_TAC type_env_num_tv_thm THEN FULL_SIMP_TAC list_ss [shiftt_add_thm],
 Cases_on `h` THEN FULL_SIMP_TAC list_ss [store_env_def] THEN
    MATCH_MP_TAC ((SIMP_RULE list_ss [num_tv_def, shiftt_add_thm] o Q.SPEC `[EB_l n t']`) tkind_weak_thm) THEN
    `tkind (E1 ++ E3) t` by METIS_TAC [value_env_ok_str_thm, APPEND, APPEND_ASSOC, store_env_def] THEN
    METIS_TAC [ok_ok_thm, APPEND]]);

val lem2 = Q.prove (
`Eok (E2 ++ EB_l n t::E3 ++ E4) ==> ~MEM (name_l n) (MAP domEB E2)`,
Induct_on `E2` THEN SRW_TAC [] [] THEN `Eok (E2 ++ EB_l n t::E3 ++ E4)` by METIS_TAC [APPEND, ok_ok_thm] THEN
FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [Eok_def] THEN
FULL_SIMP_TAC list_ss [domEB_def] THEN SRW_TAC [] []);

in

val ok_store_type_perm_thm = Q.prove (
`(!E1 E2 E3 E4. Eok (E1++E2++E3++E4) /\ type_env E2 /\ store_env E3 ==>
                  Eok (E1++E3++E2++E4)) /\
 (!E1 tc E2 E3 E4 k. (typeconstr_kind (E1++E2++E3++E4) tc = SOME k) /\ type_env E2 /\
                       store_env E3 ==>
                      (typeconstr_kind (E1++E3++E2++E4) tc = SOME k)) /\
 (!E1 ts E2 E3 E4. tsok (E1++E2++E3++E4) ts /\ type_env E2 /\ store_env E3 ==>
                     tsok (E1++E3++E2++E4) ts) /\
 (!E1 tpo ts E2 E3 E4. ntsok (E1++E2++E3++E4) tpo ts /\ type_env E2 /\ store_env E3 ==>
                         ntsok (E1++E3++E2++E4) tpo ts) /\
 (!E1 t E2 E3 E4. tkind (E1++E2++E3++E4) t /\ type_env E2 /\ store_env E3 ==>
                    tkind (E1++E3++E2++E4) t)`,
HO_MATCH_MP_TAC Eok_ind THEN SRW_TAC [] [Eok_def, COND_EXPAND_EQ] THEN
FULL_SIMP_TAC list_ss [Eok_def, type_env_def, store_env_def, EVERY_MEM] THEN SRW_TAC [] [] THENL
[ALL_TAC,
 METIS_TAC [lookup_store_type_perm_thm],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [lookup_store_type_perm_thm],
 METIS_TAC [lookup_store_type_perm_thm],
 METIS_TAC [lookup_store_type_perm_thm],
 Cases_on `lookup (E1 ++ E2 ++ E3 ++ E4) (name_tcn typeconstr_name)` THEN
       FULL_SIMP_TAC list_ss [option_case_def] THEN IMP_RES_TAC lookup_store_type_perm_thm THEN SRW_TAC [] [],
 METIS_TAC [idx_bound_store_type_perm_thm]]
THEN
Induct_on `E3` THEN SRW_TAC [] [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [store_env_def] THEN
`Eok (EB_l n t::E3 ++ E4)` by METIS_TAC [ok_ok_thm, APPEND, APPEND_ASSOC] THEN
FULL_SIMP_TAC list_ss [Eok_def] THEN
`Eok (E2++E3++E4)` by METIS_TAC [value_env_ok_str_thm, store_env_def, APPEND, APPEND_ASSOC] THEN
SRW_TAC [] [lem1] THEN METIS_TAC [lem2]);

end;


val teq_store_type_perm_thm = Q.prove (
`!E t t'. JTeq E t t' ==> !E1 E2 E3 E4. (E = E1++E2++E3++E4) /\ store_env E3 /\ type_env E2 ==>
          JTeq (E1++E3++E2++E4) t t'`,
INDUCT_TAC JTeq_ind []
[([``"JTeq_refl"``], METIS_TAC [ok_store_type_perm_thm, ok_ok_thm, JTeq_rules]),
 ([``"JTeq_sym"``, ``"JTeq_trans"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_expand"``], 
  SRW_TAC [] [] THEN ONCE_REWRITE_TAC [JTeq_cases] THEN NTAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN 
      METIS_TAC [lookup_store_type_perm_thm, ok_store_type_perm_thm]),
 ([``"JTeq_arrow"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_tuple"``], 
  SRW_TAC [] [] THEN ONCE_REWRITE_TAC [JTeq_cases] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
      METIS_TAC []),
 ([``"JTeq_constr"``], 
  SRW_TAC [] [] THEN ONCE_REWRITE_TAC [JTeq_cases] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
      METIS_TAC [ok_store_type_perm_thm])]);



val uprim_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 up t. JTuprim (E1++E2++E3++E4) up t /\ store_env E3 /\ type_env E2 ==>
                    JTuprim (E1++E3++E2++E4) up t`,
SRW_TAC [] [JTuprim_cases, ok_store_type_perm_thm]);

val bprim_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 bp t. JTbprim (E1++E2++E3++E4) bp t /\ store_env E3 /\ type_env E2 ==>
                    JTbprim (E1++E3++E2++E4) bp t`,
SRW_TAC [] [JTbprim_cases, ok_store_type_perm_thm]);

val inst_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 t ts. JTinst (E1++E2++E3++E4) t ts /\ store_env E3 /\ type_env E2 ==>
                    JTinst (E1++E3++E2++E4) t ts`,
SRW_TAC [] [JTinst_cases, EVERY_MEM] THEN METIS_TAC [ok_store_type_perm_thm]);

val inst_named_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 t tpo ts. JTinst_named (E1++E2++E3++E4) t tpo ts /\ store_env E3 /\ type_env E2 ==>
                        JTinst_named (E1++E3++E2++E4) t tpo ts`,
SRW_TAC [] [JTinst_named_cases, EVERY_MEM] THEN METIS_TAC [ok_store_type_perm_thm]);

val vn_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 vn t. JTvalue_name (E1++E2++E3++E4) vn t /\ store_env E3 /\ type_env E2 ==>
                    JTvalue_name (E1++E3++E2++E4) vn t`,
SRW_TAC [] [JTvalue_name_cases] THEN Q.EXISTS_TAC `ts` THEN
SRW_TAC [] [lookup_store_type_perm_thm, inst_store_type_perm_thm]);

val constr_c_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 c t. JTconstr_c (E1++E2++E3++E4) c t /\ store_env E3 /\ type_env E2 ==>
                   JTconstr_c (E1++E3++E2++E4) c t`,
SRW_TAC [] [JTconstr_c_cases, ok_store_type_perm_thm, lookup_store_type_perm_thm, EVERY_MEM]);

val const_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 c t. JTconst (E1++E2++E3++E4) c t /\ store_env E3 /\ type_env E2 ==>
                   JTconst (E1++E3++E2++E4) c t`,
SRW_TAC [] [JTconst_cases, ok_store_type_perm_thm, constr_c_store_type_perm_thm]);

val constr_p_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 c t t'. JTconstr_p (E1++E2++E3++E4) c t t' /\ store_env E3 /\ type_env E2 ==>
                      JTconstr_p (E1++E3++E2++E4) c t t'`,
SRW_TAC [] [JTconstr_p_cases, ok_store_type_perm_thm] THEN
METIS_TAC [lookup_store_type_perm_thm, inst_named_store_type_perm_thm]);

val field_store_type_perm_thm = Q.prove (
`!E1 E2 E3 E4 fn t t'. JTfield (E1++E2++E3++E4) fn t t' /\ store_env E3 /\ type_env E2 ==>
                       JTfield (E1++E3++E2++E4) fn t t'`,
SRW_TAC [] [JTfield_cases] THEN
METIS_TAC [lookup_store_type_perm_thm, inst_named_store_type_perm_thm]);

val inst_any_store_type_perm_thm = Q.prove (
`!E t t'. JTinst_any E t t' ==> !E1 E2 E3 E4. (E=E1++E2++E3++E4) /\ store_env E3 /\ type_env E2 ==>
          JTinst_any (E1++E3++E2++E4) t t'`,
RULE_INDUCT_TAC JTinst_any_ind [JTinst_any_fun, EVERY_MEM]
[] THEN
METIS_TAC [ok_store_type_perm_thm]);

val pat_store_type_perm_thm = Q.prove (
`!S E p t E'. JTpat S E p t E' ==> !E1 E2 E3 E4. (E=E1++E2++E3++E4) /\ store_env E3 /\ type_env E2 ==>
              JTpat S (E1++E3++E2++E4) p t E'`,
RULE_INDUCT_TAC JTpat_ind [JTpat_fun, EVERY_MEM]
[([``"JTpat_var"``, ``"JTpat_any"``, ``"JTpat_tuple"``, ``"JTpat_cons"``],
  METIS_TAC [ok_store_type_perm_thm]),
 ([``"JTpat_typed"``], SRW_TAC [] [] THEN METIS_TAC [inst_any_store_type_perm_thm, teq_store_type_perm_thm]),
 ([``"JTpat_constant"``],
  METIS_TAC [const_store_type_perm_thm]),
 ([``"JTpat_construct"``, ``"JTpat_construct_any"``],
  METIS_TAC [constr_p_store_type_perm_thm]),
 ([``"JTpat_record"``],
  METIS_TAC [field_store_type_perm_thm]),
 ([``"JTpat_or"``],
  METIS_TAC [])]);

val store_type_perm_thm = Q.prove (
`(!S E e t. JTe S E e t ==> !E1 E2 E3 E4. (E=E1++E2++E3++E4) /\ store_env E3 /\ type_env E2 ==>
            JTe S (E1++E3++E2++E4) e t) /\
 (!S E pm t t'. JTpat_matching S E pm t t' ==>
                !E1 E2 E3 E4. (E=E1++E2++E3++E4) /\ store_env E3 /\ type_env E2 ==>
                JTpat_matching S (E1++E3++E2++E4) pm t t') /\
 (!S E lb E'. JTlet_binding S E lb E' ==> !E1 E2 E3 E4. (E=E1++E2++E3++E4) /\ store_env E3 /\ type_env E2 ==>
              JTlet_binding S (E1++E3++E2++E4) lb E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==>
                !E1 E2 E3 E4. (E=E1++E2++E3++E4) /\ store_env E3 /\ type_env E2 ==>
                JTletrec_binding S (E1++E3++E2++E4) lrbs E')`,
RULE_INDUCT_TAC JTe_ind [JTe_fun, EVERY_MEM]
[([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_ident"``, ``"JTe_constant"``],
  METIS_TAC [uprim_store_type_perm_thm, bprim_store_type_perm_thm, vn_store_type_perm_thm,
             const_store_type_perm_thm, teq_store_type_perm_thm]),
 ([``"JTe_typed"``], SRW_TAC [] [] THEN METIS_TAC [inst_any_store_type_perm_thm, teq_store_type_perm_thm]),
 ([``"JTe_tuple"``, ``"JTe_apply"``, ``"JTe_match"``, ``"JTe_cons"``, ``"JTe_and"``, ``"JTe_or"``,
   ``"JTe_while"``, ``"JTe_function"``, ``"JTe_assert"``],
  METIS_TAC [teq_store_type_perm_thm]),
 ([``"JTe_construct"``],
  METIS_TAC [constr_p_store_type_perm_thm, teq_store_type_perm_thm]),
 ([``"JTe_record_constr"``],
  SRW_TAC [] [] THEN
  MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`, `field_name_e_t_list`] THEN
  METIS_TAC [field_store_type_perm_thm, lookup_store_type_perm_thm, teq_store_type_perm_thm]),
 ([``"JTe_record_with"``, ``"JTe_record_proj"``],
  METIS_TAC [field_store_type_perm_thm, teq_store_type_perm_thm]),
 ([``"JTe_for"``],
  METIS_TAC [APPEND, teq_store_type_perm_thm]),
 ([``"JTe_let_mono"``],
  METIS_TAC [APPEND_ASSOC]),
 ([``"JTe_let_poly"``],
  SRW_TAC [] [] THEN DISJ2_TAC THEN Q.EXISTS_TAC `x_t_list` THEN METIS_TAC [APPEND, APPEND_ASSOC]),
 ([``"JTe_letrec"``],
  METIS_TAC [APPEND, APPEND_ASSOC]),
 ([``"JTe_assertfalse"``],
  SRW_TAC [] [JTconst_cases] THEN METIS_TAC [ok_store_type_perm_thm]),
 ([``"JTe_location"``],
  METIS_TAC [lookup_store_type_perm_thm, ok_store_type_perm_thm, teq_store_type_perm_thm]),
 ([``"JTpat_matching_pm"``], 
  SRW_TAC [] [] THEN Q.EXISTS_TAC `pattern_e_E_list` THEN SRW_TAC [] [] THEN 
         METIS_TAC [pat_store_type_perm_thm]),
 ([``"JTlet_binding_poly"``],
  METIS_TAC [pat_store_type_perm_thm, APPEND_ASSOC]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `value_name_pattern_matching_t_t'_list` THEN SRW_TAC [] [])]);

val type_def_store_type_perm_thm = Q.prove (
`!E td E'. JTtype_definition E td E' ==> !E1 E2 E3 E4. (E = E1++E2++E3++E4) /\ type_env E2 /\ store_env E3 ==>
           JTtype_definition (E1++E3++E2++E4) td E'`,
RULE_INDUCT_TAC JTtype_definition_ind [JTtype_definition_rules] [] THEN
SRW_TAC [] [] THEN IMP_RES_TAC JTtype_definition_rules THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`Eok ((E''' ++ E'' ++ E' ++ E1) ++ E2 ++ E3 ++ E4) ==>
 Eok ((E''' ++ E'' ++ E' ++ E1) ++ E3 ++ E2 ++ E4)` by METIS_TAC [ok_store_type_perm_thm] THEN
 FULL_SIMP_TAC (srw_ss()) []);


val def_store_type_perm_thm = Q.prove (
`!E d E'. JTdefinition E d E' ==> !E1 E2 E3 E4. (E = E1++E2++E3++E4) /\ type_env E2 /\ store_env E3 ==>
          JTdefinition (E1++E3++E2++E4) d E'`,
RULE_INDUCT_TAC JTdefinition_ind [JTdefinition_fun]
[([``"JTdefinition_let_poly"``, ``"JTdefinition_let_mono"``, ``"JTdefinition_letrec"``],
  SRW_TAC [] [] THEN METIS_TAC [store_type_perm_thm, APPEND, APPEND_ASSOC]),
 ([``"JTdefinition_typedef"``],
  METIS_TAC [type_def_store_type_perm_thm]),
 ([``"JTdefinition_exndef"``],
  SRW_TAC [] [JTconstr_decl_cases] THEN METIS_TAC [ok_store_type_perm_thm])]);

val defs_store_type_perm_thm = Q.store_thm ("defs_store_type_perm_thm",
`!E ds E'. JTdefinitions E ds E' ==> !E1 E2 E3 E4. (E = E1++E2++E3++E4) /\ type_env E2 /\ store_env E3 ==>
           JTdefinitions (E1++E3++E2++E4) ds E'`,
RULE_INDUCT_TAC JTdefinitions_ind [JTdefinitions_fun]
[([``"JTdefinitions_empty"``], METIS_TAC [ok_store_type_perm_thm]),
 ([``"JTdefinitions_item"``], METIS_TAC [def_store_type_perm_thm, APPEND_ASSOC])]);

local

val lem1 = Q.prove (
`!x E. value_env (x::E) = (?n ts. x = EB_vn n ts) /\ value_env E`,
Cases THEN SRW_TAC [] [value_env_def]);

val lem2 = Q.prove (
`!E1 E2. PERM E1 E2 ==> ALL_DISTINCT (MAP domEB E1) /\ value_env E1 ==> PERM E1 E2 /\ 
                        !name. (lookup E1 name = lookup E2 name)`,
HO_MATCH_MP_TAC PERM_IND THEN
SRW_TAC [] [PERM_REFL, PERM_MONO, PERM_SWAP_AT_FRONT, PERM_TRANS, lem1] THENL
[SRW_TAC [] [lookup_def],
 SRW_TAC [] [lookup_def, shiftEB_add_thm, OPTION_MAP_ID, domEB_def] THEN FULL_SIMP_TAC (srw_ss()) [domEB_def],
 METIS_TAC [PERM_ALL_DISTINCT, PERM_MAP, PERM_TRANS, value_env_perm_thm],
 METIS_TAC [PERM_ALL_DISTINCT, PERM_MAP, PERM_TRANS, value_env_perm_thm]]);

in

val lookup_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 EB name. value_env E2 /\ PERM E2 E3 /\ (ALL_DISTINCT (MAP domEB E2) \/ !n. ~(name = name_vn n)) /\
          (lookup (E1++E2++E4) name = SOME EB) ==> (lookup (E1++E3++E4) name = SOME EB)`,
SRW_TAC [] [lookup_append_thm] THEN IMP_RES_TAC value_env_perm_thm THEN 
Cases_on `lookup E1 name` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `lookup E2 name` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `lookup E3 name` THEN FULL_SIMP_TAC (srw_ss()) [num_tv_append_thm] THEN
IMP_RES_TAC value_env_num_tv_thm THEN FULL_SIMP_TAC (srw_ss()) [] THEN IMP_RES_TAC value_env_lookup_lem THENL
[METIS_TAC [NOT_SOME_NONE, lem2, PERM_SYM, SOME_11],
 METIS_TAC [NOT_SOME_NONE, lem2, PERM_SYM, SOME_11],
 METIS_TAC [NOT_SOME_NONE, lem2, PERM_SYM, SOME_11],
 Cases_on `name` THEN FULL_SIMP_TAC (srw_ss()) [],
 Cases_on `name` THEN FULL_SIMP_TAC (srw_ss()) [],
 Cases_on `name` THEN FULL_SIMP_TAC (srw_ss()) []]);

end;


val idx_bound_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 idx. value_env E2 /\ PERM E2 E3 /\ idx_bound (E1 ++ E2 ++ E4) idx ==>
                   idx_bound (E1 ++ E3 ++ E4) idx`,
SRW_TAC [ARITH_ss] [idx_bound_append_thm, idx_env_thm, num_tv_append_thm] THEN
METIS_TAC [idx_env_thm, value_env_perm_thm, value_env_num_tv_thm]);

local

val lem1 = Q.prove (
`!E1 E2 E3 t. tkind (E1++E3) t /\ Eok (E1++E2++E3) /\ store_env E1 /\ type_env E2 ==> tkind (E1++E2++E3) t`,
Induct THEN SRW_TAC [] [] THENL
[IMP_RES_TAC tkind_weak_thm THEN IMP_RES_TAC type_env_num_tv_thm THEN FULL_SIMP_TAC list_ss [shiftt_add_thm],
 Cases_on `h` THEN FULL_SIMP_TAC list_ss [store_env_def] THEN
    MATCH_MP_TAC ((SIMP_RULE list_ss [num_tv_def, shiftt_add_thm] o Q.SPEC `[EB_l n t']`) tkind_weak_thm) THEN
    `tkind (E1 ++ E3) t` by METIS_TAC [value_env_ok_str_thm, APPEND, APPEND_ASSOC, store_env_def] THEN
    METIS_TAC [ok_ok_thm, APPEND]]);

val lem2 = Q.prove (
`Eok (E2 ++ EB_l n t::E3 ++ E4) ==> ~MEM (name_l n) (MAP domEB E2)`,
Induct_on `E2` THEN SRW_TAC [] [] THEN `Eok (E2 ++ EB_l n t::E3 ++ E4)` by METIS_TAC [APPEND, ok_ok_thm] THEN
FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [Eok_def] THEN
FULL_SIMP_TAC list_ss [domEB_def] THEN SRW_TAC [] []);

val lem3 = Q.prove (
`!x E. value_env (x::E) = (?n ts. x = EB_vn n ts) /\ value_env E`,
Cases THEN SRW_TAC [] [value_env_def]);

val lem4 = Q.prove (
`!E. value_env E ==> ~MEM EB_tv E`,
Induct THEN SRW_TAC [] [lem3]);

val lem5 = Q.prove (
`tsok (E2 ++ E4) ts /\ value_env E2 /\ value_env E3 /\ Eok (E3 ++ E4) ==> tsok (E3++E4) ts`,
METIS_TAC [value_env_ok_str_thm, APPEND, lem4, weak_ok_thm]);

val lem6 = Q.prove (
`!E2 E3. PERM E2 E3 ==> Eok (E2 ++ E4) /\ value_env E2 ==> 
         PERM E2 E3 /\ Eok (E3 ++ E4)`,
HO_MATCH_MP_TAC PERM_IND THEN SRW_TAC [] [lem3] THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THENL
[METIS_TAC [ok_ok_thm],
 METIS_TAC [ok_ok_thm, lem5, value_env_perm_thm],
 IMP_RES_TAC ok_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN IMP_RES_TAC ok_ok_thm THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [PERM_SWAP_AT_FRONT],
 IMP_RES_TAC ok_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN IMP_RES_TAC ok_ok_thm THEN
     SIMP_TAC pure_ss [GSYM APPEND] THEN MATCH_MP_TAC (GEN_ALL lem5) THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def, lem3] THEN Q.EXISTS_TAC `E2` THEN
     SRW_TAC [] [] THEN1 METIS_TAC [value_env_perm_thm] THEN
     METIS_TAC [value_env_ok_str_thm, APPEND, lem4, weak_ok_thm, value_env_perm_thm, lem3],
 METIS_TAC [value_env_perm_thm, PERM_TRANS],
 METIS_TAC [value_env_perm_thm]]);

in

val ok_value_perm_thm = Q.prove (
`(!E1 E2 E3 E4. Eok (E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 ==>
                  Eok (E1++E3++E4)) /\
 (!E1 tc E2 E3 E4 k. (typeconstr_kind (E1++E2++E4) tc = SOME k) /\ value_env E2 /\
                       PERM E2 E3 ==>
                      (typeconstr_kind (E1++E3++E4) tc = SOME k)) /\
 (!E1 ts E2 E3 E4. tsok (E1++E2++E4) ts /\ value_env E2 /\ PERM E2 E3 ==>
                     tsok (E1++E3++E4) ts) /\
 (!E1 tpo ts E2 E3 E4. ntsok (E1++E2++E4) tpo ts /\ value_env E2 /\ PERM E2 E3 ==>
                         ntsok (E1++E3++E4) tpo ts) /\
 (!E1 t E2 E3 E4. tkind (E1++E2++E4) t /\ value_env E2 /\ PERM E2 E3 ==>
                    tkind (E1++E3++E4) t)`,
HO_MATCH_MP_TAC Eok_ind THEN SRW_TAC [] [Eok_def, COND_EXPAND_EQ] THEN
FULL_SIMP_TAC list_ss [Eok_def, value_env_def, EVERY_MEM] THEN SRW_TAC [] [] THEN
IMP_RES_TAC value_env_perm_thm THEN IMP_RES_TAC value_env_lookup_lem THEN 
FULL_SIMP_TAC (srw_ss()) [GSYM lookup_dom_thm] THENL
[METIS_TAC [lem6],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [lookup_value_perm_thm, name_distinct],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [lookup_value_perm_thm, name_distinct],
 METIS_TAC [],
 METIS_TAC [lookup_value_perm_thm, name_distinct],
 METIS_TAC [],
 METIS_TAC [lookup_value_perm_thm, name_distinct],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 Cases_on `lookup (E1 ++ E2 ++ E4) (name_tcn typeconstr_name)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `lookup (E1 ++ E3 ++ E4) (name_tcn typeconstr_name) = SOME x` 
             by METIS_TAC [lookup_value_perm_thm, name_distinct] THEN
      SRW_TAC [] [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [idx_bound_value_perm_thm],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC []]);

end;

val teq_value_perm_thm = Q.prove (
`!E t t'. JTeq E t t' ==> !E1 E2 E3 E4. (E = E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 ==>
          JTeq (E1++E3++E4) t t'`,
INDUCT_TAC JTeq_ind []
[([``"JTeq_refl"``], METIS_TAC [ok_value_perm_thm, ok_ok_thm, JTeq_rules]),
 ([``"JTeq_sym"``, ``"JTeq_trans"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_expand"``], 
  SRW_TAC [] [] THEN ONCE_REWRITE_TAC [JTeq_cases] THEN NTAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN 
      METIS_TAC [lookup_value_perm_thm, ok_value_perm_thm, name_distinct]),
 ([``"JTeq_arrow"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_tuple"``], 
  SRW_TAC [] [] THEN ONCE_REWRITE_TAC [JTeq_cases] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
      METIS_TAC []),
 ([``"JTeq_constr"``], 
  SRW_TAC [] [] THEN ONCE_REWRITE_TAC [JTeq_cases] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
      METIS_TAC [ok_value_perm_thm])]);


val uprim_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 up t. JTuprim (E1++E2++E4) up t /\ value_env E2 /\ PERM E2 E3 ==>
                    JTuprim (E1++E3++E4) up t`,
SRW_TAC [] [JTuprim_cases] THEN METIS_TAC [ok_value_perm_thm]);

val bprim_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 bp t. JTbprim (E1++E2++E4) bp t /\ value_env E2 /\ PERM E2 E3 ==>
                    JTbprim (E1++E3++E4) bp t`,
SRW_TAC [] [JTbprim_cases] THEN METIS_TAC [ok_value_perm_thm]);

val inst_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 t ts. JTinst (E1++E2++E4) t ts /\ value_env E2 /\ PERM E2 E3==>
                    JTinst (E1++E3++E4) t ts`,
SRW_TAC [] [JTinst_cases, EVERY_MEM] THEN METIS_TAC [ok_value_perm_thm]);

val inst_named_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 t tpo ts. JTinst_named (E1++E2++E4) t tpo ts /\ value_env E2 /\ PERM E2 E3 ==>
                        JTinst_named (E1++E3++E4) t tpo ts`,
SRW_TAC [] [JTinst_named_cases, EVERY_MEM] THEN METIS_TAC [ok_value_perm_thm]);

val vn_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 vn t. JTvalue_name (E1++E2++E4) vn t /\ value_env E2 /\ PERM E2 E3 /\ 
                    ALL_DISTINCT (MAP domEB E2) ==>
                    JTvalue_name (E1++E3++E4) vn t`,
SRW_TAC [] [JTvalue_name_cases] THEN Q.EXISTS_TAC `ts` THEN
SRW_TAC [] [] THEN METIS_TAC [lookup_value_perm_thm, inst_value_perm_thm]);

val constr_c_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 c t. JTconstr_c (E1++E2++E4) c t /\ value_env E2 /\ PERM E2 E3 ==>
                   JTconstr_c (E1++E3++E4) c t`,
SRW_TAC [] [JTconstr_c_cases, EVERY_MEM] THEN 
METIS_TAC [ok_value_perm_thm, lookup_value_perm_thm, name_distinct]);

val const_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 c t. JTconst (E1++E2++E4) c t /\ value_env E2 /\ PERM E2 E3 ==>
                   JTconst (E1++E3++E4) c t`,
SRW_TAC [] [JTconst_cases] THEN METIS_TAC [ok_value_perm_thm, constr_c_value_perm_thm]);

val constr_p_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 c t t'. JTconstr_p (E1++E2++E4) c t t' /\ value_env E2 /\ PERM E2 E3 ==>
                      JTconstr_p (E1++E3++E4) c t t'`,
SRW_TAC [] [JTconstr_p_cases] THEN
METIS_TAC [ok_value_perm_thm, lookup_value_perm_thm, inst_named_value_perm_thm, name_distinct]);

val field_value_perm_thm = Q.prove (
`!E1 E2 E3 E4 fn t t'. JTfield (E1++E2++E4) fn t t' /\ value_env E2 /\ PERM E2 E3 ==>
                       JTfield (E1++E3++E4) fn t t'`,
SRW_TAC [] [JTfield_cases] THEN
METIS_TAC [ok_value_perm_thm, lookup_value_perm_thm, inst_named_value_perm_thm, name_distinct]);

val inst_any_value_perm_thm = Q.prove (
`!E t t'. JTinst_any E t t' ==> !E1 E2 E3 E4. (E=E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 ==>
          JTinst_any (E1++E3++E4) t t'`,
RULE_INDUCT_TAC JTinst_any_ind [JTinst_any_fun, EVERY_MEM] [] THEN
METIS_TAC [ok_value_perm_thm]);

val pat_value_perm_thm = Q.prove (
`!S E p t E'. JTpat S E p t E' ==> !E1 E2 E3 E4. (E=E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 ==>
              JTpat S (E1++E3++E4) p t E'`,
RULE_INDUCT_TAC JTpat_ind [JTpat_fun, EVERY_MEM]
[([``"JTpat_var"``, ``"JTpat_any"``, ``"JTpat_tuple"``, ``"JTpat_cons"``],
  METIS_TAC [ok_value_perm_thm]),
 ([``"JTpat_typed"``], SRW_TAC [] [] THEN METIS_TAC [inst_any_value_perm_thm, teq_value_perm_thm]),
 ([``"JTpat_constant"``],
  METIS_TAC [const_value_perm_thm]),
 ([``"JTpat_construct"``, ``"JTpat_construct_any"``],
  METIS_TAC [constr_p_value_perm_thm]),
 ([``"JTpat_record"``],
  METIS_TAC [field_value_perm_thm]),
 ([``"JTpat_or"``],
  METIS_TAC [])]);

val value_perm_thm = Q.store_thm ("value_perm_thm",
`(!S E e t. JTe S E e t ==> !E1 E2 E3 E4. (E=E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 /\ 
                                          ALL_DISTINCT (MAP domEB E2) ==>
            JTe S (E1++E3++E4) e t) /\
 (!S E pm t t'. JTpat_matching S E pm t t' ==>
                !E1 E2 E3 E4. (E=E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 /\ ALL_DISTINCT (MAP domEB E2) ==>
                JTpat_matching S (E1++E3++E4) pm t t') /\
 (!S E lb E'. JTlet_binding S E lb E' ==> !E1 E2 E3 E4. (E=E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 /\
                                                        ALL_DISTINCT (MAP domEB E2) ==>
              JTlet_binding S (E1++E3++E4) lb E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==>
                !E1 E2 E3 E4. (E=E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 /\ ALL_DISTINCT (MAP domEB E2) ==>
                JTletrec_binding S (E1++E3++E4) lrbs E')`,
RULE_INDUCT_TAC JTe_ind [JTe_fun, EVERY_MEM]
[([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_ident"``, ``"JTe_constant"``],
  METIS_TAC [uprim_value_perm_thm, bprim_value_perm_thm, vn_value_perm_thm, const_value_perm_thm,
             teq_value_perm_thm]),
 ([``"JTe_typed"``], SRW_TAC [] [] THEN METIS_TAC [inst_any_value_perm_thm, teq_value_perm_thm]),
 ([``"JTe_tuple"``, ``"JTe_apply"``, ``"JTe_match"``, ``"JTe_cons"``, ``"JTe_and"``, ``"JTe_or"``, 
   ``"JTe_while"``, ``"JTe_function"``, ``"JTe_assert"``],
  METIS_TAC [teq_value_perm_thm]),
 ([``"JTe_construct"``],
  METIS_TAC [constr_p_value_perm_thm, teq_value_perm_thm]),
 ([``"JTe_record_constr"``],
  SRW_TAC [] [] THEN
  MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`, `field_name_e_t_list`] THEN SRW_TAC [] [] THEN
  METIS_TAC [field_value_perm_thm, lookup_value_perm_thm, teq_value_perm_thm]),
 ([``"JTe_record_with"``, ``"JTe_record_proj"``],
  METIS_TAC [field_value_perm_thm, teq_value_perm_thm]),
 ([``"JTe_for"``],
  METIS_TAC [APPEND, teq_value_perm_thm]),
 ([``"JTe_let_mono"``],
  METIS_TAC [APPEND_ASSOC]),
 ([``"JTe_let_poly"``],
  SRW_TAC [] [] THEN DISJ2_TAC THEN Q.EXISTS_TAC `x_t_list` THEN METIS_TAC [APPEND, APPEND_ASSOC]),
 ([``"JTe_letrec"``],
  METIS_TAC [APPEND, APPEND_ASSOC]),
 ([``"JTe_assertfalse"``],
  SRW_TAC [] [JTconst_cases] THEN METIS_TAC [ok_value_perm_thm]),
 ([``"JTe_location"``],
  METIS_TAC [lookup_value_perm_thm, ok_value_perm_thm, teq_value_perm_thm]),
 ([``"JTlet_binding_poly"``],
  METIS_TAC [pat_value_perm_thm, APPEND_ASSOC]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `pattern_e_E_list` THEN SRW_TAC [] [] THEN METIS_TAC [pat_value_perm_thm]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `value_name_pattern_matching_t_t'_list` THEN SRW_TAC [] [])]);

val type_def_value_perm_thm = Q.prove (
`!E td E'. JTtype_definition E td E' ==> !E1 E2 E3 E4. (E = E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 ==>
           JTtype_definition (E1++E3++E4) td E'`,
RULE_INDUCT_TAC JTtype_definition_ind [JTtype_definition_rules] [] THEN
SRW_TAC [] [] THEN IMP_RES_TAC JTtype_definition_rules THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`Eok ((E''' ++ E'' ++ E' ++ E1) ++ E2 ++ E4) ==>
 Eok ((E''' ++ E'' ++ E' ++ E1) ++ E3 ++ E4)` by METIS_TAC [ok_value_perm_thm] THEN
 FULL_SIMP_TAC (srw_ss()) []);

val def_value_perm_thm = Q.prove (
`!E d E'. JTdefinition E d E' ==> !E1 E2 E3 E4. (E = E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 /\
          ALL_DISTINCT (MAP domEB E2) ==>
          JTdefinition (E1++E3++E4) d E'`,
RULE_INDUCT_TAC JTdefinition_ind [JTdefinition_fun]
[([``"JTdefinition_let_poly"``, ``"JTdefinition_let_mono"``, ``"JTdefinition_letrec"``],
  SRW_TAC [] [] THEN METIS_TAC [value_perm_thm, APPEND, APPEND_ASSOC]),
 ([``"JTdefinition_typedef"``],
  METIS_TAC [type_def_value_perm_thm]),
 ([``"JTdefinition_exndef"``],
  SRW_TAC [] [JTconstr_decl_cases] THEN METIS_TAC [ok_value_perm_thm])]);

val defs_value_perm_thm = Q.store_thm ("defs_value_perm_thm",
`!E ds E'. JTdefinitions E ds E' ==> !E1 E2 E3 E4. (E = E1++E2++E4) /\ value_env E2 /\ PERM E2 E3 /\
           ALL_DISTINCT (MAP domEB E2) ==>
           JTdefinitions (E1++E3++E4) ds E'`,
RULE_INDUCT_TAC JTdefinitions_ind [JTdefinitions_fun]
[([``"JTdefinitions_empty"``], METIS_TAC [ok_value_perm_thm]),
 ([``"JTdefinitions_item"``], 
  SRW_TAC [] [] THEN Q.EXISTS_TAC `E'` THEN SRW_TAC [] [] THEN METIS_TAC [def_value_perm_thm, APPEND_ASSOC])]);

val _ = export_theory();
