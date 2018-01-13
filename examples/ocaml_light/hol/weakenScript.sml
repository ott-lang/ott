open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory shiftTheory environmentTheory validTheory type_substsTheory;

val _ = Parse.hide "S";

val _ = new_theory "weaken";

val idxsub_shift_thm = Q.prove (
`!t_list t n. shiftt n 1 (idxsub t_list t) = 
  idxsub (MAP (\t. shiftt n 1 t) t_list) (shiftt (n + 1) 1 t)`,
HO_MATCH_MP_TAC idxsub_ind THEN 
SRW_TAC [ARITH_ss] [idxsub_def, shiftt_def, EL_MAP, ADD1, MAP_MAP, MAP_EQ] THEN
SRW_TAC [] [GSYM ADD1, idxsub_def, DECIDE ``!x:num.x + 2 = SUC (x + 1)``]);


val weak_one_tv_teq_thm = Q.store_thm ("weak_one_tv_teq_thm",
`!E t1 t2. JTeq E t1 t2 ==> (E = E1++E2) ==>
           JTeq (shiftE 0 1 E1++[EB_tv]++E2) (shiftt (num_tv E1) 1 t1) (shiftt (num_tv E1) 1 t2)`,
RULE_INDUCT_TAC JTeq_ind [shiftt_def]
[([``"JTeq_refl"``], METIS_TAC [weak_one_tv_ok_thm, JTeq_rules]),
 ([``"JTeq_sym"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_trans"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_arrow"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_tuple"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 3 DISJ2_TAC THEN
      Q.EXISTS_TAC `MAP (\(x,y). (shiftt (num_tv E1) 1 x, shiftt (num_tv E1) 1 y))
                        t_t'_list` THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP]),
 ([``"JTeq_constr"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 4 DISJ2_TAC THEN
      Q.EXISTS_TAC `MAP (\(x,y). (shiftt (num_tv E1) 1 x, shiftt (num_tv E1) 1 y))
                        t_t'_list` THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP, weak_one_tv_ok_thm]),
 ([``"JTeq_expand"``],
  SRW_TAC [] [] THEN SRW_TAC [] [Once JTeq_cases, MAP_MAP] THEN NTAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
     IMP_RES_TAC weak_one_tv_lookup_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN
     Q.EXISTS_TAC `MAP (\(x,y). (shiftt (num_tv E1) 1 x, y)) t_typevar_list` THEN
     SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP] THENL
     [SRW_TAC [] [subst_shiftt_com_lem, MAP_MAP],
      METIS_TAC [weak_one_tv_ok_thm],
      POP_ASSUM (K ALL_TAC) THEN Q.PAT_ASSUM `lookup x y = z` (K ALL_TAC) THEN
         Induct_on `t_typevar_list` THEN SRW_TAC [] [] THEN METIS_TAC [weak_one_tv_ok_thm]])]);

val weak_one_tv_inst_thm = Q.prove (
`!E1 E2 t ts. JTinst (E1++E2) t ts ==> 
              JTinst (shiftE 0 1 E1++[EB_tv]++E2) (shiftt (num_tv E1) 1 t) (shiftts (num_tv E1) 1 ts)`,
SRW_TAC [] [JTinst_cases] THEN SRW_TAC [] [shiftts_def, Eok_def] THEN 
Q.EXISTS_TAC `MAP (\t. shiftt (num_tv E1) 1 t) t_list` THEN SRW_TAC [] [Eok_def, EVERY_MAP] THEN
FULL_SIMP_TAC list_ss [EVERY_MEM, Eok_def, idxsub_shift_thm] THENL
[FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC weak_one_tv_ok_thm THEN 
       FULL_SIMP_TAC list_ss [num_tv_def, shiftE_def, shiftEB_def],
 METIS_TAC [weak_one_tv_ok_thm]]);

val weak_one_tv_inst_named_thm = Q.prove (
`!E1 E2 t tpo t'. JTinst_named (E1++E2) t tpo t' ==>
                  JTinst_named (shiftE 0 1 E1++[EB_tv]++E2) (shiftt (num_tv E1) 1 t) tpo 
                                                            (shiftt (num_tv E1) 1 t')`,
SRW_TAC [] [JTinst_named_cases] THEN 
Q.EXISTS_TAC `MAP (\(tv, t). (tv, shiftt (num_tv E1) 1 t)) typevar_t_list` THEN
SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, weak_one_tv_ok_thm, subst_shiftt_com_lem, EVERY_MAP] THEN 
FULL_SIMP_TAC list_ss [EVERY_MEM, weak_one_tv_ok_thm]);

val weak_one_tv_uprim_thm = Q.prove (
`!E1 E2 uprim t. JTuprim (E1++E2) uprim t ==> 
                 JTuprim (shiftE 0 1 E1++[EB_tv]++E2) uprim (shiftt (num_tv E1) 1 t)`,
SRW_TAC [] [JTuprim_cases, shiftt_def] THEN METIS_TAC [weak_one_tv_ok_thm]);

val weak_one_tv_bprim_thm = Q.prove (
`!E1 E2 bprim t. JTbprim (E1++E2) bprim t ==> 
                 JTbprim (shiftE 0 1 E1++[EB_tv]++E2) bprim (shiftt (num_tv E1) 1 t)`,
SRW_TAC [] [JTbprim_cases, shiftt_def] THEN METIS_TAC [weak_one_tv_ok_thm]);

val weak_one_tv_val_name_thm = Q.prove (
`!E1 E2 vn t. JTvalue_name (E1++E2) vn t ==> 
              JTvalue_name (shiftE 0 1 E1++[EB_tv]++E2) vn (shiftt (num_tv E1) 1 t)`,
SRW_TAC [] [JTvalue_name_cases] THEN IMP_RES_TAC weak_one_tv_lookup_thm THEN 
SRW_TAC [] [shiftEB_def, weak_one_tv_inst_thm]);

val weak_on_tv_constr_c_thm = Q.prove (
`!E1 E2 constr t. JTconstr_c (E1++E2) constr t ==>
                  JTconstr_c (shiftE 0 1 E1++[EB_tv]++E2) constr (shiftt (num_tv E1) 1 t)`,
SRW_TAC [] [JTconstr_c_cases, shiftt_def, weak_one_tv_ok_thm, EVERY_MAP] THEN 
IMP_RES_TAC weak_one_tv_lookup_thm THEN SRW_TAC [] [shiftEB_def] THEN
FULL_SIMP_TAC list_ss [EVERY_MEM, weak_one_tv_ok_thm]);

val weak_one_tv_const_thm = Q.prove (
`!E1 E2 const t. JTconst (E1++E2) const t ==>
                 JTconst (shiftE 0 1 E1++[EB_tv]++E2) const (shiftt (num_tv E1) 1 t)`,
SRW_TAC [] [JTconst_cases, shiftt_def, weak_one_tv_ok_thm, weak_on_tv_constr_c_thm]);

val weak_one_tv_constr_p_thm = Q.prove (
`!E1 E2 constr tl t. JTconstr_p (E1++E2) constr tl t ==>
                     JTconstr_p (shiftE 0 1 E1++[EB_tv]++E2) constr (MAP (shiftt (num_tv E1) 1) tl)
                                                                    (shiftt (num_tv E1) 1 t)`,
SRW_TAC [] [JTconstr_p_cases, shiftt_def, weak_one_tv_ok_thm] THEN IMP_RES_TAC weak_one_tv_lookup_thm THEN
SRW_TAC [] [shiftEB_def, shifttes_def] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (\(t, t'). (shiftt (num_tv E1) 1 t, shiftt (num_tv E1) 1 t')) t'_t_list`,
                        `MAP (\(t, tv). (shiftt (num_tv E1) 1 t, tv)) t''_tv_list`] THEN
SRW_TAC [] [MAP_MAP, LAMBDA_PROD2] THEN IMP_RES_TAC weak_one_tv_inst_named_thm THEN
FULL_SIMP_TAC list_ss [shiftt_def, MAP_MAP]);

val weak_one_tv_field_thm = Q.prove (
`!E1 E2 fn t t'. JTfield (E1++E2) fn t t' ==>
                 JTfield (shiftE 0 1 E1++[EB_tv]++E2) fn (shiftt (num_tv E1) 1 t)
                                                         (shiftt (num_tv E1) 1 t')`,
SRW_TAC [] [JTfield_cases] THEN IMP_RES_TAC weak_one_tv_lookup_thm THEN
SRW_TAC [] [shiftEB_def, shifttes_def] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (\(t, tv). (shiftt (num_tv E1) 1 t, tv)) t'_tv_list`] THEN
SRW_TAC [] [MAP_MAP, LAMBDA_PROD2] THEN IMP_RES_TAC weak_one_tv_inst_named_thm THEN
FULL_SIMP_TAC list_ss [shiftt_def, MAP_MAP, shiftt_def]);

val weak_one_tv_inst_any_thm = Q.prove (
`!E t t'. JTinst_any E t t' ==> !E1 E2. (E = E1++E2) ==>
          JTinst_any (shiftE 0 1 E1++[EB_tv]++E2) (shiftt (num_tv E1) 1 t) (shiftt (num_tv E1) 1 t')`,
RULE_INDUCT_TAC JTinst_any_ind [shiftt_def, JTinst_any_fun, EVERY_MEM]
[([``"JTinst_any_tyvar"``],
  SRW_TAC [] [] THEN SRW_TAC [] [COND_EXPAND, JTinst_any_fun] THEN 
      IMP_RES_TAC weak_one_tv_ok_thm THEN FULL_SIMP_TAC list_ss [shiftt_def] THEN METIS_TAC []),
 ([``"JTinst_any_any"``], METIS_TAC [weak_one_tv_ok_thm]),
 ([``"JTinst_any_tuple"``, ``"JTinst_any_ctor"``], 
  SRW_TAC [] [] THEN 
      Q.EXISTS_TAC `MAP (\a. (shiftt (num_tv E1) 1 (FST a), shiftt (num_tv E1) 1 (SND a))) t_t'_list` THEN
      SRW_TAC [] [MAP_MAP] THEN FULL_SIMP_TAC list_ss [MEM_MAP, weak_one_tv_ok_thm])]);


local

val lem1 = SIMP_RULE list_ss [] (Q.SPECL [`t`, `n`, `0`, `1`] (hd (CONJUNCTS shiftt_com_lem)));

val lem2 = Q.prove (
`!l n m f g h. EVERY (\x. JTpat Tsig (E1 ++ E2) (f x) (g x) (h x)) l ==>
               (num_tv (FLAT (MAP (\x. h x) l)) = 0)`,
Induct THEN SRW_TAC [] [num_tv_def, num_tv_append_thm] THEN METIS_TAC [pat_env_lem, value_env_num_tv_thm]);

val lem3 = Q.prove (
`!l n m f. (num_tv (FLAT (MAP (\x. f x) l)) = 0) ==>
           (shiftE n m (FLAT (MAP (\x. f x) l)) = FLAT (MAP (\x. shiftE n m (f x)) l))`,
Induct THEN SRW_TAC [] [shiftE_def, shiftE_append_thm, num_tv_append_thm]);

val lem6 = Q.prove (
`!E m n. value_env E ==> (shiftE m n E = MAP (\EB. shiftEB m n EB) E)`,
Induct_on `E` THEN SRW_TAC [] [value_env_def, shiftE_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [value_env_def, shiftE_def]  THEN IMP_RES_TAC value_env_num_tv_thm 
THEN FULL_SIMP_TAC (srw_ss()) []);

in

val weak_one_tv_pat_thm = Q.prove (
`!Tsig E pat t E'. JTpat Tsig E pat t E' ==> !E1 E2. (E = E1++E2) ==>
     JTpat (shiftTsig (num_tv E1) 1 Tsig) (shiftE 0 1 E1++[EB_tv]++E2) pat 
           (shiftt (num_tv E1) 1 t) (shiftE (num_tv E1) 1 E')`,
RULE_INDUCT_TAC JTpat_sind [JTpat_fun] 
[([``"JTpat_var"``, ``"JTpat_any"``, ``"JTpat_constant"``], 
  SRW_TAC [] [shiftE_def, shiftEB_def, shiftts_def, num_tv_def] THEN 
        SRW_TAC [] [weak_one_tv_ok_thm, lem1, weak_one_tv_const_thm]),
 ([``"JTpat_alias"``], 
  SRW_TAC [] [shiftE_def, shiftEB_def, shiftts_def, domEB_def, shiftE_dom_thm, lem1] THEN
        IMP_RES_TAC pat_env_lem THEN IMP_RES_TAC value_env_num_tv_thm THEN SRW_TAC [] []),
 ([``"JTpat_typed"``],
  SRW_TAC [] [shiftTsig_def, subst_shiftt_com_lem, LAMBDA_PROD2] THEN
      IMP_RES_TAC weak_one_tv_inst_any_thm THEN
      FULL_SIMP_TAC list_ss [subst_shiftt_com_lem, LAMBDA_PROD2] THEN 
      METIS_TAC [is_src_t_shift_thm, weak_one_tv_teq_thm]),
 ([``"JTpat_construct_any"``], 
  SRW_TAC [] [shiftE_def] THEN METIS_TAC [weak_one_tv_constr_p_thm]),
 ([``"JTpat_construct"``],
  SRW_TAC [] [ELIM_UNCURRY] THEN
     Q.EXISTS_TAC `MAP (\(p, E, t). (p, shiftE (num_tv E1) 1 E, shiftt (num_tv E1) 1 t)) pattern_E_t_list` THEN 
     SRW_TAC [] [LAMBDA_PROD2, MAP_MAP, ETA_THM, ELIM_UNCURRY, EVERY_MAP] THENL
     [METIS_TAC [MAP_REVERSE, EVERY_REVERSE, lem2, lem3],
      IMP_RES_TAC weak_one_tv_constr_p_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP],
      FULL_SIMP_TAC list_ss [EVERY_MEM],
      FULL_SIMP_TAC list_ss [MAP_FLAT, MAP_REVERSE, MAP_MAP, shiftE_dom_thm]]),
 ([``"JTpat_tuple"``],
  SRW_TAC [] [ELIM_UNCURRY] THEN
     Q.EXISTS_TAC `MAP (\(p, t, E). (p, shiftt (num_tv E1) 1 t, shiftE (num_tv E1) 1 E)) pattern_t_E_list` THEN 
     SRW_TAC [] [LAMBDA_PROD2, MAP_MAP, ETA_THM, ELIM_UNCURRY, EVERY_MAP, shiftt_def] THENL
     [METIS_TAC [MAP_REVERSE, EVERY_REVERSE, lem3, lem2],
      FULL_SIMP_TAC list_ss [EVERY_MEM],
      FULL_SIMP_TAC list_ss [MAP_FLAT, MAP_REVERSE, MAP_MAP, shiftE_dom_thm]]),
 ([``"JTpat_record"``],
   SRW_TAC [] [ELIM_UNCURRY] THEN
     Q.EXISTS_TAC `MAP (\(fn, p, E, t). 
                         (fn, p, shiftE (num_tv E1) 1 E, shiftt (num_tv E1) 1 t)) field_name_pattern_E_t_list` 
     THEN
     SRW_TAC [] [LAMBDA_PROD2, MAP_MAP, ETA_THM, ELIM_UNCURRY, EVERY_MAP] THENL
     [METIS_TAC [MAP_REVERSE, EVERY_REVERSE, lem2, lem3],
      FULL_SIMP_TAC list_ss [EVERY_MEM],
      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN RES_TAC THEN 
              IMP_RES_TAC weak_one_tv_field_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP],
      FULL_SIMP_TAC list_ss [MAP_FLAT, MAP_REVERSE, MAP_MAP, shiftE_dom_thm]]),
 ([``"JTpat_cons"``],
  SRW_TAC [] [] THEN 
     MAP_EVERY Q.EXISTS_TAC [`shiftt (num_tv E1) 1 t`, `shiftE (num_tv E1) 1 E'`, 
                             `shiftE (num_tv E1) 1 E''`] THEN 
     SRW_TAC [] [shiftt_def, shiftE_append_thm] THEN FULL_SIMP_TAC list_ss [shiftt_def, shiftE_dom_thm] THEN
     IMP_RES_TAC pat_env_lem THEN IMP_RES_TAC value_env_num_tv_thm THEN SRW_TAC [] []),
 ([``"JTpat_or"``],
  SRW_TAC [] [] THEN IMP_RES_TAC pat_env_lem THEN FULL_SIMP_TAC (srw_ss()) [lem6] THEN 
     METIS_TAC [PERM_MAP])]);


val lem4 = Q.prove (
`!l m n f g. shiftE m 1 (MAP (\z. EB_vn (f z) (TS_forall (shiftt 0 1 (g z)))) l) =
             MAP (\z. EB_vn (f z) (TS_forall (shiftt 0 1 (shiftt m 1 (g z))))) l`,
Induct THEN SRW_TAC [] [shiftE_def, shiftEB_def, lem1, shiftts_def] THEN
METIS_TAC [value_env_map_thm, value_env_num_tv_thm, ADD_0]); 

val lem5 = Q.prove (
`!l m n. shiftE m 1 (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) l) =
         MAP (\z. EB_vn (FST z) (TS_forall (shiftt (m + 1) 1 (SND z)))) l`,
Induct THEN SRW_TAC [] [shiftE_def, shiftEB_def, lem1, shiftts_def] THEN
METIS_TAC [value_env_map_thm, value_env_num_tv_thm, ADD_0]); 

val weak_one_tv_thm = Q.store_thm ("weak_one_tv_thm",
`(!S E e t. JTe S E e t ==>
      !E1 E2. (E = E1++E2) ==> JTe (shiftTsig (num_tv E1) 1 S) (shiftE 0 1 E1++[EB_tv]++E2)
                                   e (shiftt (num_tv E1) 1 t)) /\
 (!S E pm t1 t2. JTpat_matching S E pm t1 t2 ==> 
      !E1 E2. (E = E1++E2) ==> JTpat_matching (shiftTsig (num_tv E1) 1 S) (shiftE 0 1 E1++[EB_tv]++E2) 
                                              pm (shiftt (num_tv E1) 1 t1) (shiftt (num_tv E1) 1 t2)) /\
 (!S E lb E'. JTlet_binding S E lb E' ==>
      !E1 E2. (E = E1++E2) ==> JTlet_binding (shiftTsig (num_tv E1) 1 S) (shiftE 0 1 E1++[EB_tv]++E2) 
                                             lb (shiftE (num_tv E1) 1 E')) /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==>
      !E1 E2. (E = E1++E2) ==> JTletrec_binding (shiftTsig (num_tv E1) 1 S) (shiftE 0 1 E1++[EB_tv]++E2) 
                                                lrbs (shiftE (num_tv E1) 1 E'))`,
RULE_INDUCT_TAC JTe_ind [JTe_fun, shiftt_def]
[([``"JTe_cons"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `shiftt (num_tv E1) 1 t''` THEN SRW_TAC [] [] THEN 
            IMP_RES_TAC weak_one_tv_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftt_def]),
 ([``"JTe_apply"``, ``"JTe_record_proj"``, ``"JTe_match"``, ``"JTe_assertfalse"``],
   METIS_TAC [weak_one_tv_field_thm, weak_one_tv_ok_thm, weak_one_tv_teq_thm]),
 ([``"JTe_and"``, ``"JTe_or"``, ``"JTe_while"``, ``"JTe_function"``, ``"JTe_assert"``],
  SRW_TAC [] [] THEN IMP_RES_TAC weak_one_tv_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftt_def] THEN
      METIS_TAC []),
 ([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_ident"``, ``"JTe_constant"``], 
  SRW_TAC [] [] THEN METIS_TAC [weak_one_tv_uprim_thm, weak_one_tv_bprim_thm, weak_one_tv_val_name_thm,
                                weak_one_tv_const_thm, weak_one_tv_teq_thm]),
 ([``"JTe_location"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `shiftt (num_tv E1) 1 t''` THEN SRW_TAC [] [] THEN1 
      METIS_TAC [weak_one_tv_ok_thm] THEN IMP_RES_TAC weak_one_tv_lookup_thm THEN 
      FULL_SIMP_TAC list_ss [shiftEB_def] THEN IMP_RES_TAC weak_one_tv_teq_thm THEN 
      FULL_SIMP_TAC (srw_ss()) [shiftt_def]),
 ([``"JTe_typed"``],
  SRW_TAC [] [shiftTsig_def, subst_shiftt_com_lem, LAMBDA_PROD2] THEN
      IMP_RES_TAC weak_one_tv_inst_any_thm THEN
      FULL_SIMP_TAC list_ss [subst_shiftt_com_lem, LAMBDA_PROD2] THEN
      METIS_TAC [is_src_t_shift_thm, weak_one_tv_teq_thm]),
 ([``"JTe_tuple"``], 
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\(e, t). (e, shiftt (num_tv E1) 1 t)) e_t_list` THEN
       SRW_TAC [] [shiftt_def, MAP_MAP, LAMBDA_PROD2, ETA_THM] THEN 
       FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MEM_MAP] THEN
       IMP_RES_TAC weak_one_tv_constr_p_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP] THEN 
       IMP_RES_TAC weak_one_tv_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftt_def, MAP_MAP]),
 ([``"JTe_construct"``], 
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\(e, t). (e, shiftt (num_tv E1) 1 t)) e_t_list` THEN
       SRW_TAC [] [shiftt_def, MAP_MAP, LAMBDA_PROD2, ETA_THM] THEN 
       FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MEM_MAP] THEN
       IMP_RES_TAC weak_one_tv_constr_p_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP] THEN 
       IMP_RES_TAC weak_one_tv_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftt_def, MAP_MAP] THEN
       Q.EXISTS_TAC `shiftt (num_tv E1) 1 t''` THEN SRW_TAC [] [] THEN SRW_TAC [] []),
 ([``"JTe_record_constr"``], 
  SRW_TAC [] [] THEN 
       MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `MAP (\x. shiftt (num_tv E1) 1 x) t'_list`,
                               `MAP (\(fn, e, t). (fn, e, shiftt (num_tv E1) 1 t)) field_name_e_t_list`,
                               `typeconstr_name`, `kind`] THEN
       SRW_TAC [] [shiftt_def, MAP_MAP, LAMBDA_PROD2, ETA_THM, EVERY_MAP] THEN 
       FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN RES_TAC THEN
       IMP_RES_TAC weak_one_tv_field_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP, shiftt_def] THEN
       IMP_RES_TAC weak_one_tv_lookup_thm THEN FULL_SIMP_TAC list_ss [shiftEB_def] THEN
       IMP_RES_TAC weak_one_tv_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftt_def, MAP_MAP]),
 ([``"JTe_record_with"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\(fn, e, t). (fn, e, shiftt (num_tv E1) 1 t)) field_name_e_t_list` THEN
       SRW_TAC [] [shiftt_def, MAP_MAP, LAMBDA_PROD2, ETA_THM, EVERY_MAP] THEN
       FULL_SIMP_TAC list_ss [EVERY_MEM] THEN 
       Q.EXISTS_TAC `shiftt (num_tv E1) 1 t''` THEN SRW_TAC [] [] THEN RES_TAC THEN
       IMP_RES_TAC weak_one_tv_field_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP, shiftt_def] THEN
       METIS_TAC [weak_one_tv_teq_thm]),
 ([``"JTe_for"``],
  SRW_TAC [] [] THEN
       Q.PAT_ASSUM `!E1' E2'. P E1' E2' ==> JTe (shiftTsig (num_tv E1') 1 S)
                             (shiftE 0 1 E1' ++ [EB_tv] ++ E2') e'' (TE_constr [] TC_unit)`
            (MP_TAC o
             Q.SPECL [`EB_vn (VN_id lowercase_ident) (TS_forall (TE_constr [] TC_int))::E1`, `E2`]) THEN
       SRW_TAC [] [num_tv_def, shiftE_def, shiftEB_def, shiftts_def, shiftt_def] THEN
       IMP_RES_TAC weak_one_tv_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [shiftt_def, MAP_MAP]),
 ([``"JTe_let_mono"``],
  SRW_TAC [] [] THEN DISJ1_TAC THEN Q.EXISTS_TAC `MAP (\(x, t). (x, shiftt (num_tv E1) 1 t)) x_t_list` THEN
      SRW_TAC [] [] THENL
      [Q.PAT_ASSUM `!E1' E2'. (E1 ++ E2 = E1' ++ E2') ==> P E1' E2'` (MP_TAC o Q.SPECL [`E1`, `E2`]) THEN
           SRW_TAC [] [] THEN MAP_EVERY Q.EXISTS_TAC [`x_t_list'`, `t'`] THEN 
           FULL_SIMP_TAC list_ss [MAP_MAP, LAMBDA_PROD2] THEN METIS_TAC [lem4, MAP_REVERSE],
       Q.PAT_ASSUM `!E1' E2'. P E1' E2' ==> JTe (shiftTsig (num_tv E1') 1 S)
                                                (shiftE 0 1 E1' ++ [EB_tv] ++ E2') e (shiftt (num_tv E1') 1 t)`
                   (MP_TAC o Q.SPECL [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z))))
                                                    x_t_list)++E1`,
                                      `E2`]) THEN
           SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, num_tv_append_thm, GSYM MAP_REVERSE, 
                       shiftE_append_thm] THEN
           METIS_TAC [ADD, value_env_map_thm, value_env_num_tv_thm, lem4]]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\(p, e, E). (p, e, shiftE (num_tv E1) 1 E)) pattern_e_E_list` THEN
     SRW_TAC [] [MAP_MAP, LAMBDA_PROD2] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN
     FULL_SIMP_TAC list_ss [MEM_MAP] THEN1 METIS_TAC [weak_one_tv_pat_thm] THEN RES_TAC THEN SRW_TAC [] [] THEN
     Q.PAT_ASSUM `!E2' E1'. (SND (SND z) ++ E1 ++ E2 = E1' ++ E2') ==> 
                   JTe (shiftTsig (num_tv E1') 1 S) (shiftE 0 1 E1' ++ [EB_tv] ++ E2') (FST (SND z)) 
                       (shiftt (num_tv E1') 1 t2)`
                 (ASSUME_TAC o Q.SPECL [`E2`, `SND (SND (z:pattern # expr # environment)) ++ E1`]) THEN
     FULL_SIMP_TAC list_ss [shiftE_def, num_tv_append_thm, shiftE_append_thm] THEN
     METIS_TAC [ADD_0, pat_env_lem, value_env_num_tv_thm]),
 ([``"JTlet_binding_poly"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\(x, t). (x, shiftt (num_tv E1) 1 t)) x_t_list` THEN
     SRW_TAC [] [GSYM MAP_REVERSE, MAP_MAP, LAMBDA_PROD2, lem4] THEN
     METIS_TAC [weak_one_tv_pat_thm, MAP_REVERSE, lem4]),
 ([``"JTe_let_poly"``],
  SRW_TAC [] [] THEN DISJ2_TAC THEN 
     Q.EXISTS_TAC `MAP (\(x, t). (x, shiftt (num_tv E1 + 1) 1 t)) x_t_list` THEN SRW_TAC [] [] THENL
     [Q.PAT_ASSUM `!E1' E2'. (EB_tv::(E1 ++ E2) = E1' ++ E2') ==> P E1' E2'` 
                  (MP_TAC o Q.SPECL [`EB_tv::E1`, `E2`]) THEN
           SRW_TAC [] [] THEN MAP_EVERY Q.EXISTS_TAC [`x_t_list'`, `t'`] THEN
           FULL_SIMP_TAC list_ss [MAP_MAP, LAMBDA_PROD2, shiftE_def, shiftEB_def, num_tv_def, 
                                  lem4, GSYM MAP_REVERSE] THEN
           METIS_TAC [shiftTsig_com_lem, ADD, ADD_0],
      Q.PAT_ASSUM `!E1' E2'. P E1' E2' ==> JTe (shiftTsig (num_tv E1') 1 S)
                                                (shiftE 0 1 E1' ++ [EB_tv] ++ E2') e (shiftt (num_tv E1') 1 t)`
                   (MP_TAC o Q.SPECL [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z)))
                                                    x_t_list)++E1`,
                                      `E2`]) THEN
           SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, num_tv_append_thm, GSYM MAP_REVERSE,
                       shiftE_append_thm] THEN
           FULL_SIMP_TAC list_ss [lem5] THEN 
           METIS_TAC [ADD_0, value_env_map_thm, value_env_num_tv_thm]]),
 ([``"JTe_letrec"``],
  SRW_TAC [] [] THEN
     Q.PAT_ASSUM `!E1' E2'. (EB_tv::(E1 ++ E2) = E1' ++ E2') ==> P E1' E2'`
                  (MP_TAC o Q.SPECL [`EB_tv::E1`, `E2`]) THEN
     Q.PAT_ASSUM `!E1' E2'. P E1' E2' ==> JTe (shiftTsig (num_tv E1') 1 S)
                                                (shiftE 0 1 E1' ++ [EB_tv] ++ E2') e (shiftt (num_tv E1') 1 t)`
                   (MP_TAC o Q.SPECL [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z)))
                                                    x_t_list)++E1`,
                                      `E2`]) THEN
     SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, num_tv_append_thm, GSYM MAP_REVERSE,
                 shiftE_append_thm] THEN
     Q.EXISTS_TAC `MAP (\(x, t). (x, shiftt (num_tv E1 + 1) 1 t)) x_t_list` THEN
     FULL_SIMP_TAC list_ss [MAP_MAP, LAMBDA_PROD2, shiftE_def, shiftEB_def, num_tv_def,
                            lem4, GSYM MAP_REVERSE, lem5] THEN
     METIS_TAC [ADD_0, value_env_map_thm, value_env_num_tv_thm, shiftTsig_com_lem, ADD]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [] THEN 
     Q.EXISTS_TAC `MAP (\(vn, pm, t1, t2). (vn, pm, shiftt (num_tv E1) 1 t1, shiftt (num_tv E1) 1 t2)) 
                       value_name_pattern_matching_t_t'_list` THEN
     SRW_TAC [] [GSYM MAP_REVERSE, MAP_MAP, LAMBDA_PROD2, EVERY_MAP] THEN1
     SRW_TAC [] [GSYM shiftt_def, lem4] THEN
     FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN RES_TAC THEN
     POP_ASSUM (ASSUME_TAC o Q.SPECL [`E2`, 
                                  `REVERSE (MAP (\(z:value_name # pattern_matching # typexpr # typexpr).
                                                    EB_vn (FST z) 
                                                       (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z))) 
                                                                                        (SND (SND (SND z)))))))
                                                 value_name_pattern_matching_t_t'_list) ++ E1`]) THEN 
     FULL_SIMP_TAC list_ss [GSYM shiftt_def, GSYM MAP_REVERSE, lem4, shiftE_append_thm, num_tv_append_thm] THEN
     METIS_TAC [ADD_0, value_env_map_thm, value_env_num_tv_thm, ADD])]);

end;

val weak_teq_thm = Q.store_thm ("weak_teq_thm",
`!E t1 t2. JTeq E t1 t2 ==> !E3. (E = E1++E2) /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==> JTeq (E1++E3++E2) t1 t2`,
RULE_INDUCT_TAC JTeq_ind []
[([``"JTeq_refl"``], METIS_TAC [weak_ok_thm, JTeq_rules]),
 ([``"JTeq_sym"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_trans"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_arrow"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_tuple"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 3 DISJ2_TAC THEN
      FULL_SIMP_TAC (srw_ss ()) [EVERY_MEM] THEN METIS_TAC []),
 ([``"JTeq_constr"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 4 DISJ2_TAC THEN
      FULL_SIMP_TAC (srw_ss ()) [EVERY_MEM] THEN METIS_TAC [weak_ok_thm]),
 ([``"JTeq_expand"``],
  SRW_TAC [] [] THEN SRW_TAC [] [Once JTeq_cases, MAP_MAP] THEN NTAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
      Q.EXISTS_TAC `t_typevar_list` THEN Q.EXISTS_TAC `t` THEN SRW_TAC [] [] THENL
      [`MEM (name_tcn typeconstr_name) (MAP domEB E1) \/ ~MEM (name_tcn typeconstr_name) (MAP domEB E3)` by
                            METIS_TAC [lookup_dom_thm, weak_helper_lem2] THEN
           METIS_TAC [weak_lookup_thm],
       FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN METIS_TAC [weak_ok_thm]])]);

val weak_inst_thm = Q.prove (
`!E1 E2 t ts E3. JTinst (E1++E2) t ts /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==> JTinst (E1++E3++E2) t ts`,
SRW_TAC [] [JTinst_cases] THEN SRW_TAC [] [Eok_def] THEN FULL_SIMP_TAC list_ss [Eok_def, EVERY_MEM] THEN 
`Eok (EB_tv::(E1 ++ E3 ++ E2))` by SRW_TAC [] [Eok_def] THEN METIS_TAC [APPEND, weak_ok_thm]);

val weak_inst_named_thm = Q.prove (
`!E1 E2 t tpo ts E3. JTinst_named (E1++E2) t tpo ts /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==> 
			  JTinst_named (E1++E3++E2) t tpo ts`,
SRW_TAC [] [JTinst_named_cases] THEN SRW_TAC [] [Eok_def] THEN FULL_SIMP_TAC list_ss [Eok_def, EVERY_MEM] THEN
`Eok (EB_tv::(E1 ++ E3 ++ E2))` by SRW_TAC [] [Eok_def] THEN METIS_TAC [APPEND, weak_ok_thm]);

val weak_uprim_thm = Q.prove (
`!E1 E2 uprim t E3. JTuprim (E1++E2) uprim t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                 JTuprim (E1++E3++E2) uprim t`,
SRW_TAC [] [JTuprim_cases] THEN METIS_TAC [weak_ok_thm]);

val weak_bprim_thm = Q.prove (
`!E1 E2 bprim t E3. JTbprim (E1++E2) bprim t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                    JTbprim (E1++E3++E2) bprim t`,
SRW_TAC [] [JTbprim_cases] THEN METIS_TAC [weak_ok_thm]);

val weak_val_name_thm = Q.prove (
`!E1 E2 vn t E3. JTvalue_name (E1++E2) vn t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) /\
                 (MEM (name_vn vn) (MAP domEB E3) ==> MEM (name_vn vn) (MAP domEB E1)) ==>
                 JTvalue_name (E1++E3++E2) vn t`,
SRW_TAC [] [JTvalue_name_cases] THEN IMP_RES_TAC weak_helper_lem3 THEN FULL_SIMP_TAC list_ss [] THEN
METIS_TAC [weak_lookup_thm, weak_inst_thm]);

val weak_constr_c_thm = Q.prove (
`!E1 E2 constr t E3. JTconstr_c (E1++E2) constr t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                     JTconstr_c (E1++E3++E2) constr t`,
SRW_TAC [] [JTconstr_c_cases, weak_ok_thm, EVERY_MAP] THEN
IMP_RES_TAC weak_helper_lem3 THEN IMP_RES_TAC weak_helper_lem2 THEN SRW_TAC [] [] THEN 
IMP_RES_TAC weak_lookup_thm THEN 
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_MEM, weak_ok_thm]);

val weak_const_thm = Q.prove (
`!E1 E2 const t EB. JTconst (E1++E2) const t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                    JTconst (E1++E3++E2) const t`,
SRW_TAC [] [JTconst_cases, weak_ok_thm, weak_constr_c_thm]);

val weak_constr_p_thm = Q.prove (
`!E1 E2 constr tl t E3. JTconstr_p (E1++E2) constr tl t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                        JTconstr_p (E1++E3++E2) constr tl t`,
SRW_TAC [] [JTconstr_p_cases, weak_ok_thm] THEN
IMP_RES_TAC weak_helper_lem3 THEN IMP_RES_TAC weak_helper_lem2 THEN SRW_TAC [] [] THEN 
IMP_RES_TAC weak_lookup_thm THEN SRW_TAC [] [] THEN METIS_TAC [weak_inst_named_thm]);

val weak_field_thm = Q.prove (
`!E1 E2 fn t t' E3. JTfield (E1++E2) fn t t' /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                    JTfield (E1++E3++E2) fn t t'`,
SRW_TAC [] [JTfield_cases, weak_ok_thm] THEN
IMP_RES_TAC weak_helper_lem3 THEN IMP_RES_TAC weak_helper_lem2 THEN SRW_TAC [] [] THEN 
IMP_RES_TAC weak_lookup_thm THEN SRW_TAC [] [] THEN METIS_TAC [weak_inst_named_thm]);

val weak_inst_any_thm = Q.prove (
`!E t t'. JTinst_any E t t' ==> !E1 E2 E3. (E = E1++E2) /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
    JTinst_any (E1++E3++E2) t t'`,
RULE_INDUCT_TAC JTinst_any_ind [JTinst_any_fun, EVERY_MEM] [] THEN
METIS_TAC [weak_ok_thm]);

val weak_pat_thm = Q.prove (
`!Tsig E pat t E'. JTpat Tsig E pat t E' ==> !E1 E2 E3. (E = E1++E2) /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
     JTpat Tsig (E1++E3++E2) pat t E'`,
RULE_INDUCT_TAC JTpat_sind [JTpat_fun]
[([``"JTpat_var"``, ``"JTpat_any"``, ``"JTpat_cons"``], METIS_TAC [weak_ok_thm]),
 ([``"JTpat_typed"``], METIS_TAC [weak_inst_any_thm, weak_teq_thm]),
 ([``"JTpat_constant"``], METIS_TAC [weak_const_thm]),
 ([``"JTpat_construct"``, ``"JTpat_construct_any"``, ``"JTpat_tuple"``],
  FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [weak_constr_p_thm]),
 ([``"JTpat_record"``],
  FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [weak_field_thm]),
 ([``"JTpat_or"``],
  METIS_TAC [])]);

local

val lem1 = Q.prove (
`(!t E. tkind (EB_tv::EB_tv::E) (shiftt 0 1 t) = tkind (EB_tv::E) t) /\
 (!tl E. EVERY (\t. tkind (EB_tv::EB_tv::E) (shiftt 0 1 t)) tl =
         EVERY (\t. tkind (EB_tv::E) t) tl)`,
Induct THEN SRW_TAC [] [Eok_def, shiftt_def, EVERY_MAP, idx_bound_def, GSYM ADD1] THEN
Cases_on `t` THEN SRW_TAC [] [Eok_def, lookup_def] THEN Cases_on `lookup E (name_tcn t')` THEN
SRW_TAC [] [shiftEB_add_thm] THEN IMP_RES_TAC lookup_name_thm THEN FULL_SIMP_TAC list_ss [] THEN
SRW_TAC [] [shiftEB_def]);

val lem2 = (GEN_ALL o SIMP_RULE list_ss [] o Q.SPECL [`t`, `[EB_tv]`, `x`, `[EB_tv] ++ E`] o
            SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o hd o tl o tl o tl o tl o CONJUNCTS)
           value_env_ok_str_thm;

val lem3 = (GEN_ALL o SIMP_RULE list_ss [Eok_def] o Q.SPECL [`[EB_tv]`, `t`, `E1++E2`, `[h]`] o
            SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o hd o tl o tl o tl o tl o CONJUNCTS)
           weak_ok_thm;

val lem4 = Q.prove (
`!E' E t. value_env E' /\ Eok (E'++E) /\ tkind (EB_tv::E) t ==> tkind (EB_tv::(E'++E)) t`,
Induct THEN SRW_TAC [] [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [value_env_def, Eok_def] THEN
MATCH_MP_TAC lem3 THEN SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_ok_thm]);

in

val tv_ok_str_thm = Q.prove (
`!x_t_list. Eok (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list ++ [EB_tv] ++ E) ==>
             Eok (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list ++ E)`,
Induct THEN SRW_TAC [] [Eok_def] THEN IMP_RES_TAC lem2 THEN
FULL_SIMP_TAC list_ss [value_env_map_thm, lem1] THEN IMP_RES_TAC ok_ok_thm THEN
FULL_SIMP_TAC list_ss [Eok_def] THEN METIS_TAC [lem4, value_env_map_thm]);
end;

local

val lem1 = Q.prove (
`!lrbs S E E'. Eok E /\ JTletrec_binding S E lrbs E' ==> Eok (E'++E)`,
Cases THEN SRW_TAC [] [JTe_fun] THEN Cases_on `value_name_pattern_matching_t_t'_list` THEN 
FULL_SIMP_TAC list_ss [] THEN METIS_TAC [ok_thm, ok_ok_thm]);

val lem2 = Q.prove (
`!l f g E1 E2 E3. Eok (MAP (\x. EB_vn (f x) (g x)) l ++ E1 ++ E2) /\ Eok (E1++E3++E2) /\ ~MEM EB_tv E3 ==>
                  Eok (MAP (\x. EB_vn (f x) (g x)) l ++ E1 ++ E3 ++ E2)`,
Induct THEN SRW_TAC [] [Eok_def] THEN METIS_TAC [weak_ok_thm, ok_ok_thm]);

val lem3 = Q.prove (
`!l1 l2. (MAP name_vn l1 = MAP (\z. name_vn (FST z)) l2) = 
         (l1 = MAP FST l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN SRW_TAC [] []);

val lem4 = Q.prove (
`!l1 l2. (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l1 = 
          MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l2) =
         (l1 = l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN SRW_TAC [] [shiftt_11] THEN
Cases_on `h` THEN Cases_on `h'` THEN SRW_TAC [] []);

val lem5 = Q.prove (
`!E3 lrbs x_t_list e E1.
 ~MEM EB_tv E3 /\
 (!n. MEM n (MAP domEB E3) /\ (MEM n (MAP name_vn (list_minus (fv_letrec_bindings lrbs) (MAP FST x_t_list))) \/
                               MEM n (MAP name_vn (list_minus (fv_expr e) (MAP FST x_t_list)))) ==>
  MEM n (MAP domEB E1))
 ==>
  (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_expr e)) ==> 
   MEM n (MAP (\z. name_vn (FST z)) x_t_list) \/ MEM n (MAP domEB E1))
 /\
  (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_letrec_bindings lrbs)) /\
           ~MEM n (MAP (\z. name_vn (FST z)) x_t_list) ==>
           (n = name_tv) \/ MEM n (MAP domEB E1))`,
SRW_TAC [] [MEM_MAP, list_minus_thm] THEN METIS_TAC []);

val lem6 = Q.prove (
`!E1 EB E2. E1++[EB]++E2 = E1++EB::E2`,
METIS_TAC [APPEND, APPEND_ASSOC]);

val lem7 = Q.prove (
`!l1 l2. MAP name_vn (list_minus l1 l2) = list_minus (MAP name_vn l1) (MAP name_vn l2)`,
Induct THEN SRW_TAC [] [list_minus_def, MEM_MAP]);

val lem8 = Q.prove (
`(!n. MEM n (MAP domEB E3) /\
    MEM n 
      (list_minus (FLAT (MAP (\z. MAP name_vn (fv_pattern_matching (FST (SND z))))
                              value_name_pattern_matching_t_t'_list))
                  (MAP name_vn (aux_xs_letrec_bindings_of_letrec_bindings
                                  (LRBs_inj (MAP (\z. LRB_simple (FST z) (FST (SND z)))
                                                 value_name_pattern_matching_t_t'_list))))) ==>
      MEM n (MAP domEB E1))
 ==>
!x. MEM x value_name_pattern_matching_t_t'_list ==>
    (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_pattern_matching (FST (SND x)))) ==>
    MEM n (MAP (\z. name_vn (FST z)) (REVERSE value_name_pattern_matching_t_t'_list)) \/
    MEM n (MAP domEB E1))`,
SRW_TAC [] [list_minus_thm, EXISTS_MEM, aux_xs_letrec_bindings_of_letrec_bindings_def, FLAT_MAP_SING, MEM_FLAT,
            aux_xs_letrec_binding_of_letrec_binding_def, MAP_MAP] THEN
      FULL_SIMP_TAC list_ss [MAP_REVERSE] THEN
      Cases_on `MEM n (MAP (\z. name_vn (FST z)) value_name_pattern_matching_t_t'_list)` THEN
      FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN 
      Q.PAT_ASSUM `!n. P n ==> MEM n (MAP domEB E1)` MATCH_MP_TAC THEN SRW_TAC [] [] THEN
      Q.EXISTS_TAC `MAP name_vn (fv_pattern_matching (FST (SND x)))` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC list_ss [MEM_MAP] THEN METIS_TAC []);

in

val weak_not_tv_thm = Q.store_thm ("weak_not_tv_thm", 
`(!S E e t. JTe S E e t ==>
      !E1. (E = E1++E2) /\ ~MEM EB_tv E3 /\ 
           (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_expr e)) ==> MEM n (MAP domEB E1)) /\ 
           Eok (E1++E3++E2) ==>
           JTe S (E1++E3++E2) e t) /\
 (!S E pm t1 t2. JTpat_matching S E pm t1 t2 ==>
      !E1. (E = E1++E2) /\ ~MEM EB_tv E3 /\ 
           (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_pattern_matching pm)) ==> 
                MEM n (MAP domEB E1)) /\ 
           Eok (E1++E3++E2) ==>
           JTpat_matching S (E1++E3++E2) pm t1 t2) /\
 (!S E lb E'. JTlet_binding S E lb E' ==>
      !E1. (E = E1++E2) /\ ~MEM EB_tv E3 /\ 
           (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_let_binding lb)) ==> MEM n (MAP domEB E1)) /\ 
           Eok (E1++E3++E2) ==>
           JTlet_binding S (E1++E3++E2) lb E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==>
      !E1. (E = E1++E2) /\ ~MEM EB_tv E3 /\
           (!n. MEM n (MAP domEB E3) /\ 
                MEM n (list_minus (MAP name_vn (fv_letrec_bindings lrbs))
                                  (MAP name_vn (aux_xs_letrec_bindings_of_letrec_bindings lrbs))) ==>
                MEM n (MAP domEB E1)) /\ 
           Eok (E1++E3++E2) ==>
           JTletrec_binding S (E1++E3++E2) lrbs E')`,
RULE_INDUCT_TAC JTe_sind [JTe_fun, EVERY_MEM, fv_letrec_binding_def, MAP_FLAT, MAP_MAP, MEM_FLAT,
                          EXISTS_MAP, EXISTS_MEM]
[([``"JTe_uprim"``], METIS_TAC [weak_uprim_thm, weak_teq_thm]),
 ([``"JTe_bprim"``], METIS_TAC [weak_bprim_thm, weak_teq_thm]),
 ([``"JTe_ident"``], METIS_TAC [weak_val_name_thm, weak_teq_thm]),
 ([``"JTe_constant"``], METIS_TAC [weak_const_thm, weak_teq_thm]),
 ([``"JTe_typed"``], METIS_TAC [weak_inst_any_thm, weak_teq_thm]),
 ([``"JTe_tuple"``, ``"JTe_apply"``, ``"JTe_match"``], METIS_TAC [weak_teq_thm]),
 ([``"JTe_construct"``], METIS_TAC [weak_constr_p_thm, weak_teq_thm]),
 ([``"JTe_cons"``, ``"JTe_and"``, ``"JTe_or"``, ``"JTe_while"``, ``"JTe_function"``, ``"JTe_assert"``],
  METIS_TAC [weak_teq_thm]),
 ([``"JTe_record_with"``, ``"JTe_record_proj"``],
      METIS_TAC [weak_field_thm, weak_teq_thm]),
 ([``"JTe_assertfalse"``], METIS_TAC [weak_ok_thm]),
 ([``"JTe_location"``],
  SRW_TAC [] [] THEN IMP_RES_TAC weak_helper_lem3 THEN IMP_RES_TAC weak_helper_lem2 THEN SRW_TAC [] [] THEN 
           IMP_RES_TAC weak_lookup_thm THEN SRW_TAC [] [] THEN METIS_TAC [weak_teq_thm]),
 ([``"JTe_record_constr"``], 
  SRW_TAC [] [] THEN 
           MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`, `field_name_e_t_list`,
                                   `typeconstr_name`, `kind`] THEN 
           IMP_RES_TAC weak_helper_lem3 THEN IMP_RES_TAC weak_helper_lem2 THEN SRW_TAC [] [] THEN
           IMP_RES_TAC weak_lookup_thm THEN IMP_RES_TAC weak_field_thm THEN IMP_RES_TAC weak_teq_thm THEN
           SRW_TAC [] [] THEN METIS_TAC []),
 ([``"JTe_for"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC std_ss [GSYM APPEND, APPEND_11, APPEND_ASSOC] THEN
           FULL_SIMP_TAC list_ss [domEB_def, Eok_def, shiftt_def, GSYM MAP_REVERSE] THEN
           FULL_SIMP_TAC list_ss [MEM_MAP, list_minus_thm] THEN
           METIS_TAC [weak_teq_thm]),
 ([``"JTe_let_mono"``],
  SRW_TAC [] [] THEN 
           IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
           FULL_SIMP_TAC std_ss [GSYM APPEND, APPEND_11, APPEND_ASSOC, GSYM MAP_REVERSE] THEN
           FULL_SIMP_TAC list_ss [MAP_MAP, lem4, REVERSE_EQ] THEN 
           FULL_SIMP_TAC list_ss [list_minus_thm, domEB_def, lem3, MAP_REVERSE, MEM_REVERSE,
                                  aux_xs_let_binding_of_let_binding_def] THEN
           SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MEM_MAP, list_minus_thm] THEN
           METIS_TAC [APPEND_ASSOC, pat_ok_thm2]),
 ([``"JTe_let_poly"``],
  SRW_TAC [] [] THEN
           IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
           FULL_SIMP_TAC std_ss [GSYM APPEND, APPEND_11, APPEND_ASSOC] THEN
           FULL_SIMP_TAC list_ss [Eok_def, MAP_MAP, GSYM MAP_REVERSE] THEN IMP_RES_TAC pat_ok_thm2 THEN
           FULL_SIMP_TAC list_ss [MAP_MAP, lem4, REVERSE_EQ] THEN
           FULL_SIMP_TAC list_ss [list_minus_thm, domEB_def, lem3, MAP_REVERSE, MEM_REVERSE,
                                  aux_xs_let_binding_of_let_binding_def] THEN
           SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MEM_MAP, list_minus_thm] THEN
           DISJ2_TAC THEN Q.EXISTS_TAC `x_t_list` THEN SRW_TAC [] [] THEN1 METIS_TAC [] THEN
           Q.PAT_ASSUM `x ==> JTe S y e t` MATCH_MP_TAC THEN
           METIS_TAC [APPEND_ASSOC, tv_ok_str_thm, MAP_REVERSE, APPEND]),
 ([``"JTe_letrec"``],
  SRW_TAC [] [] THEN 
           IMP_RES_TAC aux_xs_letrec_bindings_of_letrec_bindings_thm THEN
           FULL_SIMP_TAC std_ss [GSYM APPEND, APPEND_11, APPEND_ASSOC] THEN
           FULL_SIMP_TAC list_ss [Eok_def, MAP_MAP, GSYM MAP_REVERSE] THEN 
           FULL_SIMP_TAC list_ss [MAP_MAP, lem4, REVERSE_EQ] THEN
           FULL_SIMP_TAC list_ss [list_minus_thm, domEB_def, lem3, MAP_REVERSE, MEM_REVERSE,
                                  aux_xs_letrec_binding_of_letrec_binding_def] THEN
           SRW_TAC [] [] THEN IMP_RES_TAC lem5 THEN FULL_SIMP_TAC list_ss [] THEN
           IMP_RES_TAC lem1 THEN FULL_SIMP_TAC list_ss [Eok_def] THEN
           METIS_TAC [APPEND_ASSOC, tv_ok_str_thm, MAP_REVERSE, APPEND]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `pattern_e_E_list` THEN SRW_TAC [] [] THEN
      RES_TAC THEN FULL_SIMP_TAC list_ss [lem7] THEN SRW_TAC [] [] THEN
      IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
      FULL_SIMP_TAC list_ss [] THEN
      FULL_SIMP_TAC list_ss [list_minus_thm, MAP_REVERSE] THEN
      METIS_TAC [weak_pat_thm, pat_ok_thm2, APPEND_ASSOC, MEM_APPEND, MAP_APPEND]), 
 ([``"JTlet_binding_poly"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `x_t_list` THEN SRW_TAC [] [] THEN
      METIS_TAC [weak_pat_thm, pat_ok_thm2, APPEND_ASSOC, MEM_APPEND, MAP_APPEND]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [] THEN
      FULL_SIMP_TAC list_ss [GSYM MAP_REVERSE, MAP_MAP, domEB_def] THEN
      IMP_RES_TAC lem8 THEN METIS_TAC [lem2, ok_ok_thm, ok_thm])]);

end;

val label_lookup_weak_thm = Q.store_thm ("label_lookup_weak_thm",
`!S E L E' name EB. JTLout S E L E' /\ (!l. ~(name = name_l l)) ==> (lookup E name = lookup (E'++E) name)`,
SRW_TAC [] [JTLout_cases] THEN SRW_TAC [] [lookup_def, domEB_def, shiftEB_add_thm] THEN
Cases_on `(lookup E name)` THEN SRW_TAC [] []);

local

val lem1 = Q.prove (
`!x y. x::y = [x]++y`,
SRW_TAC [] []);

in

val label_constr_p_weak_thm = Q.store_thm ("label_constr_p_weak_thm",
`(!E constr t t'. JTconstr_p E constr t t' /\ JTLout S E L E' /\ JTLin S E L ==> 
 JTconstr_p (E'++E) constr t t')`,
SRW_TAC [] [JTLout_cases, JTLin_cases] THEN SRW_TAC [] [] THEN 
ONCE_REWRITE_TAC [lem1] THEN
MATCH_MP_TAC ((SIMP_RULE list_ss [] o Q.SPEC `[]`) weak_constr_p_thm) THEN
SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_thm]);

val label_field_weak_thm = Q.store_thm ("label_field_weak_thm",
 `(!E fn t t'. JTfield E fn t t' /\ JTLout S E L E' /\ JTLin S E L ==> JTfield (E'++E) fn t t')`,
SRW_TAC [] [JTLout_cases, JTLin_cases] THEN SRW_TAC [] [] THEN 
ONCE_REWRITE_TAC [lem1] THEN
MATCH_MP_TAC ((SIMP_RULE list_ss [] o Q.SPEC `[]`) weak_field_thm) THEN
SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_thm]);

end;

val label_weak_thm = Q.store_thm ("label_weak_thm",
`(!S E E' e t. JTe S E e t /\ JTLout S E L E' /\ JTLin S E L ==> JTe S (E'++E) e t) /\
 (!S E E' pm t t'. JTpat_matching S E pm t t' /\ JTLout S E L E' /\ JTLin S E L ==>
            JTpat_matching S (E'++E) pm t t') /\
 (!S E E' p t E''. JTpat S E p t E'' /\ JTLout S E L E' /\ JTLin S E L ==> JTpat S (E'++E) p t E'')`,
SRW_TAC [] [JTLout_cases, JTLin_cases] THEN SRW_TAC [] [] THENL
[MATCH_MP_TAC ((GEN_ALL o SIMP_RULE list_ss [] o Q.SPECL [`[EB_l location t']`, `E`, `S`, `e`, `t`, `[]`] o 
                SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] o GEN_ALL o  
                hd o CONJUNCTS) weak_not_tv_thm),  
 MATCH_MP_TAC ((GEN_ALL o SIMP_RULE list_ss [] o 
                Q.SPECL [`[EB_l location t']`, `E`, `S`, `pm`, `t1`, `t2`, `[]`] o 
                SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] o GEN_ALL o
                hd o tl o CONJUNCTS) weak_not_tv_thm),
 MATCH_MP_TAC ((GEN_ALL o SIMP_RULE list_ss [] o 
                Q.SPECL [`Tsig`, `pat`, `t`, `E'`, `[]`, `E`, `[EB_l location t']`] o 
                SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]) weak_pat_thm)] 
THEN SRW_TAC [] [Eok_def, domEB_def, MEM_MAP] THEN METIS_TAC [ok_thm]);

local

val lem1 = Q.prove (
`!l t. ~(EB_l l t = EB_tv)`, SRW_TAC [] []);

in

val weak_one_loc_ok_thm = Q.store_thm ("weak_one_loc_ok_thm",
`!E1 E2 t location. Eok (E1++E2) /\ tkind E2 t /\ ~MEM (name_l location) (MAP domEB (E1++E2)) ==>
                    Eok (E1++[EB_l location t]++E2)`,
Induct THEN SRW_TAC [] [Eok_def] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [Eok_def, domEB_def] THEN
SRW_TAC [] [] THENL
[METIS_TAC [lem1, weak_ok_thm, ok_ok_thm, MEM, APPEND],
 Cases_on `t'` THEN FULL_SIMP_TAC list_ss [Eok_def] THEN SRW_TAC [] [domEB_def] THEN
     Q.EXISTS_TAC `kind` THEN MATCH_MP_TAC weak_lookup_thm THEN SRW_TAC [] [domEB_def],
 Cases_on `t'` THEN Cases_on `t0` THEN Cases_on `t1` THEN Cases_on `l` THEN 
     FULL_SIMP_TAC list_ss [Eok_def, substs_tv_empty_thm] THEN SRW_TAC [] [domEB_def] THEN
     FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THENL
     [METIS_TAC [lem1, weak_ok_thm, ok_ok_thm, MEM],
      MATCH_MP_TAC weak_lookup_thm THEN SRW_TAC [] [domEB_def],
      METIS_TAC [],
      METIS_TAC [],
      METIS_TAC [lem1, weak_ok_thm, ok_ok_thm, MEM],
      MATCH_MP_TAC weak_lookup_thm THEN SRW_TAC [] [domEB_def],
      METIS_TAC [lem1, weak_ok_thm, ok_ok_thm, MEM]],
 Cases_on `t'` THEN FULL_SIMP_TAC list_ss [Eok_def] THEN SRW_TAC [] [domEB_def] THENL
     [METIS_TAC [lem1, weak_ok_thm, ok_ok_thm, MEM, APPEND],
      Q.EXISTS_TAC `field_name_list` THEN SRW_TAC [] [] THEN
          MATCH_MP_TAC weak_lookup_thm THEN SRW_TAC [] [domEB_def]],
 Cases_on `t'` THEN FULL_SIMP_TAC list_ss [Eok_def] THEN SRW_TAC [] [domEB_def] THEN
     METIS_TAC [lem1, weak_ok_thm, ok_ok_thm, MEM, APPEND],
 METIS_TAC [lem1, weak_ok_thm, ok_ok_thm, MEM, APPEND]]);
end;

local

val lem1 = Q.prove (
`!E l. value_env E ==> ~MEM (name_l l) (MAP domEB E)`,
recInduct Eok2_ind THEN SRW_TAC [] [domEB_def, value_env_def]);

val lem2 = Q.prove (
`!E1 EB E2. E1++[EB]++E2 = E1++EB::E2`,
METIS_TAC [APPEND, APPEND_ASSOC]);

in

val val_env_label_weak_thm = Q.store_thm ("val_env_label_weak_thm",
`(!S E E' E'' e t. JTe S (E++E') e t /\ value_env E /\ JTLout S E' L E'' /\ JTLin S E' L ==> 
                    JTe S (E++E''++E') e t) /\
 (!S E E' E'' p t E'''. JTpat S (E++E') p t E''' /\ value_env E /\ JTLout S E' L E'' /\ JTLin S E' L ==> 
                        JTpat S (E++E''++E') p t E''')`,
SRW_TAC [] [JTLout_cases, JTLin_cases] THEN SRW_TAC [] [] THENL
[MATCH_MP_TAC ((GEN_ALL o 
                SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] o
                hd o CONJUNCTS) weak_not_tv_thm),
 MATCH_MP_TAC ((GEN_ALL o
                SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]) weak_pat_thm)] THEN
SRW_TAC [] [domEB_def, MEM_MAP] THEN 
METIS_TAC [weak_one_loc_ok_thm, lem1, ok_thm, ok_ok_thm, pat_ok_thm, MAP_APPEND, MEM_APPEND]);
end;


local

val lem1 = Q.prove (
`!E n. shiftE n 0 E = E`,
Induct THEN SRW_TAC [] [shiftE_def, shiftEB_add_thm]);

val lem2 = Q.prove (
`!EB E. ~(EB = EB_tv) ==> (num_tv (EB::E) = num_tv E)`,
Cases THEN SRW_TAC [] [num_tv_def]);

in

val weak_lem = Q.prove (
`!S e t E2 E3.
     JTe S ([EB_tv]++E3) e t /\
     DISJOINT (MAP name_vn (fv_expr e)) (MAP domEB E2) /\
     Eok (E2++E3) ==>
     JTe (shiftTsig 1 (num_tv E2) S) ([EB_tv]++E2++E3) e
     (shiftt 1 (num_tv E2) t)`,
Induct_on `E2` THEN SRW_TAC [] [num_tv_def, shiftTsig_add_thm, shiftt_add_thm, lem1] THEN
Cases_on `h = EB_tv` THEN 
FULL_SIMP_TAC list_ss [num_tv_def, lem2, Eok_def, DISJOINT_RIGHT] THENL
[RES_TAC THEN
   IMP_RES_TAC ((SIMP_RULE list_ss [] o GEN_ALL o Q.SPECL [`S`, `e`, `t`, `[EB_tv]`] o 
                 SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] o
                 hd o CONJUNCTS) weak_one_tv_thm) THEN
   FULL_SIMP_TAC list_ss [num_tv_def, shiftE_def, shiftEB_def, GSYM shiftt_add_thm, shiftTsig_add_thm],
 MATCH_MP_TAC ((SIMP_RULE list_ss [] o GEN_ALL o Q.SPECL [`[h]`, `E2++E3`, `S`, `e`, `t`, `[EB_tv]`] o 
                  GEN_ALL o 
                  SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] o 
                  hd o CONJUNCTS) weak_not_tv_thm) THEN
   SRW_TAC [] [Eok_def] THEN
   METIS_TAC [APPEND, ok_ok_thm]]);

val weak_thm = Q.store_thm ("weak_thm",
`!S e t E2 E3.
     JTe S ([EB_tv]++E3) e t /\
     closed_env E3 /\
     Eok (E2++E3) ==>
     JTe (shiftTsig 1 (num_tv E2) S) ([EB_tv]++E2++E3) e
     (shiftt 1 (num_tv E2) t)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC weak_lem THEN SRW_TAC [] [] THEN
IMP_RES_TAC closed_env_tv_lem THEN IMP_RES_TAC closed_env_fv_thm THEN
SRW_TAC [] [DISJOINT_def]);

end;

val _ = export_theory ();
