open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory shiftTheory environmentTheory validTheory;

val _ = Parse.hide "S";

val _ = new_theory "type_subst";

val EVERY_FLAT = Q.prove (
`!l P. (P []) /\ (!x y. P (x++y) = P x /\ P y) ==> (EVERY P l = P (FLAT l))`,
Induct THEN SRW_TAC [] []);

val EVERY_ZIP_SAME = Q.prove (
`!l f. EVERY (\x. f (FST x) (SND x)) (ZIP (l,l)) = EVERY (\x. f x x) l`,
Induct THEN SRW_TAC [] []);


local

val lem1 = Q.prove (
`(!t l m n. shiftt 0 (m + (n + l)) t = shiftt n m (shiftt 0 (n + l) t)) /\
 (!tl l m n. MAP (\t. shiftt 0 (m + (n + l)) t) tl = MAP (\t. shiftt n m (shiftt 0 (n + l) t)) tl)`,
Induct THEN SRW_TAC [ARITH_ss] [shiftt_def, MAP_MAP]);

val lem2 = Q.prove (
`(!t m n. idxsubn (num_tv E + n + m) (MAP (shiftt 0 (num_tv E + n + m)) t_list) (shiftt n m t) =
          shiftt n m (idxsubn (num_tv E + n) (MAP (shiftt 0 (num_tv E + n)) t_list) t)) /\
 (!tl m n. MAP (\t. idxsubn (num_tv E + n + m) (MAP (shiftt 0 (num_tv E + n + m)) t_list) (shiftt n m t)) tl = 
           MAP (\t. shiftt n m (idxsubn (num_tv E + n) (MAP (shiftt 0 (num_tv E + n)) t_list) t)) tl)`,
Induct THEN SRW_TAC [ARITH_ss] [idxsubn_def, shiftt_def, EL_MAP, MAP_MAP] THEN
FULL_SIMP_TAC list_ss [lem1]);

val lem3 = Q.prove (
`!ts m n. idxsubnts (num_tv E + n + m) (MAP (shiftt 0 (num_tv E + n + m)) t_list) (shiftts n m ts) =
 shiftts n m (idxsubnts (num_tv E + n) (MAP (shiftt 0 (num_tv E + n)) t_list) ts)`,
Cases_on `ts` THEN SRW_TAC [] [idxsubnts_def, shiftts_def, MAP_MAP_o, GSYM shiftt_add_thm] THEN
SRW_TAC [ARITH_ss] [(SIMP_RULE list_ss [] o Q.SPECL [`t`, `m`, `n+1`] o hd o CONJUNCTS) lem2]);

val lem4 = Q.prove (
`!tes m n. idxsubntes (num_tv E + n + m) (MAP (shiftt 0 (num_tv E + n + m)) t_list) (shifttes n m tes) =
 shifttes n m (idxsubntes (num_tv E + n) (MAP (shiftt 0 (num_tv E + n)) t_list) tes)`,
Cases_on `tes` THEN SRW_TAC [] [idxsubntes_def, shifttes_def, MAP_MAP, lem2]);

val lem5 = Q.prove (
`!EB m n. idxsubnEB (num_tv E + n + m) (MAP (shiftt 0 (num_tv E + n + m)) t_list) (shiftEB n m EB) =
 shiftEB n m (idxsubnEB (num_tv E + n) (MAP (shiftt 0 (num_tv E + n)) t_list) EB)`,
Cases_on `EB` THEN SRW_TAC [] [idxsubnEB_def, shiftEB_def, lem2, lem3, lem4]);

in

val type_subst_lookup_thm = Q.prove (
`!E1 E2 name EB. (lookup (E1 ++ [EB_tv] ++ E2) name = SOME EB) /\ ~(name = name_tv) ==>
                 (lookup (idxsubnE 0 t_list E1 ++ E2) name = 
                      SOME (idxsubnEB (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) EB))`,
Induct THEN SRW_TAC [] [lookup_def, num_tv_def, idxsubnE_def, domEB_def, idxsubnEB_def] THEN
FULL_SIMP_TAC list_ss [idxsubnEB_dom_thm, sub_shiftEB_thm, shiftEB_add_thm] THENL
[Cases_on `EB` THEN FULL_SIMP_TAC list_ss [domEB_def, name_distinct, num_tv_def],
 Cases_on `h` THEN FULL_SIMP_TAC list_ss [domEB_def, name_distinct, num_tv_def] THEN
       RES_TAC THEN Q.EXISTS_TAC `idxsubnEB (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) EB2` THEN
       SRW_TAC [] [],
 Cases_on `h` THEN FULL_SIMP_TAC list_ss [domEB_def, name_distinct, num_tv_def]] THEN
       SRW_TAC [] [(SIMP_RULE list_ss [] o Q.SPECL [`EB2`, `1`, `0`]) lem5]);

end;

val ftv_lem1 = Q.store_thm ("ftv_lem1",
`(!t E. tkind E t ==> (ftv_typexpr t = [])) /\
 (!tl E. EVERY (tkind E) tl ==> EVERY (\t. ftv_typexpr t = []) tl)`,
Induct THEN SRW_TAC [] [Eok_def, ftv_typexpr_def, FLAT_EQ_EMPTY, EVERY_MAP] THEN
METIS_TAC []);

val ftv_lem2 = Q.prove (
`(!t m n. (ftv_typexpr t = []) ==> (ftv_typexpr (shiftt m n t) = [])) /\
 (!tl m n. EVERY (\t. ftv_typexpr t = []) tl ==> EVERY (\t. ftv_typexpr (shiftt m n t) = []) tl)`,
Induct THEN SRW_TAC [] [ftv_typexpr_def, shiftt_def, FLAT_EQ_EMPTY, EVERY_MAP]);

val idxbound_lem1 = Q.prove (
`!E1 E2 idx. idx < num_tv E1 /\ idx_bound (E1++[EB_tv]++E2) idx ==>
             idx_bound (idxsubnE 0 t_list E1 ++ E2) idx`,
Induct THEN SRW_TAC [] [num_tv_def, idx_bound_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC list_ss [num_tv_def, idx_bound_def, idxsubnE_def, idxsubnEB_def] THEN
Cases_on `idx` THEN FULL_SIMP_TAC list_ss [idx_bound_def]);

val idxbound_lem2 = Q.prove (
`!E1 E2 idx. ~(idx < num_tv E1) /\ ~(idx = num_tv E1) /\ idx_bound (E1++[EB_tv]++E2) idx ==> 
             idx_bound (idxsubnE 0 t_list E1 ++ E2) (idx - 1)`,
Induct THEN SRW_TAC [] [num_tv_def, idx_bound_def, idxsubnE_def] THEN1
(Cases_on `idx` THEN FULL_SIMP_TAC list_ss [idx_bound_def]) THEN
Cases_on `h` THEN FULL_SIMP_TAC list_ss [num_tv_def, idx_bound_def, idxsubnE_def, idxsubnEB_def] THEN
Cases_on `idx` THEN FULL_SIMP_TAC list_ss [idx_bound_def] THEN Cases_on `n` THEN 
SRW_TAC [] [idx_bound_def] THEN RES_TAC THEN FULL_SIMP_TAC list_ss []);

val type_subst_ok_thm = Q.store_thm ("type_subst_ok_thm",
`(!E1 E2 t_list. Eok (E1++[EB_tv]++E2) /\ EVERY (tkind E2) t_list ==> Eok (idxsubnE 0 t_list E1 ++ E2)) /\
 (!E1 tcn E2 k t_list. (typeconstr_kind (E1++[EB_tv]++E2) tcn = SOME k) /\ EVERY (tkind E2) t_list ==>
                       (typeconstr_kind (idxsubnE 0 t_list E1++E2) tcn = SOME k)) /\
 (!E1 ts E2 t_list. tsok (E1++[EB_tv]++E2) ts /\ EVERY (tkind E2) t_list ==> 
                    tsok (idxsubnE 0 t_list E1++E2) 
                         (idxsubnts (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) ts)) /\
 (!E1 tpo t E2 t_list. ntsok (E1++[EB_tv]++E2) tpo t /\ EVERY (tkind E2) t_list ==> 
                       ntsok (idxsubnE 0 t_list E1++E2) tpo
                             (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) /\
 (!E1 t E2 t_list. tkind (E1++[EB_tv]++E2) t /\ EVERY (tkind E2) t_list ==>
                   tkind (idxsubnE 0 t_list E1++E2)
                         (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t))`,
HO_MATCH_MP_TAC Eok_ind THEN 
SRW_TAC [] [Eok_def, idxsubnE_def, idxsubnEB_def, idxsubnE_dom_thm, idxsubntes_def, EVERY_MAP,
            COND_EXPAND_EQ, domEB_def, idxsubn_def] THEN
IMP_RES_TAC type_subst_lookup_thm THEN SRW_TAC [] [idxsubnts_def, idxsubnEB_def, Eok_def, COND_EXPAND_EQ] THEN
FULL_SIMP_TAC list_ss [EVERY_MEM]  THEN SRW_TAC [] [idxbound_lem1, idxbound_lem2, EL_MAP, MAP_MAP]
THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 Cases_on `lookup (E1++[EB_tv]++E2) (name_tcn typeconstr_name)` THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on `x` THEN FULL_SIMP_TAC list_ss [environment_binding_case_def] THEN
         IMP_RES_TAC type_subst_lookup_thm THEN SRW_TAC [] [idxsubnEB_def],
 RES_TAC THEN FULL_SIMP_TAC list_ss [num_tv_def, GSYM shiftt_add_thm] THEN METIS_TAC [],
 RES_TAC THEN 
         `EVERY (\t. ftv_typexpr t = []) (MAP (shiftt 0 (num_tv E1)) t_list)` by 
                      (SRW_TAC [] [EVERY_MAP] THEN METIS_TAC [ftv_lem1, ftv_lem2, EVERY_MEM])
         THEN IMP_RES_TAC idxsubn_subst_com_lem THEN FULL_SIMP_TAC list_ss [MAP_MAP, idxsubn_def],
 FULL_SIMP_TAC list_ss [MEM_EL] THEN RES_TAC THEN FULL_SIMP_TAC list_ss [] THEN
        METIS_TAC [tkind_weak_thm, idxsubnE_num_tv_thm]]);
 

val type_subst_teq_thm = Q.prove (
`!E t1 t2. JTeq E t1 t2 ==> (E = E1++[EB_tv]++E2) /\ EVERY (tkind E2) t_list ==>
           JTeq (idxsubnE 0 t_list E1 ++ E2)
                (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t1)
                (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t2)`,
RULE_INDUCT_TAC JTeq_ind [idxsubn_def]
[([``"JTeq_refl"``], METIS_TAC [type_subst_ok_thm, JTeq_rules]),
 ([``"JTeq_sym"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_trans"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_arrow"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_tuple"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 3 DISJ2_TAC THEN
      Q.EXISTS_TAC `MAP (\(x,y). (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) x,
                                  idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) y))
                        t_t'_list` THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP]),
 ([``"JTeq_constr"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Once JTeq_cases] THEN NTAC 4 DISJ2_TAC THEN
      Q.EXISTS_TAC `MAP (\(x,y). (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) x,
                                  idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) y))
                        t_t'_list` THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP, type_subst_ok_thm]),
 ([``"JTeq_expand"``],
  SRW_TAC [] [] THEN SRW_TAC [] [Once JTeq_cases, MAP_MAP]  THEN NTAC 3 DISJ2_TAC THEN DISJ1_TAC THEN
     IMP_RES_TAC type_subst_lookup_thm THEN FULL_SIMP_TAC (srw_ss()) [idxsubnEB_def] THEN
     Q.EXISTS_TAC `MAP (\(x,y). (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) x, y)) 
                       t_typevar_list` THEN
     SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP] THENL
     [`EVERY (\t. ftv_typexpr t = []) (MAP (shiftt 0 (num_tv E1)) t_list)` by 
                      (SRW_TAC [] [EVERY_MAP] THEN METIS_TAC [ftv_lem1, ftv_lem2, EVERY_MEM])
         THEN IMP_RES_TAC idxsubn_subst_com_lem THEN FULL_SIMP_TAC list_ss [MAP_MAP, idxsubn_def],
      METIS_TAC [type_subst_ok_thm],
      POP_ASSUM (K ALL_TAC) THEN Q.PAT_ASSUM `lookup x y = z` (K ALL_TAC) THEN
         Induct_on `t_typevar_list` THEN SRW_TAC [] [] THEN METIS_TAC [type_subst_ok_thm]])]);


local

val lem1 = Q.prove (
`(!t' t_list t_list' n. idxsubn n (MAP (shiftt 0 n) t_list) (idxsub t_list' t') =
                        idxsub (MAP (\t. idxsubn n (MAP (shiftt 0 n) t_list) t) t_list')
                               (idxsubn (n + 1) (MAP (shiftt 0 (1 + n)) t_list) t')) /\
 (!tl t_list t_list' n. MAP (\t'. idxsubn n (MAP (shiftt 0 n) t_list) (idxsub t_list' t')) tl =
                        MAP (\t'. idxsub (MAP (\t. idxsubn n (MAP (shiftt 0 n) t_list) t) t_list')
                                  (idxsubn (n + 1) (MAP (shiftt 0 (1 + n)) t_list) t')) tl)`,
Induct THEN 
SRW_TAC [] [idxsubn_def, idxsub_def, MAP_MAP, EL_MAP, GSYM ADD1, COND_EXPAND_EQ] THEN1
METIS_TAC [idxsubn0_thm, sub_shiftt_thm, shiftt_add_thm] THEN
Cases_on `n` THEN FULL_SIMP_TAC list_ss [idxsub_def, idxsubn_def, COND_EXPAND_EQ] THEN
SRW_TAC [] [idxsubn_def, EL_MAP] THEN Cases_on `n''` THEN FULL_SIMP_TAC list_ss [idxsub_def]);

in

val type_subst_inst_thm = Q.prove (
`!E1 E2 t ts t_list. JTinst (E1++[EB_tv]++E2) t ts /\ EVERY (tkind E2) t_list ==>
                     JTinst (idxsubnE 0 t_list E1 ++ E2)
                            (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)
                            (idxsubnts (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) ts)`,
SRW_TAC [] [JTinst_cases, Eok_def] THEN SRW_TAC [] [idxsubnts_def, MAP_MAP_o, GSYM shiftt_add_thm] THEN
Q.EXISTS_TAC `MAP (\t. idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t) t_list'` THEN
SRW_TAC [] [MAP_MAP, EVERY_MAP] THENL
[FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC type_subst_ok_thm THEN
        FULL_SIMP_TAC list_ss [idxsubnE_def, num_tv_def, idxsubnEB_def],
 FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [EVERY_MEM, type_subst_ok_thm],
 METIS_TAC [lem1]]);

end;

val type_subst_inst_named_thm = Q.prove (
`!E1 E2 t tpo t' t_list. 
    JTinst_named (E1++[EB_tv]++E2) t tpo t' /\ EVERY (tkind E2) t_list ==>
    JTinst_named (idxsubnE 0 t_list E1 ++ E2) (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)
                 tpo (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t')`,
SRW_TAC [] [JTinst_named_cases] THEN
Q.EXISTS_TAC `MAP (\(tv, t). (tv, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) typevar_t_list`
THEN
SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP, type_subst_ok_thm] THENL
[IMP_RES_TAC ftv_lem1 THEN IMP_RES_TAC ftv_lem2 THEN
        SRW_TAC [] [idxsubn_subst_com_lem, EVERY_MAP, shiftTsig_def, LAMBDA_PROD2,
        MAP_MAP, sub_shiftt_thm2, MAP_I, src_t_idxsubn_thm],
  FULL_SIMP_TAC list_ss [EVERY_MEM, type_subst_ok_thm]]);

val type_subst_uprim_thm = Q.prove (
`!E1 E2 up t t_list. JTuprim (E1++[EB_tv]++E2) up t /\ EVERY (tkind E2) t_list ==>
                     JTuprim (idxsubnE 0 t_list E1 ++ E2) up 
                             (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)`,
SRW_TAC [] [JTuprim_cases, idxsubn_def] THEN METIS_TAC [type_subst_ok_thm]);

val type_subst_bprim_thm = Q.prove (
`!E1 E2 bp t t_list. JTbprim (E1++[EB_tv]++E2) bp t /\ EVERY (tkind E2) t_list ==>
                     JTbprim (idxsubnE 0 t_list E1 ++ E2) bp 
                             (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)`,
SRW_TAC [] [JTbprim_cases, idxsubn_def] THEN METIS_TAC [type_subst_ok_thm]);

val type_subst_vn_thm = Q.prove (
`!E E2 vn t t_list. JTvalue_name (E1++[EB_tv]++E2) vn t /\ EVERY (tkind E2) t_list ==>
                    JTvalue_name (idxsubnE 0 t_list E1 ++ E2) vn 
                                 (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)`,
SRW_TAC [] [JTvalue_name_cases] THEN IMP_RES_TAC type_subst_lookup_thm THEN 
FULL_SIMP_TAC list_ss [name_distinct, idxsubnEB_def] THEN SRW_TAC [] [type_subst_inst_thm]);

val type_subst_constr_c_thm = Q.prove (
`!E1 E2 c t t_list. JTconstr_c (E1++[EB_tv]++E2) c t /\ EVERY (tkind E2) t_list ==>
                    JTconstr_c (idxsubnE 0 t_list E1 ++ E2) c 
                               (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)`,
SRW_TAC [] [JTconstr_c_cases, idxsubn_def, EVERY_MAP] THEN 
IMP_RES_TAC type_subst_lookup_thm THEN SRW_TAC [] [type_subst_ok_thm, idxsubnEB_def] THEN
FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [EVERY_MEM, type_subst_ok_thm]);

val type_subst_const_thm = Q.prove (
`!E1 E2 c t t_list. JTconst (E1++[EB_tv]++E2) c t /\ EVERY (tkind E2) t_list ==>
                    JTconst (idxsubnE 0 t_list E1 ++ E2) c 
                            (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)`,
SRW_TAC [] [JTconst_cases, idxsubn_def] THEN METIS_TAC [type_subst_ok_thm, type_subst_constr_c_thm]);

val type_subst_constr_p_thm = Q.prove (
`!E1 E2 c tl t t_list. JTconstr_p (E1++[EB_tv]++E2) c tl t /\ EVERY (tkind E2) t_list ==>
                       JTconstr_p (idxsubnE 0 t_list E1 ++ E2) c 
                       (MAP (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list)) tl)
                       (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)`,
SRW_TAC [] [JTconstr_p_cases, idxsubn_def, type_subst_ok_thm, MAP_MAP] THEN
MAP_EVERY Q.EXISTS_TAC [`MAP (\(t, t'). (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t,
                                         idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t'))
                             t'_t_list`, 
                        `MAP (\(t, tv). (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t, tv))
                             t''_tv_list`]
THEN
IMP_RES_TAC type_subst_lookup_thm THEN FULL_SIMP_TAC list_ss [] THEN 
SRW_TAC [] [idxsubnEB_def, idxsubntes_def, MAP_MAP, LAMBDA_PROD2] THEN
IMP_RES_TAC type_subst_inst_named_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP, idxsubn_def]);

val type_subst_field_thm = Q.prove (
`!E1 E2 fn t t' t_list. JTfield (E1++[EB_tv]++E2) fn t t' /\ EVERY (tkind E2) t_list ==>
                        JTfield (idxsubnE 0 t_list E1 ++ E2) fn
                                (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)
                                (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t')`,
SRW_TAC [] [JTfield_cases] THEN
Q.EXISTS_TAC `MAP (\(t, tv). (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t, tv))
                             t'_tv_list`
THEN SRW_TAC [] [idxsubn_def, MAP_MAP, LAMBDA_PROD2] THEN
Q.EXISTS_TAC `idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t''` THEN
IMP_RES_TAC type_subst_lookup_thm THEN FULL_SIMP_TAC list_ss [] THEN
SRW_TAC [] [idxsubnEB_def, idxsubntes_def, MAP_MAP, LAMBDA_PROD2] THEN
IMP_RES_TAC type_subst_inst_named_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP, idxsubn_def]);

val inst_any_refl_thm = Q.store_thm ("inst_any_refl_thm",
`(!t E. tkind E t ==> JTinst_any E t t) /\
 (!tl E. EVERY (\t. tkind E t) tl ==> EVERY (\t. JTinst_any E t t) tl)`,
Induct THEN SRW_TAC [] [JTinst_any_fun, Eok_def] THEN 
Q.EXISTS_TAC `ZIP (tl, tl)` THEN SRW_TAC [] [MAP_FST_ZIP, MAP_SND_ZIP, EVERY_ZIP_SAME, LENGTH_ZIP]);

val type_subst_inst_any_thm = Q.prove (
`!E' t t'. JTinst_any E' t t' ==>
                 !E1 E2 t_list. (E' = E1++[EB_tv]++E2) /\ EVERY (tkind E2) t_list ==>
                 JTinst_any (idxsubnE 0 t_list E1++E2) 
                       (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)
                       (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t')`,
RULE_INDUCT_TAC JTinst_any_ind [JTinst_any_fun, idxsubn_def] 
[([``"JTinst_any_tyvar"``],
  SRW_TAC [] [] THEN SRW_TAC [] [JTinst_any_fun] THENL 
  [MATCH_MP_TAC (hd (CONJUNCTS inst_any_refl_thm)) THEN 
       `MEM (EL num t_list) t_list` by METIS_TAC [MEM_EL] THEN
       `Eok (E1 ++ [EB_tv] ++ E2)` by METIS_TAC [ok_ok_thm] THEN
       IMP_RES_TAC type_subst_ok_thm THEN
       FULL_SIMP_TAC list_ss [EVERY_MEM, idxsubn_def] THEN METIS_TAC [],
   FULL_SIMP_TAC list_ss [Eok_def] THEN METIS_TAC [idxbound_lem1, type_subst_ok_thm],
   FULL_SIMP_TAC list_ss [Eok_def] THEN METIS_TAC [idxbound_lem1, type_subst_ok_thm],
   FULL_SIMP_TAC list_ss [Eok_def] THEN METIS_TAC [idxbound_lem2, type_subst_ok_thm]]),
 ([``"JTinst_any_any"``], METIS_TAC [type_subst_ok_thm]),
 ([``"JTinst_any_tuple"``, ``"JTinst_any_ctor"``],
  SRW_TAC [] [EVERY_MEM, MAP_MAP] THEN 
      Q.EXISTS_TAC `MAP (\x. (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) (FST x),
                              idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) (SND x))) 
                        t_t'_list` THEN
      SRW_TAC [] [MAP_MAP] THEN FULL_SIMP_TAC list_ss [MEM_MAP] THEN
      METIS_TAC [type_subst_ok_thm, EVERY_MEM])]);

local

val lem1 = Q.prove (
`!E' E1 E2 E1'. (E'++(E1++[EB_tv]++E2) = E1'++[EB_tv]++E2) = (E1' = E'++E1)`,
METIS_TAC [APPEND_ASSOC, APPEND_11]);

val lem2 = Q.prove (
`!l f g. num_tv (MAP (\z. EB_vn (f z) (g z)) l) = 0`,
METIS_TAC [MAP_REVERSE, value_env_num_tv_thm, value_env_map_thm]);

val lem3 = Q.prove (
`!S S' n. (shiftTsig n 1 S = shiftTsig n 1 S') = (S = S')`,
Induct THEN FULL_SIMP_TAC list_ss [shiftTsig_def, LAMBDA_PROD2] THEN1 METIS_TAC [] THEN
Cases_on `S''` THEN SRW_TAC [] [] THEN EQ_TAC THEN SRW_TAC [] [] THEN
Cases_on `h` THEN Cases_on `h'` THEN FULL_SIMP_TAC list_ss [shiftt_11]);

val lem4 = Q.prove (
`!l n tl f g. idxsubnE n tl (MAP (\z. EB_vn (f z) (g z)) l) = 
              MAP (\z. EB_vn (f z) (idxsubnts n (MAP (shiftt 0 n) tl) (g z))) l`,
Induct THEN SRW_TAC [] [idxsubnE_def, idxsubnEB_def, lem2]);

val lem5 = SIMP_RULE list_ss [EVERY_MAP] (Q.prove (
`!l f. EVERY value_env (MAP f l) = value_env (FLAT (MAP f l))`,
METIS_TAC [value_env_def, value_env_append_thm, EVERY_FLAT]));

val lem6 = Q.prove (
`!l f n t_list. EVERY (\x. value_env (f x)) l ==>
                (idxsubnE n t_list (FLAT (MAP f l)) = FLAT (MAP (\x. idxsubnE n t_list (f x)) l))`,
Induct THEN SRW_TAC [] [idxsubnE_append_thm, idxsubnE_def] THEN 
FULL_SIMP_TAC list_ss [lem5, value_env_num_tv_thm]);

val lem7 = Q.prove (
`!E' E1 E2 E1'. (EB_tv::(E1++[EB_tv]++E2) = E1'++[EB_tv]++E2) = (E1' = EB_tv::E1)`,
METIS_TAC [APPEND_ASSOC, APPEND_11, APPEND]);

val lem8 = Q.prove (
`!S S' n. (shiftTsig 0 1 (shiftTsig n 1 S) = shiftTsig (n + 1) 1 S') = (S' = shiftTsig 0 1 S)`,
Induct THEN FULL_SIMP_TAC list_ss [shiftTsig_def, LAMBDA_PROD2] THEN
Cases_on `S''` THEN SRW_TAC [] [] THEN EQ_TAC THEN SRW_TAC [] [] THENL
[Cases_on `h` THEN Cases_on `h'` THEN
       FULL_SIMP_TAC list_ss [shiftt_11, 
                              (GSYM o SIMP_RULE list_ss [] o Q.SPECL [`r'`, `n`, `0`, `1`] o hd o CONJUNCTS)
                              shiftt_com_lem],
 METIS_TAC[shiftt_com_lem, ADD, ADD_0]]);

val lem9 = Q.prove (
`!E n t_list. value_env E ==> 
              (idxsubnE n t_list E = MAP (\EB. idxsubnEB n (MAP (shiftt 0 n) t_list) EB) E)`,
Induct_on `E` THEN SRW_TAC [] [value_env_def, idxsubnE_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [value_env_def, idxsubnE_def]  THEN IMP_RES_TAC value_env_num_tv_thm 
THEN FULL_SIMP_TAC (srw_ss()) []);


in

val type_subst_pat_thm = Q.prove (
`!S' E' p t E''. JTpat S' E' p t E'' ==>
                 !S E1 t_list. (S' = shiftTsig (num_tv E1) 1 S) /\ (E' = E1++[EB_tv]++E2) /\
                               EVERY (tkind E2) t_list ==>
                 JTpat S (idxsubnE 0 t_list E1++E2) p 
                       (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)
                       (idxsubnE (num_tv E1) t_list E'')`,
RULE_INDUCT_TAC JTpat_sind [JTpat_fun]
[([``"JTpat_var"``],
  SRW_TAC [ARITH_ss] [idxsubnE_def, idxsubnEB_def, idxsubnts_def, num_tv_def, MAP_MAP, 
                      shift_idxsubn_com_thm] THEN
       METIS_TAC [type_subst_ok_thm]),
 ([``"JTpat_any"``, ``"JTpat_constant"``, ``"JTpat_construct_any"``],
  SRW_TAC [] [idxsubnE_def] THEN METIS_TAC [type_subst_const_thm, type_subst_ok_thm, type_subst_constr_p_thm]),
 ([``"JTpat_alias"``],
  SRW_TAC [ARITH_ss] [idxsubnE_def, idxsubnEB_def, idxsubnts_def, num_tv_def, MAP_MAP, 
                      shift_idxsubn_com_thm, GSYM shiftt_add_thm, domEB_def, idxsubnE_dom_thm] THEN
      IMP_RES_TAC pat_env_lem THEN SRW_TAC [] [value_env_num_tv_thm]),
 ([``"JTpat_typed"``],
  SRW_TAC [] [] THEN
       `idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list)
                (substs_typevar_typexpr (shiftTsig (num_tv E1) 1 S) src_t) =
        substs_typevar_typexpr S src_t` by
                      (IMP_RES_TAC ftv_lem1 THEN IMP_RES_TAC ftv_lem2 THEN
                                 SRW_TAC [] [idxsubn_subst_com_lem, EVERY_MAP, shiftTsig_def, LAMBDA_PROD2,
                                             MAP_MAP, sub_shiftt_thm2, MAP_I, src_t_idxsubn_thm]) THEN
       METIS_TAC [type_subst_inst_any_thm, type_subst_teq_thm]),
 ([``"JTpat_construct"``],
  SRW_TAC [] [] THEN 
      Q.EXISTS_TAC `MAP (\(p, E, t). (p, idxsubnE (num_tv E1) t_list E,
                                     idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t))
                        pattern_E_t_list` THEN
      FULL_SIMP_TAC list_ss [LAMBDA_PROD2, ELIM_UNCURRY, EVERY_MAP, MAP_REVERSE, REVERSE_FLAT, MAP_FLAT, 
                             MAP_MAP, ETA_THM, idxsubnE_dom_thm]  THEN
      SRW_TAC [] [] THENL
      [FULL_SIMP_TAC list_ss [GSYM MAP_REVERSE] THEN HO_MATCH_MP_TAC lem6 THEN
           FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [pat_env_lem],
       IMP_RES_TAC type_subst_constr_p_thm THEN FULL_SIMP_TAC list_ss [MAP_MAP],
       FULL_SIMP_TAC list_ss [EVERY_MEM]]),
 ([``"JTpat_tuple"``],
  SRW_TAC [] [] THEN
      Q.EXISTS_TAC `MAP (\(p, t, E). (p, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t,
                                      idxsubnE (num_tv E1) t_list E))
                        pattern_t_E_list` THEN
      FULL_SIMP_TAC list_ss [LAMBDA_PROD2, ELIM_UNCURRY, EVERY_MAP, MAP_REVERSE, REVERSE_FLAT, MAP_FLAT,
                             MAP_MAP, ETA_THM, idxsubnE_dom_thm, idxsubn_def]  THEN
      SRW_TAC [] [] THENL
      [FULL_SIMP_TAC list_ss [GSYM MAP_REVERSE] THEN HO_MATCH_MP_TAC lem6 THEN
           FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [pat_env_lem],
       FULL_SIMP_TAC list_ss [EVERY_MEM]]),
 ([``"JTpat_record"``],
  SRW_TAC [] [] THEN
      Q.EXISTS_TAC `MAP (\(fn, p, E, t). (fn, p, idxsubnE (num_tv E1) t_list E,
                                          idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t))
                        field_name_pattern_E_t_list` THEN
      FULL_SIMP_TAC list_ss [LAMBDA_PROD2, ELIM_UNCURRY, EVERY_MAP, MAP_REVERSE, REVERSE_FLAT, MAP_FLAT,
                             MAP_MAP, ETA_THM, idxsubnE_dom_thm]  THEN
      SRW_TAC [] [] THENL
      [FULL_SIMP_TAC list_ss [GSYM MAP_REVERSE] THEN HO_MATCH_MP_TAC lem6 THEN
           FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [pat_env_lem],
       FULL_SIMP_TAC list_ss [EVERY_MEM],
       FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN RES_TAC THEN
           IMP_RES_TAC type_subst_field_thm THEN FULL_SIMP_TAC list_ss [EVERY_MEM, MAP_MAP]]),
 ([``"JTpat_cons"``],
  SRW_TAC [] [idxsubnE_append_thm, idxsubn_def] THEN IMP_RES_TAC pat_env_lem THEN 
      SRW_TAC [] [value_env_num_tv_thm] THEN METIS_TAC [idxsubnE_dom_thm]),
 ([``"JTpat_or"``],
  SRW_TAC [] [] THEN IMP_RES_TAC pat_env_lem THEN FULL_SIMP_TAC (srw_ss()) [lem9] THEN 
      METIS_TAC [PERM_MAP])]);

val type_subst_lem = Q.prove (
`(!S' E' e t. JTe S' E' e t ==>
              !S E1 t_list. (S' = shiftTsig (num_tv E1) 1 S) /\ (E' = E1++[EB_tv]++E2) /\
                               EVERY (tkind E2) t_list ==> 
              JTe S (idxsubnE 0 t_list E1++E2) e (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) /\
 (!S' E' pm t1 t2. JTpat_matching S' E' pm t1 t2 ==>
              !S E1 t_list. (S' = shiftTsig (num_tv E1) 1 S) /\ (E' = E1++[EB_tv]++E2) /\
                               EVERY (tkind E2) t_list ==>
              JTpat_matching S (idxsubnE 0 t_list E1++E2) pm 
                               (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t1)
                               (idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t2)) /\
 (!S' E' lb E''. JTlet_binding S' E' lb E'' ==>
              !S E1 t_list. (S' = shiftTsig (num_tv E1) 1 S) /\ (E' = E1++[EB_tv]++E2) /\
                               EVERY (tkind E2) t_list ==>
              JTlet_binding S (idxsubnE 0 t_list E1++E2) lb (idxsubnE (num_tv E1) t_list E'')) /\
 (!S' E' lrbs E''. JTletrec_binding S' E' lrbs E'' ==>
              !S E1 t_list. (S' = shiftTsig (num_tv E1) 1 S) /\ (E' = E1++[EB_tv]++E2) /\
                               EVERY (tkind E2) t_list ==>
              JTletrec_binding S (idxsubnE 0 t_list E1++E2) lrbs (idxsubnE (num_tv E1) t_list E''))`,
RULE_INDUCT_TAC JTe_ind [JTe_fun]
[([``"JTe_cons"``, ``"JTe_apply"``, ``"JTe_and"``, ``"JTe_or"``, ``"JTe_ifthenelse"``, ``"JTe_while"``,
   ``"JTe_sequence"``, ``"JTe_match"``, ``"JTe_function"``, ``"JTe_try"``, ``"JTe_assert"``],
  SRW_TAC [] [idxsubn_def] THEN IMP_RES_TAC type_subst_teq_thm THEN 
          FULL_SIMP_TAC (srw_ss()) [idxsubn_def] THEN
          METIS_TAC [type_subst_ok_thm]),
 ([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_ident"``, ``"JTe_constant"``],
  METIS_TAC [type_subst_uprim_thm, type_subst_bprim_thm, type_subst_vn_thm, type_subst_const_thm,
             type_subst_teq_thm]), 
 ([``"JTe_typed"``], 
  SRW_TAC [] [] THEN
       `idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list)
                (substs_typevar_typexpr (shiftTsig (num_tv E1) 1 S) src_t) = 
        substs_typevar_typexpr S src_t` by 
                      (IMP_RES_TAC ftv_lem1 THEN IMP_RES_TAC ftv_lem2 THEN 
                                 SRW_TAC [] [idxsubn_subst_com_lem, EVERY_MAP, shiftTsig_def, LAMBDA_PROD2, 
                                             MAP_MAP, sub_shiftt_thm2, MAP_I, src_t_idxsubn_thm]) THEN
       METIS_TAC [type_subst_inst_any_thm, type_subst_teq_thm]),
 ([``"JTe_tuple"``],
  SRW_TAC [] [idxsubn_def, MAP_MAP] THEN
      Q.EXISTS_TAC `MAP (\(e, t). (e, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) e_t_list` THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, ETA_THM, EVERY_MAP] THEN
      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN IMP_RES_TAC type_subst_teq_thm THEN 
      FULL_SIMP_TAC (srw_ss()) [idxsubn_def, MAP_MAP, EVERY_MEM]),
 ([``"JTe_construct"``],
  SRW_TAC [] [idxsubn_def, MAP_MAP] THEN
      Q.EXISTS_TAC `MAP (\(e, t). (e, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) 
                        e_t_list` THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, ETA_THM, EVERY_MAP] THEN
      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN IMP_RES_TAC type_subst_constr_p_thm THEN
      IMP_RES_TAC type_subst_teq_thm THEN
      FULL_SIMP_TAC list_ss [EVERY_MEM, MAP_MAP] THEN METIS_TAC []),
 ([``"JTe_record_constr"``],
  SRW_TAC [] [idxsubn_def, MAP_MAP] THEN 
      MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, 
                              `MAP (\a.  idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) a) t'_list`,
                       `MAP (\(fn, e, t). (fn, e, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) 
                             field_name_e_t_list`, `typeconstr_name`, `kind`] THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP, ETA_THM] THEN
      IMP_RES_TAC type_subst_lookup_thm THEN IMP_RES_TAC type_subst_teq_thm THEN 
      SRW_TAC [] [idxsubnEB_def] THEN
      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [GSYM idxsubn_def] THEN 
      MATCH_MP_TAC type_subst_field_thm THEN METIS_TAC [EVERY_MEM]),
 ([``"JTe_record_with"``],
  SRW_TAC [] [] THEN 
      MAP_EVERY Q.EXISTS_TAC [`MAP (\(fn, e, t). 
                                       (fn, e, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) 
                                   field_name_e_t_list`,
                              `idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t''`] THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP] THEN
      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [GSYM idxsubn_def] THEN
      IMP_RES_TAC type_subst_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [idxsubnEB_def, EVERY_MEM] THEN
      MATCH_MP_TAC type_subst_field_thm THEN METIS_TAC [EVERY_MEM]),
 ([``"JTe_record_proj"``],
  SRW_TAC [] [] THEN METIS_TAC [type_subst_field_thm, type_subst_teq_thm]),
 ([``"JTe_assertfalse"``],
  SRW_TAC [] [idxsubn_def] THEN METIS_TAC [type_subst_ok_thm, type_subst_teq_thm]),
 ([``"JTe_location"``],
  SRW_TAC [] [idxsubn_def] THEN IMP_RES_TAC type_subst_lookup_thm THEN SRW_TAC [] [idxsubnEB_def] THEN1
      METIS_TAC [type_subst_ok_thm] THEN IMP_RES_TAC type_subst_teq_thm THEN 
      FULL_SIMP_TAC (srw_ss ()) [idxsubn_def]),
 ([``"JTe_for"``],
  SRW_TAC [] [idxsubn_def, shiftt_def] THEN FULL_SIMP_TAC list_ss [shiftt_def] THENL
      [Q.PAT_ASSUM `!S' E1' t_list. P S' E1' t_list ==> 
                                JTe S' (idxsubnE 0 t_list E1' ++ E2) e'' (TE_constr [] TC_unit)`
             (MATCH_MP_TAC o 
              SIMP_RULE list_ss [idxsubnE_def, idxsubnEB_def, idxsubnts_def, idxsubn_def] o
              Q.SPECL [`S`, `EB_vn (VN_id lowercase_ident) (TS_forall (TE_constr [] TC_int))::E1`]) THEN
          SRW_TAC [] [num_tv_def],
       IMP_RES_TAC type_subst_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [idxsubn_def]]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN
      Q.EXISTS_TAC `MAP (\(p, e, E). (p, e, idxsubnE (num_tv E1) t_list E)) pattern_e_E_list` THEN
      SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP] THEN 
      FULL_SIMP_TAC list_ss [lem1, EVERY_MEM, num_tv_append_thm] THEN SRW_TAC [] [] THEN RES_TAC THEN
      IMP_RES_TAC pat_env_lem THEN FULL_SIMP_TAC list_ss [value_env_num_tv_thm, lem3] THEN
      IMP_RES_TAC (SIMP_RULE list_ss [EVERY_MEM] type_subst_pat_thm) THEN 
      FULL_SIMP_TAC list_ss [idxsubnE_append_thm] THEN METIS_TAC []),
 ([``"JTlet_binding_poly"``],
  SRW_TAC [] [] THEN 
      MAP_EVERY Q.EXISTS_TAC [`MAP (\(x, t). (x, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t)) 
                                   x_t_list`, 
                              `idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t`] THEN
      FULL_SIMP_TAC list_ss [lem3] THEN 
      SRW_TAC [ARITH_ss] [MAP_MAP, LAMBDA_PROD2, GSYM MAP_REVERSE, lem4, idxsubnts_def, 
                          shift_idxsubn_com_thm] THEN
      IMP_RES_TAC type_subst_pat_thm THEN 
      FULL_SIMP_TAC list_ss [lem1, lem3, GSYM MAP_REVERSE, shift_idxsubn_com_thm, lem4, idxsubnts_def,
                             MAP_MAP, shiftt_add_thm]),
 ([``"JTe_let_mono"``],
  SRW_TAC [] [GSYM LEFT_EXISTS_AND_THM, GSYM MAP_REVERSE] THEN 
      FULL_SIMP_TAC list_ss [lem1, lem2, lem3, lem4, num_tv_append_thm, idxsubnE_append_thm,
                             idxsubnts_def, MAP_MAP, GSYM shiftt_add_thm] THEN 
      RES_TAC THEN DISJ1_TAC THEN 
      MAP_EVERY Q.EXISTS_TAC [`MAP (\(x, t). (x, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t))
                                    x_t_list`, 
                              `x_t_list'`, `t'`] THEN 
      SRW_TAC [ARITH_ss] [GSYM MAP_REVERSE, MAP_MAP, LAMBDA_PROD2, shift_idxsubn_com_thm, 
                          GSYM shiftt_add_thm] THEN
      METIS_TAC []),
 ([``"JTe_let_poly"``],
  SRW_TAC [] [GSYM LEFT_EXISTS_AND_THM, GSYM MAP_REVERSE] THEN
      FULL_SIMP_TAC list_ss [lem1, lem2, lem3, lem4, num_tv_append_thm, idxsubnE_append_thm, num_tv_def,
                             idxsubnts_def, MAP_MAP_o, GSYM shiftt_add_thm, lem7, lem8,
                             idxsubnE_def, idxsubnEB_def] THEN
      RES_TAC THEN DISJ2_TAC THEN
      MAP_EVERY Q.EXISTS_TAC [`MAP (\(x, t). (x, idxsubn (num_tv E1 + 1) (MAP (shiftt 0 (num_tv E1 + 1))
                                                                              t_list) t))
                                    x_t_list`,
                              `x_t_list'`, `t'`] THEN
      SRW_TAC [ARITH_ss] [GSYM MAP_REVERSE, MAP_MAP_o, o_DEF, LAMBDA_PROD2, shift_idxsubn_com_thm,
                          GSYM shiftt_add_thm]),
 ([``"JTe_letrec"``],
   SRW_TAC [] [GSYM MAP_REVERSE] THEN
      FULL_SIMP_TAC list_ss [lem1, lem2, lem3, lem4, num_tv_append_thm, idxsubnE_append_thm, num_tv_def,
                             idxsubnts_def, MAP_MAP_o, o_DEF, GSYM shiftt_add_thm, lem7, lem8,
                             idxsubnE_def, idxsubnEB_def] THEN
      RES_TAC THEN
      Q.EXISTS_TAC `MAP (\(x, t). (x, idxsubn (num_tv E1 + 1) (MAP (shiftt 0 (num_tv E1 + 1)) t_list) t))
                        x_t_list` THEN
      SRW_TAC [ARITH_ss] [GSYM MAP_REVERSE, MAP_MAP_o, o_DEF, LAMBDA_PROD2, shift_idxsubn_com_thm,
                          GSYM shiftt_add_thm]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [] THEN
      FULL_SIMP_TAC list_ss [lem1, lem2, lem3, lem4, GSYM MAP_REVERSE, num_tv_append_thm, 
                             idxsubnE_append_thm] THEN
      Q.EXISTS_TAC `MAP (\(vn, pm, t, t'). (vn, pm, idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t,
                                            idxsubn (num_tv E1) (MAP (shiftt 0 (num_tv E1)) t_list) t'))
                        value_name_pattern_matching_t_t'_list` THEN
      SRW_TAC [ARITH_ss] [LAMBDA_PROD2, MAP_MAP, GSYM MAP_REVERSE, EVERY_MAP, shiftt_def,
                          shift_idxsubn_com_thm, GSYM shiftt_add_thm, idxsubnts_def, idxsubn_def] THEN
      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN RES_TAC THEN
      FULL_SIMP_TAC list_ss [LAMBDA_PROD2, MAP_MAP, GSYM MAP_REVERSE, EVERY_MAP, shiftt_def,
                             shift_idxsubn_com_thm, GSYM shiftt_add_thm, idxsubnts_def, idxsubn_def])]);

end;

val type_subst_thm = save_thm ("type_subst_thm",
(GEN_ALL o 
 SIMP_RULE list_ss [num_tv_def, idxsubnE_def, shiftt_add_thm, AND_IMP_INTRO] o
 Q.SPECL [`e`, `t`, `S`, `[]`, `t_list`] o
 SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM] o hd o CONJUNCTS) type_subst_lem);

val _ = export_theory();

