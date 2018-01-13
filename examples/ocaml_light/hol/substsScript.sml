open HolKernel bossLib boolLib combinTheory listTheory rich_listTheory optionTheory pairTheory sortingTheory;
open wordsTheory markerTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory environmentTheory shiftTheory validTheory strengthenTheory;
open weakenTheory type_substTheory remv_tyvarTheory teqTheory;

val _ = new_theory "substs";

val _ = Parse.hide "S";

val subst_nexp_thm = Q.store_thm ("subst_nexp_thm",
`!nexp v x. is_non_expansive_of_expr nexp /\ is_non_expansive_of_expr v ==>
            is_non_expansive_of_expr (subst_value_name_expr v x nexp)`,
recInduct is_non_expansive_of_expr_ind THEN 
SRW_TAC [] [is_non_expansive_of_expr_def, subst_value_name_letrec_binding_def,
                EVERY_MAP, EVERY_MEM, LAMBDA_PROD2] THENL
[Cases_on `z` THEN METIS_TAC [SND],
 Cases_on `expr1` THEN
        FULL_SIMP_TAC list_ss [is_binary_prim_app_value_of_expr_def, subst_value_name_letrec_binding_def],
 METIS_TAC []]);

val substs_nexp_thm = Q.store_thm ("substs_nexp_thm",
`!nexp subs. is_non_expansive_of_expr nexp /\ EVERY (\x. is_non_expansive_of_expr (SND x)) subs ==>
             is_non_expansive_of_expr (substs_value_name_expr subs nexp)`,
recInduct is_non_expansive_of_expr_ind THEN
SRW_TAC [] [is_non_expansive_of_expr_def, substs_value_name_letrec_binding_def, EVERY_MAP, EVERY_MEM,
                LAMBDA_PROD2] THEN 
FULL_SIMP_TAC list_ss [MEM_FILTER] THENL
[Cases_on `list_assoc value_name subs` THEN SRW_TAC [] [is_non_expansive_of_expr_def] THEN
        METIS_TAC [list_assoc_mem, SND],
 Cases_on `z` THEN METIS_TAC [SND],
 Cases_on `expr1` THEN
        FULL_SIMP_TAC list_ss [is_binary_prim_app_value_of_expr_def, substs_value_name_letrec_binding_def]]);

local

val lem1 = Q.prove (
`!f. (case f of NONE -> NONE || SOME EB -> SOME EB) = f`,
Cases THEN SRW_TAC [] []);

val lem2 = Q.prove (
`!l x_t_list z. ~MEM (FST z) l /\ (MAP name_vn l = MAP (\z. name_vn (FST z)) x_t_list) ==>
                ~MEM z x_t_list`,
Induct THEN SRW_TAC [] [] THEN Cases_on `x_t_list` THEN FULL_SIMP_TAC list_ss [name_11] THEN METIS_TAC []);

val lem3 = Q.prove (
`JTpat (shiftTsig 0 (num_tv E1) S') (E1 ++ [EB_vn x (TS_forall  t'')] ++ E2) p t E /\
 JTe (shiftTsig 0 (num_tv E1) S') (E ++ E1 ++ [EB_vn x (TS_forall t'')] ++ E2) e t' /\
 (  is_non_expansive_of_expr v /\
    (E ++ E1 ++ [EB_vn x (TS_forall t'')] ++ E2 =
     (E++E1) ++ [EB_vn x (TS_forall t'')] ++ E2) /\
    (shiftTsig 0 (num_tv E1) S' = shiftTsig 0 (num_tv (E++E1)) S') /\
    ~MEM (name_vn x) (MAP domEB (E++E1)) /\
    closed_env E2 /\
    JTe (shiftTsig 0 1 S') (EB_tv::E2) v t'' ==>
    JTe (shiftTsig 0 (num_tv (E++E1)) S') ((E++E1) ++ E2) (subst_value_name_expr v x e) t') /\
 is_non_expansive_of_expr v /\
 ~MEM (name_vn x) (MAP domEB E1) /\
 closed_env E2 /\
 JTe (shiftTsig 0 1 S') (EB_tv::E2) v t'' ==>
    JTe (shiftTsig 0 (num_tv E1) S') (E ++ E1 ++ E2)
        (if MEM x (aux_xs_pattern_of_pattern p) then
           e
         else
           subst_value_name_expr v x e)
        t'`,
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN
IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN SRW_TAC [] [] THEN
`num_tv E = 0` by METIS_TAC [pat_env_lem, value_env_num_tv_thm] THEN
FULL_SIMP_TAC list_ss [] THENL
[MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
        Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
        SRW_TAC [] [value_env_def, domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
        METIS_TAC [MEM_MAP, MEM_REVERSE],
 FULL_SIMP_TAC list_ss [num_tv_append_thm] THEN
        Q.PAT_ASSUM `~MEM (name_vn x) (MAP domEB E) ==> JTe 
                   (shiftTsig 0 (num_tv E1) S') (E ++ E1 ++ E2) (subst_value_name_expr v x e) t'`
             MATCH_MP_TAC THEN
        METIS_TAC [MEM_MAP, name_11, MEM_REVERSE]]);

val lem4 = Q.prove (
`MEM x (MAP FST l) /\
 JTpat_matching (shiftTsig 0 (num_tv E1) S')
                (REVERSE (MAP (\z. EB_vn (FST z)
                                         (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z)))
                                                                          (SND (SND (SND z))))))) l) ++ E1 ++ 
                [EB_vn x (TS_forall t'')] ++ E2) pm t t' ==>
JTpat_matching (shiftTsig 0 (num_tv E1) S')
               (REVERSE (MAP (\z. EB_vn (FST z) 
                                         (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z)))
                                                                          (SND (SND (SND z))))))) l) ++ E1 ++ 
                E2) pm t t'`,
Cases_on `pm` THEN SRW_TAC [] [JTe_fun] THEN
Q.EXISTS_TAC `pattern_e_E_list` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THENL
[METIS_TAC [value_env_pat_str_thm, value_env_def],
 SRW_TAC [] [] THEN
        MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
        Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
        SRW_TAC [] [value_env_def, MAP_REVERSE, MAP_MAP, domEB_def] THEN
        Q.PAT_ASSUM `MEM x (MAP FST l)` MP_TAC THEN
        REPEAT (POP_ASSUM (K ALL_TAC)) THEN Induct_on `l` THEN SRW_TAC [] [] THEN METIS_TAC []]);

val lem5 = Q.prove (
`!l f g. num_tv (MAP (\x. EB_vn (f x) (g x)) l) = 0`,
METIS_TAC [value_env_map_thm, value_env_num_tv_thm]);

val lem6 = Q.prove (
`(!t n m. shiftt n m (shiftt 0 n t) = shiftt 0 (n + m) t) /\
 (!tl n m. MAP (\t. shiftt n m (shiftt 0 n t)) tl = MAP (\t. shiftt 0 (n + m) t) tl)`,
Induct THEN SRW_TAC [] [shiftt_def, MAP_MAP] THEN DECIDE_TAC);

val lem7 = Q.prove (
`!S n m. shiftTsig n m (shiftTsig 0 n S) = shiftTsig 0 (n + m) S`,
Induct THEN SRW_TAC [] [shiftTsig_def, LAMBDA_PROD2, MAP_MAP, lem6]);

val lem8 = Q.prove (
`!S e t E E' t_list.
     JTe (shiftTsig 0 1 S) (EB_tv::E) e t /\
     closed_env E /\
     Eok (E'++E) /\
     EVERY (tkind (E'++E)) t_list ==>
     JTe (shiftTsig 0 (num_tv E') S) (E'++E) e (idxsub t_list (shiftt 1 (num_tv E') t))`,
SRW_TAC [] [GSYM idxsubn0_thm] THEN MATCH_MP_TAC type_subst_thm THEN SRW_TAC [] [] THEN
IMP_RES_TAC ((SIMP_RULE list_ss [Eok_def, num_tv_def] o 
              Q.SPECL [`shiftTsig 0 1 S`, `e`, `t`, `E'`, `E`]) weak_thm) THEN
FULL_SIMP_TAC list_ss [shiftTsig_add_thm, lem7]);

in

val subst_lem = Q.store_thm ("subst_lem",
`(!S E e t. JTe S E e t ==>
  !S' E1 E2 x v t'.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t')] ++ E2) /\
     (S = shiftTsig 0 (num_tv E1) S') /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     JTe (shiftTsig 0 1 S') (EB_tv::E2) v t' ==>
     JTe S (E1++E2) (subst_value_name_expr v x e) t) /\
 (!S E pm t t'. JTpat_matching S E pm t t' ==>
    !S' E1 E2 x v t''.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t'')] ++ E2) /\
     (S = shiftTsig 0 (num_tv E1) S') /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     JTe (shiftTsig 0 1 S') (EB_tv::E2) v t'' ==>
     JTpat_matching S (E1++E2) (subst_value_name_pattern_matching v x pm) t t') /\
 (!S E lb E'. JTlet_binding S E lb E' ==> 
    !S' E1 E2 x v t''.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t'')] ++ E2) /\
     (S = shiftTsig 0 (num_tv E1) S') /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     JTe (shiftTsig 0 1 S') (EB_tv::E2) v t'' ==>
     JTlet_binding S (E1++E2) (subst_value_name_let_binding v x lb) E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==> 
    !S' x E1 E2 v t''.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t'')] ++ E2) /\
     (S = shiftTsig 0 (num_tv E1) S') /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     JTe (shiftTsig 0 1 S') (EB_tv::E2) v t'' ==>
     if MEM x (aux_xs_letrec_bindings_of_letrec_bindings lrbs) then
       JTletrec_binding S (E1++E2) lrbs E'
     else
       JTletrec_binding S (E1++E2) (subst_value_name_letrec_bindings v x lrbs) E')`,
RULE_INDUCT_TAC JTe_sind [subst_value_name_letrec_binding_def, JTe_fun]
[([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_constant"``, ``"JTe_typed"``],
  FULL_SIMP_TAC list_ss [JTuprim_cases, JTbprim_cases, JTconst_cases, JTconstr_c_cases] THEN
        SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [lookup_def, domEB_def, name_distinct, EVERY_MEM] THEN
        METIS_TAC [value_env_lookup_str_thm, value_env_ok_str_thm, APPEND, value_env_def, 
                   value_env_inst_any_thm, value_env_teq_str_thm]),
 ([``"JTe_apply"``, ``"JTe_match"``], METIS_TAC []),
 ([``"JTe_ident"``], 
  SRW_TAC [] [] THEN SRW_TAC [] [JTe_fun] THEN
         FULL_SIMP_TAC list_ss [JTvalue_name_cases, lookup_def, domEB_def, name_11, lookup_append_thm,
                                lookup_dom_thm] THEN
         SRW_TAC [] [] THENL
         [FULL_SIMP_TAC list_ss [JTinst_cases, shiftEB_def, shiftts_def] THEN SRW_TAC [] [] THEN
                  `JTe (shiftTsig 0 (num_tv E1) S'') (E1 ++ E2) v (idxsub t_list (shiftt 1 (num_tv E1) t'))`
                            by (MATCH_MP_TAC lem8 THEN SRW_TAC [] [] THENL
                                     [METIS_TAC [value_env_ok_str_thm, value_env_def, ok_ok_thm],
                                      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN 
                                          METIS_TAC [value_env_ok_str_thm, value_env_def]]) THEN
                  METIS_TAC [teq_thm, value_env_def, value_env_teq_str_thm],
          FULL_SIMP_TAC list_ss [lem1] THEN Cases_on `lookup E1 (name_vn value_name)` THEN
                  FULL_SIMP_TAC list_ss [option_case_def] THEN SRW_TAC [] [] THENL
                  [Cases_on `EB` THEN
                          FULL_SIMP_TAC list_ss [environment_binding_distinct, shiftEB_def, num_tv_append_thm,
                                                 num_tv_def] THEN
                          SRW_TAC [] [] THEN
                          METIS_TAC [value_env_inst_str_thm, value_env_ok_str_thm, value_env_def,
                                     value_env_teq_str_thm],
                   METIS_TAC [value_env_inst_str_thm, value_env_ok_str_thm, value_env_def, 
                              value_env_teq_str_thm]]]),
 ([``"JTe_tuple"``, ``"JTe_construct"``],
  SRW_TAC [] [] THEN 
        Q.EXISTS_TAC `MAP (\e_t. (subst_value_name_expr v x (FST e_t), SND e_t)) e_t_list` THEN
        SRW_TAC [] [MAP_MAP, ETA_THM, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [value_env_def, value_env_constr_p_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_cons"``, ``"JTe_and"``, ``"JTe_or"``, ``"JTe_while"``, ``"JTe_function"``],
  METIS_TAC [value_env_teq_str_thm, value_env_def]),
 ([``"JTe_record_constr"``],
  SRW_TAC [] [] THEN
  MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`,
                          `MAP (\fn_e_t. (FST fn_e_t,
                                          subst_value_name_expr v x (FST (SND fn_e_t)), 
                                          SND (SND fn_e_t)))
                               field_name_e_t_list`,
                          `typeconstr_name`,
                          `kind`] THEN
        SRW_TAC [] [MAP_MAP, ETA_THM, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN1
        METIS_TAC [] THEN1
        METIS_TAC [value_env_def, value_env_field_str_thm, APPEND] THEN1
        METIS_TAC [value_env_def, value_env_lookup_str_thm, APPEND] THEN1
        METIS_TAC [value_env_teq_str_thm, value_env_def]),
 ([``"JTe_record_with"``],
  SRW_TAC [] [] THEN 
  Q.EXISTS_TAC `MAP (\fn_e_t. (FST fn_e_t,
                               subst_value_name_expr v x (FST (SND fn_e_t)), 
                               SND (SND fn_e_t)))
                    field_name_e_t_list` THEN
        SRW_TAC [] [MAP_MAP, ETA_THM, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [value_env_def, value_env_field_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_record_proj"``],
  METIS_TAC [value_env_def, value_env_field_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_assert"``, ``"JTe_assertfalse"``],
  FULL_SIMP_TAC list_ss [JTconst_cases] THEN SRW_TAC [] [] THEN 
        METIS_TAC [last (CONJUNCTS value_env_ok_str_thm), value_env_def, APPEND, value_env_teq_str_thm]),
 ([``"JTe_location"``],
  METIS_TAC [value_env_def, value_env_ok_str_thm, value_env_lookup_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_for"``],
  SRW_TAC [] [shiftt_def] THEN SRW_TAC [] [] THENL 
  [MATCH_MP_TAC (SIMP_RULE list_ss [AND_IMP_INTRO]
                (Q.SPECL [`E2`, `[EB_vn (VN_id lowercase_ident) (TS_forall t')]`, 
                          `shiftTsig 0 (num_tv E1) S'`, `e''`, 
                          `TE_constr [] TC_unit`, 
                          `EB_vn (VN_id lowercase_ident) (TS_forall (TE_constr [] TC_int))::E1`]
                         (GEN_ALL (hd (CONJUNCTS value_env_str_thm))))) THEN
           SRW_TAC [] [value_env_def, domEB_def],
   Q.PAT_ASSUM `!S'' E1' E2' x' v t''. P S'' E1' E2' x' v t'' ==>
                       JTe (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') (subst_value_name_expr v x' e'')
                           (TE_constr [] TC_unit)`
               (MATCH_MP_TAC o 
                SIMP_RULE list_ss [num_tv_def] o
                Q.SPECL [`S'`, `EB_vn (VN_id lowercase_ident)
                                (TS_forall (TE_constr [] TC_int)) :: E1`]) THEN
           SRW_TAC [] [domEB_def, DISJOINT_RIGHT, MEM_MAP] THEN METIS_TAC [],
   METIS_TAC [value_env_def, value_env_teq_str_thm]]),
 ([``"JTe_let_mono"``],
  SRW_TAC [] [] THEN 
        FULL_SIMP_TAC list_ss [REVERSE_EQ, EB_vn_list_thm, aux_xs_let_binding_of_let_binding_def] THEN
        IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
        FULL_SIMP_TAC list_ss [REVERSE_REVERSE, domEB_def, MAP_MAP] THEN
        SRW_TAC [] [] THEN DISJ1_TAC THEN Q.EXISTS_TAC `x_t_list` THEN 
        SRW_TAC [] [] THENL
        [MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
                 Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
                 SRW_TAC [] [value_env_def, domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP],
         Q.PAT_ASSUM `!S'' E1' E2' x' v' t'. P S'' E1' E2' x' v' t' ==> 
                      JTe (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') (subst_value_name_expr v' x' e) t` 
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [MAP_REVERSE] o
                      SIMP_RULE list_ss [num_tv_append_thm, lem5, GSYM MAP_REVERSE] o
                      Q.SPECL [`S'`, 
                               `REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list) ++
                                E1`]) 
                 THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP, name_11]]),
 ([``"JTe_let_poly"``],
   SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [REVERSE_EQ, EB_vn_list_thm, aux_xs_let_binding_of_let_binding_def] THEN
        IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
        FULL_SIMP_TAC list_ss [REVERSE_REVERSE, domEB_def, MAP_MAP] THEN
        SRW_TAC [] [] THEN DISJ2_TAC THEN Q.EXISTS_TAC `x_t_list` THEN
        SRW_TAC [ARITH_ss] [shiftTsig_add_thm] THENL
        [METIS_TAC [subst_nexp_thm],
         Q.PAT_ASSUM `!S'' E1' E2' x' v' t'''. P S'' E1' E2' x' v' t''' ==>
                      ?t'. JTpat (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') pat t' E /\ 
                           JTe (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') 
                               (subst_value_name_expr v' x' nexp) t'`
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [num_tv_def] o
                      Q.SPECL [`S'`, `EB_tv::E1`])
                 THEN
                 SRW_TAC [] [MAP_MAP, domEB_def, MAP_REVERSE, MEM_REVERSE] THEN
                 SRW_TAC [ARITH_ss] [MEM_MAP, shiftTsig_add_thm],
         MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
                 Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
                 SRW_TAC [] [value_env_def, domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP],
         METIS_TAC [subst_nexp_thm],
         Q.PAT_ASSUM `!S'' E1' E2' x' v' t'''. P S'' E1' E2' x' v' t''' ==>
                      ?t'. JTpat (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') pat t' E /\
                           JTe (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2')
                               (subst_value_name_expr v' x' nexp) t'`
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [num_tv_def] o
                      Q.SPECL [`S'`, `EB_tv::E1`])
                 THEN
                 SRW_TAC [] [MAP_MAP, domEB_def, MAP_REVERSE, MEM_REVERSE] THEN
                 SRW_TAC [ARITH_ss] [MEM_MAP, shiftTsig_add_thm],
         Q.PAT_ASSUM `!S'' E1' E2' x' v' t'. P S'' E1' E2' x' v' t' ==>
                      JTe (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') (subst_value_name_expr v' x' e) t` 
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [MAP_REVERSE] o
                      SIMP_RULE list_ss [num_tv_def, GSYM MAP_REVERSE, lem5, num_tv_append_thm] o
                      Q.SPECL [`S'`, `REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list) ++E1`])
                 THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP, name_11]]),
 ([``"JTe_letrec"``],
  SRW_TAC [] [] THEN IMP_RES_TAC aux_xs_letrec_bindings_of_letrec_bindings_thm THEN 
        FULL_SIMP_TAC list_ss [REVERSE_REVERSE, MAP_MAP, domEB_def] THEN
        Q.EXISTS_TAC `x_t_list` THEN SRW_TAC [] [] THENL
        [Q.PAT_ASSUM `!S'' x' E1' E2' v' t''. P S'' x' E1' E2' v' t'' ==>
                      (if MEM x' (aux_xs_letrec_bindings_of_letrec_bindings lrbs) then
                         JTletrec_binding (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') lrbs E'
                       else
                         JTletrec_binding (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') 
                                          (subst_value_name_letrec_bindings v' x' lrbs) E'')`
                     (MP_TAC o 
                      Q.SPECL [`S''`, `x`, `EB_tv::E1`]) THEN
                 SRW_TAC [] [num_tv_def, shiftTsig_add_thm] THEN POP_ASSUM MATCH_MP_TAC THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 SRW_TAC [] [MEM_MAP] THEN METIS_TAC [],
         Q.PAT_ASSUM `!S'' x' E1' E2' v' t''. P S'' x' E1' E2' v' t'' ==>
                      (if MEM x' (aux_xs_letrec_bindings_of_letrec_bindings lrbs) then
                         JTletrec_binding (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') lrbs E'
                       else
                         JTletrec_binding (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2')
                                          (subst_value_name_letrec_bindings v' x' lrbs) E'')`
                     (MP_TAC o
                      Q.SPECL [`S''`, `x`, `EB_tv::E1`]) THEN
                 SRW_TAC [] [num_tv_def, shiftTsig_add_thm] THEN POP_ASSUM MATCH_MP_TAC THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 SRW_TAC [] [MEM_MAP] THEN METIS_TAC [],
         MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
                 Q.EXISTS_TAC `[EB_vn x (TS_forall t')]` THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 FULL_SIMP_TAC list_ss [] THEN METIS_TAC [MEM_MAP],
         Q.PAT_ASSUM `!S'' E1' E2' x' v t''. P E1' E2' x' v t'' ==>
                      JTe (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') (subst_value_name_expr v x' e) t` 
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [MAP_REVERSE] o
                      SIMP_RULE list_ss [num_tv_def, GSYM MAP_REVERSE, lem5, num_tv_append_thm] o
                      Q.SPECL [`S'`, `REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list) ++E1`])
                 THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 SRW_TAC [] [MEM_MAP] THEN Cases_on `x = FST z` THEN SRW_TAC [] [] THEN METIS_TAC [lem2]]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN
  Q.EXISTS_TAC `MAP (\z. (FST z,
                         (if MEM x (aux_xs_pattern_of_pattern (FST z)) then
                            FST (SND z)
                          else subst_value_name_expr v x (FST (SND z))),
                         (SND (SND z))))
                   pattern_e_E_list` THEN
        SRW_TAC [] [MAP_MAP, subst_value_name_letrec_binding_def, EVERY_MAP] THEN
        FULL_SIMP_TAC list_ss [EVERY_MEM] THENL
        [METIS_TAC [value_env_pat_str_thm, value_env_def],
         METIS_TAC [lem3]]), 
 ([``"JTlet_binding_poly"``],
  SRW_TAC [] [] THEN  MAP_EVERY Q.EXISTS_TAC [`x_t_list`, `t`] THEN SRW_TAC [] [] THEN1
        METIS_TAC [value_env_pat_str_thm, value_env_def]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [aux_xs_letrec_bindings_of_letrec_bindings_def, MAP_MAP,
              aux_xs_letrec_binding_of_letrec_binding_def, FLAT_MAP_SING] THEN
        SRW_TAC [] [] THENL
        [FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [lem4],
         Q.EXISTS_TAC `MAP (\(a, b, c, d). (a, subst_value_name_pattern_matching v x b, c, d))
                           value_name_pattern_matching_t_t'_list` THEN
                 SRW_TAC [] [subst_value_name_letrec_binding_def, MAP_MAP, LAMBDA_PROD2,
                                 EVERY_MAP] THEN
                 FULL_SIMP_TAC list_ss [EVERY_MEM, AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] THEN
                 SRW_TAC [] [] THEN
                 Q.PAT_ASSUM `!x' S'' E1' E2' x'' v' t'''. P x' S'' E1' E2' x'' v' t''' ==>
                              JTpat_matching (shiftTsig 0 (num_tv E1') S'') (E1' ++ E2') 
                                             (subst_value_name_pattern_matching v x'' (FST (SND x')))
                                             (FST (SND (SND x'))) (SND (SND (SND x')))`
                             (MATCH_MP_TAC o
                              SIMP_RULE list_ss [num_tv_append_thm, lem5, MAP_REVERSE] o 
                              Q.SPECL [`x'`, `S'`, 
                                       `MAP (\z. EB_vn (FST z)  
                                                       (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z))) 
                                                                                        (SND (SND (SND z)))))))
                                            (REVERSE value_name_pattern_matching_t_t'_list) ++ E1`])
                 THEN
                 SRW_TAC [] [MAP_MAP, domEB_def, MAP_REVERSE, MEM_REVERSE] THEN
                 Q.PAT_ASSUM `~MEM x (MAP FST value_name_pattern_matching_t_t'_list)` MP_TAC THEN
                 REPEAT (POP_ASSUM (K ALL_TAC)) THEN
                 Induct_on `value_name_pattern_matching_t_t'_list` THEN SRW_TAC [] []])]
);


(* This is a slight variant on the substitution lemma needed for substitution
* for definitions.  The difference is all in the S argument (which is used for
* type variable annotations in the source), and I haven't found a way to unite
* the two lemmas into one.  It was copied from the proof above and modified
* slightly.  *)

val lem9 = Q.prove (
`JTpat S (E1 ++ [EB_vn x (TS_forall  t'')] ++ E2) p t E /\
 JTe S (E ++ E1 ++ [EB_vn x (TS_forall t'')] ++ E2) e t' /\
 (  is_non_expansive_of_expr v /\
    (E ++ E1 ++ [EB_vn x (TS_forall t'')] ++ E2 =
     (E++E1) ++ [EB_vn x (TS_forall t'')] ++ E2) /\
    ~MEM (name_vn x) (MAP domEB (E++E1)) /\
    closed_env E2 /\
    (?S'. JTe S' (EB_tv::E2) (remv_tyvar_expr v) t'') ==>
    JTe S ((E++E1) ++ E2) (subst_value_name_expr (remv_tyvar_expr v) x e) t') /\
 is_non_expansive_of_expr v /\
 ~MEM (name_vn x) (MAP domEB E1) /\
 closed_env E2 /\
 JTe S' (EB_tv::E2) (remv_tyvar_expr v) t'' ==>
    JTe S (E ++ E1 ++ E2)
        (if MEM x (aux_xs_pattern_of_pattern p) then
           e
         else
           subst_value_name_expr (remv_tyvar_expr v) x e)
        t'`,
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN
IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN SRW_TAC [] [] THENL
[MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
        Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
        SRW_TAC [] [value_env_def, domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
        METIS_TAC [MEM_MAP, MEM_REVERSE],
        METIS_TAC [MEM_MAP, name_11, MEM_REVERSE]]);

val lem10 = Q.prove (
`MEM x (MAP FST l) /\
 JTpat_matching S
                (REVERSE (MAP (\z. EB_vn (FST z)
                                         (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z)))
                                                                          (SND (SND (SND z))))))) l) ++ E1 ++ 
                [EB_vn x (TS_forall t'')] ++ E2) pm t t' ==>
JTpat_matching S
               (REVERSE (MAP (\z. EB_vn (FST z) 
                                         (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z)))
                                                                          (SND (SND (SND z))))))) l) ++ E1 ++ 
                E2) pm t t'`,
Cases_on `pm` THEN SRW_TAC [] [JTe_fun] THEN
Q.EXISTS_TAC `pattern_e_E_list` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THENL
[METIS_TAC [value_env_pat_str_thm, value_env_def],
 SRW_TAC [] [] THEN
        MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
        Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
        SRW_TAC [] [value_env_def, MAP_REVERSE, MAP_MAP, domEB_def] THEN
        Q.PAT_ASSUM `MEM x (MAP FST l)` MP_TAC THEN
        REPEAT (POP_ASSUM (K ALL_TAC)) THEN Induct_on `l` THEN SRW_TAC [] [] THEN METIS_TAC []]);

val lem11 = Q.prove (
`!S v t E E' t_list.
  JTe (shiftTsig 0 1 S) (EB_tv::E) (remv_tyvar_expr v) t /\ closed_env E /\ Eok (E' ++ E) /\
      EVERY (tkind (E' ++ E)) t_list ==>
  JTe S (E' ++ E) (remv_tyvar_expr v) (idxsub t_list (shiftt 1 (num_tv E') t))`,
METIS_TAC [lem8, remv_tyvar_thm, remv_tyvar_idem_thm]);


val subst_for_def_lem = Q.store_thm ("subst_for_def_lem",
`(!S E e t. JTe S E e t ==>
  !E1 E2 x v t'.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t')] ++ E2) /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     (?S'. JTe S' (EB_tv::E2) (remv_tyvar_expr v) t') ==>
     JTe S (E1++E2) (subst_value_name_expr (remv_tyvar_expr v) x e) t) /\
 (!S E pm t t'. JTpat_matching S E pm t t' ==>
    !E1 E2 x v t''.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t'')] ++ E2) /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     (?S'. JTe S' (EB_tv::E2) (remv_tyvar_expr v) t'') ==>
     JTpat_matching S (E1++E2) (subst_value_name_pattern_matching (remv_tyvar_expr v) x pm) t t') /\
 (!S E lb E'. JTlet_binding S E lb E' ==> 
    !E1 E2 x v t''.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t'')] ++ E2) /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     (?S'. JTe S' (EB_tv::E2) (remv_tyvar_expr v) t'') ==>
     JTlet_binding S (E1++E2) (subst_value_name_let_binding (remv_tyvar_expr v) x lb) E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==> 
    !x E1 E2 v t''.
     is_non_expansive_of_expr v /\
     (E = E1 ++ [EB_vn x (TS_forall t'')] ++ E2) /\
     ~MEM (name_vn x) (MAP domEB E1) /\
     closed_env E2 /\
     (?S'. JTe S' (EB_tv::E2) (remv_tyvar_expr v) t'') ==>
     if MEM x (aux_xs_letrec_bindings_of_letrec_bindings lrbs) then
       JTletrec_binding S (E1++E2) lrbs E'
     else
       JTletrec_binding S (E1++E2) (subst_value_name_letrec_bindings (remv_tyvar_expr v) x lrbs) E')`,
RULE_INDUCT_TAC JTe_sind [subst_value_name_letrec_binding_def, JTe_fun]
[([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_constant"``, ``"JTe_typed"``],
  FULL_SIMP_TAC list_ss [JTuprim_cases, JTbprim_cases, JTconst_cases, JTconstr_c_cases] THEN
        SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [lookup_def, domEB_def, name_distinct, EVERY_MEM] THEN
        METIS_TAC [value_env_lookup_str_thm, value_env_ok_str_thm, APPEND, value_env_def, 
                   value_env_inst_any_thm, value_env_teq_str_thm]),
 ([``"JTe_apply"``, ``"JTe_match"``], METIS_TAC []),
 ([``"JTe_ident"``], 
  SRW_TAC [] [] THEN SRW_TAC [] [JTe_fun] THEN
         FULL_SIMP_TAC list_ss [JTvalue_name_cases, lookup_def, domEB_def, name_11, lookup_append_thm,
                                lookup_dom_thm] THEN
         SRW_TAC [] [] THENL
         [FULL_SIMP_TAC list_ss [JTinst_cases, shiftEB_def, shiftts_def] THEN SRW_TAC [] [] THEN
                  `JTe S' (E1 ++ E2) (remv_tyvar_expr v) (idxsub t_list (shiftt 1 (num_tv E1) t'))`
                        by (MATCH_MP_TAC lem11 THEN SRW_TAC [] [] THENL
                                 [METIS_TAC [remv_tyvar_idem_thm, remv_tyvar_thm],
                                  METIS_TAC [value_env_ok_str_thm, value_env_def, ok_ok_thm],
                                  FULL_SIMP_TAC list_ss [EVERY_MEM] THEN 
                                          METIS_TAC [value_env_ok_str_thm, value_env_def]]) THEN
                  METIS_TAC [value_env_def, value_env_teq_str_thm, teq_thm],
          FULL_SIMP_TAC list_ss [lem1] THEN Cases_on `lookup E1 (name_vn value_name)` THEN
                  FULL_SIMP_TAC list_ss [option_case_def] THEN SRW_TAC [] [] THENL
                  [Cases_on `EB` THEN
                          FULL_SIMP_TAC list_ss [environment_binding_distinct, shiftEB_def, num_tv_append_thm,
                                                 num_tv_def] THEN
                          SRW_TAC [] [] THEN
                          METIS_TAC [value_env_inst_str_thm, value_env_ok_str_thm, value_env_def,
                                     value_env_teq_str_thm],
                   METIS_TAC [value_env_inst_str_thm, value_env_ok_str_thm, value_env_def,
                              value_env_teq_str_thm]]]),
 ([``"JTe_tuple"``, ``"JTe_construct"``],
  SRW_TAC [] [] THEN 
        Q.EXISTS_TAC `MAP (\e_t. (subst_value_name_expr (remv_tyvar_expr v) x (FST e_t), SND e_t)) 
                          e_t_list` THEN
        SRW_TAC [] [MAP_MAP, ETA_THM, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [value_env_def, value_env_constr_p_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_cons"``, ``"JTe_and"``, ``"JTe_or"``, ``"JTe_while"``, ``"JTe_function"``],
  METIS_TAC [value_env_teq_str_thm, value_env_def]),
 ([``"JTe_record_constr"``],
  SRW_TAC [] [] THEN
  MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`,
                          `MAP (\fn_e_t. (FST fn_e_t,
                                          subst_value_name_expr (remv_tyvar_expr v) x (FST (SND fn_e_t)), 
                                          SND (SND fn_e_t)))
                               field_name_e_t_list`,
                          `typeconstr_name`,
                          `kind`] THEN
        SRW_TAC [] [MAP_MAP, ETA_THM, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN1
        METIS_TAC [] THEN1
        METIS_TAC [value_env_def, value_env_field_str_thm, APPEND] THEN
        METIS_TAC [value_env_def, value_env_lookup_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_record_with"``],
  SRW_TAC [] [] THEN 
  Q.EXISTS_TAC `MAP (\fn_e_t. (FST fn_e_t,
                               subst_value_name_expr (remv_tyvar_expr v) x (FST (SND fn_e_t)), 
                               SND (SND fn_e_t)))
                    field_name_e_t_list` THEN
        SRW_TAC [] [MAP_MAP, ETA_THM, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [value_env_def, value_env_field_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_record_proj"``],
  METIS_TAC [value_env_def, value_env_field_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_assert"``, ``"JTe_assertfalse"``],
  FULL_SIMP_TAC list_ss [JTconst_cases] THEN SRW_TAC [] [] THEN 
        METIS_TAC [last (CONJUNCTS value_env_ok_str_thm), value_env_def, APPEND, value_env_teq_str_thm]),
 ([``"JTe_location"``],
  METIS_TAC [value_env_def, value_env_ok_str_thm, value_env_lookup_str_thm, APPEND, value_env_teq_str_thm]),
 ([``"JTe_for"``],
  SRW_TAC [] [shiftt_def] THEN SRW_TAC [] [] THENL 
  [MATCH_MP_TAC (SIMP_RULE list_ss [AND_IMP_INTRO]
                (Q.SPECL [`E2`, `[EB_vn (VN_id lowercase_ident) (TS_forall t')]`, 
                          `S`, `e''`, 
                          `TE_constr [] TC_unit`, 
                          `EB_vn (VN_id lowercase_ident) (TS_forall (TE_constr [] TC_int))::E1`]
                         (GEN_ALL (hd (CONJUNCTS value_env_str_thm))))) THEN
           SRW_TAC [] [value_env_def, domEB_def],
   Q.PAT_ASSUM `!E1' E2' x' v t''. P E1' E2' x' v t'' ==>
                       JTe S (E1' ++ E2')
                           (subst_value_name_expr (remv_tyvar_expr v) x' e'')
                           (TE_constr [] TC_unit)`
               (MATCH_MP_TAC o 
                SIMP_RULE list_ss [num_tv_def] o
                Q.SPECL [`EB_vn (VN_id lowercase_ident)
                                (TS_forall (TE_constr [] TC_int)) :: E1`]) THEN
           SRW_TAC [] [domEB_def, DISJOINT_RIGHT, MEM_MAP] THEN METIS_TAC [],
   METIS_TAC [value_env_def, value_env_teq_str_thm]]),
 ([``"JTe_let_mono"``],
  SRW_TAC [] [] THEN 
        FULL_SIMP_TAC list_ss [REVERSE_EQ, EB_vn_list_thm, aux_xs_let_binding_of_let_binding_def] THEN
        IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
        FULL_SIMP_TAC list_ss [REVERSE_REVERSE, domEB_def, MAP_MAP] THEN
        SRW_TAC [] [] THEN DISJ1_TAC THEN Q.EXISTS_TAC `x_t_list` THEN 
        SRW_TAC [] [] THENL
        [METIS_TAC [],
         MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
                 Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
                 SRW_TAC [] [value_env_def, domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP],
         METIS_TAC [],
         Q.PAT_ASSUM `!E1' E2' x' v' t'. P E1' E2' x' v' t' ==> 
                      JTe S (E1' ++ E2') (subst_value_name_expr (remv_tyvar_expr v') x' e) t` 
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [MAP_REVERSE] o
                      SIMP_RULE list_ss [num_tv_append_thm, lem5, GSYM MAP_REVERSE] o
                      Q.SPECL [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list) ++
                                E1`]) 
                 THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP, name_11]]),
 ([``"JTe_let_poly"``],
   SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [REVERSE_EQ, EB_vn_list_thm, aux_xs_let_binding_of_let_binding_def] THEN
        IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
        FULL_SIMP_TAC list_ss [REVERSE_REVERSE, domEB_def, MAP_MAP] THEN
        SRW_TAC [] [] THEN DISJ2_TAC THEN Q.EXISTS_TAC `x_t_list` THEN
        SRW_TAC [ARITH_ss] [shiftTsig_add_thm] THENL
        [METIS_TAC [subst_nexp_thm, nexp_remv_tyvar_thm],
         Q.PAT_ASSUM `!E1' E2' x' v' t'''. P E1' E2' x' v' t''' ==>
                      ?t'. JTpat (shiftTsig 0 1 S) (E1' ++ E2') pat t' E /\ 
                           JTe (shiftTsig 0 1 S) (E1' ++ E2') 
                               (subst_value_name_expr (remv_tyvar_expr v') x' nexp) t'`
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [num_tv_def] o
                      Q.SPECL [`EB_tv::E1`])
                 THEN
                 SRW_TAC [] [MAP_MAP, domEB_def, MAP_REVERSE, MEM_REVERSE] THEN
                 SRW_TAC [ARITH_ss] [MEM_MAP, shiftTsig_add_thm] THEN METIS_TAC [],
         MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
                 Q.EXISTS_TAC `[EB_vn x (TS_forall t'')]` THEN
                 SRW_TAC [] [value_env_def, domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP],
         METIS_TAC [subst_nexp_thm, nexp_remv_tyvar_thm],
         Q.PAT_ASSUM `!E1' E2' x' v' t'''. P E1' E2' x' v' t''' ==>
                      ?t'. JTpat (shiftTsig 0 1 S) (E1' ++ E2') pat t' E /\
                           JTe (shiftTsig 0 1 S) (E1' ++ E2')
                               (subst_value_name_expr (remv_tyvar_expr v') x' nexp) t'`
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [num_tv_def] o
                      Q.SPECL [`EB_tv::E1`])
                 THEN
                 SRW_TAC [] [MAP_MAP, domEB_def, MAP_REVERSE, MEM_REVERSE] THEN
                 SRW_TAC [ARITH_ss] [MEM_MAP, shiftTsig_add_thm] THEN METIS_TAC [],
         Q.PAT_ASSUM `!E1' E2' x' v' t'. P E1' E2' x' v' t' ==>
                      JTe S (E1' ++ E2') (subst_value_name_expr (remv_tyvar_expr v') x' e) t` 
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [MAP_REVERSE] o
                      SIMP_RULE list_ss [num_tv_def, GSYM MAP_REVERSE, lem5, num_tv_append_thm] o
                      Q.SPECL [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list) ++E1`])
                 THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP] THEN
                 METIS_TAC [MEM_MAP, name_11]]),
 ([``"JTe_letrec"``],
  SRW_TAC [] [] THEN IMP_RES_TAC aux_xs_letrec_bindings_of_letrec_bindings_thm THEN 
        FULL_SIMP_TAC list_ss [REVERSE_REVERSE, MAP_MAP, domEB_def] THEN
        Q.EXISTS_TAC `x_t_list` THEN SRW_TAC [] [] THENL
        [Q.PAT_ASSUM `!x' E1' E2' v' t''. P x' E1' E2' v' t'' ==>
                      (if MEM x' (aux_xs_letrec_bindings_of_letrec_bindings lrbs) then
                         JTletrec_binding (shiftTsig 0 1 S) (E1' ++ E2') lrbs E'
                       else
                         JTletrec_binding (shiftTsig 0 1 S) (E1' ++ E2') 
                                          (subst_value_name_letrec_bindings (remv_tyvar_expr v') x' lrbs) E'')`
                     (MP_TAC o 
                      Q.SPECL [`x`, `EB_tv::E1`]) THEN
                 SRW_TAC [] [num_tv_def, shiftTsig_add_thm] THEN POP_ASSUM MATCH_MP_TAC THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 SRW_TAC [] [MEM_MAP] THEN METIS_TAC [],
         Q.PAT_ASSUM `!x' E1' E2' v' t''. P x' E1' E2' v' t'' ==>
                      (if MEM x' (aux_xs_letrec_bindings_of_letrec_bindings lrbs) then
                         JTletrec_binding (shiftTsig 0 1 S'') (E1' ++ E2') lrbs E'
                       else
                         JTletrec_binding (shiftTsig 0 1 S'') (E1' ++ E2')
                                          (subst_value_name_letrec_bindings (remv_tyvar_expr v') x' lrbs) E'')`
                     (MP_TAC o
                      Q.SPECL [`x`, `EB_tv::E1`]) THEN
                 SRW_TAC [] [num_tv_def, shiftTsig_add_thm] THEN POP_ASSUM MATCH_MP_TAC THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 SRW_TAC [] [MEM_MAP] THEN METIS_TAC [],
         MATCH_MP_TAC (GEN_ALL (hd (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO] value_env_str_thm)))) THEN
                 Q.EXISTS_TAC `[EB_vn x (TS_forall t')]` THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 FULL_SIMP_TAC list_ss [] THEN METIS_TAC [MEM_MAP],
         Q.PAT_ASSUM `!E1' E2' x' v t''. P E1' E2' x' v t'' ==>
                      JTe S (E1' ++ E2') (subst_value_name_expr (remv_tyvar_expr v) x' e) t` 
                     (MATCH_MP_TAC o
                      SIMP_RULE list_ss [MAP_REVERSE] o
                      SIMP_RULE list_ss [num_tv_def, GSYM MAP_REVERSE, lem5, num_tv_append_thm] o
                      Q.SPECL [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list) ++E1`])
                 THEN
                 SRW_TAC [] [domEB_def, MAP_REVERSE, MEM_REVERSE, MAP_MAP, value_env_def] THEN
                 SRW_TAC [] [MEM_MAP] THEN Cases_on `x = FST z` THEN SRW_TAC [] [] THEN METIS_TAC [lem2]]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN
  Q.EXISTS_TAC `MAP (\z. (FST z,
                         (if MEM x (aux_xs_pattern_of_pattern (FST z)) then
                            FST (SND z)
                          else subst_value_name_expr (remv_tyvar_expr v) x (FST (SND z))),
                         (SND (SND z))))
                   pattern_e_E_list` THEN
        SRW_TAC [] [MAP_MAP, subst_value_name_letrec_binding_def, EVERY_MAP] THEN
        FULL_SIMP_TAC list_ss [EVERY_MEM] THENL
        [METIS_TAC [value_env_pat_str_thm, value_env_def],
         METIS_TAC [lem9]]), 
 ([``"JTlet_binding_poly"``],
  SRW_TAC [] [] THEN  MAP_EVERY Q.EXISTS_TAC [`x_t_list`, `t`] THEN SRW_TAC [] [] THEN
        METIS_TAC [value_env_pat_str_thm, value_env_def]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [aux_xs_letrec_bindings_of_letrec_bindings_def, MAP_MAP,
              aux_xs_letrec_binding_of_letrec_binding_def, FLAT_MAP_SING] THEN
        SRW_TAC [] [] THENL
        [FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [lem10],
         Q.EXISTS_TAC `MAP (\(a, b, c, d). (a, subst_value_name_pattern_matching (remv_tyvar_expr v) x b, c, d))
                           value_name_pattern_matching_t_t'_list` THEN
                 SRW_TAC [] [subst_value_name_letrec_binding_def, MAP_MAP, LAMBDA_PROD2,
                                 EVERY_MAP] THEN
                 FULL_SIMP_TAC list_ss [EVERY_MEM, AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] THEN
                 SRW_TAC [] [] THEN
                 Q.PAT_ASSUM `!x' E1' E2' x'' v' t'''. P x' E1' E2' x'' v' t''' ==>
                              JTpat_matching S (E1' ++ E2') 
                                             (subst_value_name_pattern_matching 
                                                 (remv_tyvar_expr v) x'' (FST (SND x')))
                                             (FST (SND (SND x'))) (SND (SND (SND x')))`
                             (MATCH_MP_TAC o
                              SIMP_RULE list_ss [num_tv_append_thm, lem5, MAP_REVERSE] o 
                              Q.SPECL [`x'`,
                                       `MAP (\z. EB_vn (FST z)  
                                                       (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z))) 
                                                                                        (SND (SND (SND z)))))))
                                            (REVERSE value_name_pattern_matching_t_t'_list) ++ E1`])
                 THEN
                 SRW_TAC [] [MAP_MAP, domEB_def, MAP_REVERSE, MEM_REVERSE] THEN
                 Q.PAT_ASSUM `~MEM x (MAP FST value_name_pattern_matching_t_t'_list)` MP_TAC THENL
                 [REPEAT (POP_ASSUM (K ALL_TAC)) THEN
                      Induct_on `value_name_pattern_matching_t_t'_list` THEN SRW_TAC [] [],
                  METIS_TAC []]])]
);

end;

val substs_empty_thm = Q.store_thm ("substs_empty_thm",
`(!lrb. substs_value_name_letrec_binding [] lrb = lrb) /\
 (!lrbs. substs_value_name_letrec_bindings [] lrbs = lrbs) /\
 (!lb. substs_value_name_let_binding [] lb = lb) /\
 (!pe. substs_value_name_pat_exp [] pe = pe) /\
 (!pm. substs_value_name_pattern_matching [] pm = pm) /\
 (!e. substs_value_name_expr [] e = e) /\
 (!lrb_list. MAP (substs_value_name_letrec_binding []) lrb_list = lrb_list) /\
 (!pe_list. MAP (substs_value_name_pat_exp []) pe_list = pe_list) /\
 (!fe_list. MAP (\(f:field, e). (f, substs_value_name_expr [] e)) fe_list = fe_list) /\
 (!e_list. MAP (substs_value_name_expr []) e_list = e_list) /\
 (!fe:(field#expr). (FST fe, substs_value_name_expr [] (SND fe)) = fe)`,
Induct THEN SRW_TAC [] [substs_value_name_letrec_binding_def, list_assoc_def] THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 Cases_on `fe` THEN FULL_SIMP_TAC list_ss []]);

val substs_DISJOINT_thm = Q.prove (
`(!subs lrb. DISJOINT (fv_letrec_binding lrb) (MAP FST subs) ==>
             (substs_value_name_letrec_binding subs lrb = lrb)) /\
 (!subs lrbs. DISJOINT (fv_letrec_bindings lrbs) (MAP FST subs) ==>
              (substs_value_name_letrec_bindings subs lrbs = lrbs)) /\
 (!subs lb. DISJOINT (fv_let_binding lb) (MAP FST subs) ==>
            (substs_value_name_let_binding subs lb = lb)) /\
 (!subs pe. DISJOINT (fv_pat_exp pe) (MAP FST subs) ==> 
            (substs_value_name_pat_exp subs pe = pe)) /\
 (!subs pm. DISJOINT (fv_pattern_matching pm) (MAP FST subs) ==>
            (substs_value_name_pattern_matching subs pm = pm)) /\
 (!subs e. DISJOINT (fv_expr e) (MAP FST subs) ==>
           (substs_value_name_expr subs e = e))`,
HO_MATCH_MP_TAC substs_value_name_letrec_binding_ind THEN 
SRW_TAC [] [substs_value_name_letrec_binding_def, fv_letrec_binding_def, FLAT_EQ_EMPTY, EVERY_MAP,
                EVERY_MEM, DISJOINT_MEM] THEN 
FULL_SIMP_TAC list_ss [LAMBDA_PROD2] THENL
[Induct_on `letrec_binding_list` THEN SRW_TAC [] [],
 FULL_SIMP_TAC list_ss [list_minus_thm, MEM_MAP, MEM_FILTER] THEN METIS_TAC [],
 Induct_on `pat_exp_list` THEN SRW_TAC [] [],
 IMP_RES_TAC not_mem_list_assoc THEN SRW_TAC [] [],
 Induct_on `expr_list` THEN SRW_TAC [] [],
 Induct_on `expr_list` THEN SRW_TAC [] [],
 Induct_on `field_expr_list` THEN SRW_TAC [] [] THENL
        [Cases_on `h` THEN SRW_TAC [] [],
         FULL_SIMP_TAC list_ss [MEM_MAP, MEM_FILTER] THEN METIS_TAC []],
 Induct_on `field_expr_list` THEN SRW_TAC [] [] THENL
        [Cases_on `h` THEN SRW_TAC [] [],
         FULL_SIMP_TAC list_ss [MEM_MAP, MEM_FILTER] THEN METIS_TAC []],
 FULL_SIMP_TAC list_ss [list_minus_thm, MEM_MAP, MEM_FILTER] THEN METIS_TAC [],
 FULL_SIMP_TAC list_ss [list_minus_thm, MEM_MAP, MEM_FILTER] THEN METIS_TAC [],
 FULL_SIMP_TAC list_ss [list_minus_thm, MEM_MAP, MEM_FILTER] THEN METIS_TAC [],
 FULL_SIMP_TAC list_ss [list_minus_thm, MEM_MAP, MEM_FILTER] THEN METIS_TAC []]);

val substs_closed_thm = Q.store_thm ("substs_closed_thm",
`!e subs. (fv_expr e = []) ==> (substs_value_name_expr subs e = e)`,
METIS_TAC [DISJOINT_MEM, MEM, substs_DISJOINT_thm, EVERY_MEM]);

local

val lem1 = Q.prove (
`(!lrbs subs. aux_xs_letrec_bindings_of_letrec_bindings (substs_value_name_letrec_bindings subs lrbs) =
              aux_xs_letrec_bindings_of_letrec_bindings lrbs) /\
 (!lrb subs. aux_xs_letrec_binding_of_letrec_binding (substs_value_name_letrec_binding subs lrb) =
              aux_xs_letrec_binding_of_letrec_binding lrb) /\
 (!lrb_list subs. MAP (\lrb. aux_xs_letrec_binding_of_letrec_binding
                                    (substs_value_name_letrec_binding subs lrb)) lrb_list =
                  MAP aux_xs_letrec_binding_of_letrec_binding lrb_list)`,
Induct THEN 
SRW_TAC [] [aux_xs_letrec_bindings_of_letrec_bindings_def, substs_value_name_letrec_binding_def,
                aux_xs_letrec_binding_of_letrec_binding_def, MAP_MAP]);
in

val substs_iter_thm = Q.store_thm ("substs_iter_thm",
`(!lrb subs. (fv_expr v = []) ==>
             (substs_value_name_letrec_binding ((x,v)::subs) lrb = 
              substs_value_name_letrec_binding subs (subst_value_name_letrec_binding v x lrb))) /\
 (!lrbs subs. (fv_expr v = []) ==>
              (substs_value_name_letrec_bindings ((x,v)::subs) lrbs =
               substs_value_name_letrec_bindings subs (subst_value_name_letrec_bindings v x lrbs))) /\
 (!lb subs. (fv_expr v = []) ==> 
            (substs_value_name_let_binding ((x,v)::subs) lb = 
             substs_value_name_let_binding subs (subst_value_name_let_binding v x lb))) /\
 (!pe subs. (fv_expr v = []) ==>
            (substs_value_name_pat_exp ((x,v)::subs) pe =
             substs_value_name_pat_exp subs (subst_value_name_pat_exp v x pe))) /\
 (!pm subs. (fv_expr v = []) ==>
            (substs_value_name_pattern_matching ((x,v)::subs) pm =
             substs_value_name_pattern_matching subs (subst_value_name_pattern_matching v x pm))) /\
 (!e subs. (fv_expr v = []) ==> 
           (substs_value_name_expr ((x,v)::subs) e = 
            substs_value_name_expr subs (subst_value_name_expr v x e))) /\
 (!lrb_list subs. (fv_expr v = []) ==>
                  (MAP (substs_value_name_letrec_binding ((x,v)::subs)) lrb_list =
                   MAP (\lrb. substs_value_name_letrec_binding subs (subst_value_name_letrec_binding v x lrb))
                       lrb_list)) /\
 (!pe_list subs. (fv_expr v = []) ==>
                 (MAP (substs_value_name_pat_exp ((x,v)::subs)) pe_list =
                  MAP (\pe. substs_value_name_pat_exp subs (subst_value_name_pat_exp v x pe)) pe_list)) /\
 (!fe_list subs. (fv_expr v = []) ==>
                 (MAP (\(f:field, e). (f, substs_value_name_expr ((x,v)::subs) e)) fe_list =
                  MAP (\(f, e). (f, substs_value_name_expr subs (subst_value_name_expr v x e))) fe_list)) /\
 (!e_list subs. (fv_expr v = []) ==> 
                (MAP (substs_value_name_expr ((x,v)::subs)) e_list = 
                 MAP (\e. substs_value_name_expr subs (subst_value_name_expr v x e)) e_list)) /\
 (!fe:(field#expr) subs. (fv_expr v = []) ==>
                         ((FST fe, substs_value_name_expr ((x,v)::subs) (SND fe)) =
                          (FST fe, substs_value_name_expr subs (subst_value_name_expr v x (SND fe)))))`,
Induct THEN
SRW_TAC [] [substs_value_name_letrec_binding_def, subst_value_name_letrec_binding_def, MAP_MAP,
            list_assoc_def] THEN
FULL_SIMP_TAC list_ss [LAMBDA_PROD2] THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [substs_closed_thm],
 METIS_TAC [],
 METIS_TAC [],
 Cases_on `lb` THEN
        FULL_SIMP_TAC list_ss [subst_value_name_letrec_binding_def, aux_xs_let_binding_of_let_binding_def],
 Cases_on `lb` THEN
        FULL_SIMP_TAC list_ss [subst_value_name_letrec_binding_def, aux_xs_let_binding_of_let_binding_def],
 METIS_TAC [lem1],
 METIS_TAC [lem1]]);

end;

local

val lem5 = Q.prove (
`!l f g. num_tv (MAP (\x. EB_vn (f x) (g x)) l) = 0`,
METIS_TAC [value_env_map_thm, value_env_num_tv_thm]);

in

val substs_lem = Q.store_thm ("substs_lem",
`!S e t E x_t_list x_v_list.
 (LENGTH x_t_list = LENGTH x_v_list) /\
 JTe S (REVERSE (MAP (\(x,t). EB_vn x (TS_forall t)) x_t_list) ++ E) e t /\
 EVERY (\(x, v). is_non_expansive_of_expr v) x_v_list /\
 closed_env E /\
 ALL_DISTINCT (MAP FST x_t_list) /\
 EVERY (\((x,t),x',v). (x = x') /\ JTe (shiftTsig 0 1 S) (EB_tv::E) v t)
       (ZIP (x_t_list,x_v_list)) ==>
 JTe S E (substs_value_name_expr x_v_list e) t`,
Induct_on `x_t_list` THEN Cases_on `x_v_list` THEN SRW_TAC [] [substs_empty_thm] THEN
Cases_on `h'` THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
`fv_expr r' = []` by (FULL_SIMP_TAC list_ss [GSYM MAP_REVERSE, ELIM_UNCURRY] THEN
                      METIS_TAC [closed_env_fv_thm, closed_env_tv_lem]) THEN
SRW_TAC [] [substs_iter_thm] THEN
Q.PAT_ASSUM `!S' e' t' E' x_v_list. P S' e' t' E' x_v_list ==>
             JTe S' E' (substs_value_name_expr x_v_list e') t'` MATCH_MP_TAC THEN
SRW_TAC [] [LAMBDA_PROD2] THEN
MATCH_MP_TAC ((SIMP_RULE list_ss [MAP_REVERSE] o
               SIMP_RULE list_ss [lem5, LAMBDA_PROD2, shiftTsig_add_thm] o
               (*Q.SPECL [`e`, `t'`, `S`, `MAP (\(x,t). EB_vn x (TS_forall t)) (REVERSE x_t_list)`] o*)
               Q.SPECL [`shiftTsig 0 (num_tv (MAP (\(x,t). EB_vn x (TS_forall t)) (REVERSE x_t_list)))
                                   S`, 
                        `e`, `t'`, `S`, `MAP (\(x,t). EB_vn x (TS_forall t)) (REVERSE x_t_list)`] o
               SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o hd o CONJUNCTS) subst_lem) THEN
SRW_TAC [] [MAP_REVERSE, MEM_REVERSE, MAP_MAP, domEB_def] THEN
FULL_SIMP_TAC list_ss [LAMBDA_PROD2, domEB_def] THEN
Q.EXISTS_TAC `r` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [MEM_MAP, name_11]);

val substs_pm_lem = Q.store_thm ("substs_pm_lem",
`!S pm t t' E x_t_list x_v_list.
 (LENGTH x_t_list = LENGTH x_v_list) /\
 JTpat_matching S (REVERSE (MAP (\(x,t). EB_vn x (TS_forall t)) x_t_list) ++ E) pm t t' /\
 EVERY (\(x, v). is_non_expansive_of_expr v) x_v_list /\
 closed_env E /\
 ALL_DISTINCT (MAP FST x_t_list) /\
 EVERY (\((x,t),x',v). (x = x') /\ JTe (shiftTsig 0 1 S) (EB_tv::E) v t) (ZIP (x_t_list,x_v_list)) ==>
 JTpat_matching S E (substs_value_name_pattern_matching x_v_list pm) t t'`,
Induct_on `x_t_list` THEN Cases_on `x_v_list` THEN SRW_TAC [] [substs_empty_thm] THEN
Cases_on `h'` THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
`fv_expr r' = []` by (FULL_SIMP_TAC list_ss [GSYM MAP_REVERSE, ELIM_UNCURRY] THEN
                      METIS_TAC [closed_env_fv_thm, closed_env_tv_lem]) THEN
SRW_TAC [] [substs_iter_thm] THEN
Q.PAT_ASSUM `!S' pm' t' t''' E' x_v_list. P S' pm' t' t''' E' x_v_list ==>
             JTpat_matching S' E' (substs_value_name_pattern_matching x_v_list pm') t' t'''` MATCH_MP_TAC THEN
SRW_TAC [] [LAMBDA_PROD2] THEN
MATCH_MP_TAC ((SIMP_RULE list_ss [MAP_REVERSE] o
               SIMP_RULE list_ss [lem5, LAMBDA_PROD2, shiftTsig_add_thm] o
               (*Q.SPECL [`pm`, `t'`, `t''`, `S`, `MAP (\(x,t). EB_vn x (TS_forall t)) (REVERSE x_t_list)`] o*)
               Q.SPECL [`shiftTsig 0 (num_tv (MAP (\(x,t). EB_vn x (TS_forall t)) (REVERSE x_t_list)))
                                   S`,
                        `pm`, `t'`, `t''`, `S`, `MAP (\(x,t). EB_vn x (TS_forall t)) (REVERSE x_t_list)`] o
               SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o hd o tl o CONJUNCTS) subst_lem)
THEN
SRW_TAC [] [MAP_REVERSE, MEM_REVERSE, MAP_MAP, domEB_def] THEN
FULL_SIMP_TAC list_ss [LAMBDA_PROD2, domEB_def] THEN
Q.EXISTS_TAC `r` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [MEM_MAP, name_11]);

end;

val substs_ftv_thm = Q.store_thm ("substs_ftv_thm",
`(!subs lrb. EVERY (\xv. ftv_expr (SND xv) = []) subs /\ (ftv_letrec_binding lrb = []) ==>
             (ftv_letrec_binding (substs_value_name_letrec_binding subs lrb) = [])) /\
 (!subs lrbs. EVERY (\xv. ftv_expr (SND xv) = []) subs /\ (ftv_letrec_bindings lrbs = []) ==>
              (ftv_letrec_bindings (substs_value_name_letrec_bindings subs lrbs) = [])) /\
 (!subs lb. EVERY (\xv. ftv_expr (SND xv) = []) subs /\ (ftv_let_binding lb = []) ==>
            (ftv_let_binding (substs_value_name_let_binding subs lb) = [])) /\
 (!subs pe. EVERY (\xv. ftv_expr (SND xv) = []) subs /\ (ftv_pat_exp pe = []) ==>
            (ftv_pat_exp (substs_value_name_pat_exp subs pe) = [])) /\
 (!subs pm. EVERY (\xv. ftv_expr (SND xv) = []) subs /\ (ftv_pattern_matching pm = []) ==>
            (ftv_pattern_matching (substs_value_name_pattern_matching subs pm) = [])) /\
 (!subs e. EVERY (\xv. ftv_expr (SND xv) = []) subs /\ (ftv_expr e = []) ==>
           (ftv_expr (substs_value_name_expr subs e) = []))`,
HO_MATCH_MP_TAC substs_value_name_letrec_binding_ind THEN
SRW_TAC [] [substs_value_name_letrec_binding_def, ftv_letrec_binding_def, FLAT_EQ_EMPTY, EVERY_MAP,
                EVERY_MEM, MEM_FILTER] THEN
FULL_SIMP_TAC list_ss [LAMBDA_PROD2, ftv_letrec_binding_def] THENL
[Cases_on `list_assoc value_name subs` THEN SRW_TAC [] [ftv_letrec_binding_def] THEN
        METIS_TAC [list_assoc_mem, SND],
 Cases_on `x` THEN METIS_TAC [SND],
 Cases_on `x` THEN METIS_TAC [SND]]);

val _ = export_theory ();
