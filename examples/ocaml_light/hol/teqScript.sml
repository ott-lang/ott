open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory pairTheory;
open ottLib ottTheory caml_typedefTheory;
open utilTheory basicTheory environmentTheory validTheory weakenTheory shiftTheory type_substTheory;
open type_substsTheory;

val _ = new_theory "teq";


val EVERY_ZIP_SAME = Q.prove (
`!l f. EVERY (\(x, y). f x y) (ZIP (l, l)) = EVERY (\x. f x x) l`,
Induct THEN SRW_TAC [] []);

val EVERY_ZIP_SWAP = Q.prove (
`!l1 l2 f. (LENGTH l1 = LENGTH l2) ==>
           (EVERY (\(x, y). f x y) (ZIP (l1, l2)) = EVERY (\(x, y). f y x) (ZIP (l2, l1)))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) []);

val EVERY_T = Q.prove (
`!l. EVERY (\x. T) l = T`,
Induct THEN SRW_TAC [] []);


local

val lem1 = Q.prove (
`!E. value_env E ==> ~MEM EB_tv E`,
Induct THEN SRW_TAC [] [value_env_def] THEN Cases_on `h` THEN FULL_SIMP_TAC (srw_ss ()) [value_env_def]);

in

val teq_thm = Q.store_thm ("teq_thm",
`(!Tsigma E e t. JTe Tsigma E e t ==> !t'. JTeq E t t' ==> JTe Tsigma E e t') /\
 (!Tsigma E pm t1 t2. JTpat_matching Tsigma E pm t1 t2 ==> 
          !t'. JTeq E t2 t' ==> JTpat_matching Tsigma E pm t1 t') /\
 (!Tsigma E e E'. JTlet_binding Tsigma E e E' ==> T) /\
 (!Tsigma E e E'. JTletrec_binding Tsigma E e E' ==> T)`,
RULE_INDUCT_TAC JTe_sind [JTe_fun] 
[([``"JTe_uprim"``, ``"JTe_bprim"``, ``"JTe_ident"``, ``"JTe_constant"``, ``"JTe_typed"``, ``"JTe_cons"``,
   ``"JTe_and"``, ``"JTe_or"``, ``"JTe_while"``, ``"JTe_for"``, ``"JTe_assert"``, ``"JTe_location"``,
   ``"JTe_record_proj"``, ``"JTe_function"``],
  METIS_TAC [JTeq_rules]),
 ([``"JTe_match"``],
  METIS_TAC []),
 ([``"JTe_tuple"``, ``"JTe_construct"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `e_t_list` THEN SRW_TAC [] [] THEN METIS_TAC [JTeq_rules]),
 ([``"JTe_record_constr"``],
  SRW_TAC [] [] THEN MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`, `field_name_e_t_list`] THEN
      SRW_TAC [] [] THEN METIS_TAC [JTeq_rules]),
 ([``"JTe_record_with"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `field_name_e_t_list` THEN SRW_TAC [] [] THEN METIS_TAC [JTeq_rules]),
 ([``"JTe_apply"``],
  METIS_TAC [JTeq_rules, ok_thm]),
 ([``"JTe_assertfalse"``],
  SRW_TAC [] [JTconst_cases] THEN METIS_TAC [ok_ok_thm, JTeq_rules, teq_ok_thm]),
 ([``"JTe_let_mono"``],
  SRW_TAC [] [] THEN DISJ1_TAC THEN Q.EXISTS_TAC `x_t_list` THEN SRW_TAC [] [] THEN1 METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [REVERSE_EQ, EB_vn_list_thm] THEN SRW_TAC [] [] THEN
      `~MEM EB_tv (REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list))` by
             SRW_TAC [] [MEM_REVERSE, MEM_MAP] THEN
      METIS_TAC [weak_teq_thm, ok_thm, APPEND, APPEND_ASSOC, ok_ok_thm]),
 ([``"JTe_let_poly"``],
  SRW_TAC [] [] THEN DISJ2_TAC THEN Q.EXISTS_TAC `x_t_list` THEN SRW_TAC [] [] THEN1 METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [REVERSE_EQ, EB_vn_list_thm] THEN SRW_TAC [] [] THEN
      `~MEM EB_tv (REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list))` by
             SRW_TAC [] [MEM_REVERSE, MEM_MAP] THEN
      METIS_TAC [weak_teq_thm, ok_thm, APPEND, APPEND_ASSOC, ok_ok_thm]),
 ([``"JTe_letrec"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `x_t_list` THEN SRW_TAC [] [] THEN
      `~MEM EB_tv (REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list))` by
             SRW_TAC [] [MEM_REVERSE, MEM_MAP] THEN
      METIS_TAC [weak_teq_thm, ok_thm, APPEND, APPEND_ASSOC, ok_ok_thm]),
 ([``"JTpat_matching_pm"``],
   SRW_TAC [] [] THEN Q.EXISTS_TAC `pattern_e_E_list` THEN SRW_TAC [] [] THEN 
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN
      METIS_TAC [weak_teq_thm, ok_thm, APPEND, APPEND_ASSOC, ok_ok_thm, pat_env_lem, lem1])]);
end;

val num_abbrev_def = Define 
`(num_abbrev [] = 0:num) /\
 (num_abbrev (EB_ta x y z :: E) = 1 + num_abbrev E) /\
 (num_abbrev (_ :: E) = num_abbrev E)`;

local

val lem1 = Q.prove (
`!l x. MEM x l ==> typexpr_size x <= typexpr1_size l`,
Induct THEN SRW_TAC [] [typexpr_size_def] THEN RES_TAC THEN DECIDE_TAC);

in

val apply_abbrev_def = tDefine "apply_abbrev"
`(apply_abbrev tpo tcn t (TE_var tv) = TE_var tv) /\
 (apply_abbrev tpo tcn t (TE_idxvar i1 i2) = TE_idxvar i1 i2) /\
 (apply_abbrev tpo tcn t TE_any = TE_any) /\
 (apply_abbrev tpo tcn t (TE_arrow t1 t2) = 
   TE_arrow (apply_abbrev tpo tcn t t1) (apply_abbrev tpo tcn t t2)) /\
 (apply_abbrev tpo tcn t (TE_tuple ts) = TE_tuple (MAP (apply_abbrev tpo tcn t) ts)) /\
 (apply_abbrev tpo tcn t (TE_constr ts tc) =
   if (tc = TC_name tcn) /\ (LENGTH ts = LENGTH tpo) then
     substs_typevar_typexpr (ZIP (MAP tp_to_tv tpo, MAP (apply_abbrev tpo tcn t) ts)) t
   else
     TE_constr (MAP (apply_abbrev tpo tcn t) ts) tc)`
(WF_REL_TAC `measure (\(a, b, c, d). typexpr_size d)` THEN SRW_TAC [] [] THEN IMP_RES_TAC lem1 THEN
 DECIDE_TAC);

end;

val remove_abbrev_def = Define
`(remove_abbrev [] = (NONE, [])) /\
 (remove_abbrev (EB_ta tpo tcn t :: E) = (SOME (EB_ta tpo tcn t), E)) /\
 (remove_abbrev (EB_td tcn k :: E) =
   let (a, E') = remove_abbrev E in
     (a, EB_td tcn k :: E')) /\
 (remove_abbrev (EB_tr tcn k fns :: E) =
   let (a, E') = remove_abbrev E in
     (a, EB_tr tcn k fns :: E')) /\
 (remove_abbrev (EB_tv :: E) =
   let (a, E') = remove_abbrev E in
     (OPTION_MAP (\EB. shiftEB 0 1 EB) a, EB_tv :: E')) /\
 (remove_abbrev (EB_l k t :: E) = remove_abbrev E) /\
 (remove_abbrev (EB_fn fn tpo tcn t :: E) = remove_abbrev E) /\
 (remove_abbrev (EB_pc cn tpo tl tc :: E) = remove_abbrev E) /\
 (remove_abbrev (EB_cc cn tc :: E) = remove_abbrev E) /\
 (remove_abbrev (EB_vn vn ts :: E) = remove_abbrev E)`;

val remove_abbrev_result_thm = Q.prove (
`!E. ?E'. (remove_abbrev E = (NONE, E')) \/ ?tpo tcn t. remove_abbrev E = (SOME (EB_ta tpo tcn t), E')`,
Induct THEN SRW_TAC [] [remove_abbrev_def] THEN Cases_on `h` THEN 
SRW_TAC [] [remove_abbrev_def, shiftEB_def]);

val remove_abbrev_num_abbrev_thm = Q.prove (
`!E E' a. (remove_abbrev E = (a, E')) ==> (num_abbrev E' = num_abbrev E - 1)`,
Induct THEN SRW_TAC [] [remove_abbrev_def, num_abbrev_def] THEN SRW_TAC [] [num_abbrev_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss ()) [remove_abbrev_def, num_abbrev_def, LET_THM, LAMBDA_PROD2] THEN
SRW_TAC [] [num_abbrev_def] THEN Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) []);

val remove_abbrev_num_abbrev_thm2 = Q.prove (
`!E. (?E'. remove_abbrev E = (NONE, E')) = (num_abbrev E = 0)`,
Induct THEN SRW_TAC [] [remove_abbrev_def, num_abbrev_def] THEN SRW_TAC [] [num_abbrev_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss ()) [remove_abbrev_def, num_abbrev_def, LET_THM, LAMBDA_PROD2] THEN
SRW_TAC [] [num_abbrev_def] THEN Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) []);

val Eok_lem1 = Q.prove (
`!EB E. Eok (EB::E) ==> Eok E`, 
METIS_TAC [ok_ok_thm, APPEND]);

val remove_lookup_lem = Q.prove (
`!E tcn E' tpo t. Eok E /\ (remove_abbrev E = (SOME (EB_ta tpo tcn t), E')) ==>
                  (lookup E (name_tcn tcn) = SOME (EB_ta tpo tcn t))`,
Induct THEN SRW_TAC [] [lookup_def, remove_abbrev_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, lookup_def, domEB_def, LET_THM, LAMBDA_PROD2, 
                          shiftEB_add_thm, Eok_def] THEN
IMP_RES_TAC Eok_lem1 THEN IMP_RES_TAC ok_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `E'` THEN FULL_SIMP_TAC (srw_ss ()) [] THEN SRW_TAC [] [] THEN Cases_on `remove_abbrev E` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THENL
[METIS_TAC [lookup_dom_thm],
 METIS_TAC [lookup_dom_thm],
 Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def]]);

local

val lem1 = Q.prove (
`!EB E t1 t2. Eok (EB::E) /\ ~(EB = EB_tv) /\ JTeq E t1 t2 ==> JTeq (EB::E) t1 t2`,
METIS_TAC [weak_teq_thm, MEM, APPEND]);

val lem2 = Q.prove (
`!E. ?EBopt E'. remove_abbrev E = (EBopt, E')`,
SRW_TAC [] [] THEN Cases_on `remove_abbrev E` THEN METIS_TAC []);

val lem3 = Q.prove (
`!E1 EB E2 tpo tcn t E'.
     (remove_abbrev (E1 ++ [EB] ++ E2) = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) /\
     (remove_abbrev (E1 ++ E2) = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) ==>
     ~is_tc_EB EB`,
Induct THEN SRW_TAC [] [remove_abbrev_def, is_tc_EB_def] THENL
[Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, is_tc_EB_def, LET_THM] THEN
     SRW_TAC [] [] THEN IMP_RES_TAC remove_abbrev_num_abbrev_thm THEN 
     `~(num_abbrev E' = 0)` by METIS_TAC [remove_abbrev_num_abbrev_thm2, NOT_SOME_NONE, PAIR_EQ] THEN
     DECIDE_TAC,
 Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, is_tc_EB_def, LET_THM, LAMBDA_PROD2] THENL
     [STRIP_ASSUME_TAC (Q.SPEC `E1++[EB]++E2` lem2) THEN
          STRIP_ASSUME_TAC (Q.SPEC `E1++E2` lem2) THEN SRW_TAC [] [] THEN Cases_on `EB'` THEN
          FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN
          Cases_on `EB''` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def, shiftt_11] THEN
          METIS_TAC [SND],
      METIS_TAC [],
      METIS_TAC [],
      METIS_TAC [],
      METIS_TAC [],
      STRIP_ASSUME_TAC (Q.SPEC `E1++[EB]++E2` lem2) THEN
          STRIP_ASSUME_TAC (Q.SPEC `E1++E2` lem2) THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
          SRW_TAC [] [] THEN METIS_TAC [SND],
     STRIP_ASSUME_TAC (Q.SPEC `E1++[EB]++E2` lem2) THEN
          STRIP_ASSUME_TAC (Q.SPEC `E1++E2` lem2) THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
          SRW_TAC [] [] THEN METIS_TAC [SND],
     SRW_TAC [] [] THEN Cases_on `E1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
          `LENGTH (t++[EB]) = LENGTH t` by METIS_TAC [] THEN
          FULL_SIMP_TAC (srw_ss()) [],
     METIS_TAC []]]);
 
val lem4 = Q.prove (
`!E1 EB E2'. Eok (E1++[EB]++E2) /\ ~is_tc_EB EB ==> Eok (E1++E2)`,
METIS_TAC [ok_str_thm, EXISTS_DEF]);

in

val remove_abbrev_split_lem = Q.prove (
`!E EB E'. (remove_abbrev E = (SOME EB, E')) ==>
           ?E1 EB' E2. ~(EB' = EB_tv) /\ (E = E1++[EB']++E2) /\
                       ((remove_abbrev (E1++E2) = (SOME EB, E')) \/ (E' = E1++E2))`,
Induct THEN SRW_TAC [] [remove_abbrev_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, LET_THM] THEN
STRIP_ASSUME_TAC (Q.SPEC `E` lem2) THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN SRW_TAC [] [] THENL
[MAP_EVERY Q.EXISTS_TAC [`EB_tv::E1`, `EB'''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 METIS_TAC [APPEND, APPEND_ASSOC],
 MAP_EVERY Q.EXISTS_TAC [`EB_vn v t::E1`, `EB''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`[]`, `EB_vn v t`, `E1++[EB'']++E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`EB_cc c t::E1`, `EB''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`[]`, `EB_cc c t`, `E1++[EB'']++E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`EB_pc c t t0 t1::E1`, `EB''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`[]`, `EB_pc c t t0 t1`, `E1++[EB'']++E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`EB_fn f t t0 t1::E1`, `EB''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`[]`, `EB_fn f t t0 t1`, `E1++[EB'']++E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`EB_td t n::E1`, `EB''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 METIS_TAC [APPEND, APPEND_ASSOC],
 MAP_EVERY Q.EXISTS_TAC [`EB_tr t n l::E1`, `EB''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 METIS_TAC [APPEND, APPEND_ASSOC],
 MAP_EVERY Q.EXISTS_TAC [`[]`, `EB_ta t t0 t1`, `E`] THEN SRW_TAC [] [],
 MAP_EVERY Q.EXISTS_TAC [`EB_l n t::E1`, `EB''`, `E2`] THEN SRW_TAC [] [remove_abbrev_def],
 MAP_EVERY Q.EXISTS_TAC [`[]`, `EB_l n t`, `E1++[EB'']++E2`] THEN SRW_TAC [] [remove_abbrev_def]]);

val remove_abbrev_teq_weak_thm = Q.prove (
`!E E' tpo tcn t t1 t2. 
    Eok E /\ (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) /\ JTeq E' t1 t2 ==> 
    JTeq E t1 t2`,
STRIP_TAC THEN Induct_on `LENGTH E` THEN SRW_TAC [] [] THEN Cases_on `E` THEN 
FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def] THEN IMP_RES_TAC remove_abbrev_split_lem THENL
[`LENGTH (h::t') = LENGTH (E1++[EB']++E2)` by METIS_TAC [] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     `LENGTH t' = LENGTH (E1++E2)` by (SRW_TAC [] [] THEN DECIDE_TAC) THEN
     IMP_RES_TAC lem3 THEN IMP_RES_TAC lem4 THEN
     RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
     IMP_RES_TAC weak_teq_thm THEN FULL_SIMP_TAC (srw_ss()) [],
 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
     IMP_RES_TAC weak_teq_thm THEN FULL_SIMP_TAC (srw_ss()) []]);

end;

val abbrev_occurs_def = ottDefine "abbrev_occurs"
`(abbrev_occurs tcn (TE_var _) = F) /\
 (abbrev_occurs tcn (TE_idxvar _ _) = F) /\
 (abbrev_occurs tcn TE_any = F) /\
 (abbrev_occurs tcn (TE_arrow t1 t2) = abbrev_occurs tcn t1 \/ abbrev_occurs tcn t2) /\
 (abbrev_occurs tcn (TE_tuple ts) = EXISTS (abbrev_occurs tcn) ts) /\
 (abbrev_occurs tcn (TE_constr ts tc) = (tc = TC_name tcn) \/ EXISTS (abbrev_occurs tcn) ts)`;

val apply_abbrev_no_occur_thm = Q.prove (
`(!t2 tpo tcn t1. ~abbrev_occurs tcn t2 ==> (apply_abbrev tpo tcn t1 t2 = t2)) /\
 (!ts tpo tcn t1. ~EXISTS (abbrev_occurs tcn) ts ==> (MAP (\x. apply_abbrev tpo tcn t1 x) ts = ts))`,
Induct THEN SRW_TAC [] [apply_abbrev_def, abbrev_occurs_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);

val abbrev_occur_lem1 = Q.prove (
`(!t tcn E tp l.
  ~MEM (name_tcn tcn) (MAP domEB E) /\ 
  tkind E (substs_typevar_typexpr (MAP (\tp. (tp_to_tv tp,TE_constr [] TC_unit)) l) t) ==>
  ~abbrev_occurs tcn t) /\
 (!ts tcn E tp l.
  ~MEM (name_tcn tcn) (MAP domEB E) /\ 
  EVERY (\t. tkind E (substs_typevar_typexpr (MAP (\tp. (tp_to_tv tp,TE_constr [] TC_unit)) l) t)) ts ==>
  EVERY (\t. ~abbrev_occurs tcn t) ts)`,
Induct THEN SRW_TAC [] [substs_typevar_typexpr_def, Eok_def, abbrev_occurs_def, EVERY_MAP, o_DEF] THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 CCONTR_TAC THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def, COND_EXPAND_EQ] THEN
     IMP_RES_TAC lookup_dom_thm THEN FULL_SIMP_TAC (srw_ss()) [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC []]);


local

val lem2 = Q.prove (
`(!t x y tcn. abbrev_occurs tcn (shiftt x y t) = abbrev_occurs tcn t) /\
 (!ts x y tcn. EXISTS (\t. abbrev_occurs tcn (shiftt x y t)) ts = EXISTS (\t. abbrev_occurs tcn t) ts)`,
Induct THEN SRW_TAC [] [abbrev_occurs_def, shiftt_def, EXISTS_MAP]);

in

val abbrev_no_occur_thm = Q.prove (
`!E tpo tcn t E'. Eok E /\ (remove_abbrev E = (SOME (EB_ta tpo tcn t),E')) ==> ~abbrev_occurs tcn t`,
recInduct (fetch "-" "remove_abbrev_ind") THEN
SRW_TAC [] [remove_abbrev_def, LAMBDA_PROD2, LET_THM, Eok_def] THEN
Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THENL
[Cases_on `tpo` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [abbrev_occur_lem1],
 Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN SRW_TAC [] [] THEN METIS_TAC [lem2],
 METIS_TAC [ok_ok_thm],
 Cases_on `tpo` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [ok_ok_thm],
 Cases_on `tpo` THEN Cases_on `tl` THEN Cases_on `tc` THEN Cases_on `l` THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
     METIS_TAC [ok_ok_thm],
 Cases_on `tc` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [ok_ok_thm],
 METIS_TAC [ok_ok_thm]]);


end;

val remove_abbrev_lem1 = Q.prove (
`!E tpo tcn t E'. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) /\ 
                 MEM (name_tcn typeconstr_name) (MAP domEB E') ==>
                 MEM (name_tcn typeconstr_name) (MAP domEB E)`,
Induct THEN SRW_TAC [] [remove_abbrev_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, domEB_def, LET_THM, LAMBDA_PROD2] THEN
Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [domEB_def] THEN Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN
SRW_TAC [] []);

val remove_abbrev_lem2 = Q.prove (
`!E tpo tcn t E' tcn2 EB. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) /\ ~(tcn = tcn2) /\
       (lookup E (name_tcn tcn2) = SOME EB) ==>
       (lookup E' (name_tcn tcn2) = SOME EB)`,
Induct THEN SRW_TAC [] [remove_abbrev_def, lookup_def] THENL
[Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, domEB_def, LET_THM, LAMBDA_PROD2] THEN
     Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [lookup_def] THEN
     FULL_SIMP_TAC (srw_ss()) [domEB_def],
 Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, domEB_def, LET_THM, LAMBDA_PROD2] THEN
     Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [lookup_def] THEN 
     FULL_SIMP_TAC (srw_ss()) [domEB_def] THEN Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN
     SRW_TAC [] [] THEN METIS_TAC [],
 Cases_on `h` THEN 
     FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, domEB_def, LET_THM, LAMBDA_PROD2, shiftEB_add_thm] THEN
     Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [lookup_def] THEN 
     FULL_SIMP_TAC (srw_ss()) [domEB_def, shiftEB_add_thm]]);


local

val lem3 = Q.prove (
`!E tpo tcn t E' idx. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) /\ 
       idx_bound E idx ==> idx_bound E' idx`,
Induct THEN SRW_TAC [] [remove_abbrev_def, idx_bound_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, idx_bound_def, LET_THM, LAMBDA_PROD2] THEN
Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [idx_bound_def] THEN
Cases_on `idx` THEN FULL_SIMP_TAC (srw_ss()) [idx_bound_def] THEN Cases_on `EB` THEN 
FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN SRW_TAC [] []);

val lem4 = Q.prove (
`!E tpo tcn t E'. 
     Eok E /\ (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) /\
     (lookup E (name_tcn tcn) = SOME (EB_ta (TPS_nary tpo) tcn t)) ==>
     tkind E' (substs_typevar_typexpr (MAP (\tp. (tp_to_tv tp,TE_constr [] TC_unit)) tpo) t)`,
Induct THEN SRW_TAC [] [lookup_def, remove_abbrev_def] THEN 
FULL_SIMP_TAC (srw_ss()) [domEB_def, Eok_def, remove_abbrev_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [domEB_def, Eok_def, remove_abbrev_def, LET_THM, LAMBDA_PROD2, shiftEB_add_thm] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THENL
[Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `EB2` THEN 
     FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN 
     SRW_TAC [] [] THEN Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN 
     FULL_SIMP_TAC (srw_ss()) [shiftEB_def, shiftt_11] THEN SRW_TAC [] [] THEN 
     `tkind (EB_tv::r) 
            (shiftt 0 1 (substs_typevar_typexpr (MAP (\tp. (tp_to_tv tp,TE_constr [] TC_unit)) tpo) t1))` by
         METIS_TAC [weak_one_tv_ok_thm, APPEND, num_tv_def, APPEND_ASSOC, shiftE_def] THEN
     FULL_SIMP_TAC (srw_ss()) [subst_shiftt_com_lem, MAP_MAP, shiftt_def],
 METIS_TAC [ok_ok_thm],
 Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def],
 Cases_on `t'` THEN Cases_on `t0` THEN Cases_on `t1` THEN Cases_on `l` THEN 
     FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN Cases_on `l'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
     METIS_TAC [ok_ok_thm],
 Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [ok_ok_thm],
 Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
     `Eok (EB_td t' n::r)` by (SRW_TAC [] [Eok_def] THEN METIS_TAC [remove_abbrev_lem1, ok_ok_thm]) THEN
     `~MEM EB_tv [EB_td t' n]` by SRW_TAC [] [] THEN METIS_TAC [weak_ok_thm, APPEND],
 Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
     `Eok (EB_tr t' n l::r)` by (SRW_TAC [] [Eok_def] THEN METIS_TAC [remove_abbrev_lem1, ok_ok_thm]) THEN
     `~MEM EB_tv [EB_tr t' n l]` by SRW_TAC [] [] THEN METIS_TAC [weak_ok_thm, APPEND],
 METIS_TAC [ok_ok_thm]]);

in

val teq_remove_abbrev_ok_thm = Q.prove (
`(!E. Eok E ==> !tpo tcn t E'. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) ==> Eok E') /\
 (!E tc k. (typeconstr_kind E tc = SOME k) ==> 
           !tpo tcn t E'. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) ==>
           if (TC_name tcn = tc) /\ (LENGTH tpo = k) then
             EBok E' (EB_ta (TPS_nary tpo) tcn t)
           else
             (typeconstr_kind E' tc = SOME k)) /\
 (!E ts. tsok E ts ==> !tpo tcn t E'. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t),E')) ==> 
         Eok E') /\
 (!E tps t. ntsok E tps t ==> !tpo tcn t' E'. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t'),E')) ==>
            Eok E') /\
 (!E t. tkind E t ==> !tpo tcn t' E'. (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t'),E')) ==>
        tkind E' (apply_abbrev tpo tcn t' t))`,
HO_MATCH_MP_TAC Eok_ind THEN SRW_TAC [] [Eok_def] THEN 
FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, LET_THM, LAMBDA_PROD2, apply_abbrev_def] THENL
[Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN SRW_TAC [] [Eok_def] THEN
     Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [],
 FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN Cases_on `t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
     METIS_TAC [ok_ok_thm],
 FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN Cases_on `t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
     METIS_TAC [ok_ok_thm],
 FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN Cases_on `t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
     METIS_TAC [ok_ok_thm],
 Cases_on `E'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Eok_def] THEN
     Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN 
     METIS_TAC [remove_abbrev_lem1],
 METIS_TAC [ok_ok_thm], 
 Cases_on `E'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Eok_def] THEN
     Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN 
     METIS_TAC [remove_abbrev_lem1],
 METIS_TAC [ok_ok_thm], 
 Cases_on `lookup E (name_tcn typeconstr_name)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THENL
     [IMP_RES_TAC lookup_name_thm THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
          IMP_RES_TAC remove_lookup_lem THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN 
          SRW_TAC [] [EBok_def, Eok_def] THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ] THEN METIS_TAC [lem4],
      IMP_RES_TAC lookup_name_thm THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
          Cases_on `tcn = typeconstr_name` THEN SRW_TAC [] [] THEN IMP_RES_TAC remove_abbrev_lem2 THEN 
          SRW_TAC [] [] THEN
          IMP_RES_TAC remove_lookup_lem THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN 
          FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ]],
 FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN METIS_TAC [ok_ok_thm, APPEND],
 METIS_TAC [ok_ok_thm],
 SRW_TAC [] [Eok_def] THEN METIS_TAC [lem3],
 SRW_TAC [] [Eok_def],
 SRW_TAC [] [Eok_def, EVERY_MAP] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM], 
 SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [Eok_def, EVERY_MAP] THEN 
     FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN MATCH_MP_TAC tvar_subst_ok_lem THEN 
     SRW_TAC [] [MAP_FST_ZIP, EVERY_REVERSE] THEN SRW_TAC [] [GSYM EVERY_MAP] THEN SRW_TAC [] [MAP_SND_ZIP] THEN
     SRW_TAC [] [EVERY_MAP] THEN SRW_TAC [] [EVERY_MEM] THEN FULL_SIMP_TAC (srw_ss()) [EBok_def, Eok_def] THEN
     Q.EXISTS_TAC `MAP (\x. (tp_to_tv x, TE_constr [] TC_unit)) tpo` THEN SRW_TAC [] [MAP_MAP, ETA_THM] THEN
     METIS_TAC []]);

end;

val type_substs_com_thm = Q.prove (
`(!t subs1 subs2. 
  (!tv. MEM tv (ftv_typexpr t) ==> MEM tv (MAP FST subs1))
   ==>
  (substs_typevar_typexpr subs2 (substs_typevar_typexpr subs1 t) = 
   substs_typevar_typexpr (MAP (\(tv,t). (tv,substs_typevar_typexpr subs2 t)) subs1) t)) /\
 (!tlist subs1 subs2. 
  (!tv. MEM tv (FLAT (MAP ftv_typexpr tlist)) ==> MEM tv (MAP FST subs1))
   ==>
  (MAP (\t. substs_typevar_typexpr subs2 (substs_typevar_typexpr subs1 t)) tlist = 
   MAP (\t. substs_typevar_typexpr (MAP (\(tv,t). (tv,substs_typevar_typexpr subs2 t)) subs1) t)
       tlist))`,
Induct THEN SRW_TAC [] [substs_typevar_typexpr_def, ftv_typexpr_def, MAP_MAP] THENL 
[Cases_on `list_assoc t subs1` THEN 
         SRW_TAC [] [substs_typevar_typexpr_def, list_assoc_map, LAMBDA_PROD2] THEN
         IMP_RES_TAC mem_list_assoc THEN FULL_SIMP_TAC (srw_ss()) [],
 METIS_TAC [],
 METIS_TAC []]);

local

val lem1 = Q.prove (
`!tpo typexpr_list. (LENGTH tpo = LENGTH typexpr_list) ==> 
   (MAP (\p. tp_to_tv (FST p)) (ZIP (tpo,typexpr_list)) = MAP tp_to_tv tpo)`, 
METIS_TAC [MAP_MAP, MAP_FST_ZIP, ETA_THM]);

in

val type_subst_apply_abbrev_thm = Q.prove (
`!substs t' tpo tcn t. (!tv. MEM tv (ftv_typexpr t) ==> MEM tv (MAP tp_to_tv tpo)) ==> 
                       (apply_abbrev tpo tcn t (substs_typevar_typexpr substs t') = 
                       substs_typevar_typexpr (MAP (\s. (FST s, apply_abbrev tpo tcn t (SND s))) substs)
                                              (apply_abbrev tpo tcn t t'))`,
recInduct substs_typevar_typexpr_ind THEN SRW_TAC [] [] THEN 
SRW_TAC [] [apply_abbrev_def, substs_typevar_typexpr_def, MAP_MAP, MAP_EQ, ZIP_MAP] THEN
FULL_SIMP_TAC (srw_ss()) [ftv_typexpr_def, MEM_FLAT, EXISTS_MAP] THEN 
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM] THENL
[Cases_on `list_assoc typevar sub` THEN SRW_TAC [] [apply_abbrev_def, list_assoc_map],
 MP_TAC ((SIMP_RULE (srw_ss()) [MAP_MAP] o 
               Q.SPECL [`t`, 
                        `MAP (\p. (tp_to_tv (FST p),apply_abbrev tpo tcn t (SND p))) 
                             (ZIP (tpo,typexpr_list))`,
                        `MAP (\s. (FST s,apply_abbrev tpo tcn t (SND s))) sub`])
              (hd (CONJUNCTS type_substs_com_thm))) THEN
     SRW_TAC [] [lem1] THEN
     MATCH_MP_TAC (METIS_PROVE [] ``!x y f z. (x = y) ==> (f x z = f y z)``) THEN
     SRW_TAC [] [MAP_EQ] THEN
     `MEM (SND p) typexpr_list` by METIS_TAC [MEM_ZIP, SND, MEM_EL] THEN
     METIS_TAC []]);

end;

local

val lem1 = Q.prove (
`!l1 l2.
 tkind E (substs_typevar_typexpr (MAP (\x. (FST x,TE_constr [] TC_unit)) l1) (TE_var typevar)) /\
 (MAP FST l1 = MAP FST l2) /\
 EVERY (\(t,t'). JTeq E t t') (ZIP (MAP SND l1,MAP SND l2)) ==>
 JTeq E (substs_typevar_typexpr l1 (TE_var typevar)) (substs_typevar_typexpr l2 (TE_var typevar))`,
Induct THEN SRW_TAC [] [substs_typevar_typexpr_def, list_assoc_def] THEN1 METIS_TAC [JTeq_rules] THEN
Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [substs_typevar_typexpr_def] THEN
Cases_on `h` THEN Cases_on `h'` THEN FULL_SIMP_TAC (srw_ss()) [list_assoc_def]);

in

val teq_substs_same_thm = Q.store_thm ("teq_substs_same_thm",
`!l1 t l2. tkind E (substs_typevar_typexpr (MAP (\x. (FST x, TE_constr [] TC_unit)) l1) t) /\
           (MAP FST l1 = MAP FST l2) /\ 
           EVERY (\(t, t'). JTeq E t t') (ZIP (MAP SND l1, MAP SND l2)) ==>
           JTeq E (substs_typevar_typexpr l1 t) (substs_typevar_typexpr l2 t)`,
recInduct substs_typevar_typexpr_ind THEN SRW_TAC [] [lem1, substs_typevar_typexpr_def] THENL
[METIS_TAC [JTeq_rules],
 FULL_SIMP_TAC (srw_ss()) [Eok_def],
 FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [JTeq_rules],
 FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN
     ONCE_REWRITE_TAC [JTeq_cases] THEN NTAC 5 DISJ2_TAC THEN DISJ1_TAC THEN
     Q.EXISTS_TAC `ZIP (MAP (\typexpr_. substs_typevar_typexpr sub typexpr_) typexpr_list, 
                        MAP (\typexpr_. substs_typevar_typexpr l2 typexpr_) typexpr_list)` THEN
     SRW_TAC [] [MAP_FST_ZIP, MAP_SND_ZIP, LENGTH_MAP, LENGTH_ZIP, ZIP_MAP, MAP_ZIP_SAME, EVERY_MAP] THEN
     FULL_SIMP_TAC (srw_ss()) [EVERY_MEM, MEM_MAP] THEN METIS_TAC [],
 FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN
     ONCE_REWRITE_TAC [JTeq_cases] THEN NTAC 6 DISJ2_TAC THEN 
     MAP_EVERY Q.EXISTS_TAC [`ZIP (MAP (\typexpr_. substs_typevar_typexpr sub typexpr_) typexpr_list, 
                                   MAP (\typexpr_. substs_typevar_typexpr l2 typexpr_) typexpr_list)`,
                             `typeconstr`] THEN 
     SRW_TAC [] [MAP_FST_ZIP, MAP_SND_ZIP, LENGTH_MAP, LENGTH_ZIP, ZIP_MAP, MAP_ZIP_SAME, EVERY_MAP] THEN
     FULL_SIMP_TAC (srw_ss()) [EVERY_MEM, MEM_MAP] THEN METIS_TAC []]);

end;

local

val teq_refl_lem = Q.prove (
`!E t. JTeq E t t = tkind E t`,
METIS_TAC [JTeq_rules, teq_ok_thm]);

val lem1 = Q.prove (
`(MAP f (MAP FST l) = MAP FST (MAP (\x. (f (FST x), f (SND x))) l)) /\
 (MAP f (MAP SND l) = MAP SND (MAP (\x. (f (FST x), f (SND x))) l))`,
SRW_TAC [] [MAP_MAP]);

val lem2 = Q.prove (
`(MAP f (MAP FST l) = MAP FST (MAP (\x. (f (FST x), SND x)) l))`,
SRW_TAC [] [MAP_MAP]);

val lem3 = Q.prove (
`!t f l. (ftv_typexpr (substs_typevar_typexpr (MAP (\z. (f z, TE_constr [] TC_unit)) l) t) = []) ==>
         (!tv. MEM tv (ftv_typexpr t) ==> MEM tv (MAP f l))`,
recInduct ftv_typexpr_ind THEN SRW_TAC [] [ftv_typexpr_def, substs_typevar_typexpr_def] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_FLAT, MAP_MAP, EXISTS_MAP, FLAT_EQ_EMPTY, EVERY_MAP] THEN 
FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM, EVERY_MEM] THENL
[Cases_on `list_assoc typevar (MAP (\z. (f z,TE_constr [] TC_unit)) l)` THEN 
         FULL_SIMP_TAC (srw_ss()) [ftv_typexpr_def] THEN IMP_RES_TAC list_assoc_mem THEN
         FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN METIS_TAC [],
 METIS_TAC [],
 METIS_TAC []]);

val lem4 = Q.prove (
`!l. EVERY (\x. tkind E (FST x)) l ==>
     EVERY (\s. ftv_typexpr (SND s) = []) (MAP (\z. (SND z,FST z)) l)`,
Induct THEN SRW_TAC [] [] THEN METIS_TAC [ftv_lem1]);

val lem5 = Q.prove (
`!l.
 (!t E.
    tkind E (substs_typevar_typexpr (MAP (\z. (SND z,TE_constr [] TC_unit)) l) t) ==>
    !tv. MEM tv (ftv_typexpr t) ==> MEM tv (MAP SND l)) /\
 (!ts E.
    EVERY (\t. tkind E (substs_typevar_typexpr (MAP (\z. (SND z,TE_constr [] TC_unit)) l) t)) ts ==>
    !tv. MEM tv (FLAT (MAP ftv_typexpr ts)) ==> MEM tv (MAP SND l))`,
STRIP_TAC THEN Induct THEN 
SRW_TAC [] [Eok_def, ftv_typexpr_def, substs_typevar_typexpr_def, EVERY_MAP, ETA_THM] THENL
[Cases_on `list_assoc t (MAP (\z. (SND z,TE_constr [] TC_unit)) l)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN IMP_RES_TAC list_assoc_mem THEN 
     FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN SRW_TAC [] [] THEN METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC []]);

val lem6 = Q.prove (
`!E tpo tcn t' E'. Eok E /\ (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t'),E')) ==>
 (lookup E' (name_tcn tcn) = NONE)`,
Induct THEN SRW_TAC [] [remove_abbrev_def, lookup_def, domEB_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss()) [remove_abbrev_def, lookup_def, domEB_def] THEN IMP_RES_TAC Eok_lem1 THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THENL
[Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [lookup_def, domEB_def] THEN
     Cases_on `EB` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN SRW_TAC [] [],
 Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [lookup_def, domEB_def] THEN
     METIS_TAC [remove_lookup_lem, lookup_dom_thm],
 Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [lookup_def, domEB_def] THEN
     METIS_TAC [remove_lookup_lem, lookup_dom_thm],
 METIS_TAC [lookup_dom_thm]]);

val lem7 = Q.prove (
`!tpo t_t'_list.
 (LENGTH tpo = LENGTH t_t'_list) ==>
 (MAP (\tp. (tp_to_tv tp,TE_constr [] TC_unit)) tpo =
  MAP (\p. (tp_to_tv (FST p),TE_constr [] TC_unit)) (ZIP (tpo,t_t'_list)))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `t_t'_list` THEN FULL_SIMP_TAC (srw_ss()) []);

val lem8 = Q.prove (
`!E tpo t t_t'_list.
  (LENGTH tpo = LENGTH t_t'_list) /\ ntsok E tpo t /\ EVERY (\x. JTeq E (FST x) (SND x)) t_t'_list ==>
  JTeq E (substs_typevar_typexpr (MAP (\p. (tp_to_tv (FST p), (FST (SND p)))) (ZIP (tpo,t_t'_list))) t)
         (substs_typevar_typexpr (MAP (\p. (tp_to_tv (FST p), (SND (SND p)))) (ZIP (tpo,t_t'_list))) t)`,
SRW_TAC [] [Eok_def] THEN MATCH_MP_TAC teq_substs_same_thm THEN
SRW_TAC [] [MAP_FST_ZIP, MAP_SND_ZIP, MAP_MAP, MAP_ZIP_SAME, ZIP_MAP, ETA_THM, LAMBDA_PROD2] THEN
METIS_TAC [lem7]);

in

val apply_abbrev_str_thm = Q.prove (
`!E t1 t2. JTeq E t1 t2 ==> !tpo tcn t E'.
            (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t), E')) ==>
            JTeq E' (apply_abbrev tpo tcn t t1) (apply_abbrev tpo tcn t t2)`,
RULE_INDUCT_TAC JTeq_ind [remove_abbrev_def, apply_abbrev_def, teq_refl_lem]
[([``"JTeq_sym"``, ``"JTeq_trans"``, ``"JTeq_arrow"``], METIS_TAC [JTeq_rules]),
 ([``"JTeq_refl"``],  METIS_TAC [teq_remove_abbrev_ok_thm]),
 ([``"JTeq_tuple"``],
  SRW_TAC [] [lem1] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN 
      FULL_SIMP_TAC (srw_ss()) [GSYM EVERY_MEM] THEN MATCH_MP_TAC (List.nth (CONJUNCTS JTeq_rules, 5)) THEN
      SRW_TAC [] [EVERY_MAP]),
 ([``"JTeq_expand"``],
  SRW_TAC [] [] THEN SRW_TAC [] [] THENL
      [IMP_RES_TAC remove_lookup_lem THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN 
           FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN SRW_TAC [] [ZIP_MAP, MAP_ZIP_SAME] THEN
           SRW_TAC [] [MAP_MAP, tp_to_tv_def] THEN IMP_RES_TAC lookup_ok_thm THEN
           FULL_SIMP_TAC (srw_ss()) [EBok_def, Eok_def] THEN IMP_RES_TAC teq_remove_abbrev_ok_thm THEN
           IMP_RES_TAC lem4 THEN FULL_SIMP_TAC (srw_ss()) [MAP_MAP] THEN
           `EVERY (\s. ftv_typexpr (SND s) = [])
                  (MAP (\z. (tp_to_tv (TP_var (SND z)),TE_constr [] TC_unit)) t_typevar_list)`
                 by SRW_TAC [] [EVERY_MAP, ftv_typexpr_def] THEN
           FULL_SIMP_TAC (srw_ss()) [tp_to_tv_def] THEN
           `!tv. MEM tv (ftv_typexpr t) ==> MEM tv (MAP tp_to_tv (MAP (\z. TP_var (SND z)) t_typevar_list))`
                by (SRW_TAC [] [MAP_MAP, tp_to_tv_def] THEN METIS_TAC [lem5]) THEN
           FULL_SIMP_TAC (srw_ss()) [type_subst_apply_abbrev_thm] THEN
           IMP_RES_TAC abbrev_no_occur_thm THEN 
           FULL_SIMP_TAC (srw_ss()) [apply_abbrev_no_occur_thm, tp_to_tv_def, MAP_MAP, apply_abbrev_def] THEN
           MATCH_MP_TAC (List.nth (CONJUNCTS JTeq_rules, 0)) THEN
           MATCH_MP_TAC tvar_subst_ok_lem THEN SRW_TAC [] [MAP_MAP, EVERY_REVERSE, EVERY_MAP] THEN
           Q.EXISTS_TAC `MAP (\z. (SND z,TE_constr [] TC_unit)) t_typevar_list` THEN SRW_TAC [] [MAP_MAP] THEN
           FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN RES_TAC THEN
           IMP_RES_TAC teq_remove_abbrev_ok_thm,
       IMP_RES_TAC remove_lookup_lem THEN IMP_RES_TAC lookup_ok_thm THEN
           FULL_SIMP_TAC (srw_ss()) [EBok_def, Eok_def] THEN SRW_TAC [] [] THEN IMP_RES_TAC ftv_lem1 THEN
           FULL_SIMP_TAC (srw_ss()) [MAP_MAP, tp_to_tv_def] THEN IMP_RES_TAC lem3 THEN IMP_RES_TAC lem4 THEN
           SRW_TAC [] [type_subst_apply_abbrev_thm, MAP_MAP] THEN
           MATCH_MP_TAC ((SIMP_RULE (srw_ss()) [MAP_MAP] o
                          Q.SPEC `MAP (\x. (apply_abbrev tpo tcn t' (FST x), SND x)) t_typevar_list`)
                         (List.nth (CONJUNCTS JTeq_rules, 3))) THEN
           SRW_TAC [] [EVERY_MAP] THEN IMP_RES_TAC teq_remove_abbrev_ok_thm THENL
           [`lookup E' (name_tcn typeconstr_name) = 
                     SOME (EB_ta (TPS_nary (MAP (\z. TP_var (SND z)) t_typevar_list)) typeconstr_name t)`
                               by METIS_TAC [remove_abbrev_lem2] THEN
                IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def, Eok_def] THEN
                METIS_TAC [lem6, abbrev_occur_lem1, lookup_dom_thm, apply_abbrev_no_occur_thm],
            FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN METIS_TAC [teq_remove_abbrev_ok_thm],
            Cases_on `tcn = typeconstr_name` THENL
                [SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
                     METIS_TAC [LENGTH_MAP],
                 `lookup E' (name_tcn typeconstr_name) = 
                         SOME (EB_ta (TPS_nary (MAP (\z. TP_var (SND z)) t_typevar_list)) typeconstr_name t)`
                                    by METIS_TAC [remove_abbrev_lem2] THEN
                     IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def, Eok_def] THEN
                     METIS_TAC [lem6, abbrev_occur_lem1, lookup_dom_thm, apply_abbrev_no_occur_thm]],
            FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN METIS_TAC [teq_remove_abbrev_ok_thm]]]),
 ([``"JTeq_constr"``],
  SRW_TAC [] [lem1] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN 
      FULL_SIMP_TAC (srw_ss()) [GSYM EVERY_MEM] THEN SRW_TAC [] [] THENL
      [IMP_RES_TAC teq_remove_abbrev_ok_thm THEN POP_ASSUM MP_TAC THEN
           SRW_TAC [] [EBok_def] THEN
           `EVERY (\x. JTeq E' (FST x) (SND x)) 
                  (MAP (\x. (apply_abbrev tpo tcn t (FST x), apply_abbrev tpo tcn t (SND x))) t_t'_list)`
                      by SRW_TAC [] [EVERY_MAP] THEN
           IMP_RES_TAC lem8 THEN POP_ASSUM MP_TAC THEN SRW_TAC [] [MAP_MAP, ZIP_MAP],
       MATCH_MP_TAC (List.nth (CONJUNCTS JTeq_rules, 6)) THEN SRW_TAC [] [EVERY_MAP] THEN 
           IMP_RES_TAC teq_remove_abbrev_ok_thm THEN METIS_TAC []])]);

end;

local

val lem1 = Q.prove (
`!l1 l2 P. (LENGTH l1 = LENGTH l2) ==> (EVERY (\x. P (FST x)) (ZIP (l1,l2)) = EVERY (\x. P x) l1)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) []);

val lem2 = Q.prove (
`!tpo ts l tcn t'. (LENGTH ts = LENGTH tpo) ==>
            (MAP (\p. (tp_to_tv (FST p),apply_abbrev l tcn t' (SND p))) (ZIP (tpo,ts)) =
             MAP (\p. (tp_to_tv (SND p),apply_abbrev l tcn t' (FST p))) (ZIP (ts,tpo)))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `ts` THEN FULL_SIMP_TAC (srw_ss()) []);

in

val abbrev_eq_thm = Q.prove (
`(!t tpo tcn t' E. tkind E t /\ (lookup E (name_tcn tcn) = SOME (EB_ta (TPS_nary tpo) tcn t')) ==> 
                   JTeq E t (apply_abbrev tpo tcn t' t)) /\
 (!ts tpo tcn t' E. EVERY (\x. tkind E x) ts /\ 
                    (lookup E (name_tcn tcn) = SOME (EB_ta (TPS_nary tpo) tcn t')) ==> 
                    EVERY (\t. JTeq E t (apply_abbrev tpo tcn t' t)) ts)`,
Induct THEN SRW_TAC [] [apply_abbrev_def, Eok_def] THENL
[`tkind E (TE_idxvar n n0)` by SRW_TAC [] [Eok_def] THEN METIS_TAC [JTeq_rules],
 METIS_TAC [JTeq_rules],
 MATCH_MP_TAC ((SIMP_RULE (srw_ss()) [MAP_FST_ZIP, MAP_SND_ZIP, LENGTH_MAP] o
                Q.SPEC `ZIP (ts, MAP (\a. apply_abbrev tpo tcn t' a) ts)`)
               (List.nth (CONJUNCTS JTeq_rules, 5))) THEN
 SRW_TAC [] [LENGTH_MAP, LENGTH_ZIP, ZIP_MAP, MAP_ZIP_SAME, EVERY_MAP],
 FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ] THEN
     IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ, EBok_def, Eok_def] THEN
     ONCE_REWRITE_TAC [JTeq_cases] THEN SRW_TAC [] [] THEN 
     NTAC 2 DISJ2_TAC THEN DISJ1_TAC THEN 
     Q.EXISTS_TAC `TE_constr (MAP (apply_abbrev tpo tcn t') ts) (TC_name tcn)` THEN
     SRW_TAC [] [] THENL
     [ONCE_REWRITE_TAC [JTeq_cases] THEN NTAC 6 DISJ2_TAC THEN SRW_TAC [] [] THEN
          Q.EXISTS_TAC `ZIP (ts, MAP (apply_abbrev tpo tcn t') ts)` THEN 
          SRW_TAC [] [MAP_FST_ZIP, MAP_SND_ZIP, LENGTH_ZIP, ZIP_MAP, MAP_ZIP_SAME, EVERY_MAP, Eok_def],
      ONCE_REWRITE_TAC [JTeq_cases] THEN NTAC 3 DISJ2_TAC THEN DISJ1_TAC THEN SRW_TAC [] [] THEN
          Q.EXISTS_TAC `ZIP (MAP (apply_abbrev tpo tcn t') ts, MAP tp_to_tv tpo)` THEN
          SRW_TAC [] [MAP_FST_ZIP, ZIP_MAP, LENGTH_ZIP, EVERY_MAP, lem1, MAP_MAP, tp_to_tv_thm, ETA_THM,
                      MAP_SND_ZIP] THENL
          [METIS_TAC [lem2],
           FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [teq_ok_thm]]],
 MATCH_MP_TAC ((SIMP_RULE (srw_ss()) [MAP_FST_ZIP, MAP_SND_ZIP, LENGTH_MAP] o
                Q.SPEC `ZIP (ts, MAP (\a. apply_abbrev tpo tcn t' a) ts)`)
               (List.nth (CONJUNCTS JTeq_rules, 6))) THEN
     SRW_TAC [] [LENGTH_MAP, LENGTH_ZIP, ZIP_MAP, MAP_ZIP_SAME, EVERY_MAP]]);

end;


val not_abbrev_lem = Q.prove (
`!E ts1 tc2 tcn tpo t E'. Eok E /\ ~is_abbrev_tc E (TE_constr ts1 tc2) /\ 
                           (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t), E')) ==>
                           ~(tc2 = TC_name tcn)`,
Cases_on `tc2` THEN SRW_TAC [] [is_abbrev_tc_def] THEN Cases_on `lookup E (name_tcn t')` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1 METIS_TAC [remove_lookup_lem, NOT_SOME_NONE] THEN Cases_on `x` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN IMP_RES_TAC remove_lookup_lem THEN CCONTR_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [environment_binding_distinct]);
                           

val alg_eq_step_def = Define 
`alg_eq_step E t1 t2 = 
   case t1 of
      TE_var tv -> F
   || TE_idxvar i1 i2 -> (t2 = TE_idxvar i1 i2)
   || TE_any -> F
   || TE_arrow t1' t2' -> (?t1'' t2''. (t2 = TE_arrow t1'' t2'') /\ JTeq E t1' t1'' /\ JTeq E t2' t2'')
   || TE_tuple ts -> 
       (?ts'. (t2 = TE_tuple ts') /\ (LENGTH ts = LENGTH ts') /\ (LENGTH ts >= 2) /\ 
              EVERY (\(t, t'). JTeq E t t') (ZIP (ts, ts')))
   || TE_constr ts tc ->
       (?ts'. (t2 = TE_constr ts' tc) /\ (LENGTH ts = LENGTH ts') /\ 
              (SOME (LENGTH ts) = typeconstr_kind E tc) /\
              EVERY (\(t, t'). JTeq E t t') (ZIP (ts, ts')))`;
         
val apply_abbrev_weak_thm = Q.prove ( 
`!E E' tpo tcn t1 t2. 
            tkind E t1 /\ tkind E t2 /\
            (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t), E')) /\ 
            JTeq E' (apply_abbrev tpo tcn t t1) (apply_abbrev tpo tcn t t2) ==>
            JTeq E t1 t2`,
SRW_TAC [] [] THEN `Eok E` by METIS_TAC [ok_ok_thm] THEN 
MAP_EVERY IMP_RES_TAC [remove_lookup_lem, abbrev_eq_thm, remove_abbrev_teq_weak_thm] THEN
METIS_TAC [JTeq_rules]);


local

val tac = 
Q.PAT_ASSUM `EVERY A B` MP_TAC THEN SRW_TAC [] [LENGTH_MAP, ZIP_MAP, EVERY_MAP] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_MEM, LAMBDA_PROD2] THEN 
IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def, EVERY_MEM] THEN
`!a. MEM a (ZIP (l, l')) ==> tkind E (FST a) /\ tkind E (SND a)` by 
          (SRW_TAC [] [MEM_ZIP] THEN SRW_TAC [] [] THEN METIS_TAC [MEM_EL]) THEN
METIS_TAC [apply_abbrev_weak_thm];

in

val alg_eq_step_abbrev_lem = Q.prove (
`!E t1 t2 E' tpo tcn t. JTeq E t1 t2 /\ JTeq E' (apply_abbrev tpo tcn t t1) (apply_abbrev tpo tcn t t2) /\
 (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t), E')) /\
 ~is_abbrev_tc E t1 /\ ~is_abbrev_tc E t2 /\
 alg_eq_step E' (apply_abbrev tpo tcn t t1) (apply_abbrev tpo tcn t t2) ==>
 alg_eq_step E t1 t2`,
REWRITE_TAC [alg_eq_step_def] THEN Cases_on `t1` THEN SRW_TAC [] [apply_abbrev_def, COND_EXPAND_EQ] THEN
`Eok E` by METIS_TAC [teq_ok_thm, ok_ok_thm] THENL
[Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) [apply_abbrev_def, COND_EXPAND_EQ] THEN
     METIS_TAC [not_abbrev_lem],
 Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) [apply_abbrev_def, COND_EXPAND_EQ] THEN 
     IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN
     METIS_TAC [apply_abbrev_weak_thm, not_abbrev_lem],
 Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) [apply_abbrev_def, COND_EXPAND_EQ] THEN 
     SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THENL 
     [tac,
      METIS_TAC [not_abbrev_lem]],
 Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) [apply_abbrev_def, COND_EXPAND_EQ] THEN 
     SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THEN 
     METIS_TAC [not_abbrev_lem],
 Cases_on `t2` THEN FULL_SIMP_TAC (srw_ss()) [apply_abbrev_def, COND_EXPAND_EQ] THEN 
     SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_MAP] THENL 
     [METIS_TAC [not_abbrev_lem],
      IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def],
      tac,
      IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def],
      tac,
      METIS_TAC [not_abbrev_lem],
      IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def],
      tac,
      IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def],
      tac]]);

end;

local

val lem1 = Q.prove (
`!E tcn tpo tcn' t. (num_abbrev E = 0) ==> ~(lookup E (name_tcn tcn) = SOME (EB_ta tpo tcn' t))`,
Induct THEN SRW_TAC [] [lookup_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss ()) [num_abbrev_def, lookup_def, domEB_def, shiftEB_add_thm] THEN1
(Cases_on `EB2` THEN FULL_SIMP_TAC (srw_ss ()) [num_abbrev_def, lookup_def, domEB_def, shiftEB_def])
THEN METIS_TAC []);

in

val no_abbrev_thm = Q.prove (
`!E t1 t2. JTeq E t1 t2 ==> (num_abbrev E = 0) ==> (t1 = t2)`,
RULE_INDUCT_TAC JTeq_ind []
[([``"JTeq_expand"``], METIS_TAC [lem1]),
 ([``"JTeq_tuple"``, ``"JTeq_constr"``], SRW_TAC [] [EVERY_MEM, MAP_EQ])]);

end;

local

val lem1 = Q.prove (
`!E tpo tcn t' E' n EB. Eok E /\ (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t'),E')) /\
     (lookup E' n = SOME EB) /\ (~?vn. (n = name_vn vn)) ==> (lookup E n = SOME EB)`,
recInduct (fetch "-" "remove_abbrev_ind") THEN 
SRW_TAC [] [remove_abbrev_def, domEB_def, Eok_def, lookup_def] THEN
FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN IMP_RES_TAC Eok_lem1 THEN 
FULL_SIMP_TAC (srw_ss()) [LET_THM, LAMBDA_PROD2] THEN
IMP_RES_TAC ok_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [lookup_dom_thm, shiftEB_add_thm, lookup_def, domEB_def] THENL
[Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [],
 Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [],
 Cases_on `remove_abbrev E` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
     Cases_on `EB'` THEN FULL_SIMP_TAC (srw_ss()) [shiftEB_def] THEN SRW_TAC [] [] THEN
     METIS_TAC [],
 METIS_TAC [NOT_SOME_NONE, name_distinct],
 Cases_on `tpo` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [lookup_dom_thm, name_distinct],
 Cases_on `tpo` THEN Cases_on `tl` THEN Cases_on `tc` THEN Cases_on `l` THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [lookup_dom_thm, name_distinct],
 Cases_on `tc` THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN METIS_TAC [lookup_dom_thm, name_distinct]]);

in

val remove_abbrev_is_abbrev_lem = Q.prove (
`!E tpo tcn t E' t'. Eok E /\
            (remove_abbrev E = (SOME (EB_ta (TPS_nary tpo) tcn t), E')) /\ ~is_abbrev_tc E t' ==>
            ~is_abbrev_tc E' (apply_abbrev tpo tcn t t')`,
Cases_on `t'` THEN SRW_TAC [] [is_abbrev_tc_def, apply_abbrev_def] THENL
[Cases_on `lookup E (name_tcn tcn)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
     METIS_TAC [remove_lookup_lem, NOT_SOME_NONE] THEN Cases_on `x` THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN IMP_RES_TAC remove_lookup_lem THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [environment_binding_distinct],
 Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def] THEN
     Cases_on `lookup E' (name_tcn t')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
     Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
     Cases_on `lookup E (name_tcn t'')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
     IMP_RES_TAC lem1 THEN FULL_SIMP_TAC (srw_ss ()) [] THEN
     Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) []]);
end;

val alg_eq_step_complete_thm = Q.prove (
`!E t1 t2. ~is_abbrev_tc E t1 /\ ~is_abbrev_tc E t2 /\ JTeq E t1 t2 ==> alg_eq_step E t1 t2`,
STRIP_TAC THEN Induct_on `num_abbrev E` THENL
[SRW_TAC [] [] THEN `t1 = t2` by METIS_TAC [no_abbrev_thm] THEN SRW_TAC [] [alg_eq_step_def] THEN
    Cases_on `t1` THEN SRW_TAC [] [] THEN
    IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss ()) [Eok_def, EVERY_ZIP_SAME] THEN
    FULL_SIMP_TAC (srw_ss ()) [EVERY_MEM] THEN METIS_TAC [JTeq_rules],
 SRW_TAC [] [] THEN STRIP_ASSUME_TAC (Q.SPEC `E` remove_abbrev_result_thm) THEN1
    (IMP_RES_TAC remove_abbrev_num_abbrev_thm2 THEN FULL_SIMP_TAC (srw_ss()) []) THEN 
    IMP_RES_TAC remove_abbrev_num_abbrev_thm THEN `v = num_abbrev E'` by DECIDE_TAC THEN
    MATCH_MP_TAC alg_eq_step_abbrev_lem THEN Cases_on `tpo` THEN SRW_TAC [] [] THEN 
    IMP_RES_TAC remove_abbrev_is_abbrev_lem THEN METIS_TAC [apply_abbrev_str_thm, teq_ok_thm, ok_ok_thm]]);

val teq_fun1 = Q.prove (
`(!E t a. ~is_abbrev_tc E t ==> (JTeq E (TE_var a) t = F)) /\
(!E t i1 i2. ~is_abbrev_tc E t ==> (JTeq E (TE_idxvar i1 i2) t = (t = TE_idxvar i1 i2) /\ tkind E t)) /\
(!E t. ~is_abbrev_tc E t ==> (JTeq E TE_any t = F)) /\
(!E t t1 t2. ~is_abbrev_tc E t ==> 
      (JTeq E (TE_arrow t1 t2) t = ?t1' t2'. (t = TE_arrow t1' t2') /\ JTeq E t1 t1' /\ JTeq E t2 t2')) /\
(!E t ts. ~is_abbrev_tc E t ==> 
      (JTeq E (TE_tuple ts) t = 
       ?ts'. (t = TE_tuple ts') /\ (LENGTH ts = LENGTH ts') /\ (LENGTH ts >= 2) /\ 
             EVERY (\(t, t'). JTeq E t t') (ZIP (ts, ts')))) /\
(!E t ts tc. ~is_abbrev_tc E t /\ ~is_abbrev_tc E (TE_constr ts tc) ==>
      (JTeq E (TE_constr ts tc) t =
       ?ts'. (t = TE_constr ts' tc) /\ (LENGTH ts = LENGTH ts') /\ 
             (SOME (LENGTH ts) = typeconstr_kind E tc) /\
             EVERY (\(t, t'). JTeq E t t') (ZIP (ts, ts'))))`,
SRW_TAC [] [] THENL
[CCONTR_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN IMP_RES_TAC teq_ok_thm THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def],
 EQ_TAC THEN SRW_TAC [] [] THENL [ALL_TAC, METIS_TAC [teq_ok_thm], METIS_TAC [JTeq_rules]],
 CCONTR_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN IMP_RES_TAC teq_ok_thm THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def],
 EQ_TAC THEN SRW_TAC [] [] THENL [ALL_TAC, METIS_TAC [JTeq_rules]],
 EQ_TAC THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2] THENL 
     [ALL_TAC,
      IMP_RES_TAC JTeq_rules THEN METIS_TAC [MAP_FST_ZIP, MAP_SND_ZIP, LENGTH_ZIP, LENGTH_MAP]],
 EQ_TAC THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2] THENL 
     [ALL_TAC,
      IMP_RES_TAC JTeq_rules THEN METIS_TAC [MAP_FST_ZIP, MAP_SND_ZIP, LENGTH_ZIP, LENGTH_MAP]]] THEN
IMP_RES_TAC alg_eq_step_complete_thm THEN 
FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, alg_eq_step_def, LAMBDA_PROD2]);


val _ = save_thm ("teq_fun1", teq_fun1);

val teq_fun2 = Q.store_thm ("teq_fun2",
`(!E t a. ~is_abbrev_tc E t ==> (JTeq E t (TE_var a) = F)) /\
(!E t i1 i2. ~is_abbrev_tc E t ==> (JTeq E t (TE_idxvar i1 i2) = (t = TE_idxvar i1 i2) /\ tkind E t)) /\
(!E t. ~is_abbrev_tc E t ==> ((JTeq E t TE_any) = F)) /\
(!E t t1 t2. ~is_abbrev_tc E t ==> 
      (JTeq E t (TE_arrow t1 t2) = ?t1' t2'. (t = TE_arrow t1' t2') /\ JTeq E t1 t1' /\ JTeq E t2 t2')) /\
(!E t ts. ~is_abbrev_tc E t ==> 
      (JTeq E t (TE_tuple ts) = 
       ?ts'. (t = TE_tuple ts') /\ (LENGTH ts = LENGTH ts') /\ (LENGTH ts >= 2) /\ 
             EVERY (\(t, t'). JTeq E t t') (ZIP (ts, ts')))) /\
(!E t ts tc. ~is_abbrev_tc E t /\ ~is_abbrev_tc E (TE_constr ts tc) ==>
      (JTeq E t (TE_constr ts tc) =
       ?ts'. (t = TE_constr ts' tc) /\ (LENGTH ts = LENGTH ts') /\ 
             (SOME (LENGTH ts) = typeconstr_kind E tc) /\
             EVERY (\(t, t'). JTeq E t t') (ZIP (ts, ts'))))`,
METIS_TAC [teq_fun1, List.nth (CONJUNCTS JTeq_rules, 1)]);


val _ = export_theory ();
