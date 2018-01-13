open bossLib HolKernel boolLib sortingTheory combinTheory wordsTheory listTheory rich_listTheory optionTheory;
open pairTheory;
open ottLib ottTheory caml_typedefTheory;
open utilTheory basicTheory environmentTheory validTheory teqTheory;

val _ = new_theory "progress";

val _ = Parse.hide "S";

val MEM_SPLIT_FIRST = Q.prove (
`!l x. MEM x (MAP FST l) = ?l1 l2 y. (l = l1 ++ [(x,y)] ++ l2) /\ ~MEM x (MAP FST l1)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [] THEN
EQ_TAC THEN SRW_TAC [] [] THENL 
[METIS_TAC [APPEND, MAP, MEM],
 Cases_on `x=q` THEN SRW_TAC [] [] THENL
     [MAP_EVERY Q.EXISTS_TAC [`[]`, `l1 ++ [(q,y)] ++ l2`, `r`] THEN SRW_TAC [] [],
      MAP_EVERY Q.EXISTS_TAC [`(q,r)::l1`, `l2`, `y`] THEN SRW_TAC [] []],
 Cases_on `l1` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []]);


val is_constr_p_def = Define 
`is_constr_p E e = ?c es tpo ts tc. (e = Expr_construct (C_name c) es) /\
                                  (lookup E (name_cn c) = SOME (EB_pc c tpo (typexprs_inj ts) tc)) /\
                                  (LENGTH es = LENGTH ts)`;

val uprim_lem1 = Q.prove (
`!E up t. JTuprim E up t ==> ?t1 t2. t = TE_arrow t1 t2`,
SRW_TAC [] [JTuprim_cases]);

val bprim_lem1 = Q.prove (
`!E bp t. JTbprim E bp t ==> ?t1 t2 t3. t = TE_arrow t1 (TE_arrow t2 t3)`,
SRW_TAC [] [JTbprim_cases]);

local

val lem3 = Q.prove (
`!E constr t. JTconstr_c E constr t ==> ~is_abbrev_tc E t /\ ?tl tc. t = TE_constr tl tc`,
SRW_TAC [] [JTconstr_c_cases] THEN SRW_TAC [] [is_abbrev_tc_def]);

val lem4 = Q.prove (
`!E constr tl t. JTconstr_p E constr tl t ==> ~is_abbrev_tc E t /\ ?tl' tc. t = TE_constr tl' tc`,
SRW_TAC [] [JTconstr_p_cases] THEN SRW_TAC [] [is_abbrev_tc_def] THEN
SRW_TAC [] [is_abbrev_tc_cases] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN Cases_on `typeconstr` THEN
FULL_SIMP_TAC (srw_ss()) [EBok_def] THEN CCONTR_TAC THEN FULL_SIMP_TAC (srw_ss()) []);

val lem5 = Q.prove (
`!E constr tl t tcn. 
  (lookup E (name_tcn tcn) = SOME (EB_tr tcn kind field_name'_list)) ==> 
  ~is_abbrev_tc E (TE_constr t'_list (TC_name tcn))`,
SRW_TAC [] [is_abbrev_tc_def]);

val lem6 = Q.prove (
`!E fn t1 t2. JTfield E fn t1 t2 ==> is_abbrev_tc E t1 \/ is_record_tc E t1`,
SRW_TAC [] [JTfield_cases, JTinst_named_cases, substs_typevar_typexpr_def] THEN
`Eok E` by METIS_TAC [ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC list_ss [EBok_def] THEN
(* FULL_SIMP_TAC list_ss [teq_arrow_rw, teq_tup_rw, typexpr_11, typexpr_distinct] THEN *)
SRW_TAC [] [is_abbrev_tc_def, is_record_tc_def] THEN
SRW_TAC [] []);

val lem7 = Q.prove (
`!E t l. LENGTH l >= 1 /\ EVERY (\x. JTfield E (FST x) t (SND (SND x))) l ==>
         is_abbrev_tc E t \/ is_record_tc E t`,
Cases_on `l` THEN SRW_TAC [] [] THEN METIS_TAC [lem6]);

val is_constr_p_lem1 = SIMP_RULE list_ss [is_constr_p_def, expr_11] (Q.prove (
`!E c l ts tcn. JTconstr_p E c (MAP SND l) (TE_constr ts (TC_name tcn)) ==> 
                is_constr_p E (Expr_construct c (MAP FST l))`,
SRW_TAC [] [is_constr_p_def, JTconstr_p_cases] THEN METIS_TAC [LENGTH_MAP]));

val is_constr_p_lem2 = SIMP_RULE list_ss [is_constr_p_def, expr_11] (Q.prove (
`!E c l ts tcn. JTconstr_p E c (MAP SND l) (TE_constr [] TC_exn) ==> 
                is_constr_p E (Expr_construct c (MAP FST l)) \/
                ((c = C_invalidargument) /\ (LENGTH l = 1))`,
SRW_TAC [] [is_constr_p_def, JTconstr_p_cases] THEN1 METIS_TAC [LENGTH_MAP] THEN
Cases_on `l` THEN FULL_SIMP_TAC list_ss []));

val cv_tac = 
Cases_on `e` THEN SRW_TAC [] [is_value_of_expr_def, JTe_fun, JTconst_cases] THEN CCONTR_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [teq_fun2, is_abbrev_tc_def] THEN
MAP_EVERY IMP_RES_TAC [uprim_lem1, bprim_lem1, lem3, lem4, lem5] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [teq_fun2, is_abbrev_tc_def, JTe_fun] THEN 
IMP_RES_TAC bprim_lem1 THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [teq_fun2, is_abbrev_tc_def];

in

val cv_var = Q.prove (
`!S E e a. is_value_of_expr e /\ JTe S E e (TE_var a) ==> F`,
cv_tac);

val cv_idx = Q.prove (
`!S E e n1 n2. is_value_of_expr e /\ JTe S E e (TE_idxvar n1 n2) ==> F`,
cv_tac);

val cv_any = Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e TE_any ==> F`,
cv_tac);

val cv_fun = Q.prove (
`!S E e t1 t2. is_value_of_expr e /\ JTe S E e (TE_arrow t1 t2) ==> 
               (?up. e = Expr_uprim up) \/
               (?bp. e = Expr_bprim bp) \/
               (?bp e'. e = Expr_apply (Expr_bprim bp) e') \/
               (?pm. e = Expr_function pm)`,
cv_tac);

val cv_tup = Q.prove (
`!S E e ts. is_value_of_expr e /\ JTe S E e (TE_tuple ts) ==>
            ?es. (e = Expr_tuple es) /\ (LENGTH ts = LENGTH es)`,
cv_tac);

val cv_int = Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e (TE_constr [] TC_int) ==>
         ?n. e = Expr_constant (CONST_int n)`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def]);

val cv_float = Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e (TE_constr [] TC_float) ==>
         ?n. e = Expr_constant (CONST_float n)`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def]);

val cv_char = Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e (TE_constr [] TC_char) ==>
         ?n. e = Expr_constant (CONST_char n)`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def]);

val cv_string = Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e (TE_constr [] TC_string) ==>
         ?n. e = Expr_constant (CONST_string n)`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def]);

val cv_bool = Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e (TE_constr [] TC_bool) ==>
         (e = Expr_constant CONST_true) \/
         (e = Expr_constant CONST_false)`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def]);

val cv_unit = Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e (TE_constr [] TC_unit) ==>
         (e = Expr_constant CONST_unit)`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def]);

val cv_exn = SIMP_RULE (srw_ss()) [is_constr_p_def] (Q.prove (
`!S E e. is_value_of_expr e /\ JTe S E e (TE_constr [] TC_exn) ==>
         is_constr_p E e \/
         (?c. e = Expr_constant (CONST_constr c)) \/
         (?e'. e = Expr_construct C_invalidargument [e'])`,
cv_tac THEN Cases_on `tl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN IMP_RES_TAC is_constr_p_lem2 THEN
FULL_SIMP_TAC (srw_ss()) [is_constr_p_def] THEN Cases_on `e_t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []));

val cv_option = Q.prove (
`!S E e t. is_value_of_expr e /\ JTe S E e (TE_constr [t] TC_option) ==>
           (?e'. e = Expr_construct C_some [e']) \/
           (e = Expr_constant (CONST_constr C_none))`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def] THEN
Cases_on `e_t_list` THEN FULL_SIMP_TAC (srw_ss()) []);

val cv_list = Q.prove (
`!S E e t. is_value_of_expr e /\ JTe S E e (TE_constr [t] TC_list) ==>
           (e = Expr_constant CONST_nil) \/
           (?e1 e2. e = Expr_cons e1 e2)`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def] THEN
Cases_on `e_t_list` THEN FULL_SIMP_TAC (srw_ss()) []);

val cv_ref = Q.prove (
`!S E e t. is_value_of_expr e /\ JTe S E e (TE_constr [t] TC_ref) ==>
           ?l. e = Expr_location l`,
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases, JTconstr_p_cases] THEN SRW_TAC [] [] THEN
`Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def] THEN
Cases_on `e_t_list` THEN FULL_SIMP_TAC (srw_ss()) []);

val cv_tcn = SIMP_RULE (srw_ss()) [is_constr_p_def] (Q.prove (
`!S E e ts tcn. is_value_of_expr e /\ JTe S E e (TE_constr ts (TC_name tcn)) ==>
                ((?k. lookup E (name_tcn tcn) = SOME (EB_td tcn k)) ==>
                 (?c. e = Expr_constant (CONST_constr c)) \/ is_constr_p E e) /\
                (!fns. (?k. lookup E (name_tcn tcn) = SOME (EB_tr tcn k fns)) ==>
                       (?fes. (e = Expr_record fes) /\ (PERM (MAP FST fes) (MAP F_name fns))))`, 
cv_tac THEN FULL_SIMP_TAC (srw_ss()) [JTconstr_c_cases] THENL
[IMP_RES_TAC is_constr_p_lem1 THEN FULL_SIMP_TAC (srw_ss()) [is_constr_p_def],
 FULL_SIMP_TAC (srw_ss()) [JTconstr_p_cases] THEN
     `Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN IMP_RES_TAC lookup_ok_thm THEN
     Cases_on `t''_tv_list` THEN FULL_SIMP_TAC (srw_ss()) [EBok_def],
 IMP_RES_TAC lem7 THEN FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, is_record_tc_def] THEN 
     FULL_SIMP_TAC (srw_ss()) [MAP_MAP] THEN METIS_TAC [PERM_MAP, PERM_SYM, MAP_MAP]]));

val canon_val_fun = LIST_CONJ 
    [cv_var, cv_idx, cv_any, cv_fun, cv_tup, cv_int, cv_float, cv_char, cv_string, cv_bool,
     cv_unit, cv_exn, cv_option, cv_list, cv_ref, cv_tcn];

val _ = save_thm ("canon_val_fun", canon_val_fun);

end;

val uprim_progress = Q.store_thm ("uprim_progress",
`!E uprim t1 t2 t3 S v. JTuprim E uprim t3 /\ JTeq E t3 (TE_arrow t1 t2) /\ JTe S E v t1 /\ 
                   is_value_of_expr v ==>
                   (uprim = Uprim_raise) \/ ?e L. JRuprim uprim v L e`,
SRW_TAC [] [] THEN IMP_RES_TAC uprim_lem1 THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN
`JTe S E v t1'` by METIS_TAC [JTeq_rules, teq_thm] THEN
FULL_SIMP_TAC (srw_ss()) [JTuprim_cases] THEN
IMP_RES_TAC canon_val_fun THEN SRW_TAC [] [JRuprim_cases] THEN
METIS_TAC []);

val eq_progress = Q.prove (
`!E t1 t2 t3 S v1 v2.
    ~is_abbrev_tc E t1 /\ ~is_abbrev_tc E t2 /\
    JTbprim E Bprim_equal (TE_arrow t1 (TE_arrow t2 t3)) /\ JTe S E v1 t1 /\ JTe S E v2 t2 /\
    is_value_of_expr v1 /\ is_value_of_expr v2 ==>
    ?e L. JRbprim v1 Bprim_equal v2 L e`,
SRW_TAC [] [JTbprim_cases] THEN Cases_on `t1` THENL
[METIS_TAC [cv_var],
 METIS_TAC [cv_idx],
 METIS_TAC [cv_any],
 `(?up. v1 = Expr_uprim up) \/ (?bp. v1 = Expr_bprim bp) \/ (?bp e'. v1 = Expr_apply (Expr_bprim bp) e') \/
                        ?pm. v1 = Expr_function pm` by METIS_TAC [cv_fun] THEN
     SRW_TAC [] [JRbprim_cases, funval_def] THEN FULL_SIMP_TAC list_ss [is_value_of_expr_def],
 IMP_RES_TAC cv_tup THEN
    SRW_TAC [ARITH_ss] [EXISTS_OR_THM, funval_def, ELIM_UNCURRY, JRbprim_cases] THEN
    Q.EXISTS_TAC `MAP2 (\e1 e2. (e1, e2)) es' es` THEN
    SRW_TAC [ARITH_ss] [MAP_MAP2, MAP2_IGNORE, MAP2_LENGTH, EVERY_MAP2, EVERY_MAP, MAP_I] THEN
    FULL_SIMP_TAC list_ss [EVERY_MAP, is_value_of_expr_def, Eok_def],
 Cases_on `t'` THEN FULL_SIMP_TAC list_ss [Eok_def, COND_EXPAND_EQ, LENGTH_NIL_ALT, LENGTH_1] THEN
      SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THENL
   [ALL_TAC,
    IMP_RES_TAC cv_int THEN SRW_TAC [] [JRbprim_cases] THEN METIS_TAC [],
    IMP_RES_TAC cv_char THEN SRW_TAC [] [JRbprim_cases] THEN METIS_TAC [],
    IMP_RES_TAC cv_string THEN SRW_TAC [] [JRbprim_cases] THEN METIS_TAC [],
    IMP_RES_TAC cv_float THEN SRW_TAC [] [JRbprim_cases] THEN METIS_TAC [],
    IMP_RES_TAC cv_bool THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [JRbprim_cases] THEN METIS_TAC [],
    IMP_RES_TAC cv_unit THEN SRW_TAC [] [JRbprim_cases] THEN METIS_TAC [],
    `(?c es tpo ts tc.  ((v1 = Expr_construct (C_name c) es) /\
                          (lookup E (name_cn c) = SOME (EB_pc c tpo (typexprs_inj ts) tc)) /\
                          (LENGTH es = LENGTH ts)) \/
                        (?c. v1 = Expr_constant (CONST_constr c)) \/
                        ?e'. v1 = Expr_construct C_invalidargument [e']) /\
         (?c es tpo ts tc.  ((v2 = Expr_construct (C_name c) es) /\
                              (lookup E (name_cn c) = SOME (EB_pc c tpo (typexprs_inj ts) tc)) /\
                              (LENGTH es = LENGTH ts)) \/
                            (?c. v2 = Expr_constant (CONST_constr c)) \/
                            ?e'. v2 = Expr_construct C_invalidargument [e'])`
                 by METIS_TAC [cv_exn] THEN
           SRW_TAC [] [EXISTS_OR_THM, funval_def, ELIM_UNCURRY, JRbprim_cases] THEN
           FULL_SIMP_TAC list_ss [is_value_of_expr_def, JTe_fun, ETA_THM] THEN
           SRW_TAC [] [] THENL 
           [Cases_on `(c' = c)` THEN SRW_TAC [] [] THEN
                    Q.EXISTS_TAC `MAP2 (\t t'. (FST t, FST t')) e_t_list e_t_list'` THEN
                    `LENGTH e_t_list = LENGTH e_t_list'` by
                                 METIS_TAC [LENGTH_MAP, SOME_11, environment_binding_11, typexprs_11] THEN
                    FULL_SIMP_TAC list_ss [MAP_MAP2, MAP2_IGNORE, MAP2_LENGTH, EVERY_MAP2,
                                           EVERY_MAP, MAP_I],
            METIS_TAC [],
            Cases_on `e_t_list` THEN Cases_on `e_t_list'` THEN FULL_SIMP_TAC list_ss [] THEN
                    SRW_TAC [] [] THEN
                    Q.EXISTS_TAC `[(FST h, FST h')]` THEN SRW_TAC [] []],
    IMP_RES_TAC cv_list THEN SRW_TAC [] [JRbprim_cases] THEN
          FULL_SIMP_TAC list_ss [is_value_of_expr_def] THEN METIS_TAC [],
    IMP_RES_TAC cv_option THEN SRW_TAC [] [EXISTS_OR_THM, funval_def, JRbprim_cases, ELIM_UNCURRY] THEN
          FULL_SIMP_TAC list_ss [is_value_of_expr_def] THEN 
          Q.EXISTS_TAC `[(e'', e')]` THEN FULL_SIMP_TAC list_ss [],
    IMP_RES_TAC cv_ref THEN SRW_TAC [] [JRbprim_cases] THEN METIS_TAC []] THEN
 Cases_on `lookup E (name_tcn t'')` THEN FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def] THEN
    IMP_RES_TAC lookup_name_thm THEN FULL_SIMP_TAC (srw_ss()) [] THENL
    [`((?c. v1 = Expr_constant (CONST_constr c)) \/
           ?c es tpo ts tc.  (v1 = Expr_construct (C_name c) es) /\
                             (lookup E (name_cn c) = SOME (EB_pc c tpo (typexprs_inj ts) tc)) /\
                             (LENGTH es = LENGTH ts)) /\
             ((?c. v2 = Expr_constant (CONST_constr c)) \/
               ?c es tpo ts tc.  (v2 = Expr_construct (C_name c) es) /\
                                 (lookup E (name_cn c) = SOME (EB_pc c tpo (typexprs_inj ts) tc)) /\
                                 (LENGTH es = LENGTH ts))` by METIS_TAC [cv_tcn] THEN
          SRW_TAC [] [EXISTS_OR_THM, funval_def, ELIM_UNCURRY, JRbprim_cases] THEN
          Cases_on `c' = c` THEN SRW_TAC [] [] THEN
          FULL_SIMP_TAC list_ss [is_value_of_expr_def, ETA_THM] THEN 
          `LENGTH ts = LENGTH ts'` by METIS_TAC [LENGTH_MAP, SOME_11, environment_binding_11, typexprs_11] THEN
          Q.EXISTS_TAC `MAP2 (\e e'. (e, e')) es es'` THEN
          FULL_SIMP_TAC list_ss [is_value_of_expr_def, MAP_MAP2, MAP2_IGNORE, MAP2_LENGTH, EVERY_MAP2,
                                 EVERY_MAP, MAP_I, ETA_THM],
     IMP_RES_TAC cv_tcn THEN SRW_TAC [] [EXISTS_OR_THM, funval_def, JRbprim_cases] THEN
         FULL_SIMP_TAC list_ss [JTe_fun, is_value_of_expr_def] THEN SRW_TAC [] [] THEN
         FULL_SIMP_TAC list_ss [EVERY_MAP] THEN 
         MAP_EVERY Q.EXISTS_TAC [`MAP (\z. (FST z,FST (SND z))) field_name_e_t_list'`,
                                 `MAP (\z. (FST z,FST (SND z))) field_name_e_t_list`] THEN
         SRW_TAC [] [MAP_MAP, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [MAP_MAP] THEN
         `PERM (MAP field_to_fn (MAP (\z. F_name (FST z)) field_name_e_t_list)) 
               (MAP field_to_fn (MAP (\z. F_name (FST z)) field_name_e_t_list'))` by
                       METIS_TAC [PERM_SYM, PERM_TRANS, PERM_MAP] THEN
         FULL_SIMP_TAC (srw_ss()) [MAP_MAP, field_to_fn_def]]]);

val value_type_thm = Q.prove (
`!S E e t. JTe S E e t /\ is_value_of_expr e ==> ?t'. ~is_abbrev_tc E t' /\ JTeq E t t'`,
Cases_on `e` THEN SRW_TAC [] [JTe_fun, is_value_of_expr_def] THENL
[Q.EXISTS_TAC `t'` THEN SRW_TAC [] [] THEN1 FULL_SIMP_TAC (srw_ss()) [JTuprim_cases, is_abbrev_tc_def] THEN
     METIS_TAC [JTeq_rules, teq_ok_thm],
 Q.EXISTS_TAC `t'` THEN SRW_TAC [] [] THEN1 FULL_SIMP_TAC (srw_ss()) [JTbprim_cases, is_abbrev_tc_def] THEN
     METIS_TAC [JTeq_rules, teq_ok_thm],
 Q.EXISTS_TAC `t'` THEN SRW_TAC [] [] THEN1 
     FULL_SIMP_TAC (srw_ss()) [JTconst_cases, is_abbrev_tc_def, JTconstr_c_cases] THEN
     METIS_TAC [JTeq_rules, teq_ok_thm],
 Q.EXISTS_TAC `TE_tuple (MAP SND e_t_list)` THEN SRW_TAC [] [is_abbrev_tc_def] THEN
     METIS_TAC [JTeq_rules],
 Q.EXISTS_TAC `t'` THEN SRW_TAC [] [] THENL
     [FULL_SIMP_TAC (srw_ss()) [JTconstr_p_cases, is_abbrev_tc_def] THEN
          Cases_on `typeconstr` THEN FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def] THEN
          `Eok E` by METIS_TAC [teq_ok_thm, ok_ok_thm] THEN
          IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def],
      METIS_TAC [JTeq_rules, teq_ok_thm]],
 Q.EXISTS_TAC `TE_constr [t'] TC_list` THEN SRW_TAC [] [is_abbrev_tc_def] THEN METIS_TAC [JTeq_rules],
 Q.EXISTS_TAC `TE_constr t'_list (TC_name typeconstr_name)` THEN SRW_TAC [] [] THENL
     [Cases_on `typeconstr_name` THEN FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def] THEN
          `Eok E` by METIS_TAC [teq_ok_thm, ok_ok_thm] THEN
          IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def],
      METIS_TAC [JTeq_rules]],
 FULL_SIMP_TAC (srw_ss()) [JTe_fun] THEN IMP_RES_TAC bprim_lem1 THEN SRW_TAC [] [] THEN
     Q.EXISTS_TAC `TE_arrow t2 t3` THEN SRW_TAC [] [] THEN
     FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN
     METIS_TAC [JTeq_rules, teq_ok_thm, teq_thm],
 Q.EXISTS_TAC `TE_arrow t' t''` THEN SRW_TAC [] [is_abbrev_tc_def] THEN METIS_TAC [JTeq_rules],
 Q.EXISTS_TAC `TE_constr [t'] TC_ref` THEN SRW_TAC [] [is_abbrev_tc_def] THEN METIS_TAC [JTeq_rules]]);

val bprim_progress = Q.store_thm ("bprim_progress",
`!E bprim t1 t2 t3 t4 S v1 v2. 
    JTbprim E bprim t4 /\ JTeq E t4 (TE_arrow t1 (TE_arrow t2 t3)) /\
    JTe S E v1 t1 /\ JTe S E v2 t2 /\ is_value_of_expr v1 /\ is_value_of_expr v2 ==>
    ?e L. JRbprim v1 bprim v2 L e`,
SRW_TAC [] [] THEN IMP_RES_TAC bprim_lem1 THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN
`JTe S E v1 t1'` by METIS_TAC [JTeq_rules, teq_thm] THEN
`JTe S E v2 t2'` by METIS_TAC [JTeq_rules, teq_thm] THEN
FULL_SIMP_TAC (srw_ss()) [JTbprim_cases] THEN SRW_TAC [] [] THEN1
    (IMP_RES_TAC value_type_thm THEN MATCH_MP_TAC eq_progress THEN SRW_TAC [] [JTbprim_cases] THEN
     METIS_TAC [teq_thm, teq_ok_thm]) THEN
MAP_EVERY IMP_RES_TAC [cv_int, cv_ref] THEN SRW_TAC [] [JRbprim_cases] THEN
METIS_TAC []);

val JMmatch_val_subst_thm = Q.store_thm ("JMmatch_val_subst_thm",
`!e p s. JM_match e p s ==> ?l. (s = substs_x_xs l) /\ EVERY (\xv. is_value_of_expr (SND xv)) l`,
RULE_INDUCT_TAC JM_match_ind [MAP_MAP, ELIM_UNCURRY] [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [EVERY_MEM, MEM_FLAT, EXISTS_MAP, EXISTS_MEM] THEN SRW_TAC [] [] THEN
Cases_on `x` THEN Cases_on `r` THEN Cases_on `r'` THEN FULL_SIMP_TAC list_ss [substs_x_case_def] THEN
RES_TAC THEN FULL_SIMP_TAC list_ss [substs_x_11] THEN FULL_SIMP_TAC list_ss [substs_x_case_def]);

local

val LRB_lem1 = Q.prove (
`!lrbs f g h x z. (f (case lrbs of LRB_simple x y -> g x y) = case lrbs of LRB_simple x y -> f (g x y)) /\
                  (((case lrbs of LRB_simple x y -> h x y) z) = (case lrbs of LRB_simple x y -> h x y z))`,
Cases THEN SRW_TAC [] []);

val LRB_lem2 = Q.prove (
`!lrbs f. (case lrbs of LRB_simple vn pm -> case lrbs of LRB_simple vn' pm' -> f vn pm vn' pm') =
          (case lrbs of LRB_simple vn pm -> f vn pm vn pm)`,
Cases THEN SRW_TAC [] []);

val LRB_lem3 = Q.prove (
`!lrbs f. (case lrbs of LRB_simple vn pm -> LRB_simple vn pm) = lrbs`,
Cases THEN SRW_TAC [] []);

in

val e_progress_thm = Q.prove (
`(!S E e t. JTe S E e t ==> closed_env E ==> JRB_ebehaviour e) /\
 (!S E pm t1 t2. JTpat_matching S E pm t1 t2 ==> T) /\
 (!S E lb E'. JTlet_binding S E lb E' ==> closed_env E  ==> ?p e. (lb = LB_simple p e) /\ JRB_ebehaviour e) /\
 (!S E lrb E'. JTletrec_binding S E lrb E' ==> T)`,
RULE_INDUCT_TAC JTe_sind [JRB_ebehaviour_cases, JR_expr_fun, is_value_of_expr_def]
[([``"JTe_ident"``], METIS_TAC [closed_env_lem]),
 ([``"JTe_cons"``, ``"JTe_sequence"``], METIS_TAC []),
 ([``"JTe_ifthenelse"``, ``"JTe_assert"``], METIS_TAC [cv_bool]),
 ([``"JTe_let_mono"``, ``"JTe_let_poly"``], 
  METIS_TAC [MAP_REVERSE, closed_env_tv_lem, JMmatch_val_subst_thm, JM_matchP_thm]),
 ([``"JTe_try"``], METIS_TAC [pattern_matching_nchotomy]),
 ([``"JTe_apply"``],
    SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN1
      (IMP_RES_TAC cv_fun THEN SRW_TAC [] [] THEN
       FULL_SIMP_TAC (srw_ss()) [JTe_fun, is_value_of_expr_def] THEN 
       METIS_TAC [uprim_progress, bprim_progress])
    THEN METIS_TAC []),
 ([``"JTe_record_proj"``],
   SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JTfield_cases] THENL
      [SRW_TAC [] [] THEN `Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN
           IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC list_ss [EBok_def] THEN
           IMP_RES_TAC cv_tcn THEN SRW_TAC [] [] THEN
           IMP_RES_TAC PERM_MEM_EQ THEN
           FULL_SIMP_TAC list_ss [is_value_of_expr_def, EVERY_MEM, LAMBDA_PROD2] THEN
           `?l1 l2 y. (fes = l1 ++ [(F_name field_name,y)] ++ l2) /\ ~MEM (F_name field_name) (MAP FST l1)` by
                 METIS_TAC [MEM_SPLIT_FIRST, MEM_MAP] THEN
           SRW_TAC [] [EXISTS_OR_THM] THEN DISJ2_TAC THEN
           MAP_EVERY Q.EXISTS_TAC
                     [`y`,
                      `MAP (\z. (field_to_fn (FST z), SND z)) l2`,
                      `MAP (\z. (field_to_fn (FST z), SND z)) l1`] THEN
           SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I] THEN
           FULL_SIMP_TAC list_ss [MEM_MAP, MEM_APPEND] THEN1 METIS_TAC [SND] THEN
           Cases THEN SRW_TAC [] [] THEN Cases_on `q` THEN SRW_TAC [] [field_to_fn_def] THEN
           METIS_TAC [FST],
       METIS_TAC [],
       METIS_TAC []]),
  ([``"JTe_for"``],
   SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN IMP_RES_TAC cv_int THEN SRW_TAC [] [] THEN1
      (Cases_on `for_dirn` THEN
       SRW_TAC [] [EXISTS_OR_THM, integerTheory.NUM_OF_INT,
                       integer_wordTheory.i2w_def, EVAL ``1:int<0``] THEN
       Cases_on `n'<=n` THEN SRW_TAC [] [] THEN
       FULL_SIMP_TAC list_ss [WORD_NOT_LESS_EQUAL, WORD_GREATER] THEN METIS_TAC [WORD_LESS_CASES])
   THEN METIS_TAC []),
  ([``"JTe_letrec"``],
   SRW_TAC [] [] THEN 
   Q.EXISTS_TAC `MAP (\lrbs. case lrbs of LRB_simple vn pm -> (vn, recfun lrb pm, pm)) (lrbs_to_lrblist lrb)`
       THEN
   SRW_TAC [] [MAP_MAP, letrec_binding_nchotomy, EVERY_MAP, LRB_lem1, LRB_lem2, LRB_lem3,
                   MAP_I, lrbs_to_lrblist_thm, EVERY_MEM] THEN Cases_on `lrbs` THEN SRW_TAC [] []),
  ([``"JTe_match"``],
   SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JRmatching_step_cases, JRmatching_success_cases] THENL
      [Cases_on `pm` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JTe_fun, EXISTS_OR_THM] THEN
           SRW_TAC [] [] THEN Cases_on `pattern_e_E_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
           Cases_on `~JM_matchP e (FST h)` THEN SRW_TAC [] [] THENL
           [Cases_on `t'` THEN FULL_SIMP_TAC list_ss [] THEN NTAC 2 DISJ2_TAC THEN DISJ1_TAC THEN
                     Q.EXISTS_TAC `(FST h', FST (SND h'))::MAP (\x. (FST x, FST (SND x))) t''` THEN 
                     SRW_TAC [ARITH_ss] [MAP_MAP],
            FULL_SIMP_TAC list_ss [JM_matchP_thm] THEN NTAC 2 DISJ2_TAC THEN
                     Q.EXISTS_TAC `s` THEN SRW_TAC [] [] THEN
                     IMP_RES_TAC JM_match_is_val_thm THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MAP] THEN
                     Q.EXISTS_TAC `MAP (\(a,b,c). (a,b)) t'` THEN SRW_TAC [] [LAMBDA_PROD2, MAP_MAP]],
       METIS_TAC [],
       METIS_TAC []]),
  ([``"JTe_tuple"``, ``"JTe_construct"``],
   SRW_TAC [] [] THEN 
   FULL_SIMP_TAC list_ss [EVERY_MAP] THEN Cases_on `EXISTS (\x. ~is_value_of_expr (FST x)) e_t_list` THEN
   FULL_SIMP_TAC list_ss [o_DEF] THEN IMP_RES_TAC EXISTS_LAST_SPLIT THEN
   FULL_SIMP_TAC list_ss [o_DEF] THEN
   METIS_TAC [EVERY_MAP]),
  ([``"JTe_record_constr"``],
   SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_MAP] THEN
   Cases_on `EVERY (\z. is_value_of_expr (FST (SND z))) field_name_e_t_list` THEN
   FULL_SIMP_TAC list_ss [o_DEF] THEN IMP_RES_TAC EXISTS_LAST_SPLIT THEN
   FULL_SIMP_TAC list_ss [o_DEF] THEN  SRW_TAC [] [EXISTS_OR_THM] THENL
   [DISJ1_TAC THEN
        MAP_EVERY Q.EXISTS_TAC [`L`, `MAP (\x. (FST x, FST (SND x))) l2`, `MAP (\x. (FST x, FST (SND x))) l1`,
                                `FST y`, `FST (SND y)`, `e'`] THEN
        SRW_TAC [] [MAP_MAP, EVERY_MAP],
    DISJ2_TAC THEN
        MAP_EVERY Q.EXISTS_TAC [`MAP (\x. (FST x, FST (SND x))) l2`, `MAP (\x. (FST x, FST (SND x))) l1`,
                                `FST y`, `v`] THEN
        SRW_TAC [] [MAP_MAP, EVERY_MAP]]),
  ([``"JTe_record_with"``],
   SRW_TAC [] [] THEN Cases_on `~is_value_of_expr e` THEN SRW_TAC [] [] THEN1
       (FULL_SIMP_TAC list_ss [EXISTS_OR_THM] THEN SRW_TAC [] [] THENL
            [DISJ1_TAC THEN MAP_EVERY Q.EXISTS_TAC [`L`, `MAP (\x. (FST x, FST (SND x))) field_name_e_t_list`,
                                                    `e'`] THEN
                 SRW_TAC [] [MAP_MAP, EVERY_MAP],
             DISJ2_TAC THEN Q.EXISTS_TAC `MAP (\x. (FST x, FST (SND x))) field_name_e_t_list` THEN
                 SRW_TAC [] [MAP_MAP, EVERY_MAP]]) 
       THEN
       Cases_on `EXISTS (\x. ~is_value_of_expr (FST (SND x))) field_name_e_t_list` THEN1
       (Q.PAT_ASSUM `closed_env E ==> P` (K ALL_TAC) THEN
           FULL_SIMP_TAC list_ss [o_DEF] THEN SRW_TAC [] [EXISTS_OR_THM] THEN
           IMP_RES_TAC EXISTS_LAST_SPLIT THEN FULL_SIMP_TAC list_ss [o_DEF] THEN SRW_TAC [] [] THENL
           [DISJ1_TAC THEN
                MAP_EVERY Q.EXISTS_TAC [`L`, `MAP (\x. (FST x, FST (SND x))) l2`,
                                        `MAP (\x. (FST x, FST (SND x))) l1`, `FST y`, `FST (SND y)`, `e'`] THEN
                SRW_TAC [] [MAP_MAP, EVERY_MAP],
            DISJ2_TAC THEN DISJ1_TAC THEN
                MAP_EVERY Q.EXISTS_TAC [`MAP (\x. (FST x, FST (SND x))) l2`,
                                        `MAP (\x. (FST x, FST (SND x))) l1`, `FST y`, `v`] THEN
                SRW_TAC [] [MAP_MAP, EVERY_MAP]])
   THEN
   FULL_SIMP_TAC list_ss [o_DEF] THEN SRW_TAC [] [EXISTS_OR_THM] THEN
   NTAC 4 DISJ2_TAC THEN
   Cases_on `field_name_e_t_list` THEN FULL_SIMP_TAC list_ss [] THEN
   FULL_SIMP_TAC list_ss [JTfield_cases] THEN
   `Eok E` by METIS_TAC [inst_named_ok_thm, ok_ok_thm] THEN SRW_TAC [] [] THEN
   IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC list_ss [EBok_def] THEN
   IMP_RES_TAC cv_tcn THEN SRW_TAC [] [] THEN
   IMP_RES_TAC PERM_MEM_EQ THEN
   FULL_SIMP_TAC list_ss [is_value_of_expr_def, EVERY_MEM, LAMBDA_PROD2] THEN
   `?l1 l2 y. (fes = l1 ++ [(F_name (FST h),y)] ++ l2) /\ ~MEM (F_name (FST h)) (MAP FST l1)` by
             METIS_TAC [MEM_SPLIT_FIRST, MEM_MAP] THEN
   SRW_TAC [] [] THEN Cases_on `t'` THEN FULL_SIMP_TAC list_ss [is_value_of_expr_def] THEN SRW_TAC [] [] THENL
   [MAP_EVERY Q.EXISTS_TAC [`MAP (\z. (field_to_fn (FST z), SND z)) l2`,
                            `MAP (\z. (field_to_fn (FST z), SND z)) l1`,
                            `y`] THEN
          SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I] THEN
          FULL_SIMP_TAC list_ss [MEM_MAP, MEM_APPEND] THEN1 METIS_TAC [SND] THEN
          Cases THEN SRW_TAC [] [] THEN Cases_on `q` THEN SRW_TAC [] [field_to_fn_def] THEN
          METIS_TAC [FST],
    MAP_EVERY Q.EXISTS_TAC [`(FST h', FST (SND h'))::MAP (\z. (FST z,FST (SND z))) t''`,
                            `MAP (\z. (field_to_fn (FST z), SND z)) l2`,
                            `MAP (\z. (field_to_fn (FST z), SND z)) l1`,
                            `y`] THEN
          SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I] THEN
          FULL_SIMP_TAC list_ss [MEM_MAP, MEM_APPEND] THEN1
          METIS_TAC [SND] THEN
          Cases THEN SRW_TAC [] [] THEN Cases_on `q` THEN SRW_TAC [] [field_to_fn_def] THEN
          METIS_TAC [FST]])]);

end;

val e_progress_thm = save_thm ("e_progress_thm", SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] 
                 e_progress_thm);


local

val lem1 = Q.prove (
`!st. ?l:num. !l' v. (list_assoc l' st = SOME v) ==> (l' < l)`,
Induct THEN SRW_TAC [] [list_assoc_def] THEN Cases_on `h` THEN 
SRW_TAC [] [list_assoc_def, COND_EXPAND_EQ] THEN Q.EXISTS_TAC `l+q+1` THEN SRW_TAC [] [] THEN
RES_TAC THEN DECIDE_TAC);

in

val fresh_alloc = Q.prove (
`!st. ?l:num. !v. ~(list_assoc l st = SOME v)`,
METIS_TAC [DECIDE ``!x:num. ~(x<x)``, lem1]);

end;

val uprim_store_progress_thm = Q.prove (
`!up v L e. JRuprim up v L e ==> !st.
            (!l. MEM l (fl_expr v) ==> ?v. (list_assoc l st = SOME v) /\ is_value_of_expr v) ==>
            ?L' st' e'. JRuprim up v L' e' /\ JRstore st L' st'`,
RULE_INDUCT_TAC JRuprim_ind [JRstore_cases, JRuprim_cases, fl_letrec_binding_def]
[] THEN METIS_TAC [fresh_alloc]);

val bprim_store_progress_thm = Q.prove (
`!v1 bp v2 L e. JRbprim v1 bp v2 L e ==> !st.
                (!l. (MEM l (fl_expr v1) \/ MEM l (fl_expr v2)) ==>
                      ?v. (list_assoc l st = SOME v) /\ is_value_of_expr v) ==>
                ?L' st' e'. JRbprim v1 bp v2 L' e' /\ JRstore st L' st'`,
RULE_INDUCT_TAC JRbprim_ind [JRstore_cases, JRbprim_cases, fl_letrec_binding_def]
[([``"Jbprim_equal_fun"``],
  Cases_on `v1` THEN FULL_SIMP_TAC list_ss [funval_def] THEN SRW_TAC [] [] THEN METIS_TAC []),
 ([``"Jbprim_assign"``],
  SRW_TAC [] [list_assoc_split] THEN 
      POP_ASSUM (MP_TAC o Q.SPEC `l`) THEN SRW_TAC [] [] THEN 
      MAP_EVERY Q.EXISTS_TAC [`l2`, `v`, `l1`] THEN SRW_TAC [] [] THEN1 METIS_TAC [APPEND_ASSOC, APPEND] THEN
      CCONTR_TAC THEN FULL_SIMP_TAC list_ss [])]
 THEN METIS_TAC []);

val e_store_progress_thm = Q.prove (
`!e L e'. JR_expr e L e' ==> !st.
          (!l. MEM l (fl_expr e) ==> ?v. (list_assoc l st = SOME v) /\ is_value_of_expr v) ==>
          ?L' st' e'. JR_expr e L' e' /\ JRstore st L' st'`,
RULE_INDUCT_TAC JR_expr_ind [JR_expr_fun, fl_letrec_binding_def, is_value_of_expr_def]
[([``"JR_expr_uprim"``, ``"JR_expr_bprim"``],
  METIS_TAC [uprim_store_progress_thm, bprim_store_progress_thm]),
 ([``"JR_expr_apply_ctx_arg"``, ``"JR_expr_apply_ctx_fun"``, ``"JR_expr_let_ctx"``,
   ``"JR_expr_sequence_ctx_left"``, ``"JR_expr_ifthenelse_ctx"``, ``"JR_expr_match_ctx"``,
   ``"JR_expr_for_ctx1"``, ``"JR_expr_for_ctx2"``, ``"JR_expr_try_ctx"``, ``"JR_expr_cons_ctx1"``,
   ``"JR_expr_cons_ctx2"``, ``"JR_expr_record_with_ctx2"``, ``"JR_expr_record_access_ctx"``,
   ``"JR_expr_assert_ctx"``],
  METIS_TAC []),
 ([``"JR_expr_tuple_ctx"``, ``"JR_expr_constr_ctx"``, ``"JR_expr_record_ctx"``, ``"JR_expr_record_with_ctx1"``],
  SRW_TAC [] [MEM_FLAT, EXISTS_MAP] THEN METIS_TAC [])]
THEN
SRW_TAC [] [JRstore_cases] THEN METIS_TAC []);

val e_store_progress_thm = 
         save_thm ("e_store_progress_thm", SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]
                  e_store_progress_thm);

local

val lem1 = Q.prove (
`!E l. value_env E ==> ~MEM (name_l l) (MAP domEB E)`,
Induct THEN SRW_TAC [] [value_env_def, domEB_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC list_ss [value_env_def, domEB_def] THEN SRW_TAC [] []);

in

val env_fl_thm = Q.store_thm ("env_fl_thm",
`(!S E e t. JTe S E e t ==> !x. MEM x (fl_expr e) ==> MEM (name_l x) (MAP domEB E)) /\
 (!S E pm t t'. JTpat_matching S E pm t t' ==>
          !x. MEM x (fl_pattern_matching pm) ==> MEM (name_l x) (MAP domEB E)) /\
 (!S E lb E'. JTlet_binding S E lb E' ==>
          !x. MEM x (fl_let_binding lb) ==> MEM (name_l x) (MAP domEB E)) /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==>
          !x. MEM x (fl_letrec_bindings lrbs) ==> MEM (name_l x) (MAP domEB E))`,
RULE_INDUCT_TAC JTe_sind [fl_letrec_binding_def, EVERY_MEM, MEM_FLAT, EXISTS_MAP, EXISTS_MEM, domEB_def,
                          MAP_REVERSE, MAP_MAP]
[([``"JTe_let_mono"``, ``"JTe_let_poly"``, ``"JTe_letrec"``, ``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [MEM_MAP] THEN METIS_TAC []),
 ([``"JTe_location"``],
  METIS_TAC [lookup_dom_thm]),
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN RES_TAC THEN IMP_RES_TAC pat_env_lem THEN METIS_TAC [lem1])]
THEN METIS_TAC []);

end;


val  _= export_theory();

