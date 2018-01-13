open HolKernel bossLib boolLib listTheory pairTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory;

val _ = new_theory "remv_tyvar";

val value_remv_tyvar_thm = Q.store_thm ("value_remv_tyvar_thm",
`!v. is_value_of_expr v ==> is_value_of_expr (remv_tyvar_expr v)`,
HO_MATCH_MP_TAC is_value_of_expr_ind THEN 
SRW_TAC [] [is_value_of_expr_def, remv_tyvar_letrec_binding_def, EVERY_MAP, EVERY_MEM, LAMBDA_PROD2] THEN
SRW_TAC [] [remv_tyvar_letrec_binding_def] THEN Cases_on `z` THEN METIS_TAC [SND]);

val nexp_remv_tyvar_thm = Q.store_thm ("nexp_remv_tyvar_thm",
`!e. is_non_expansive_of_expr e ==> is_non_expansive_of_expr (remv_tyvar_expr e)`,
recInduct is_non_expansive_of_expr_ind THEN 
SRW_TAC [] [is_non_expansive_of_expr_def, remv_tyvar_letrec_binding_def] THEN
FULL_SIMP_TAC list_ss [EVERY_MAP, EVERY_MEM] THENL
[FULL_SIMP_TAC list_ss [LAMBDA_PROD2] THEN Cases_on `x` THEN FULL_SIMP_TAC list_ss [] THEN
    METIS_TAC [SND],
 Cases_on `expr1` THEN 
     FULL_SIMP_TAC list_ss [is_binary_prim_app_value_of_expr_def, remv_tyvar_letrec_binding_def]]);

val JTinst_any_ok_thm = Q.prove (
`!E t t'. JTinst_any E t t' ==> tkind E t`,
RULE_INDUCT_TAC JTinst_any_ind [Eok_def, EVERY_MAP] []);

val src_t_remv_tyvar_thm = Q.prove (
`!t. is_src_typexpr_of_typexpr t ==> is_src_typexpr_of_typexpr (remv_tyvar_typexpr t)`,
recInduct is_src_typexpr_of_typexpr_ind THEN 
SRW_TAC [] [is_src_typexpr_of_typexpr_def, remv_tyvar_typexpr_def] THEN
FULL_SIMP_TAC list_ss [EVERY_MAP, EVERY_MEM]);

val remv_tyvar_subst_thm = Q.prove (
`(!t S. substs_typevar_typexpr S (remv_tyvar_typexpr t) = remv_tyvar_typexpr t) /\
 (!tl S. MAP (\t. substs_typevar_typexpr S (remv_tyvar_typexpr t)) tl = 
         MAP remv_tyvar_typexpr tl)`,
Induct THEN SRW_TAC [] [substs_typevar_typexpr_def, remv_tyvar_typexpr_def, MAP_MAP, ETA_THM]);

local

val lem1 = Q.prove (
`!l1 l2 S. 
  (!E S. EVERY (\(t,t').  JTinst_any E t (substs_typevar_typexpr S t') ==>
                          JTinst_any E t (remv_tyvar_typexpr t')) (ZIP (MAP FST l2,l1))) /\
         (MAP (\typexpr_. substs_typevar_typexpr S typexpr_) l1 = MAP SND l2) /\
         EVERY (\x. JTinst_any E (FST x) (SND x)) l2 ==>
         EVERY (\x. JTinst_any E (FST x) (SND x)) (ZIP (MAP FST l2,MAP remv_tyvar_typexpr l1))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [] THEN METIS_TAC []);

in

val JTinst_any_remv_tyvar_thm = Q.prove (
`(!t' E t S. JTinst_any E t (substs_typevar_typexpr S t') ==> 
             JTinst_any E t (remv_tyvar_typexpr t')) /\
 (!tl' E tl S. (LENGTH tl = LENGTH tl') ==>
               EVERY (\(t, t'). JTinst_any E t (substs_typevar_typexpr S t') ==>
                                JTinst_any E t (remv_tyvar_typexpr t')) 
                     (ZIP (tl, tl')))`,
Induct THEN SRW_TAC [] [JTinst_any_fun, remv_tyvar_typexpr_def, substs_typevar_typexpr_def] THENL
[METIS_TAC [JTinst_any_ok_thm],
 METIS_TAC [],
 Q.EXISTS_TAC `ZIP (MAP FST t_t'_list, MAP remv_tyvar_typexpr tl')` THEN
     SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, ETA_THM] THENL
     [METIS_TAC [MAP_FST_ZIP, LENGTH_MAP],
      METIS_TAC [MAP_SND_ZIP, LENGTH_MAP],
      METIS_TAC [lem1, LENGTH_MAP],
      METIS_TAC [LENGTH_MAP, LENGTH_ZIP]],
 Q.EXISTS_TAC `ZIP (MAP FST t_t'_list, MAP remv_tyvar_typexpr tl')` THEN
     SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, ETA_THM] THENL
     [METIS_TAC [MAP_FST_ZIP, LENGTH_MAP],
      METIS_TAC [MAP_SND_ZIP, LENGTH_MAP],
      METIS_TAC [lem1, LENGTH_MAP],
      METIS_TAC [LENGTH_MAP, LENGTH_ZIP]],
 Cases_on `tl` THEN FULL_SIMP_TAC (srw_ss()) [],
 Cases_on `tl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []]);

end;

val remv_tyvar_pat_thm = Q.store_thm ("remv_tyvar_pat_thm",
`!S E p t t'. JTpat S E p t t' ==> !S'. JTpat S' E (remv_tyvar_pattern p) t t'`,
RULE_INDUCT_TAC JTpat_ind [JTpat_fun, remv_tyvar_pattern_def]
[([``"JTpat_typed"``],
  SRW_TAC [] [src_t_remv_tyvar_thm, remv_tyvar_subst_thm] THEN METIS_TAC [JTinst_any_remv_tyvar_thm]),
 ([``"JTpat_construct"``],
  SRW_TAC [] [] THEN 
      Q.EXISTS_TAC `MAP (\x. (remv_tyvar_pattern (FST x), FST (SND x), SND (SND x))) pattern_E_t_list` THEN 
      SRW_TAC [] [MAP_MAP, EVERY_MAP, ETA_THM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM, ELIM_UNCURRY]),
 ([``"JTpat_construct_any"``, ``"JTpat_cons"``],
  METIS_TAC []),
 ([``"JTpat_tuple"``],
  SRW_TAC [] [] THEN 
      Q.EXISTS_TAC `MAP (\x. (remv_tyvar_pattern (FST x), FST (SND x), SND (SND x))) pattern_t_E_list` THEN 
      SRW_TAC [] [MAP_MAP, EVERY_MAP, ETA_THM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM, ELIM_UNCURRY]),
 ([``"JTpat_record"``],
  SRW_TAC [] [] THEN 
      Q.EXISTS_TAC `MAP (\x. (FST x, remv_tyvar_pattern (FST (SND x)), FST (SND (SND x)), SND (SND (SND x))))
                        field_name_pattern_E_t_list` THEN 
      SRW_TAC [] [MAP_MAP, EVERY_MAP, ETA_THM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM, ELIM_UNCURRY]),
 ([``"JTpat_or"``],
  METIS_TAC [])]);


val remv_tyvar_thm = Q.store_thm ("remv_tyvar_thm",
`(!S E e t. JTe S E e t ==> !S'. JTe S' E (remv_tyvar_expr e) t) /\
 (!S E p t t'. JTpat_matching S E p t t' ==> !S'. JTpat_matching S' E (remv_tyvar_pattern_matching p) t t') /\
 (!S E lb E'. JTlet_binding S E lb E' ==> !S'. JTlet_binding S' E (remv_tyvar_let_binding lb) E') /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==> 
                !S'. JTletrec_binding S' E (remv_tyvar_letrec_bindings lrbs) E')`,
RULE_INDUCT_TAC JTe_ind [remv_tyvar_letrec_binding_def, JTe_fun]
[([``"JTe_typed"``],
  SRW_TAC [] [src_t_remv_tyvar_thm, remv_tyvar_subst_thm] THEN METIS_TAC [JTinst_any_remv_tyvar_thm]),
 ([``"JTe_tuple"``, ``"JTe_construct"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\x. (remv_tyvar_expr (FST x), SND x)) e_t_list` THEN 
      SRW_TAC [] [MAP_MAP, EVERY_MAP, ETA_THM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC []),
 ([``"JTe_record_constr"``],
  SRW_TAC [] [] THEN 
      MAP_EVERY Q.EXISTS_TAC [`field_name'_list`,
                              `t'_list`,
                              `MAP (\x. (FST x, remv_tyvar_expr (FST (SND x)), SND (SND x)))
                                   field_name_e_t_list`] THEN 
      SRW_TAC [] [MAP_MAP, EVERY_MAP, ETA_THM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC []),
 ([``"JTe_record_with"``],
  SRW_TAC [] [] THEN 
      Q.EXISTS_TAC `MAP (\x. (FST x, remv_tyvar_expr (FST (SND x)), SND (SND x))) field_name_e_t_list` THEN 
      SRW_TAC [] [MAP_MAP, EVERY_MAP, ETA_THM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC []),
 ([``"JTe_apply"``, ``"JTe_record_proj"``, ``"JTe_match"``, ``"JTe_let_mono"``, ``"JTe_letrec"``],
  METIS_TAC []),
 ([``"JTe_let_poly"``],
  METIS_TAC [nexp_remv_tyvar_thm]), 
 ([``"JTpat_matching_pm"``],
  SRW_TAC [] [] THEN 
      Q.EXISTS_TAC `MAP (\x. (remv_tyvar_pattern (FST x), remv_tyvar_expr (FST (SND x)), SND (SND x)))
                        pattern_e_E_list` THEN 
      SRW_TAC [] [MAP_MAP, EVERY_MAP, ETA_THM, remv_tyvar_letrec_binding_def] THEN 
      FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [remv_tyvar_pat_thm]),
 ([``"JTlet_binding_poly"``],
  METIS_TAC [remv_tyvar_pat_thm]),
 ([``"JTletrec_binding_equal_function"``],
  SRW_TAC [] [remv_tyvar_letrec_binding_def, MAP_MAP] THEN 
      Q.EXISTS_TAC `MAP (\x. (FST x, remv_tyvar_pattern_matching (FST (SND x)),
                              FST (SND (SND x)), SND (SND (SND x))))
                        value_name_pattern_matching_t_t'_list` THEN
      SRW_TAC [] [MAP_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC list_ss [MEM_MAP])]
THEN METIS_TAC []);

val remv_tyvar_idem_typexpr_thm = Q.prove (
`!t. remv_tyvar_typexpr (remv_tyvar_typexpr t) = remv_tyvar_typexpr t`,
HO_MATCH_MP_TAC remv_tyvar_typexpr_ind THEN 
SRW_TAC [] [remv_tyvar_typexpr_def, MAP_MAP, MAP_EQ]);

val remv_tyvar_idem_pat_thm = Q.prove (
`!p. remv_tyvar_pattern (remv_tyvar_pattern p) = remv_tyvar_pattern p`,
HO_MATCH_MP_TAC remv_tyvar_pattern_ind THEN 
SRW_TAC [] [remv_tyvar_pattern_def, MAP_MAP, MAP_EQ, remv_tyvar_idem_typexpr_thm, LAMBDA_PROD2] THEN
Cases_on `z` THEN METIS_TAC [SND]);

val remv_tyvar_idem_thm = Q.store_thm ("remv_tyvar_idem_thm",
`(!lrb. remv_tyvar_letrec_binding (remv_tyvar_letrec_binding lrb) =
        remv_tyvar_letrec_binding lrb) /\
 (!lrbs. remv_tyvar_letrec_bindings (remv_tyvar_letrec_bindings lrbs) =
         remv_tyvar_letrec_bindings lrbs) /\
 (!lb. remv_tyvar_let_binding (remv_tyvar_let_binding lb) =
       remv_tyvar_let_binding lb) /\
 (!pe. remv_tyvar_pat_exp (remv_tyvar_pat_exp pe) =
       remv_tyvar_pat_exp pe) /\
 (!pm. remv_tyvar_pattern_matching (remv_tyvar_pattern_matching pm) =
       remv_tyvar_pattern_matching pm) /\
 (!expr. remv_tyvar_expr (remv_tyvar_expr expr) =
         remv_tyvar_expr expr)`,
HO_MATCH_MP_TAC remv_tyvar_letrec_binding_ind THEN 
SRW_TAC [] [remv_tyvar_letrec_binding_def, MAP_MAP, MAP_EQ, LAMBDA_PROD2,
            remv_tyvar_idem_pat_thm, remv_tyvar_idem_typexpr_thm] THEN
Cases_on `z` THEN METIS_TAC [SND]);

val remv_tyvar_aux_xs_lrb_thm = Q.prove (
`!lrb. aux_xs_letrec_binding_of_letrec_binding (remv_tyvar_letrec_binding lrb) =
       aux_xs_letrec_binding_of_letrec_binding lrb`,
Cases THEN SRW_TAC [] [remv_tyvar_letrec_binding_def, aux_xs_letrec_binding_of_letrec_binding_def]);

val remv_tyvar_aux_xs_lrbs_thm = Q.prove (
`!lrbs. aux_xs_letrec_bindings_of_letrec_bindings (remv_tyvar_letrec_bindings lrbs) =
        aux_xs_letrec_bindings_of_letrec_bindings lrbs`,
Cases THEN 
SRW_TAC [] [remv_tyvar_letrec_binding_def, aux_xs_letrec_bindings_of_letrec_bindings_def, MAP_MAP,
            remv_tyvar_aux_xs_lrb_thm, ETA_THM]);

val remv_tyvar_aux_xs_pattern_thm = Q.prove (
`!p. aux_xs_pattern_of_pattern (remv_tyvar_pattern p) = aux_xs_pattern_of_pattern p`,
HO_MATCH_MP_TAC aux_xs_pattern_of_pattern_ind THEN 
SRW_TAC [] [remv_tyvar_pattern_def, aux_xs_pattern_of_pattern_def, MAP_MAP] THENL
[Induct_on `pattern_list` THEN SRW_TAC [] [],
 Induct_on `pattern_list` THEN SRW_TAC [] [],
 Induct_on `field_pattern_list` THEN SRW_TAC [] [LAMBDA_PROD2] THEN Cases_on `h` THEN SRW_TAC [] [] THEN
      Induct_on `field_pattern_list` THEN SRW_TAC [] [LAMBDA_PROD2] THEN METIS_TAC []]);

val remv_tyvar_aux_xs_lb_thm = Q.prove (
`(!lb. aux_xs_let_binding_of_let_binding (remv_tyvar_let_binding lb) = 
       aux_xs_let_binding_of_let_binding lb)`,
Cases THEN SRW_TAC [] [aux_xs_let_binding_of_let_binding_def, remv_tyvar_letrec_binding_def, 
                       remv_tyvar_aux_xs_pattern_thm]);

val remv_tyvar_fv_thm = Q.store_thm ("remv_tyvar_fv_thm",
`(!lrb. fv_letrec_binding (remv_tyvar_letrec_binding lrb) = fv_letrec_binding lrb) /\
 (!lrbs. fv_letrec_bindings (remv_tyvar_letrec_bindings lrbs) = fv_letrec_bindings lrbs) /\
 (!lb. fv_let_binding (remv_tyvar_let_binding lb) = fv_let_binding lb) /\
 (!pe. fv_pat_exp (remv_tyvar_pat_exp pe) = fv_pat_exp pe) /\
 (!pm. fv_pattern_matching (remv_tyvar_pattern_matching pm) = fv_pattern_matching pm) /\
 (!expr. fv_expr (remv_tyvar_expr expr) = fv_expr expr)`,
HO_MATCH_MP_TAC fv_letrec_binding_ind THEN 
SRW_TAC [] [fv_letrec_binding_def, remv_tyvar_letrec_binding_def, MAP_MAP, LAMBDA_PROD2] THENL
[Induct_on `letrec_binding_list` THEN SRW_TAC [] [],
 SRW_TAC [] [remv_tyvar_aux_xs_pattern_thm],
 Induct_on `pat_exp_list` THEN SRW_TAC [] [],
 Induct_on `expr_list` THEN SRW_TAC [] [],
 Induct_on `expr_list` THEN SRW_TAC [] [],
 Induct_on `field_expr_list` THEN SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [] THEN METIS_TAC [],
 Induct_on `field_expr_list` THEN SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [] THEN METIS_TAC [],
 SRW_TAC [] [remv_tyvar_aux_xs_lb_thm],
 SRW_TAC [] [remv_tyvar_aux_xs_lrbs_thm]]);

val _ = export_theory ();
