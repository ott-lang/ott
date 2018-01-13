open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory pairTheory;
open arithmeticTheory;
open ottLib ottTheory caml_typedefTheory;
open utilTheory basicTheory shiftTheory;

val _ = new_theory "environment";

val shiftEB_dom_thm = Q.store_thm ("shiftEB_dom_thm",
`!EB m n. domEB (shiftEB m n EB) = domEB EB`,
Cases THEN SRW_TAC [] [shiftEB_def, domEB_def]);

val shiftE_dom_thm = Q.store_thm ("shiftE_dom_thm",
`!E m n. MAP domEB (shiftE m n E) = MAP domEB E`,
Induct THEN SRW_TAC [] [shiftE_def] THEN Cases_on `h` THEN
SRW_TAC [] [shiftE_def, shiftEB_def, domEB_def]);

val idxsubnEB_dom_thm = Q.store_thm ("idxsubnEB_dom_thm",
`!EB x y. domEB (idxsubnEB x y EB) = domEB EB`,
Cases THEN SRW_TAC [] [idxsubnE_def, idxsubnEB_def, domEB_def]);

val idxsubnE_dom_thm = Q.store_thm ("idxsubnE_dom_thm",
`!E x y. MAP domEB (idxsubnE x y E) = MAP domEB E`,
Induct THEN SRW_TAC [] [idxsubnE_def, idxsubnEB_def] THEN Cases_on `h` THEN
SRW_TAC [] [idxsubnE_def, idxsubnEB_def, domEB_def]);

val typexpr_has0_def = ottDefine "typexpr_has0"
`(typexpr_has0 (TE_var tv) = F) /\
 (typexpr_has0 (TE_idxvar m n) = (m = 0)) /\
 (typexpr_has0 TE_any = F) /\
 (typexpr_has0 (TE_arrow t1 t2) = (typexpr_has0 t1) \/ (typexpr_has0 t2)) /\
 (typexpr_has0 (TE_tuple tl) = EXISTS typexpr_has0 tl) /\
 (typexpr_has0 (TE_constr tl tc) = EXISTS typexpr_has0 tl)`;

val shift_has0_lem = Q.prove (
`(!t. ~(typexpr_has0 (shiftt 0 1 t))) /\
 (!tl. EVERY (\t. ~(typexpr_has0 (shiftt 0 1 t))) tl)`,
Induct THEN SRW_TAC [] [shiftt_def, typexpr_has0_def, o_DEF, EVERY_MAP]);

val mono_ts_def = Define
`mono_ts (TS_forall t) = ~(typexpr_has0 t)`;

val store_env_def = Define
`(store_env [] = T) /\
 (store_env (EB_l l t::E) = store_env E) /\
 (store_env _ = F)`;

val JTstore_env_thm = Q.store_thm ("JTstore_env_thm",
`!E store E'. JTstore E store E' ==> store_env E'`,
HO_MATCH_MP_TAC JTstore_ind THEN SRW_TAC [] [store_env_def]);

val value_env_def = Define
`(value_env [] = T) /\
 (value_env (EB_vn vn t::E) = value_env E) /\
 (value_env _ = F)`;

val mono_value_env_def = Define 
`(mono_value_env [] = T) /\
 (mono_value_env (EB_vn vn ts::E) = mono_ts ts /\ mono_value_env E) /\
 (mono_value_env _ = F)`;

val mono_value_env_value_env_thm = Q.prove (
`!E. mono_value_env E ==> value_env E`,
Induct THEN SRW_TAC [] [mono_value_env_def, value_env_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC list_ss [mono_value_env_def, value_env_def]);

val value_env_mem = Q.store_thm ("value_env_mem",
`!E. value_env E = !EB. MEM EB E ==> ?vn t. (EB = EB_vn vn t)`,
recInduct (fetch "-" "value_env_ind") THEN SRW_TAC [] [value_env_def] THENL
[METIS_TAC [],
 Q.EXISTS_TAC `EB_l v24 v25`,
 Q.EXISTS_TAC `EB_ta v21 v22 v23`,
 Q.EXISTS_TAC `EB_tr v18 v19 v20`,
 Q.EXISTS_TAC `EB_td v16 v17`,
 Q.EXISTS_TAC `EB_fn v12 v13 v14 v15`,
 Q.EXISTS_TAC `EB_pc v8 v9 v10 v11`,
 Q.EXISTS_TAC `EB_cc v6 v7`,
 Q.EXISTS_TAC `EB_tv`] THEN SRW_TAC [] []);

val mono_value_env_mem = Q.store_thm ("mono_value_env_mem",
`!E. mono_value_env E = !EB. MEM EB E ==> (?vn t. (EB = EB_vn vn t) /\ mono_ts t)`,
recInduct (fetch "-" "mono_value_env_ind") THEN SRW_TAC [] [mono_value_env_def] THENL
[METIS_TAC [environment_binding_11],
 Q.EXISTS_TAC `EB_l v24 v25`,
 Q.EXISTS_TAC `EB_ta v21 v22 v23`,
 Q.EXISTS_TAC `EB_tr v18 v19 v20`,
 Q.EXISTS_TAC `EB_td v16 v17`,
 Q.EXISTS_TAC `EB_fn v12 v13 v14 v15`,
 Q.EXISTS_TAC `EB_pc v8 v9 v10 v11`,
 Q.EXISTS_TAC `EB_cc v6 v7`,
 Q.EXISTS_TAC `EB_tv`] THEN SRW_TAC [] []);

val store_env_lookup_lem = Q.store_thm ("store_env_lookup_lem",
`!E. store_env E ==>
            (!x. lookup E (name_tcn x) = NONE) /\
            (!x. lookup E (name_cn x) = NONE) /\
            (!x. lookup E (name_fn x) = NONE) /\
            (!x. lookup E (name_vn x) = NONE) /\
            (!x. lookup E name_tv = NONE)`,
HO_MATCH_MP_TAC Eok2_ind THEN SRW_TAC [] [lookup_def, store_env_def, domEB_def]);

val value_env_lookup_lem = Q.store_thm ("value_env_lookup_lem",
`!E. value_env E ==>
            (!x. lookup E (name_tcn x) = NONE) /\
            (!x. lookup E (name_cn x) = NONE) /\
            (!x. lookup E (name_fn x) = NONE) /\
            (!x. lookup E (name_l x) = NONE) /\
            (!x. lookup E name_tv = NONE)`,
HO_MATCH_MP_TAC Eok2_ind THEN SRW_TAC [] [lookup_def, value_env_def, domEB_def]);

val value_env_num_tv_thm = Q.store_thm ("value_env_num_tv_thm",
`!E. value_env E \/ store_env E ==> (num_tv E = 0)`,
Induct THEN SRW_TAC [] [value_env_def, store_env_def, num_tv_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC list_ss [value_env_def, store_env_def, num_tv_def]);

val value_env_map_thm = Q.store_thm ("value_env_map_thm",
`!l f g. value_env (MAP (\z. EB_vn (f z) (g z)) l)`,
Induct THEN SRW_TAC [] [value_env_def]);

val value_env_append_thm = Q.store_thm ("value_env_append_thm",
`!E1 E2. value_env (E1++E2) = value_env E1 /\ value_env E2`,
Induct THEN SRW_TAC [] [value_env_def] THEN Cases_on `h` THEN SRW_TAC [] [value_env_def]);

val value_env_perm_thm = Q.store_thm ("value_env_perm_thm",
`!E E'. PERM E E' ==> value_env E ==> value_env E'`,
HO_MATCH_MP_TAC sortingTheory.PERM_IND THEN SRW_TAC [] [value_env_def] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [value_env_def] THEN
Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [value_env_def]);

val pat_env_lem = Q.prove (
`!Tsig E pat t E'. JTpat Tsig E pat t E' ==> mono_value_env E'`,
RULE_INDUCT_TAC JTpat_ind [mono_value_env_mem, domEB_def, mono_ts_def, shift_has0_lem] [] THEN
FULL_SIMP_TAC list_ss [MEM_FLAT, SOME_EL_REVERSE, EXISTS_MAP, ELIM_UNCURRY, EVERY_MEM, EXISTS_MEM] THEN 
SRW_TAC [] [mono_ts_def, shift_has0_lem] THEN
METIS_TAC []);

val pat_env_lem = Q.store_thm ("pat_env_lem",
`!Tsig E pat t E'. JTpat Tsig E pat t E' ==> mono_value_env E' /\ value_env E'`,
METIS_TAC [pat_env_lem, mono_value_env_value_env_thm]);


val closed_env_def = Define
`closed_env E = !name vn t. ~(lookup E name = SOME (EB_vn vn t))`;

val closed_env_lem = Q.store_thm ("closed_env_lem",
`!E vp t. closed_env E ==> ~JTvalue_name E vp t`,
SRW_TAC [] [closed_env_def, JTvalue_name_cases]);

val closed_env_tv_lem = Q.store_thm ("closed_env_tv_lem",
`!E. closed_env E ==> closed_env (EB_tv::E)`,
SRW_TAC [] [closed_env_def, lookup_def, domEB_def, COND_EXPAND_EQ] THEN DISJ2_TAC THEN Cases THEN
      SRW_TAC [] [shiftEB_def]);

val closed_env_append_thm = Q.store_thm ("closed_env_append_thm",
`!E1 E2. closed_env E1 /\ closed_env E2 ==> closed_env (E1++E2)`,
SRW_TAC [] [closed_env_def, lookup_append_thm] THEN Cases_on `lookup E1 name` THEN SRW_TAC [] [] THENL
[Cases_on `EB` THEN SRW_TAC [] [shiftEB_def],
METIS_TAC []]);

val store_env_closed_thm = Q.store_thm ("store_env_closed_thm",
`!E. store_env E ==> closed_env E`,
Induct THEN SRW_TAC [] [store_env_def, closed_env_def, lookup_def, COND_EXPAND_EQ] THEN
Cases_on `h` THEN FULL_SIMP_TAC list_ss [domEB_def, store_env_def] THEN SRW_TAC [] [shiftEB_add_thm] THEN
METIS_TAC [closed_env_def]);

val EB_vn_list_thm = Q.store_thm ("EB_vn_list_thm",
`!x_t_list x_t_list'. (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list =
                       MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list') =
                      (x_t_list = x_t_list')`,
Induct THEN SRW_TAC [] [] THEN Cases_on `x_t_list'` THEN FULL_SIMP_TAC list_ss [] THEN
Cases_on `h` THEN Cases_on `h'` THEN SRW_TAC [] [shiftt_11]);

val aux_xs_pattern_of_pattern_thm = Q.store_thm ("aux_xs_pattern_of_pattern_thm",
`!S E p t E'. JTpat S E p t E' ==> (MAP name_vn (aux_xs_pattern_of_pattern p) = MAP domEB (REVERSE E'))`,
RULE_INDUCT_TAC JTpat_ind [aux_xs_pattern_of_pattern_def, JTpat_fun, domEB_def, ELIM_UNCURRY, MAP_MAP,
                           MAP_FLAT, MAP_REVERSE, FLAT_REVERSE, REVERSE_APPEND]
[([``"JTpat_construct"``],
  SRW_TAC [] [] THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN POP_ASSUM (K ALL_TAC) THEN
         Induct_on `pattern_E_t_list` THEN SRW_TAC [] []),
 ([``"JTpat_tuple"``],
  SRW_TAC [] [] THEN NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM MP_TAC THEN
         Induct_on `pattern_t_E_list` THEN SRW_TAC [] []),
 ([``"JTpat_record"``],
  SRW_TAC [] [] THEN NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM MP_TAC THEN
         Induct_on `field_name_pattern_E_t_list` THEN SRW_TAC [] [])]);

val aux_xs_letrec_bindings_of_letrec_bindings_thm = 
Q.store_thm ("aux_xs_letrec_bindings_of_letrec_bindings_thm",
`!S E lrbs E'. JTletrec_binding S E lrbs E' ==>
             (MAP name_vn (aux_xs_letrec_bindings_of_letrec_bindings lrbs) = MAP domEB (REVERSE E'))`,
Cases_on `lrbs` THEN SRW_TAC [] [JTe_fun, aux_xs_letrec_bindings_of_letrec_bindings_def] THEN
SRW_TAC [] [REVERSE_REVERSE, MAP_MAP, domEB_def, aux_xs_letrec_binding_of_letrec_binding_def] THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN Induct_on `value_name_pattern_matching_t_t'_list` THEN
SRW_TAC [] []);

val env_fv_thm = Q.store_thm ("env_fv_thm",
`(!S E e t. JTe S E e t ==> (!x. MEM x (fv_expr e) ==> MEM (name_vn x) (MAP domEB E))) /\
 (!S E pm t t'. JTpat_matching S E pm t t' ==>
              (!x. MEM x (fv_pattern_matching pm) ==> MEM (name_vn x) (MAP domEB E))) /\
 (!S E lb E'. JTlet_binding S E lb E' ==>
            (!x. MEM x (fv_let_binding lb) ==> MEM (name_vn x) (MAP domEB E))) /\
 (!S E lrbs E'. JTletrec_binding S E lrbs E' ==>
              (!x. MEM x (list_minus (fv_letrec_bindings lrbs)
                                     (aux_xs_letrec_bindings_of_letrec_bindings lrbs)) ==>
                   MEM (name_vn x) (MAP domEB E)))`,
RULE_INDUCT_TAC JTe_sind [JTe_fun, fv_letrec_binding_def, domEB_def, list_minus_thm]
[([``"JTe_ident"``], FULL_SIMP_TAC list_ss [JTvalue_name_cases] THEN METIS_TAC [lookup_dom_thm]),
 ([``"JTe_tuple"``, ``"JTe_construct"``, ``"JTe_record_constr"``, ``"JTe_record_with"``],
  FULL_SIMP_TAC list_ss [MEM_FLAT, EVERY_MEM, EXISTS_MEM, MEM_MAP, LAMBDA_PROD2] THEN
        METIS_TAC [FST, SND]),
 ([``"JTe_for"``], METIS_TAC []),
 ([``"JTe_let_mono"``, ``"JTe_let_poly"``],
  SRW_TAC [] [] THENL
         [FULL_SIMP_TAC list_ss [MEM_MAP, MEM_REVERSE, aux_xs_let_binding_of_let_binding_def, REVERSE_REVERSE,
                                 MAP_MAP, domEB_def, REVERSE_EQ, EB_vn_list_thm] THEN
                  RES_TAC THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [domEB_def, name_11] THEN
                  SRW_TAC [] [] THEN METIS_TAC [],
          IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
                  FULL_SIMP_TAC list_ss [MEM_MAP, MEM_REVERSE, aux_xs_let_binding_of_let_binding_def,
                                         REVERSE_REVERSE, MAP_MAP, domEB_def, REVERSE_EQ,
                                         EB_vn_list_thm] THEN
                  RES_TAC THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [domEB_def, name_11] THEN
                  SRW_TAC [] [] THENL [ALL_TAC, METIS_TAC []] THEN
                  `MEM (name_vn (FST z)) (MAP (\z. name_vn (FST z)) x_t_list)`
                             by (SRW_TAC [] [MEM_MAP] THEN METIS_TAC []) THEN
                  `MEM (name_vn (FST z)) (MAP name_vn (aux_xs_pattern_of_pattern pat))` by METIS_TAC [] THEN
                  FULL_SIMP_TAC list_ss [MEM_MAP, name_11]]),
 ([``"JTe_letrec"``],
  SRW_TAC [] [] THENL
        [FULL_SIMP_TAC list_ss [MEM_MAP, MEM_REVERSE] THEN
                 RES_TAC THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
                 FULL_SIMP_TAC list_ss [domEB_def, name_distinct] THEN METIS_TAC [],
         IMP_RES_TAC aux_xs_letrec_bindings_of_letrec_bindings_thm THEN
                 FULL_SIMP_TAC list_ss [MEM_MAP, MEM_REVERSE, MAP_MAP, domEB_def] THEN
                 RES_TAC THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
                 FULL_SIMP_TAC list_ss [domEB_def, name_distinct, name_11] THENL
                 [ALL_TAC, METIS_TAC []] THEN
                 SRW_TAC [] [] THEN
                 `MEM (name_vn (FST z)) (MAP (\z. name_vn (FST z)) x_t_list)`
                             by (SRW_TAC [] [MEM_MAP] THEN METIS_TAC []) THEN
                 `MEM (name_vn (FST z)) (MAP name_vn (aux_xs_letrec_bindings_of_letrec_bindings lrbs))`
                             by METIS_TAC [] THEN
                 FULL_SIMP_TAC list_ss [MEM_MAP, name_11]]),
 ([``"JTpat_matching_pm"``],
  FULL_SIMP_TAC list_ss [MEM_FLAT, MEM_MAP, EVERY_MEM, EXISTS_MEM] THEN
        SRW_TAC [] [] THEN
         FULL_SIMP_TAC list_ss [fv_letrec_binding_def, list_minus_thm] THEN RES_TAC THENL
         [IMP_RES_TAC aux_xs_pattern_of_pattern_thm THEN
                  `MEM (domEB y) (MAP domEB (REVERSE (SND (SND z))))` by METIS_TAC [MEM_REVERSE, MEM_MAP] THEN
                  METIS_TAC [MEM_MAP, name_11],
          METIS_TAC []]),
 ([``"JTletrec_binding_equal_function"``],
  FULL_SIMP_TAC list_ss [aux_xs_letrec_bindings_of_letrec_bindings_def, MAP_MAP,
                         fv_letrec_binding_def, aux_xs_letrec_binding_of_letrec_binding_def,
                         MEM_FLAT, MEM_MAP, EVERY_MEM, EXISTS_MEM] THEN
         SRW_TAC [] [] THEN
         FULL_SIMP_TAC list_ss [fv_letrec_binding_def] THEN METIS_TAC [MEM, domEB_def, name_11])]
THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss []);


val closed_env_fv_thm = Q.store_thm ("closed_env_fv_thm",
`!S E e t. closed_env E /\ JTe S E e t ==> (fv_expr e = [])`,
METIS_TAC [closed_env_def, env_fv_thm, lookup_name_thm, lookup_dom_thm, NOT_MEM_EMPTY]);

val EBok_def = Define
`(EBok E EB_tv = T) /\
 (EBok E (EB_vn vn ts) = tsok E ts) /\
 (EBok E (EB_cc cn TC_exn) = T) /\
 (EBok E (EB_cc cn (TC_name tcn)) =
    ?kind. lookup E (name_tcn tcn) = SOME (EB_td tcn kind)) /\
 (EBok E (EB_cc cn _) = F) /\
 (EBok E (EB_pc cn (TPS_nary vars) (typexprs_inj t_list) TC_exn) =
    LENGTH t_list >= 1 /\ EVERY (tkind E) t_list /\ (vars = [])) /\
 (EBok E (EB_pc cn (TPS_nary vars) (typexprs_inj t_list) (TC_name tcn)) =
    EVERY (\t. ntsok E vars t) t_list /\
    (lookup E (name_tcn tcn) = SOME (EB_td tcn (LENGTH vars))) /\
    LENGTH t_list >= 1) /\
 (EBok E (EB_pc constr_name params (typexprs_inj t_list) tc) = F) /\
 (EBok E (EB_fn field_name (TPS_nary vars) tcn t) =
    ntsok E vars t /\
    ?field_name_list. (lookup E (name_tcn tcn) =
                       SOME (EB_tr tcn (LENGTH vars) field_name_list)) /\
                      MEM field_name field_name_list) /\
 (EBok E (EB_td tcn kind) = T) /\
 (EBok E (EB_ta (TPS_nary tps) tcn t) = ntsok E tps t) /\
 (EBok E (EB_tr tcn kind field_name_list) =
    ALL_DISTINCT (MAP name_fn field_name_list)) /\
 (EBok E (EB_l location t) = tkind E t)`;


val EBok_ind = fetch "-" "EBok_ind";


val remove_vn_tv_def = Define
`remove_vn_tv = FILTER (\n. case n of name_vn vn -> F || name_tv -> F || x -> T)`;

val remove_vn_tv_thm = Q.store_thm ("remove_vn_tv_thm",
`!l name. (!vn. ~(name = name_vn vn)) /\ ~(name = name_tv) ==> (MEM name (remove_vn_tv l) = MEM name l)`,
Induct THEN SRW_TAC [] [remove_vn_tv_def, MEM_FILTER] THEN Cases_on `h` THEN
FULL_SIMP_TAC list_ss [name_case_def] THEN Cases_on `name` THEN SRW_TAC [] []);

val remove_vn_tv_APPEND = Q.store_thm ("remove_vn_tv_APPEND",
`!l1 l2. remove_vn_tv (l1++l2) = remove_vn_tv l1 ++ remove_vn_tv l2`,
Induct THEN SRW_TAC [] [FILTER_APPEND, remove_vn_tv_def]);

val Eok_suffixes_def = Define
`Eok_suffixes E = !E1 E2. (E = E1++E2) ==> Eok E2`;

val ok_lem1 = Q.prove (
`(!E. Eok E ==> Eok_suffixes E) /\
 (!E tc k. (typeconstr_kind E tc = SOME k) ==> Eok_suffixes E) /\
 (!E ts. tsok E ts ==> Eok_suffixes E) /\
 (!E tps t. ntsok E tps t ==> Eok_suffixes E) /\
 (!E t. tkind E t ==> Eok_suffixes E)`,
HO_MATCH_MP_TAC Eok_ind THEN SRW_TAC [] [Eok_suffixes_def, Eok_def] THEN
  FULL_SIMP_TAC list_ss [] THEN
  Cases_on `E1` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [Eok_def] THEN
  TRY (Cases_on `t_list`) THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
  METIS_TAC [APPEND]);

val ok_ok_thm = Q.store_thm ("ok_ok_thm",
`(!E1 E2. Eok (E1++E2) ==> Eok E2) /\
 (!E tc k. (typeconstr_kind E tc = SOME k) ==> Eok E) /\
 (!E ts. tsok E ts ==> Eok E) /\
 (!E tps t. ntsok E tps t ==> Eok E) /\
 (!E t k. tkind E t ==> Eok E)`,
METIS_TAC [Eok_suffixes_def, APPEND, ok_lem1]);

val Eok_dom_thm = Q.store_thm ("Eok_dom_thm",
`!E. Eok E ==> ALL_DISTINCT (remove_vn_tv (MAP domEB E))`,
HO_MATCH_MP_TAC Eok2_ind THEN SRW_TAC [] [remove_vn_tv_def, Eok_def] THEN
FULL_SIMP_TAC list_ss [domEB_def, name_case_def, Eok_def, MEM_FILTER] THEN TRY (Cases_on `t_list`) THEN
TRY (Cases_on `tps`) THEN FULL_SIMP_TAC list_ss [Eok_def] THEN METIS_TAC [ok_ok_thm, APPEND]);

local
val lem1 = SIMP_RULE list_ss [] (Q.SPECL [`EB`, `n`, `0`, `1`] shiftEB_com_lem);
in

val weak_one_tv_lookup_thm = Q.store_thm ("weak_one_tv_lookup_thm",
`!E1 E2 name EB.
  ((lookup (E1++E2) name = SOME EB) ==>
   (lookup (shiftE 0 1 E1++[EB_tv]++E2) name = SOME (shiftEB (num_tv E1) 1 EB)))`,
Induct THEN SRW_TAC [] [lookup_def, shiftE_def, domEB_def, shiftEB_dom_thm, num_tv_def]
 THENL
[IMP_RES_TAC lookup_name_thm THEN SRW_TAC [] [shiftEB_def],
 Cases_on `EB` THEN FULL_SIMP_TAC list_ss [domEB_def, name_11, name_distinct] THEN SRW_TAC [] [shiftEB_def],
 Cases_on `EB` THEN FULL_SIMP_TAC list_ss [domEB_def, name_11, name_distinct] THEN
       SRW_TAC [] [shiftEB_def, num_tv_def],
 Cases_on `h` THEN FULL_SIMP_TAC list_ss [domEB_def, name_11, name_distinct, num_tv_def] THEN
       Q.EXISTS_TAC `shiftEB (num_tv E1) 1 EB2` THEN SRW_TAC [] [lem1],
 Q.EXISTS_TAC `shiftEB (num_tv E1) 1 EB2` THEN SRW_TAC [] [shiftEB_add_thm] THEN
       Cases_on `h` THEN FULL_SIMP_TAC list_ss [domEB_def, name_11, name_distinct, num_tv_def]]);

end;

val weak_one_tv_idx_bound_thm = Q.prove (
`!E1 E2 idx. idx_bound (E1 ++ E2) idx ==>
             ((idx < num_tv E1) ==> idx_bound (shiftE 0 1 E1 ++ [EB_tv] ++ E2) idx) /\
             (~(idx < num_tv E1) ==> idx_bound (shiftE 0 1 E1 ++ [EB_tv] ++ E2) (idx + 1))`,
Induct THEN SRW_TAC [] [idx_bound_def, num_tv_def, shiftE_def, GSYM ADD1] THEN
Cases_on `h` THEN SRW_TAC [] [shiftEB_def] THEN FULL_SIMP_TAC list_ss [idx_bound_def, num_tv_def, ADD1] THEN
Cases_on `idx` THEN FULL_SIMP_TAC list_ss [idx_bound_def, num_tv_def, ADD1]);

val weak_one_tv_ok_thm = Q.store_thm ("weak_one_tv_ok_thm",
`(!E1 E2. Eok (E1++E2) ==> Eok (shiftE 0 1 E1++[EB_tv]++E2)) /\
 (!E1 tc E2 k. (typeconstr_kind (E1++E2) tc = SOME k) ==>
               (typeconstr_kind (shiftE 0 1 E1++[EB_tv]++E2) tc = SOME k)) /\
 (!E1 ts E2. tsok (E1++E2) ts ==> tsok (shiftE 0 1 E1++[EB_tv]++E2) (shiftts (num_tv E1) 1 ts)) /\
 (!E1 tpo t E2. ntsok (E1++E2) tpo t ==> ntsok (shiftE 0 1 E1++[EB_tv]++E2) tpo (shiftt (num_tv E1) 1 t)) /\
 (!E1 t k E2. (tkind (E1++E2) t ==> tkind (shiftE 0 1 E1++[EB_tv]++E2) (shiftt (num_tv E1) 1 t)))`,
INDUCT_TAC Eok_ind [Eok_def, shiftE_def, shiftEB_def, domEB_def, shiftE_dom_thm, num_tv_def, shiftts_def]
[] THEN
SRW_TAC [] [COND_EXPAND_EQ] THEN IMP_RES_TAC weak_one_tv_lookup_thm THEN
SRW_TAC [] [shiftEB_def, shifttes_def, Eok_def, EVERY_MAP, shiftt_def] THEN
FULL_SIMP_TAC list_ss [EVERY_MEM, shiftE_dom_thm, domEB_def] THEN SRW_TAC [] [weak_one_tv_idx_bound_thm]
THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 Cases_on `lookup (E1 ++ E2) (name_tcn typeconstr_name)` THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on `x` THEN FULL_SIMP_TAC list_ss [environment_binding_case_def] THEN
         IMP_RES_TAC weak_one_tv_lookup_thm THEN SRW_TAC [] [shiftEB_def],
 RES_TAC THEN FULL_SIMP_TAC list_ss [subst_shiftt_com_lem, MAP_MAP, shiftt_def]]);

val weak_one_tv_EBok_thm = Q.store_thm ("weak_one_tv_EBok_thm",
`!EB E1 E2. EBok (E1++E2) EB ==> EBok (shiftE 0 1 E1++[EB_tv]++E2) (shiftEB (num_tv E1) 1 EB)`,
Cases THEN SRW_TAC [] [EBok_def, shiftEB_def, weak_one_tv_ok_thm] THENL
[Cases_on `t`,
 Cases_on `t` THEN Cases_on `t0` THEN Cases_on `t1`,
 Cases_on `t`,
 Cases_on `t`] THEN
FULL_SIMP_TAC list_ss [EBok_def, shifttes_def, weak_one_tv_ok_thm, EVERY_MAP, EVERY_MEM] THEN
SRW_TAC [] [] THEN
METIS_TAC [weak_one_tv_lookup_thm, shiftEB_def]);

val weak_lookup_thm = Q.store_thm ("weak_lookup_thm",
`!E1 E2 name EB1 E3.
  ((lookup (E1++E2) name = SOME EB1) /\ ~MEM EB_tv E3 /\
  (MEM name (MAP domEB E1) \/ ~MEM name (MAP domEB E3)) ==>
  (lookup (E1++E3++E2) name = SOME EB1))`,
Induct THEN SRW_TAC [] [lookup_def, domEB_def, shiftEB_add_thm] THEN
FULL_SIMP_TAC list_ss [lookup_dom_thm] THENL
[FULL_SIMP_TAC list_ss [domEB_def, name_distinct, lookup_append_thm, no_num_tv_thm, shiftEB_add_thm],
 METIS_TAC [],
 METIS_TAC []]);

val weak_idx_bound_thm = Q.prove (
`!E1 E2 idx E3. idx_bound (E1++E2) idx /\ ~MEM EB_tv E3 ==> idx_bound (E1++E3++E2) idx`,
Induct THEN SRW_TAC [] [idx_bound_def] THENL
[Induct_on `E3` THEN SRW_TAC [] [idx_bound_def] THEN Cases_on `h` THEN Cases_on `idx` THEN
     FULL_SIMP_TAC (srw_ss()) [idx_bound_def],
 Cases_on `h` THEN FULL_SIMP_TAC list_ss [idx_bound_def] THEN
          Cases_on `idx` THEN FULL_SIMP_TAC list_ss [idx_bound_def]]);

val weak_helper_lem1 = Q.store_thm ("weak_helper_lem1",
`(!t. remove_vn_tv [name_tcn t] = [name_tcn t]) /\
 (!cn. remove_vn_tv [name_cn cn] = [name_cn cn]) /\
 (!fn. remove_vn_tv [name_fn fn] = [name_fn fn]) /\
 (!l. remove_vn_tv [name_l l] = [name_l l])`,
SRW_TAC [] [remove_vn_tv_def]);

val weak_helper_lem2 = Q.store_thm ("weak_helper_lem2",
`!E1 E3 E2 n. Eok (E1++E3++E2) /\ MEM n (MAP domEB (E1++E2)) /\
              ((?tcn. n = name_tcn tcn) \/ (?fn. n = name_fn fn) \/ (?cn. n = name_cn cn) \/
               (?l. n = name_l l)) ==>
                 (MEM n (MAP domEB E1) \/ ~MEM n (MAP domEB E3))`,
SRW_TAC [] [] THEN IMP_RES_TAC Eok_dom_thm THEN FULL_SIMP_TAC list_ss [remove_vn_tv_APPEND] THEN
SRW_TAC [] [Q.prove (`a \/ ~b = b ==> a`, METIS_TAC [])] THEN 
FULL_SIMP_TAC (srw_ss()) [domEB_def, ALL_DISTINCT_APPEND, DISJOINT_APPEND, DISJOINT_MEM, EVERY_MEM] THEN
METIS_TAC [remove_vn_tv_thm, name_distinct]);

val weak_helper_lem3 = Q.store_thm ("weak_helper_lem3",
`!E1 E2 name EB. (lookup (E1++E2) name = SOME EB) ==> MEM name (MAP domEB (E1++E2))`,
METIS_TAC [lookup_dom_thm]);

val weak_ok_thm = Q.store_thm ("weak_ok_thm",
`(!E:environment. T) /\
 (!E1 tc k E2 E3. (typeconstr_kind (E1++E2) tc = SOME k) /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                  (typeconstr_kind (E1++E3++E2) tc = SOME k)) /\
 (!E1 ts E2 E3. tsok (E1++E2) ts /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==> tsok (E1++E3++E2) ts) /\
 (!E1 tps t E2 E3. ntsok (E1++E2) tps t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==>
                   ntsok (E1++E3++E2) tps t) /\
 (!E1 t E2 E3. tkind (E1++E2) t /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==> tkind (E1++E3++E2) t)`,
HO_MATCH_MP_TAC Eok_ind THEN SRW_TAC [] [Eok_def, EVERY_MEM, COND_EXPAND_EQ, weak_idx_bound_thm] THEN
Cases_on `lookup (E1 ++ E2) (name_tcn typeconstr_name)` THEN FULL_SIMP_TAC list_ss [option_case_def] THEN
IMP_RES_TAC lookup_name_thm THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC weak_helper_lem3 THEN IMP_RES_TAC weak_helper_lem2 THEN SRW_TAC [] [] THEN 
IMP_RES_TAC weak_lookup_thm THEN SRW_TAC [] []);

val weak_EBok_thm = Q.store_thm ("weak_EBok_thm",
`!EB1 E3 E1 E2. EBok (E1++E2) EB1 /\ ~MEM EB_tv E3 /\ Eok (E1++E3++E2) ==> EBok (E1++E3++E2) EB1`,
Cases THEN SRW_TAC [] [EBok_def, weak_ok_thm] THENL
[Cases_on `t`,
 Cases_on `t` THEN Cases_on `t0` THEN Cases_on `t1`,
 Cases_on `t`,
 Cases_on `t`] THEN
FULL_SIMP_TAC list_ss [EBok_def, weak_ok_thm, EVERY_MAP, EVERY_MEM] THEN
IMP_RES_TAC weak_helper_lem3 THEN IMP_RES_TAC weak_helper_lem2 THEN SRW_TAC [] [] THEN 
IMP_RES_TAC weak_lookup_thm THEN SRW_TAC [] []);

val tkind_weak_thm = Q.store_thm ("tkind_weak_thm",
`!E1 E2 t. tkind E2 t /\ Eok (E1++E2) ==> tkind (E1++E2) (shiftt 0 (num_tv E1) t)`,
Induct THEN SRW_TAC [] [num_tv_def, shiftt_add_thm] THEN Cases_on `h = EB_tv` THEN
FULL_SIMP_TAC list_ss [num_tv_def, Eok_def] THENL
[RES_TAC THEN
     IMP_RES_TAC ((SIMP_RULE list_ss [] o Q.SPECL [`[]`] o hd o tl o tl o tl o tl o CONJUNCTS)
                 weak_one_tv_ok_thm) THEN
     FULL_SIMP_TAC list_ss [num_tv_def, shiftE_def, GSYM shiftt_add_thm],
 `Eok (E1++E2)` by METIS_TAC [ok_ok_thm, APPEND] THEN
     `num_tv (h::E1) = num_tv E1` by (Cases_on `h` THEN SRW_TAC [] [num_tv_def]) THEN
      SRW_TAC [] [] THEN METIS_TAC [weak_ok_thm, APPEND, APPEND_ASSOC, MEM]]);

val is_tc_EB_def = Define
`(is_tc_EB (EB_ta _ _ _) = T) /\
 (is_tc_EB (EB_td _ _) = T) /\
 (is_tc_EB (EB_tr _ _ _) = T) /\
 (is_tc_EB EB_tv = T) /\
 (is_tc_EB _ = F)`; 

val is_tc_num_tv_thm = Q.prove (
`!E. ~EXISTS is_tc_EB E ==> (num_tv E = 0)`,
Induct THEN SRW_TAC [] [num_tv_def, is_tc_EB_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [num_tv_def, is_tc_EB_def]);

val lookup_str_lem = Q.prove (
`!E. ~EXISTS is_tc_EB E ==> !tcn. lookup E (name_tcn tcn) = NONE`,
Induct THEN SRW_TAC [] [lookup_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [is_tc_EB_def, lookup_def, domEB_def]);

val lookup_str_thm = Q.store_thm ("lookup_str_thm",
`!E1 E2 E3. ~EXISTS is_tc_EB E2 ==> (!x. lookup (E1++E2++E3) (name_tcn x) = lookup (E1++E3) (name_tcn x))`,
HO_MATCH_MP_TAC Eok2_ind THEN
SRW_TAC [] [lookup_def, lookup_append_thm, domEB_def, num_tv_def, is_tc_num_tv_thm,
            num_tv_append_thm, lookup_str_lem,
                Q.prove (`!x. (case x of NONE -> NONE || SOME EB -> SOME EB) = x`,
                         Cases THEN SRW_TAC [] [])]);

val idx_bound_str_thm = Q.prove (
`!E1 E2 E3 idx. ~EXISTS is_tc_EB E2 ==> (idx_bound (E1++E2++E3) idx = idx_bound (E1++E3) idx)`,
Induct THEN SRW_TAC [] [] THENL
[Induct_on `E2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `h` THEN
        FULL_SIMP_TAC (srw_ss()) [is_tc_EB_def, idx_bound_def],
 Cases_on `h` THEN FULL_SIMP_TAC (srw_ss())  [idx_bound_def] THEN 
        Cases_on `idx` THEN FULL_SIMP_TAC (srw_ss())  [idx_bound_def]]);

local

val SPLIT_CASES =
Cases_on `E1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Eok_def] THEN
Cases_on `E2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Eok_def] THEN
Cases_on `E3` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [Eok_def] THEN
FULL_SIMP_TAC (srw_ss()) [is_tc_EB_def];

val lem1 = Q.prove (
`!E1 EB E3. ~is_tc_EB EB ==> (!x. lookup (E1++EB::E3) (name_tcn x) = lookup (E1++E3) (name_tcn x))`,
METIS_TAC [lookup_str_thm, EXISTS_DEF, APPEND, APPEND_NIL, APPEND_ASSOC]);

in

val ok_str_thm = Q.store_thm ("ok_str_thm",
`(!E. Eok E ==> !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> ~EXISTS is_tc_EB E2 ==> Eok (E1++E3)) /\
 (!E tc k. (typeconstr_kind E tc = SOME k) ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> ~EXISTS is_tc_EB E2 ==> 
                        (typeconstr_kind (E1++E3) tc = SOME k)) /\
 (!E ts. tsok E ts ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> ~EXISTS is_tc_EB E2 ==> tsok (E1++E3) ts) /\
 (!E tpo ts. ntsok E tpo ts ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> ~EXISTS is_tc_EB E2 ==> ntsok (E1++E3) tpo ts) /\
 (!E t. tkind E t ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> ~EXISTS is_tc_EB E2 ==> tkind (E1++E3) t)`,
HO_MATCH_MP_TAC Eok_ind THEN SRW_TAC [] [Eok_def] THEN FULL_SIMP_TAC (srw_ss()) [] THENL
[SPLIT_CASES THEN METIS_TAC [ok_ok_thm],
 SPLIT_CASES THEN METIS_TAC [ok_ok_thm],
 SPLIT_CASES THEN METIS_TAC [ok_ok_thm],
 SPLIT_CASES THEN
     METIS_TAC [ok_ok_thm, lookup_str_thm, NOT_EXISTS, APPEND_ASSOC, APPEND, EVERY_DEF, EXISTS_DEF,
                APPEND_NIL, MEM],
 SPLIT_CASES THENL
     [Cases_on `t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [ok_ok_thm],
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [APPEND_NIL, MEM],
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN 
          METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM]],
 SPLIT_CASES THENL
     [Cases_on `t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [ok_ok_thm],
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [APPEND_NIL, MEM],
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN 
          METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM],
      METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM, APPEND_NIL],
      METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM, APPEND_NIL]],
 SPLIT_CASES THENL
     [Cases_on `t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [ok_ok_thm],
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN METIS_TAC [APPEND_NIL, MEM],
      FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN 
          METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM],
      METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM, APPEND_NIL],
      METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM, APPEND_NIL]],
 SPLIT_CASES THENL
     [METIS_TAC [ok_ok_thm],
      METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM, APPEND_NIL],
      METIS_TAC [lookup_str_thm, NOT_EXISTS, EVERY_DEF, EXISTS_DEF, MEM, APPEND_NIL]],
 SPLIT_CASES,
 SPLIT_CASES,
 SPLIT_CASES,
 SPLIT_CASES THEN METIS_TAC [ok_ok_thm],
 METIS_TAC [lookup_str_thm, NOT_EXISTS],
 METIS_TAC [APPEND],
 METIS_TAC [lookup_str_thm, NOT_EXISTS, idx_bound_str_thm],
 FULL_SIMP_TAC list_ss [EVERY_MEM],
 FULL_SIMP_TAC list_ss [EVERY_MEM]]);

end;

val value_env_lookup_str_thm = Q.store_thm ("value_env_lookup_str_thm",
`!E1 E2 E3. value_env E2 ==>
                  (!x. lookup (E1++E2++E3) (name_tcn x) = lookup (E1++E3) (name_tcn x)) /\
                  (!x. lookup (E1++E2++E3) (name_cn x) = lookup (E1++E3) (name_cn x)) /\
                  (!x. lookup (E1++E2++E3) (name_fn x) = lookup (E1++E3) (name_fn x)) /\
                  (!x. lookup (E1++E2++E3) (name_l x) = lookup (E1++E3) (name_l x))`,
HO_MATCH_MP_TAC Eok2_ind THEN
SRW_TAC [] [lookup_def, lookup_append_thm, value_env_lookup_lem, domEB_def, num_tv_def, value_env_num_tv_thm,
            num_tv_append_thm,
                Q.prove (`!x. (case x of NONE -> NONE || SOME EB -> SOME EB) = x`,
                         Cases THEN SRW_TAC [] [])]);

val store_env_lookup_str_thm = Q.store_thm ("store_env_lookup_str_thm",
`!E1 E2 E3. store_env E2 ==>
                  (!x. lookup (E1++E2++E3) (name_tcn x) = lookup (E1++E3) (name_tcn x)) /\
                  (!x. lookup (E1++E2++E3) (name_cn x) = lookup (E1++E3) (name_cn x)) /\
                  (!x. lookup (E1++E2++E3) (name_fn x) = lookup (E1++E3) (name_fn x)) /\
                  (!x. lookup (E1++E2++E3) (name_vn x) = lookup (E1++E3) (name_vn x))`,
HO_MATCH_MP_TAC Eok2_ind THEN
SRW_TAC [] [lookup_def, lookup_append_thm, store_env_lookup_lem, domEB_def, num_tv_def, value_env_num_tv_thm,
            num_tv_append_thm,
                Q.prove (`!x. (case x of NONE -> NONE || SOME EB -> SOME EB) = x`,
                         Cases THEN SRW_TAC [] [])]);

local

val lem1 = Q.prove (
`!E. value_env E \/ store_env E ==> ~EXISTS is_tc_EB E`,
HO_MATCH_MP_TAC Eok2_ind THEN SRW_TAC [] [value_env_def, store_env_def, is_tc_EB_def]);

in

val value_env_ok_str_thm = Q.store_thm ("value_env_ok_str_thm",
`(!E. Eok E ==> !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> value_env E2 \/ store_env E2 ==> Eok (E1++E3)) /\
 (!E tc k. (typeconstr_kind E tc = SOME k) ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> value_env E2 \/ store_env E2 ==> 
                        (typeconstr_kind (E1++E3) tc = SOME k)) /\
 (!E ts. tsok E ts ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> value_env E2 \/ store_env E2 ==> tsok (E1++E3) ts) /\
 (!E tpo ts. ntsok E tpo ts ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> value_env E2 \/ store_env E2 ==> ntsok (E1++E3) tpo ts) /\
 (!E t. tkind E t ==>
           !E1 E2 E3. (E = E1 ++ E2 ++ E3) ==> value_env E2 \/ store_env E2 ==> tkind (E1++E3) t)`,
METIS_TAC [ok_str_thm, lem1]);

end;

val type_env_def = Define
`(type_env [] = T) /\
 (type_env (EB_vn x y::E) = F) /\
 (type_env (EB_l l t::E) = F) /\
 (type_env (EB_tv::E) = F) /\
 (type_env (EB::E) = type_env E)`;

val type_env_append_thm = Q.store_thm ("type_env_append_thm",
`!E1 E2. type_env (E1++E2) = type_env E1 /\ type_env E2`,
Induct THEN SRW_TAC [] [type_env_def] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [type_env_def]);

val type_env_closed_thm = Q.store_thm ("type_env_closed_thm",
`!E. type_env E ==> closed_env E`,
Induct THEN SRW_TAC [] [type_env_def, closed_env_def, lookup_def, COND_EXPAND_EQ] THEN
Cases_on `h` THEN FULL_SIMP_TAC list_ss [domEB_def, type_env_def] THEN SRW_TAC [] [shiftEB_add_thm] THEN
METIS_TAC [closed_env_def]);


val _ = export_theory();
