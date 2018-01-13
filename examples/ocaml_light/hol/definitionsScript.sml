(*
load "preservationTheory";
load "progressTheory";
load "ottLib";
load "rich_listTheory";
load "storeTheory";
quietdec:=true;
*)
open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open sortingTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory shiftTheory environmentTheory validTheory progressTheory preservationTheory;
open weakenTheory substsTheory remv_tyvarTheory strengthenTheory env_permTheory storeTheory;
(*
quietdec:=false;
*)

val _ = new_theory("definitions");

val _ = Parse.hide "S";

val type_env_rev_thm = Q.prove (
`!E. type_env (REVERSE E) = type_env E`,
Induct THEN SRW_TAC [] [type_env_def, type_env_append_thm] THEN Cases_on `h` THEN SRW_TAC [] [type_env_def]);

val typedef_type_env_thm = Q.prove (
`!tdl E1 E2 E3. JTtypedef tdl E1 E2 E3 ==> type_env E1 /\ type_env E2 /\ type_env E3`,
RULE_INDUCT_TAC JTtypedef_ind [type_env_def, type_env_append_thm, type_env_rev_thm]
[([``"JTtypedef_def_sum"``],
  SRW_TAC [] [] THEN Induct_on `constr_decl_EB_list` THEN FULL_SIMP_TAC list_ss [type_env_def] THEN
      FULL_SIMP_TAC list_ss [type_env_def, EVERY_MEM, JTconstr_decl_cases] THEN SRW_TAC [] [] THEN
      SRW_TAC [] [type_env_def]),
 ([``"JTtypedef_def_record"``],
  SRW_TAC [] [] THEN Induct_on `field_name_t_EB_list` THEN FULL_SIMP_TAC list_ss [type_env_def] THEN
      FULL_SIMP_TAC list_ss [type_env_def, EVERY_MEM, JTfield_decl_cases, ELIM_UNCURRY] THEN SRW_TAC [] [] THEN
      SRW_TAC [] [type_env_def])]);

val type_definition_type_env_thm = Q.prove (
`!E tds E'. JTtype_definition E tds E' ==> type_env E'`,
HO_MATCH_MP_TAC JTtype_definition_ind THEN SRW_TAC [] [type_env_append_thm] THEN
METIS_TAC [typedef_type_env_thm]);

val ds_value_type_env_thm = Q.prove (
`!E ds_value E'. JTdefinitions E ds_value E' ==> type_env E /\ is_definitions_value_of_definitions ds_value
               ==> type_env E'`,
HO_MATCH_MP_TAC JTdefinitions_ind THEN SRW_TAC [] [type_env_def, type_env_append_thm] THEN
Cases_on `definition` THEN
FULL_SIMP_TAC list_ss [JTdefinition_fun, is_definitions_value_of_definitions_def, type_env_def,
                       is_definition_value_of_definition_def, JTconstr_decl_cases] THEN SRW_TAC [] [] THEN
METIS_TAC [type_definition_type_env_thm]);

val substs_x_to_vn_e_list_def = Define
`substs_x_to_vn_e_list (substs_x_xs vn_e_list) = vn_e_list`;

val substs_x_to_vn_e_list_thm = Q.prove (
`!l. substs_x_xs (substs_x_to_vn_e_list l) = l`,
Cases THEN SRW_TAC [] [substs_x_to_vn_e_list_def]);

local

val lem1 = Q.prove (
`!l f. LRBs_inj (MAP (\x. LRB_simple (FST case x of LRB_simple y z -> (y,f z,z))
                                   (SND (SND case x of LRB_simple y z -> (y,f z,z)))) (lrbs_to_lrblist l)) =
     l`,
Induct THEN SRW_TAC [] [lrbs_to_lrblist_def] THEN Induct_on `l` THEN SRW_TAC [] [] THEN Cases_on `h` THEN
SRW_TAC [] []);

val lem2 = Q.prove (
`!l'. EVERY (\x. recfun l (SND (SND case x of LRB_simple y z -> (y,recfun l z,z))) =
                 FST (SND case x of LRB_simple y z -> (y,recfun l z,z))) l'`,
Induct THEN SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] []);

in

val defs_progress_thm = Q.prove (
`!E ds E'. JTdefinitions E ds E' ==> !ds_value. is_definitions_value_of_definitions ds_value /\
                                                closed_env E ==>
           ((ds = Ds_nil) \/
            (?L ds_value' prog. JRdefn ds_value (Prog_defs ds) L ds_value' prog))`,
HO_MATCH_MP_TAC JTdefinitions_ind THEN SRW_TAC [] [] THEN Cases_on `definition` THEN
FULL_SIMP_TAC list_ss [JRdefn_fun, JTdefinition_fun] THEN SRW_TAC [] [] THEN
`closed_env (EB_tv::E)` by METIS_TAC [closed_env_tv_lem] THEN
IMP_RES_TAC e_progress_thm THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JRB_ebehaviour_cases] THEN
SRW_TAC [] [EXISTS_OR_THM] THENL
[Cases_on `~JM_matchP e p` THEN1 METIS_TAC [] THEN FULL_SIMP_TAC list_ss [JM_matchP_thm] THEN
        IMP_RES_TAC JMmatch_val_subst_thm THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [substs_x_to_vn_e_list_thm],
 METIS_TAC [],
 Cases_on `~JM_matchP e p` THEN1 METIS_TAC [] THEN FULL_SIMP_TAC list_ss [JM_matchP_thm] THEN
        IMP_RES_TAC JMmatch_val_subst_thm THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [substs_x_to_vn_e_list_thm],
 METIS_TAC [],
 Q.EXISTS_TAC `MAP (\x. case x of LRB_simple y z -> (y, recfun l z, z)) (lrbs_to_lrblist l)` THEN
        SRW_TAC [] [MAP_MAP, EVERY_MAP, lem1, lem2]]);
end;

val ds_value_thm = Q.prove (
`!ds_value prog L ds_value' prog'. JRdefn ds_value prog L ds_value' prog' ==>
                                   is_definitions_value_of_definitions ds_value /\
                                   is_definitions_value_of_definitions ds_value'`,
HO_MATCH_MP_TAC JRdefn_ind THEN
SIMP_TAC list_ss [] THEN CONJ_TAC THEN
Induct THEN SRW_TAC [] [is_definitions_value_of_definitions_def, definitions_snoc_def,
                        is_definition_value_of_definition_def]);

val defs_store_progress_thm = Q.prove (
`!ds_value prog L ds_value' prog'. JRdefn ds_value prog L ds_value' prog' ==> !st.
     (!l. MEM l (fl_program prog) ==> ?v. (list_assoc l st = SOME v) /\ is_value_of_expr v) ==>
     ?L' st' prog''. JRdefn ds_value prog L' ds_value' prog'' /\ JRstore st L' st'`,
RULE_INDUCT_TAC JRdefn_ind [JRdefn_fun, fl_definitions_def, fl_definition_def, fl_letrec_binding_def,
                            fl_program_def]
[([``"Jdefn_let_ctx"``], METIS_TAC [e_store_progress_thm])]
THEN SRW_TAC [] [JRstore_cases] THEN METIS_TAC []);

local

val lem1 = Q.prove (
`!E l. type_env E ==> ~MEM (name_l l) (MAP domEB E)`,
Induct THEN SRW_TAC [] [type_env_def, domEB_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC list_ss [type_env_def, domEB_def] THEN SRW_TAC [] []);

in

val defs_env_fl_thm = Q.prove (
`!E ds E'. JTdefinitions E ds E' ==>
           (!x. MEM x (fl_definitions ds) ==> MEM (name_l x) (MAP domEB E))`,
RULE_INDUCT_TAC JTdefinitions_ind [fl_definitions_def]
[]
THEN Cases_on `definition` THEN
SRW_TAC [] [JTdefinition_cases, fl_definition_def] THEN
FULL_SIMP_TAC list_ss [MAP_REVERSE, MAP_MAP, domEB_def, fl_letrec_binding_def] THEN
IMP_RES_TAC env_fl_thm THEN FULL_SIMP_TAC list_ss [fl_letrec_binding_def, domEB_def] THEN SRW_TAC [] [] THENL
[METIS_TAC [],
 FULL_SIMP_TAC list_ss [MEM_MAP] THEN SRW_TAC [] [] THEN METIS_TAC [],
 FULL_SIMP_TAC list_ss [MEM_MAP] THEN SRW_TAC [] [] THEN METIS_TAC [],
 FULL_SIMP_TAC list_ss [MEM_MAP] THEN SRW_TAC [] [] THEN METIS_TAC [],
 METIS_TAC [lem1, type_definition_type_env_thm],
 FULL_SIMP_TAC list_ss [JTconstr_decl_cases] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [domEB_def] THEN
             SRW_TAC [] [] THEN METIS_TAC []]);

val progress_thm = Q.prove (
`!E prog st E1. JTtop E prog st E1 ==> !ds_value. (is_definitions_value_of_definitions ds_value) /\
                                          (JTdefinitions [] ds_value E) ==> JRB_dbehaviour ds_value prog st`,
SRW_TAC [] [JTtop_cases, JRB_dbehaviour_cases, JTprog_cases, JRtop_cases] THEN
`closed_env (E'++E)` by METIS_TAC [closed_env_append_thm, store_env_closed_thm, type_env_closed_thm,
                                   JTstore_env_thm, ds_value_type_env_thm, type_env_def] THEN
IMP_RES_TAC defs_progress_thm THEN SRW_TAC [] [] THEN DISJ2_TAC THEN
IMP_RES_TAC defs_store_progress_thm THEN
IMP_RES_TAC defs_env_fl_thm THEN FULL_SIMP_TAC list_ss [] THEN
`!x. ~MEM (name_l x) (MAP domEB E)` by METIS_TAC [lem1, ds_value_type_env_thm, type_env_def] THEN
FULL_SIMP_TAC list_ss [fl_program_def] THEN IMP_RES_TAC store_typing_thm THEN FULL_SIMP_TAC list_ss [] THEN
METIS_TAC [ds_value_thm]);

val progress_thm = save_thm("progress_thm", SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]
                                                      progress_thm);
end;

val helper_lem1 = Q.prove (
`!l1 l2. (REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l1) =
          REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l2)) =
   (l2 = l1)`,
SIMP_TAC list_ss [REVERSE_EQ] THEN Induct THEN SRW_TAC [] [] THEN
Cases_on `l2` THEN SRW_TAC [] [] THEN Cases_on `h` THEN Cases_on `h'` THEN SRW_TAC [] [shiftt_11] THEN
METIS_TAC []);


local

val lem1 = Q.prove (
`!E' x. type_env E' ==> ~MEM (name_vn x) (MAP domEB E')`,
Induct THEN SRW_TAC [] [] THEN Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [type_env_def, domEB_def]);

in

val aux_xs_definition_of_definition_thm = Q.prove (
`!E d E'. JTdefinition E d E' ==> 
          (!x. MEM x (aux_xs_definition_of_definition d) = MEM (name_vn x) (MAP domEB E'))`,
RULE_INDUCT_TAC JTdefinition_ind [JTdefinition_fun, aux_xs_definition_of_definition_def,
                                  aux_xs_let_binding_of_let_binding_def , JTe_fun]
[([``"JTdefinition_let_poly"``, ``"JTdefinition_let_mono"``],
  SRW_TAC [] [MAP_MAP, MAP_REVERSE, domEB_def] THEN 
      FULL_SIMP_TAC list_ss [helper_lem1] THEN SRW_TAC [] [] THEN
      IMP_RES_TAC (GSYM aux_xs_pattern_of_pattern_thm) THEN 
      FULL_SIMP_TAC (srw_ss()) [MAP_MAP, domEB_def] THEN SRW_TAC [] [MEM_MAP]),
 ([``"JTdefinition_letrec"``],
  SRW_TAC [] [MAP_MAP, domEB_def, MAP_REVERSE] THEN 
      IMP_RES_TAC (GSYM aux_xs_letrec_bindings_of_letrec_bindings_thm) THEN
      FULL_SIMP_TAC (srw_ss()) [MAP_MAP, domEB_def] THEN SRW_TAC [] [MEM_MAP]),
 ([``"JTdefinition_typedef"``],
  METIS_TAC [lem1, type_definition_type_env_thm]),
 ([``"JTdefinition_exndef"``],
  SRW_TAC [] [JTconstr_decl_cases] THEN SRW_TAC [] [domEB_def])]);

end;


val type_def_store_env_str_thm = Q.prove (
`!E td E'. JTtype_definition E td E' ==> !E1 E2 E3. (E = E1++E2++E3) /\ (store_env E2 \/ value_env E2) ==>
           JTtype_definition (E1++E3) td E'`,
RULE_INDUCT_TAC JTtype_definition_ind []
[([``"JTtype_definition_swap"``], METIS_TAC [JTtype_definition_rules]),
 ([``"JTtype_definition_list"``],
   SRW_TAC [] [] THEN ONCE_REWRITE_TAC [JTtype_definition_cases] THEN SRW_TAC [] [] THEN DISJ1_TAC THEN
                METIS_TAC [APPEND_ASSOC, value_env_ok_str_thm])]);

val type_def_ok_thm = Q.prove (
`!E td E'. JTtype_definition E td E' ==> Eok (E'++E)`,
RULE_INDUCT_TAC JTtype_definition_ind [] []);

val defs_ok_thm = Q.prove (
`!E defs E'. JTdefinitions E defs E' ==> Eok (E'++E)`,
RULE_INDUCT_TAC JTdefinitions_ind [] []);

val prog_ok_thm = Q.prove (
`!E prog E'. JTprog E prog E' ==> Eok (E'++E)`,
SRW_TAC [] [JTprog_cases] THEN SRW_TAC [] [] THEN METIS_TAC [ok_thm, ok_ok_thm, defs_ok_thm]);

val weak_type_def_thm = Q.prove (
`!E td E'. JTtype_definition E td E' ==> 
           !E1. (E = E1++E2) /\ ~MEM EB_tv E3 /\ Eok (E'++E1++E3++E2) ==> 
           JTtype_definition (E1++E3++E2) td E'`,
RULE_INDUCT_TAC JTtype_definition_ind []
[([``"JTtype_definition_swap"``],
  SRW_TAC [] [JTtype_definition_rules]),
 ([``"JTtype_definition_list"``],
  ONCE_REWRITE_TAC [JTtype_definition_cases] THEN SRW_TAC [] [] THEN
      METIS_TAC [])]); 


local

val lem1 = 
  hd (tl (tl (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] weak_not_tv_thm))));

val lem2 = 
  hd (tl (tl (tl (CONJUNCTS (SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] weak_not_tv_thm)))));

in

val weak_def_thm = Q.prove (
`!E d E'. JTdefinition E d E' ==>
     !E1. (E = E1++E2) /\ ~MEM EB_tv E3 /\ 
          (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_definition d)) ==> MEM n (MAP domEB E1)) /\ 
          Eok (E'++E1++E3++E2) ==>
          JTdefinition (E1++E3++E2) d E'`,
RULE_INDUCT_TAC JTdefinition_ind [JTdefinition_fun, fv_definition_def]
[([``"JTdefinition_let_mono"``, ``"JTdefinition_let_poly"``],
  SRW_TAC [] [] THEN `Eok (E1++E3++E2)` by METIS_TAC [ok_ok_thm, APPEND_ASSOC] THEN
      `Eok (EB_tv::E1++E3++E2)` by SRW_TAC [] [Eok_def] THEN
      FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC lem1 THEN FULL_SIMP_TAC list_ss [domEB_def] THEN
      METIS_TAC []),
 ([``"JTdefinition_letrec"``],
  SRW_TAC [] [] THEN  `Eok (E1++E3++E2)` by METIS_TAC [ok_ok_thm, APPEND_ASSOC] THEN
      `Eok (EB_tv::E1++E3++E2)` by SRW_TAC [] [Eok_def] THEN
      FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC lem2 THEN FULL_SIMP_TAC list_ss [domEB_def] THEN
      FULL_SIMP_TAC list_ss [MEM_MAP, list_minus_thm] THEN METIS_TAC []),
 ([``"JTdefinition_typedef"``],
  METIS_TAC [weak_type_def_thm]),
 ([``"JTdefinition_exndef"``],
  METIS_TAC [ok_ok_thm, APPEND])]);

end;

val weak_defs_thm = Q.prove (
`!E ds E'. JTdefinitions E ds E' ==>
     !E1. (E = E1++E2) /\ ~MEM EB_tv E3 /\ 
          (!n. MEM n (MAP domEB E3) /\ MEM n (MAP name_vn (fv_definitions ds)) ==> MEM n (MAP domEB E1)) /\ 
          Eok (E'++E1++E3++E2) ==>
          JTdefinitions (E1++E3++E2) ds E'`,
RULE_INDUCT_TAC JTdefinitions_ind [JTdefinitions_fun, fv_definitions_def]
[([``"JTdefinitions_item"``],
 SRW_TAC [] [] THEN Q.EXISTS_TAC `E'` THEN SRW_TAC [] [] THENL
     [MATCH_MP_TAC (SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] weak_def_thm) THEN
          FULL_SIMP_TAC list_ss [MEM_MAP, list_minus_thm] THEN METIS_TAC [ok_ok_thm, APPEND_ASSOC],
      FULL_SIMP_TAC list_ss [] THEN IMP_RES_TAC aux_xs_definition_of_definition_thm THEN
          FULL_SIMP_TAC list_ss [MEM_MAP, list_minus_thm] THEN METIS_TAC []])]);

local

val lem1 = Q.prove (
`!E l. value_env E ==> ~MEM (name_l l) (MAP domEB E)`,
recInduct Eok2_ind THEN SRW_TAC [] [domEB_def, value_env_def]);

val lem3 = Q.prove (
`!E l. type_env E ==> ~MEM (name_l l) (MAP domEB E)`,
Induct THEN SRW_TAC [] [] THEN 
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [domEB_def, type_env_def]);

val lem4 = Q.prove (
`!E ds E'. JTdefinitions E ds E' ==> !l. ~MEM (name_l l) (MAP domEB E')`,
HO_MATCH_MP_TAC JTdefinitions_ind THEN SRW_TAC [] [type_env_def, type_env_append_thm] THEN
Cases_on `definition` THEN
FULL_SIMP_TAC list_ss [JTdefinition_fun, is_definitions_value_of_definitions_def, type_env_def,
                       is_definition_value_of_definition_def, JTconstr_decl_cases] THEN
SRW_TAC [] [MAP_REVERSE, MAP_MAP, domEB_def] THEN SRW_TAC [] [MEM_MAP] THEN
METIS_TAC [type_definition_type_env_thm, lem3, MEM_MAP]);

in

val val_env_defs_label_weak_thm = Q.prove (
`!E1 E2 E3 E4 ds. JTdefinitions (E1++E2) ds E4 /\ value_env E1 /\ (?S. JTLout S E2 L E3) /\
                  (?S. JTLin S E2 L) ==>
                  JTdefinitions (E1++E3++E2) ds E4`,
SRW_TAC [] [JTLout_cases, JTLin_cases] THEN SRW_TAC [] [] THEN
MATCH_MP_TAC ((GEN_ALL o 
                SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] o
                hd o CONJUNCTS) weak_defs_thm) THEN
SRW_TAC [] [domEB_def, MEM_MAP] THEN 
MATCH_MP_TAC weak_one_loc_ok_thm THEN
IMP_RES_TAC lem4 THEN IMP_RES_TAC lem1 THEN FULL_SIMP_TAC list_ss [] THEN 
METIS_TAC [APPEND_ASSOC, defs_ok_thm, ok_thm]);

end;

local

val lem1 = List.nth (CONJUNCTS (SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] subst_for_def_lem),
                     2);

val lem2 = List.nth (CONJUNCTS (SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] subst_for_def_lem),
                     3);

in

val def_subst_thm = Q.prove (
`!E d E'. JTdefinition E d E' ==>
          !S E1 E2 x v t. (E = E1++[EB_vn x (TS_forall t)]++E2) /\
                          is_non_expansive_of_expr v /\
                          ~MEM (name_vn x) (MAP domEB E1) /\ closed_env E2 /\
                          JTe S (EB_tv::E2) v t ==>
          JTdefinition (E1++E2)
                       (subst_value_name_definition (remv_tyvar_expr v) x d)
                       E'`,
RULE_INDUCT_TAC JTdefinition_ind [subst_value_name_definition_def, JTdefinition_fun]
[([``"JTdefinition_typedef"``], METIS_TAC [type_def_store_env_str_thm, value_env_def]),
 ([``"JTdefinition_exndef"``], 
  SRW_TAC [] [JTconstr_decl_cases] THEN METIS_TAC [value_env_ok_str_thm, value_env_def]),
 ([``"JTdefinition_let_mono"``],
  SRW_TAC [] [subst_value_name_letrec_binding_def] THEN
      DISJ2_TAC THEN Q.EXISTS_TAC `x_t'_list` THEN SRW_TAC [] [GSYM subst_value_name_letrec_binding_def] THEN
      Q.EXISTS_TAC `Tsigma` THEN MATCH_MP_TAC lem1 THEN METIS_TAC [remv_tyvar_thm]),
 ([``"JTdefinition_let_poly"``],
  SRW_TAC [] [subst_value_name_letrec_binding_def] THEN
      DISJ1_TAC THEN Q.EXISTS_TAC `x_t'_list` THEN SRW_TAC [] [GSYM subst_value_name_letrec_binding_def] THEN
      Q.EXISTS_TAC `Tsigma` THEN SRW_TAC [] [] THEN1
      METIS_TAC [subst_nexp_thm, nexp_remv_tyvar_thm] THEN
      SIMP_TAC std_ss [GSYM APPEND] THEN MATCH_MP_TAC lem1 THEN SRW_TAC [] [domEB_def] THEN
      METIS_TAC [remv_tyvar_thm]),
 ([``"JTdefinition_letrec"``],
  SRW_TAC [] [subst_value_name_letrec_binding_def] THEN Q.EXISTS_TAC `x_t'_list` THEN
      SRW_TAC [] [GSYM subst_value_name_letrec_binding_def] THEN Q.EXISTS_TAC `Tsigma` THEN
      FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC lem2 THEN
      FULL_SIMP_TAC (srw_ss()) [domEB_def] THEN
      METIS_TAC [remv_tyvar_thm])]);

end;

val value_env_def_str_thm = Q.prove (
`!E d E'. JTdefinition E d E' ==>
          !E1. (E = E1++E2++E3) /\ value_env E2 /\
          (!x. MEM x (MAP domEB E2) ==> MEM x (MAP domEB E1)) ==>
          JTdefinition (E1++E3) d E'`,
RULE_INDUCT_TAC JTdefinition_ind [JTdefinition_fun]
[([``"JTdefinition_let_poly"``],
  SRW_TAC [] [] THEN
      DISJ1_TAC THEN MAP_EVERY Q.EXISTS_TAC [`x_t'_list`, `Tsigma`] THEN 
      FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC value_env_str_thm THEN
      FULL_SIMP_TAC list_ss [domEB_def]),
 ([``"JTdefinition_let_mono"``],
  SRW_TAC [] [] THEN
      DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC [`x_t'_list`, `Tsigma`] THEN 
      FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC value_env_str_thm THEN
      FULL_SIMP_TAC list_ss [domEB_def]),
 ([``"JTdefinition_letrec"``],
  SRW_TAC [] [] THEN
      MAP_EVERY Q.EXISTS_TAC [`x_t'_list`, `Tsigma`] THEN 
      FULL_SIMP_TAC std_ss [GSYM APPEND] THEN IMP_RES_TAC value_env_str_thm THEN
      FULL_SIMP_TAC list_ss [domEB_def]),
 ([``"JTdefinition_typedef"``],
  METIS_TAC [type_def_store_env_str_thm]),
 ([``"JTdefinition_exndef"``],
  SRW_TAC [] [JTconstr_decl_cases] THEN METIS_TAC [value_env_ok_str_thm])]);

val value_env_defs_str_thm = Q.prove (
`!E ds E'. JTdefinitions E ds E' ==>
           !E1. (E = E1++E2++E3) /\ value_env E2 /\
           (!x. MEM x (MAP domEB E2) ==> MEM x (MAP domEB E1)) ==>
           JTdefinitions (E1++E3) ds E'`,
RULE_INDUCT_TAC JTdefinitions_ind [JTdefinitions_fun]
[([``"JTdefinitions_empty"``],
  METIS_TAC [value_env_ok_str_thm]),
 ([``"JTdefinitions_item"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `E'` THEN SRW_TAC [] [] THEN METIS_TAC [value_env_def_str_thm])]);

val defs_subst_thm = Q.prove (
`!E ds E'. JTdefinitions E ds E' ==> 
           !E1 E2 x v t. (E = E1++[EB_vn x (TS_forall t)]++E2) /\
                           is_non_expansive_of_expr v /\
                           ~MEM (name_vn x) (MAP domEB E1) /\ closed_env E2 /\
                           (?S. JTe S (EB_tv::E2) v t) ==>
           JTdefinitions (E1++E2) 
                         (subst_value_name_definitions (remv_tyvar_expr v) x ds)
                         E'`,
RULE_INDUCT_TAC JTdefinitions_sind [subst_value_name_definitions_def, JTdefinitions_fun]
[([``"JTdefinitions_empty"``],
  METIS_TAC [value_env_def, value_env_ok_str_thm]),
 ([``"JTdefinitions_item"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `E'` THEN SRW_TAC [] [] THENL
      [METIS_TAC [def_subst_thm],
       IMP_RES_TAC aux_xs_definition_of_definition_thm THEN
           MATCH_MP_TAC (GEN_ALL (SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] 
                                                    value_env_defs_str_thm)) THEN
           SRW_TAC [] [] THEN
           Q.EXISTS_TAC `[EB_vn x (TS_forall t)]` THEN SRW_TAC [] [value_env_def, domEB_def] THEN
           FULL_SIMP_TAC list_ss [],
       METIS_TAC [def_subst_thm],
       IMP_RES_TAC aux_xs_definition_of_definition_thm THEN
           Q.PAT_ASSUM `!E1' E2' x' v t'. P E1' E2' x' v t' ==> 
                             JTdefinitions (E1' ++ E2')
                                           (subst_value_name_definitions (remv_tyvar_expr v) x' ds) E''`
                       MATCH_MP_TAC THEN
           SRW_TAC [] [] THEN METIS_TAC []])]);

val def_substs_empty_thm = Q.prove (
`!d. substs_value_name_definition [] d = d`,
Induct THEN SRW_TAC [] [substs_value_name_definition_def, substs_empty_thm]);

val defs_substs_empty_thm = Q.prove (
`!ds. substs_value_name_definitions [] ds = ds`,
Induct THEN SRW_TAC [] [substs_value_name_definitions_def, def_substs_empty_thm]);

local

val lem1 = Q.prove (
`(!lrbs v x. aux_xs_letrec_bindings_of_letrec_bindings (subst_value_name_letrec_bindings v x lrbs) =
            aux_xs_letrec_bindings_of_letrec_bindings lrbs) /\
 (!lrb v x. aux_xs_letrec_binding_of_letrec_binding (subst_value_name_letrec_binding v x lrb) =
            aux_xs_letrec_binding_of_letrec_binding lrb) /\
 (!lrb_list v x. MAP (\lrb. aux_xs_letrec_binding_of_letrec_binding
                                    (subst_value_name_letrec_binding v x lrb)) lrb_list =
                 MAP aux_xs_letrec_binding_of_letrec_binding lrb_list)`,
Induct THEN 
SRW_TAC [] [aux_xs_letrec_bindings_of_letrec_bindings_def, subst_value_name_letrec_binding_def,
                aux_xs_letrec_binding_of_letrec_binding_def, MAP_MAP]);

val lem2 = Q.prove (
`!l v x. aux_xs_let_binding_of_let_binding (subst_value_name_let_binding v x l) = 
         aux_xs_let_binding_of_let_binding l`,
Cases THEN SRW_TAC [] [aux_xs_let_binding_of_let_binding_def, subst_value_name_letrec_binding_def]);

val lem3 = Q.prove (
`!d v x. aux_xs_definition_of_definition (subst_value_name_definition v x d) =
         aux_xs_definition_of_definition d`,
Induct THEN 
SRW_TAC [] [aux_xs_definition_of_definition_def, subst_value_name_definition_def, lem2, lem1]);

in

val def_substs_iter_thm = Q.prove (
`!d x v.  (fv_expr v = []) ==>
          (substs_value_name_definition ((x,v)::subs) d = 
           substs_value_name_definition subs (subst_value_name_definition v x d))`,
Induct THEN 
SRW_TAC [] [substs_value_name_definition_def, subst_value_name_definition_def, substs_iter_thm] THEN
FULL_SIMP_TAC list_ss [lem1]);

val defs_substs_iter_thm = Q.prove (
`!ds x v subs.  (fv_expr v = []) ==>
                (substs_value_name_definitions ((x,v)::subs) ds = 
                 substs_value_name_definitions subs (subst_value_name_definitions v x ds))`,
Induct THEN SRW_TAC [] [substs_value_name_definitions_def, subst_value_name_definitions_def] THEN
FULL_SIMP_TAC list_ss [def_substs_iter_thm, lem3]);

end;

val defs_substs_thm = Q.prove (
`!x_t_list x_v_list E ds E'.
  (LENGTH x_t_list = LENGTH x_v_list) /\
  JTdefinitions (REVERSE (MAP (\(x,t). EB_vn x (TS_forall t)) x_t_list)++E) ds E'/\
  EVERY (\(x, v). is_non_expansive_of_expr v) x_v_list /\
  closed_env E /\
  ALL_DISTINCT (MAP FST x_t_list) /\
  EVERY (\((x,t),x',v). (x = x') /\ ?S. JTe S (EB_tv::E) v t) (ZIP (x_t_list,x_v_list)) ==>
  JTdefinitions E (substs_value_name_definitions (MAP (\(x, v). (x, remv_tyvar_expr v)) x_v_list) ds) E'`,
Induct_on `x_t_list` THEN Cases_on `x_v_list` THEN SRW_TAC [] [defs_substs_empty_thm] THEN
Cases_on `h'` THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
`fv_expr (remv_tyvar_expr r') = []` by 
                (FULL_SIMP_TAC list_ss [GSYM MAP_REVERSE, ELIM_UNCURRY] THEN
                     METIS_TAC [closed_env_fv_thm, closed_env_tv_lem, remv_tyvar_fv_thm]) THEN
SRW_TAC [] [defs_substs_iter_thm] THEN
Q.PAT_ASSUM `!x_v_list E'' ds' E'''. P x_v_list E'' ds' E''' ==>
             JTdefinitions E'' (substs_value_name_definitions
                                       (MAP (\(x,v). (x,remv_tyvar_expr v)) x_v_list) ds') E'''`
            MATCH_MP_TAC THEN
SRW_TAC [] [] THEN
MATCH_MP_TAC ((SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o hd o CONJUNCTS) 
                         defs_subst_thm) THEN
SRW_TAC [] [MAP_REVERSE, MAP_MAP, LAMBDA_PROD2] THEN 
FULL_SIMP_TAC (srw_ss()) [domEB_def, MEM_MAP, LAMBDA_PROD2] THEN METIS_TAC []);

local

val lem1 = Q.prove (
`!ds_value E1 E2 E3 E' typedef_list.
      JTdefinitions E3 ds_value E2 /\ JTtype_definition (E1 ++ E2 ++ E3) (TDF_tdf typedef_list) E' /\ 
      store_env E1 ==>
      JTdefinitions E3 (definitions_snoc ds_value (D_type (TDF_tdf typedef_list))) (E' ++ E2)`,
Induct THEN SRW_TAC [] [definitions_snoc_def, JTdefinitions_fun] THEN FULL_SIMP_TAC list_ss [] THEN
SRW_TAC [] [JTdefinition_fun] THENL
[METIS_TAC [APPEND_NIL, type_def_store_env_str_thm],
 METIS_TAC [type_def_store_env_str_thm, type_def_ok_thm, APPEND_NIL],
 METIS_TAC [APPEND_ASSOC]]);

val lem2 = Q.prove (
`!ds_value E1 E2 E3 EB constr_decl.
      JTdefinitions E3 ds_value E2 /\ JTconstr_decl (TPS_nary []) TC_exn constr_decl EB /\
      store_env E1 /\ Eok ([EB]++E1++E2++E3) ==>
      JTdefinitions E3 (definitions_snoc ds_value (D_exception (ED_def constr_decl))) (EB::E2)`,
Induct THEN SRW_TAC [] [definitions_snoc_def, JTdefinitions_fun] THEN 
FULL_SIMP_TAC list_ss [JTconstr_decl_cases, Eok_def] THEN 
SRW_TAC [] [JTdefinition_fun, JTconstr_decl_cases] THEN FULL_SIMP_TAC list_ss [Eok_def] THEN
MAP_EVERY Q.EXISTS_TAC [`E'`, `EB_cc constr_name TC_exn::E''`] THEN SRW_TAC [] [] THEN
POP_ASSUM MATCH_MP_TAC THEN SRW_TAC [] [Eok_def] THEN METIS_TAC []);

val lem3 = Q.prove (
`!tpo tc c EB. JTconstr_decl tpo ts c EB ==> type_env [EB]`,
SRW_TAC [] [JTconstr_decl_cases] THEN SRW_TAC [] [type_env_def]);

val lem4 = Q.prove (
`EVERY (\x. recfun (LRBs_inj (MAP (\z. LRB_simple (FST z) (SND (SND z))) x_e_pattern_matching_list)) 
                   (SND (SND x)) = FST (SND x)) x_e_pattern_matching_list ==>
 EVERY (\x. is_non_expansive_of_expr (FST (SND x))) x_e_pattern_matching_list`,
SRW_TAC [] [EVERY_MEM] THEN METIS_TAC [value_nonexpansive_thm, recfun_is_value]);

val lem5 = Q.prove (
`!l1 l2 f g. (MAP (\z. EB_vn (FST z) (f z)) l1 = MAP (\z. EB_vn (FST z) (g z)) l2) ==>
             (MAP FST l1 = MAP FST l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []);
  
val lem6 = Q.prove (
`!l1 l2. (MAP (\z. LRB_simple (FST z) (SND (SND z))) l1 = MAP (\z. LRB_simple (FST z) (FST (SND z))) l2) ==> 
         (MAP FST l1 = MAP FST l2) /\ (MAP (\x. SND (SND x)) l1 = MAP (\x. FST (SND x)) l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
Cases_on `h` THEN Cases_on `h'` THEN SRW_TAC [] []);

val lem7 = Q.prove (
`!l2 l3 n. 
 n < LENGTH l2 /\
 EVERY (\x. recfun (LRBs_inj (MAP (\z. LRB_simple (FST z) (FST (SND z))) l3)) (SND (SND x)) = FST (SND x)) l2 
 ==>
 (FST (SND (EL n l2)) = 
  recfun (LRBs_inj (MAP (\z. LRB_simple (FST z) (FST (SND z))) l3)) (SND (SND (EL n l2))))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `n` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss []);

val lem8 = Q.prove (
`!l1 l3 n. 
 n < LENGTH l1 /\
 (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l1 = 
  MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z))) (SND (SND (SND z))))))) l3)
 ==>
 (SND (EL n l1) = (TE_arrow (FST (SND (SND (EL n l3)))) (SND (SND (SND (EL n l3))))))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `n` THEN Cases_on `l3` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [shiftt_11]);

val lem9 = Q.prove (
`!l2 l3 n. 
 n < LENGTH l2 /\
 (MAP (\x. SND (SND x)) l2 = MAP (\x. FST (SND x)) l3) ==> 
 (SND (SND (EL n l2)) = FST (SND (EL n l3)))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `n` THEN Cases_on `l3` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) []);


(* 12, 13 and 14 copied from preservationScript *)

val lem12 =
(GEN_ALL o Q.SPECL [`S`, `pm`, `t1`, `t2`, `E1`, `EB_tv::E`] o
SIMP_RULE list_ss [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] o hd o tl o CONJUNCTS) weak_one_tv_thm;

(* 13 and 14 copied from weakenScript *)
val lem13 = SIMP_RULE list_ss [] (Q.SPECL [`t`, `n`, `0`, `1`] (hd (CONJUNCTS shiftt_com_lem)));

val lem14 = Q.prove (
`!l m n f g. shiftE m 1 (MAP (\z. EB_vn (f z) (TS_forall (shiftt 0 1 (g z)))) l) =
             MAP (\z. EB_vn (f z) (TS_forall (shiftt 0 1 (shiftt m 1 (g z))))) l`,
Induct THEN SRW_TAC [] [shiftE_def, shiftEB_def, lem13, shiftts_def] THEN
METIS_TAC [value_env_map_thm, value_env_num_tv_thm, arithmeticTheory.ADD_0]);


(* 17, 18, 19, 20 copied from preservationScript *)

val lem17 = Q.prove (
`!E E'. PERM E E' ==> value_env E ==> value_env E'`,
HO_MATCH_MP_TAC PERM_IND THEN SRW_TAC [] [value_env_def] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [value_env_def] THEN
Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [value_env_def]);

val lem18 = Q.prove (
`!E. value_env E ==> 
     (MAP (\x.  EB_vn (FST (vn_to_x_t x)) (TS_forall (SND (vn_to_x_t x)))) E = E)`,
Induct THEN SRW_TAC [] [value_env_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [value_env_def] THEN Cases_on `t` THEN SRW_TAC [] [vn_to_x_t_def]);


val lem19 = Q.prove (
`!E x_t_list. value_env E ==> 
     (PERM (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list) E ==>
      PERM (MAP FST x_t_list) (MAP FST (MAP vn_to_x_t E)))`,
SRW_TAC [] [] THEN 
`PERM (MAP FST (MAP vn_to_x_t (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list)))
      (MAP FST (MAP vn_to_x_t E))` by METIS_TAC [PERM_MAP] THEN
FULL_SIMP_TAC (srw_ss()) [MAP_MAP, vn_to_x_t_def] THEN METIS_TAC []);


val lem20 = Q.prove (
`!E x_t_list. value_env E ==>
    PERM (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list) E ==>
    PERM (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t_list)
         (MAP (\x. EB_vn (FST (vn_to_x_t x)) (TS_forall (idxsubn 0 [] (SND (vn_to_x_t x))))) E)`,
SRW_TAC [] [] THEN
`PERM (MAP (\x. EB_vn (FST (vn_to_x_t x)) (TS_forall (idxsubn 0 [] (SND (vn_to_x_t x)))))
           (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t_list))
      (MAP (\x. EB_vn (FST (vn_to_x_t x)) (TS_forall (idxsubn 0 [] (SND (vn_to_x_t x))))) E)` by
                METIS_TAC [PERM_MAP] THEN
FULL_SIMP_TAC (srw_ss()) [MAP_MAP, vn_to_x_t_def, sub_shiftt_thm2]);

val lem21 = (SIMP_RULE (srw_ss()) [] o
             GEN_ALL o 
             Q.SPECL [`definitions`, `E''`, `[]`] o 
             SIMP_RULE (srw_ss()) [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM])
            defs_value_perm_thm;

in

val ds_preservation_thm = Q.prove (
`!ds_value p L ds_value' p'. JRdefn ds_value p L ds_value' p' ==> 
       !ds ds' E1 E2 E3 E4. store_env E1 /\ JTdefinitions [] ds_value E2 /\ JTprog (E1++E2) p E3 /\ 
                  (!S. JTLin S (E1++E2) L) ==> 
                  ?E5 E8 E6 E7. JTdefinitions [] ds_value' (E5++E2) /\ JTprog (E7++E1++E5++E2) p' E6 /\
                                (?S. JTLout S (E1++E5++E2) L E7) /\ (E3 = E6++E8++E5) /\ type_env E5 /\
                                ((E5 = []) \/ (E8 = []))`,
RULE_INDUCT_TAC JRdefn_ind [JTprog_cases, JTdefinitions_fun, JTdefinition_fun, JTe_fun, JTL_nil_lem]
[([``"Jdefn_type"``],
  SRW_TAC [] [] THEN MAP_EVERY Q.EXISTS_TAC [`E'`, `[]`, `E''`] THEN SRW_TAC [] [] THEN
         `JTdefinitions (E1 ++ E' ++ E2) definitions E''` by 
                       METIS_TAC [type_definition_type_env_thm, defs_store_type_perm_thm, APPEND] THEN
         METIS_TAC [lem1, APPEND_NIL, type_definition_type_env_thm]),
 ([``"Jdefn_exn"``],
  SRW_TAC [] [] THEN MAP_EVERY Q.EXISTS_TAC [`[EB]`, `[]`, `E''`] THEN SRW_TAC [] [] THEN
         `JTdefinitions (E1 ++ [EB] ++ E2) definitions E''` by 
                          METIS_TAC [defs_store_type_perm_thm, APPEND, lem3] THEN1
         METIS_TAC [lem2, APPEND_NIL, defs_ok_thm, ok_ok_thm] THEN
         FULL_SIMP_TAC list_ss [JTconstr_decl_cases, type_env_def]),
 ([``"Jdefn_let_ctx"``],
  SRW_TAC [] [helper_lem1] THEN MAP_EVERY Q.EXISTS_TAC [`[]`, `[]`] THEN SRW_TAC [] [type_env_def] THENL
      [IMP_RES_TAC nexp_red_thm THEN FULL_SIMP_TAC list_ss [JTLin_cases, JTLout_cases] THEN SRW_TAC [] [] THEN
           `closed_env (EB_tv::(E1 ++ E2))` 
                         by METIS_TAC [closed_env_tv_lem, ds_value_type_env_thm, closed_env_append_thm, 
                                       type_env_closed_thm, store_env_closed_thm, type_env_def] THEN
           IMP_RES_TAC e_preservation_thm THEN FULL_SIMP_TAC (srw_ss()) [JTLin_cases, JTLout_cases] THEN
           `Eok (EB_tv::(E1 ++ E2))` by METIS_TAC [ok_thm, ok_ok_thm] THEN FULL_SIMP_TAC list_ss [] THEN
           MAP_EVERY Q.EXISTS_TAC [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t'_list)`,
                                   `E''`] THEN 
           SRW_TAC [] [] THEN METIS_TAC [],
       POP_ASSUM (ASSUME_TAC o Q.SPEC `Tsigma`) THEN
           `closed_env (E1 ++ E2)`
                         by METIS_TAC [ds_value_type_env_thm, closed_env_append_thm,
                                       type_env_closed_thm, store_env_closed_thm, type_env_def] THEN
           IMP_RES_TAC e_preservation_thm THEN
           Q.EXISTS_TAC `E'''` THEN SRW_TAC [] [] THENL
           [MAP_EVERY Q.EXISTS_TAC [`REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z))))
                                                  x_t'_list)`,
                                   `E''`] THEN
                SRW_TAC [] [] THENL
                [METIS_TAC [label_weak_thm, APPEND_ASSOC],
                 METIS_TAC [val_env_defs_label_weak_thm, value_env_map_thm, MAP_REVERSE, APPEND_ASSOC]],
            METIS_TAC []]]),
 ([``"Jdefn_let_match"``],
  SRW_TAC [] [helper_lem1] THEN Q.EXISTS_TAC `[]` THEN SRW_TAC [] [type_env_def] THENL
      [Q.EXISTS_TAC `REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t'_list)`,
       Q.EXISTS_TAC `REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) x_t'_list)`] THEN
      SRW_TAC [] [] THEN
      MATCH_MP_TAC (SIMP_RULE list_ss [LAMBDA_PROD2] defs_substs_thm) THEN SRW_TAC [] [] THEN 
      IMP_RES_TAC pat_preservation_thm THEN FULL_SIMP_TAC list_ss [] THEN
      IMP_RES_TAC pat_num_bindings_lem THEN FULL_SIMP_TAC list_ss [LENGTH_REVERSE] THEN
      `closed_env (E1++E2)` by METIS_TAC [store_env_closed_thm, type_env_closed_thm, closed_env_append_thm, 
                                          ds_value_type_env_thm, type_env_def] THEN
      IMP_RES_TAC distinct_pat_env THEN 
      FULL_SIMP_TAC list_ss [MAP_REVERSE, domEB_def, MAP_MAP, ALL_DISTINCT_REVERSE] THEN
      `value_env E'''` by METIS_TAC [lem17, value_env_map_thm, MAP_REVERSE] THEN
      `LENGTH (REVERSE E''') = LENGTH x_v_list`
                        by METIS_TAC [LENGTH_REVERSE, LENGTH_MAP, PERM_LENGTH] THENL
      [Q.EXISTS_TAC `MAP (\(x,t). (x, idxsubn 0 [] t)) (MAP vn_to_x_t (REVERSE E'''))` THEN 
           SRW_TAC [] [MAP_MAP, LAMBDA_PROD2] THENL
           [SRW_TAC [] [MAP_MAP, lem18] THEN IMP_RES_TAC distinct_pat_env THEN 
                FULL_SIMP_TAC (srw_ss()) [GSYM MAP_REVERSE] THEN IMP_RES_TAC lem20 THEN
                `ALL_DISTINCT (MAP domEB (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) (REVERSE x_t'_list)))`
                        by FULL_SIMP_TAC (srw_ss()) [MAP_MAP, vn_to_x_t_def, domEB_def] THEN
                METIS_TAC [lem21, APPEND_ASSOC, value_env_map_thm],
            FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [value_nonexpansive_thm],
            SRW_TAC [] [MAP_REVERSE, ALL_DISTINCT_REVERSE] THEN 
                 FULL_SIMP_TAC (srw_ss()) [GSYM MAP_REVERSE] THEN
                 IMP_RES_TAC lem19 THEN IMP_RES_TAC distinct_pat_env THEN
                 FULL_SIMP_TAC (srw_ss()) [MAP_REVERSE, MAP_MAP, domEB_def, LAMBDA_PROD2, 
                                           ALL_DISTINCT_REVERSE] THEN
                 METIS_TAC [MAP_11_ALL_DISTINCT, name_11, PERM_ALL_DISTINCT, PERM_MAP, MAP_MAP, 
                            ALL_DISTINCT_REVERSE],
            SRW_TAC [] [ZIP_MAP, EVERY_MAP] THEN
                FULL_SIMP_TAC (srw_ss()) [ZIP_MAP, EVERY_MAP, shiftt_11] THEN 
                FULL_SIMP_TAC list_ss [EVERY_MEM, LAMBDA_PROD2] THEN 
                SRW_TAC [] [] THEN RES_TAC THEN SRW_TAC [] [vn_to_x_t_def, sub_shiftt_thm2] THEN
                METIS_TAC []],
       Q.EXISTS_TAC `MAP vn_to_x_t (REVERSE E''')` THEN SRW_TAC [] [MAP_MAP, LAMBDA_PROD2] THENL
           [FULL_SIMP_TAC (srw_ss()) [MAP_MAP, lem18, GSYM MAP_REVERSE] THEN IMP_RES_TAC distinct_pat_env THEN
                METIS_TAC [lem21, APPEND_ASSOC, value_env_map_thm], 
            FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [value_nonexpansive_thm],
            SRW_TAC [] [MAP_REVERSE, ALL_DISTINCT_REVERSE] THEN 
                 FULL_SIMP_TAC (srw_ss()) [GSYM MAP_REVERSE] THEN
                 IMP_RES_TAC lem19 THEN IMP_RES_TAC distinct_pat_env THEN
                 FULL_SIMP_TAC (srw_ss()) [MAP_REVERSE, MAP_MAP, domEB_def, LAMBDA_PROD2, 
                                           ALL_DISTINCT_REVERSE] THEN
                 METIS_TAC [MAP_11_ALL_DISTINCT, name_11, PERM_ALL_DISTINCT, PERM_MAP, MAP_MAP, 
                            ALL_DISTINCT_REVERSE],
            SRW_TAC [] [ZIP_MAP, EVERY_MAP] THEN
                FULL_SIMP_TAC (srw_ss()) [ZIP_MAP, EVERY_MAP, shiftt_11] THEN 
                FULL_SIMP_TAC list_ss [EVERY_MEM, LAMBDA_PROD2] THEN 
                SRW_TAC [] [] THEN RES_TAC THEN SRW_TAC [] [vn_to_x_t_def] THEN
                METIS_TAC [weak_one_tv_thm, num_tv_def, shiftE_def, APPEND, vn_to_x_t_def]]]),
 ([``"Jdefn_letrec"``],
  SRW_TAC [] [] THEN 
      MAP_EVERY Q.EXISTS_TAC [`[]`, `REVERSE (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) x_t'_list)`] THEN 
      SRW_TAC [] [type_env_def] THEN
      `(MAP (\z. (FST z,remv_tyvar_expr (FST (SND z)))) x_e_pattern_matching_list) =
        MAP (\z. (FST z,remv_tyvar_expr (SND z))) (MAP (\x. (FST x, FST (SND x))) x_e_pattern_matching_list)`
                      by SRW_TAC [] [MAP_MAP] THEN
      SRW_TAC [] [] THEN
      MATCH_MP_TAC (SIMP_RULE list_ss [LAMBDA_PROD2] defs_substs_thm) THEN SRW_TAC [] [EVERY_MAP] THEN
      `closed_env (E1++E2)` by METIS_TAC [store_env_closed_thm, type_env_closed_thm, closed_env_append_thm, 
                                          ds_value_type_env_thm, type_env_def] THEN
      SRW_TAC [] [] THEN
      Q.EXISTS_TAC `x_t'_list` THEN SRW_TAC [] [] THENL
      [METIS_TAC [LENGTH_MAP, LENGTH_REVERSE],
       METIS_TAC [lem4],
       METIS_TAC [REVERSE_EQ, lem5, MAP_11_ALL_DISTINCT, name_11],
       FULL_SIMP_TAC list_ss [REVERSE_EQ] THEN
           IMP_RES_TAC lem6 THEN
           `MAP FST x_t'_list = MAP FST x_e_pattern_matching_list` by METIS_TAC [lem5] THEN
           `LENGTH x_t'_list = LENGTH x_e_pattern_matching_list` by METIS_TAC [LENGTH_MAP] THEN
           SRW_TAC [] [ZIP_MAP, EVERY_MAP] THEN
           SRW_TAC [] [EVERY_MEM, MEM_ZIP] THEN SRW_TAC [] [] THEN1 METIS_TAC [EL_MAP] THEN 
           Q.EXISTS_TAC `Tsigma` THEN
           IMP_RES_TAC lem7 THEN IMP_RES_TAC lem8 THEN SRW_TAC [] [] THEN 
           MATCH_MP_TAC recfun_pres_thm THEN
           Q.EXISTS_TAC `REVERSE (MAP (\z. (FST z, (shiftt 0 1
                                                           (TE_arrow (FST (SND (SND z)))
                                                                          (SND (SND (SND z)))))))
                                      value_name_pattern_matching_t_t'_list)` THEN
           SRW_TAC [] [closed_env_def] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THENL
           [SRW_TAC [] [lookup_def, domEB_def] THEN
                Cases_on `EB2` THEN SRW_TAC [] [shiftEB_def] THEN METIS_TAC [closed_env_def],
            SRW_TAC [] [JTe_fun] THEN 
                Q.EXISTS_TAC `MAP (\(vn, pm, t, t'). (vn, pm, shiftt 0 1 t, shiftt 0 1 t'))
                                  value_name_pattern_matching_t_t'_list` THEN 
                SRW_TAC [] [EVERY_MEM, ELIM_UNCURRY, MAP_MAP, MAP_REVERSE,
                            shiftt_def] THEN
                FULL_SIMP_TAC list_ss [MEM_MAP] THEN SRW_TAC [] [] THEN
                RES_TAC THEN IMP_RES_TAC lem12 THEN
                FULL_SIMP_TAC list_ss [value_env_map_thm, value_env_num_tv_thm, lem14, 
                                       GSYM shiftt_def, shiftTsig_add_thm, GSYM MAP_REVERSE] THEN
                METIS_TAC [MAP_REVERSE, APPEND, APPEND_ASSOC],
            SRW_TAC [] [MAP_REVERSE, MAP_MAP, EVERY_MEM, ELIM_UNCURRY] THEN
                METIS_TAC [MEM_EL, lem9, LENGTH_MAP]]]),
 ([``"Jdefn_let_raise"``],
  SRW_TAC [] [is_non_expansive_of_expr_def, is_binary_prim_app_value_of_expr_def] THEN
      METIS_TAC [APPEND, APPEND_NIL, type_env_def]),
 ([``"Jdefn_let_not_match"``],
  SRW_TAC [] [is_value_of_expr_def, JTconst_cases, JTconstr_c_cases] THEN
      Q.EXISTS_TAC `[]` THEN SRW_TAC [] [type_env_def] THEN IMP_RES_TAC pat_ok_thm THEN
      IMP_RES_TAC ok_ok_thm THEN FULL_SIMP_TAC list_ss [Eok_def] THEN
      `tkind (E1++E2) (TE_constr [] TC_exn)` by SRW_TAC [] [Eok_def] THEN 
      METIS_TAC [JTeq_rules, APPEND])]);
end;


local

val lem1 = 
 (SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]) ds_preservation_thm;

in

val preservation_thm = Q.store_thm ("preservation_thm",
`!ds_value prog st ds_value' prog' st'. JRtop ds_value prog st ds_value' prog' st' ==>
    !E1 E2. JTdefinitions [] ds_value E1 /\ JTtop E1 prog st E2  ==> 
            ?E3 E4. JTdefinitions [] ds_value' E3 /\ JTtop E3 prog' st' E4`,
HO_MATCH_MP_TAC JRtop_ind THEN SRW_TAC [] [JTtop_cases] THEN 
FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
IMP_RES_TAC JTstore_env_thm THEN
IMP_RES_TAC ds_value_type_env_thm THEN
FULL_SIMP_TAC list_ss [type_env_def] THEN
IMP_RES_TAC store_in_thm THEN
SRW_TAC [] [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
`?E5 E8 E6 E7.
           JTdefinitions [] ds_value' (E5 ++ E1) /\
           JTprog (E7++E'++E5++E1) prog' E6 /\
           (?S. JTLout S (E' ++ E5 ++ E1) L E7) /\
           (E'' = E6 ++ E8 ++ E5) /\ type_env E5 /\
           ((E5 = []) \/ (E8 = []))`
           by METIS_TAC [lem1] THEN
FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THENL
[Q.EXISTS_TAC `E1` THEN SRW_TAC [] [],
 Q.EXISTS_TAC `E5++E1` THEN SRW_TAC [] []] THEN
MAP_EVERY Q.EXISTS_TAC [`E7++E'`, `E6`] THEN SRW_TAC [] [] THENL
[METIS_TAC [store_out_thm],
 `Eok (E'++E5++E1)` by METIS_TAC [prog_ok_thm, ok_ok_thm, APPEND_ASSOC] THEN
     METIS_TAC [store_out_thm, APPEND_ASSOC, type_env_append_thm, type_env_store_weak_thm]]);

end;
 
val type_soundness_thm = SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] (Q.prove (
`!p1 p2. (RTC (\(ds_value, prog, st) (ds_value', prog', st'). JRtop ds_value prog st ds_value' prog' st')) 
         p1 p2 ==>
        !ds_value prog st ds_value' prog' st' E E'.
             (p1 = (ds_value, prog, st)) /\ (p2 = (ds_value', prog', st')) /\
             JTdefinitions [] ds_value E /\ is_definitions_value_of_definitions ds_value /\
             JTtop E prog st E' ==> JRB_dbehaviour ds_value' prog' st'`,
HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN SRW_TAC [] [] THEN1 METIS_TAC [progress_thm] THEN
Cases_on `p1'` THEN Cases_on `r` THEN FULL_SIMP_TAC list_ss [] THEN 
METIS_TAC [preservation_thm, JRtop_cases, ds_value_thm]));

val _ = save_thm ("type_soundness_thm", type_soundness_thm);

val _ = export_theory();
