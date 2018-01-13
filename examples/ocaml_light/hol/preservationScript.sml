(*
load "ottLib";
load "substsTheory";
load "env_permTheory";
quietdec:=true;
*)
open HolKernel Parse bossLib boolLib combinTheory listTheory rich_listTheory optionTheory pairTheory 
open sortingTheory;
open ottLib ottTheory caml_typedefTheory;
open utilTheory basicTheory environmentTheory validTheory strengthenTheory weakenTheory type_substsTheory;
open substsTheory shiftTheory env_permTheory teqTheory;
(*
quietdec:=false;
*)

val _ = new_theory "preservation";

val PERM_lem = Q.prove (
`!l1 l2 l3 P. EVERY P l1 /\ PERM l1 (l2 ++ l3) ==> EVERY P l2`,
SRW_TAC [] [EVERY_MEM] THEN METIS_TAC [MEM_APPEND, PERM_MEM_EQ]);


val EVERY_FORALL = Q.prove (
`!P l. EVERY (\x. !y. P x y) l = !yl. (LENGTH l = LENGTH yl) ==> EVERY (\(x, y). P x y) (ZIP (l, yl))`,
STRIP_TAC THEN Induct THEN SRW_TAC [] [] THENL
[Cases_on `yl` THEN FULL_SIMP_TAC (srw_ss()) [],
 EQ_TAC THEN SRW_TAC [] [] THENL
     [Cases_on `yl` THEN FULL_SIMP_TAC (srw_ss()) [],
      POP_ASSUM (MP_TAC o Q.SPEC `y::MAP (\x. ARB) l`) THEN SRW_TAC [] [],
      Q.PAT_ASSUM `!yl. Q yl` (MP_TAC o Q.SPEC `ARB::yl`) THEN SRW_TAC [] []]]);
 
val EVERY_EXISTS = Q.prove (
`!P l. EVERY (\x. ?y. P x y) l = ?yl. (LENGTH l = LENGTH yl) /\ EVERY (\(x, y). P x y) (ZIP (l, yl))`,
STRIP_TAC THEN Induct THEN SRW_TAC [] [] THENL
[Q.EXISTS_TAC `[]` THEN SRW_TAC [] [],
 EQ_TAC THEN SRW_TAC [] [] THENL
     [Q.EXISTS_TAC `y::yl` THEN FULL_SIMP_TAC (srw_ss()) [],
      Cases_on `yl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
      Cases_on `yl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []]]);

val EVERY_IMP = Q.prove (
`!P Q l. EVERY (\x. P x ==> Q x) l /\ EVERY P l ==> EVERY Q l`,
NTAC 2 STRIP_TAC THEN Induct THEN SRW_TAC [] []);

val EVERY_NEST = Q.prove (
`!l f g. EVERY (\x. EVERY f (g x)) l = EVERY f (FLAT (MAP g l))`,
Induct THEN SRW_TAC [] []);

val LENGTH_FLAT_REVERSE = Q.prove (
`!l. LENGTH (FLAT (REVERSE l)) = LENGTH (FLAT l)`,
Induct THEN SRW_TAC [ARITH_ss] [FLAT_APPEND]);

val _ = Parse.hide "S";

val shift_has0_thm = Q.prove (
`(!t. ~typexpr_has0 t ==> ?t'. t = shiftt 0 1 t') /\
 (!tl. EVERY (\t. ~typexpr_has0 t) tl ==> ?tl'. tl = MAP (\t'. shiftt 0 1 t') tl')`,
Induct THEN SRW_TAC [] [typexpr_has0_def, shiftt_def, o_DEF] THEN1
METIS_TAC [shiftt_def] THEN1
(Q.EXISTS_TAC `TE_idxvar (n-1) n0` THEN SRW_TAC [ARITH_ss] [shiftt_def]) THEN METIS_TAC [shiftt_def, MAP]);

val distinct_pat_env = Q.store_thm ("distinct_pat_env",
`!S E p t E'. JTpat S E p t E' ==> ALL_DISTINCT (MAP domEB E')`,
RULE_INDUCT_TAC JTpat_ind [domEB_def, ALL_DISTINCT_APPEND, DISJOINT_MEM, EVERY_MEM] [] THEN
METIS_TAC []);

val no_value_red_thm = Q.prove (
`!e L e'. is_value_of_expr e ==> ~JR_expr e L e'`,
recInduct is_value_of_expr_ind THEN SRW_TAC [] [is_value_of_expr_def, JR_expr_fun] THEN 
CCONTR_TAC THEN FULL_SIMP_TAC list_ss [is_value_of_expr_def, expr_11, expr_distinct, JR_expr_fun] THEN
METIS_TAC []);

val binary_primapp_lem = Q.prove (
`!e. is_binary_prim_app_value_of_expr e = ?bp. e = Expr_bprim bp`,
Cases THEN SRW_TAC [] [is_binary_prim_app_value_of_expr_def]);

val nexp_red_lem1 = Q.prove  (
`!e L e'. is_non_expansive_of_expr e /\ JR_expr e L e' ==> (L = Lab_nil)`,
recInduct is_non_expansive_of_expr_ind THEN
SRW_TAC [] [is_non_expansive_of_expr_def, JR_expr_fun] THEN
FULL_SIMP_TAC list_ss [MEM_APPEND, EVERY_APPEND, binary_primapp_lem, expr_distinct] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JR_expr_fun] THEN METIS_TAC []);

val nexp_red_lem2 = Q.prove  (
`!e L e'. is_non_expansive_of_expr e /\ JR_expr e L e' ==> is_non_expansive_of_expr e'`,
recInduct is_non_expansive_of_expr_ind THEN
SRW_TAC [] [is_non_expansive_of_expr_def, JR_expr_fun] THEN
FULL_SIMP_TAC list_ss [is_non_expansive_of_expr_def] THEN
FULL_SIMP_TAC list_ss [MEM_APPEND, EVERY_APPEND, binary_primapp_lem, expr_distinct] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JR_expr_fun] THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 MATCH_MP_TAC substs_nexp_thm THEN SRW_TAC [] [EVERY_MAP] THEN 
        FULL_SIMP_TAC list_ss [recfun_def, EVERY_MEM, substs_value_name_letrec_binding_def] THEN
        METIS_TAC [is_non_expansive_of_expr_def]]);

val nexp_red_thm = Q.store_thm ("nexp_red_thm",
`!e L e'. is_non_expansive_of_expr e /\ JR_expr e L e' ==> is_non_expansive_of_expr e' /\ (L = Lab_nil)`,
METIS_TAC [nexp_red_lem1, nexp_red_lem2]);

val value_nonexpansive_thm = Q.store_thm ("value_nonexpansive_thm",
`!v. is_value_of_expr v ==> is_non_expansive_of_expr v`,
recInduct is_value_of_expr_ind THEN
SRW_TAC [] [is_value_of_expr_def, is_non_expansive_of_expr_def, EVERY_MEM, LAMBDA_PROD2] THEN
SRW_TAC [] [is_binary_prim_app_value_of_expr_def] THEN
Cases_on `e` THEN METIS_TAC [SND]);

local 

val lem3 = Q.prove (
`!l1 l2 l3. (MAP FST l1 = MAP (\z. substs_typevar_typexpr l3 (TE_var (SND z))) l1) /\
            (MAP SND l1 = MAP FST l2) ==>
            (l1 = MAP (\(tv, t). (substs_typevar_typexpr l3 (TE_var tv), tv)) l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2] THEN Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) []);

val lem4 = Q.prove (
`!t h'. ~MEM (FST h') (MAP FST t) ==>
 (MAP (\z. case (if FST z = FST h' then SOME r else list_assoc (FST z) l1) of
              NONE -> TE_var (FST z) || SOME t_5 -> t_5) t =
  MAP (\z. case list_assoc (FST z) l1 of NONE -> TE_var (FST z) || SOME t_5 -> t_5) t)`,
Induct THEN SRW_TAC [] []);

val lem5 = Q.prove (
`!l1 l2. ALL_DISTINCT (MAP FST l1) /\
         (MAP FST l1 = MAP FST l2) ==>
         (MAP (\z. substs_typevar_typexpr l1 (TE_var (FST z))) l2 = MAP SND l1)`,
Induct THEN SRW_TAC [] [substs_typevar_typexpr_def] THEN Cases_on `l2` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [list_assoc_def, lem4] THEN FULL_SIMP_TAC (srw_ss()) [substs_typevar_typexpr_def]);

val lem8 = Q.prove (
`!l1 l2 l3 l4.
 EVERY (\t. tkind E (substs_typevar_typexpr (MAP (\x. (FST x, TE_constr [] TC_unit)) l1) t)) (MAP SND l3) /\
 JTeq E (TE_constr (MAP SND l1) typeconstr) (TE_constr (MAP SND l2) typeconstr) /\
 ~is_abbrev_tc E (TE_constr (MAP SND l1) typeconstr) /\
 ~is_abbrev_tc E (TE_constr (MAP SND l2) typeconstr) /\
 (MAP FST l1 = MAP FST l2) /\ (MAP SND l3 = MAP SND l4) ==>
 EVERY (\x. JTeq E (FST x) (SND x))
       (ZIP (MAP (\x. substs_typevar_typexpr l1 (SND x)) l3,
             MAP (\x. substs_typevar_typexpr l2 (SND x)) l4))`,
Induct_on `l3` THEN SRW_TAC [] [] THEN Cases_on `l4` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
MATCH_MP_TAC teq_substs_same_thm THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [teq_fun1]);

in

val constr_arg_types_lem = Q.prove (
`!E c ts1 ts2 t t'. JTconstr_p E c ts1 t /\ JTconstr_p E c ts2 t' /\ JTeq E t t' ==> 
                    (LENGTH ts1 = LENGTH ts2) /\ EVERY (\(t1, t2). JTeq E t1 t2) (ZIP (ts1, ts2))`,
SRW_TAC [] [JTconstr_p_cases, JTinst_named_cases, substs_typevar_typexpr_def, MAP_11_EQ] THEN
FULL_SIMP_TAC (srw_ss()) [MAP_MAP, is_abbrev_tc_def, teq_fun1, Eok_def, ETA_THM, MAP_11_ALL_DISTINCT] THEN 
SRW_TAC [] [] THENL 
[METIS_TAC [LENGTH_MAP],
 IMP_RES_TAC lem3 THEN FULL_SIMP_TAC (srw_ss()) [MAP_MAP, LAMBDA_PROD2, ETA_THM] THEN SRW_TAC [] [] THEN
     `JTeq E (TE_constr (MAP SND typevar_t_list) typeconstr) (TE_constr (MAP SND typevar_t_list') typeconstr)` 
               by METIS_TAC [lem5] THEN
     `Eok E` by METIS_TAC [ok_ok_thm] THEN
     IMP_RES_TAC lookup_ok_thm THEN Cases_on `typeconstr` THEN FULL_SIMP_TAC (srw_ss()) [EBok_def] THEN
     MATCH_MP_TAC (GEN_ALL lem8) THEN SRW_TAC [] [] THEN 
     FULL_SIMP_TAC (srw_ss()) [MAP_11_EQ, ETA_THM, Eok_def] THENL
     [Q.EXISTS_TAC `TC_name t'`, Q.EXISTS_TAC `TC_exn`] THEN
     SRW_TAC [] [is_abbrev_tc_def] THEN
     FULL_SIMP_TAC (srw_ss()) [Eok_def, substs_typevar_typexpr_def, MAP_MAP, EVERY_CONJ, tp_to_tv_def, 
                               EVERY_MAP]]);


val record_arg_types_lem = Q.prove (
`!E fn t1 t1' t2 t2'. JTfield E fn t1 t2 /\ JTfield E fn t1' t2' /\ JTeq E t1 t1' ==> (JTeq E t2 t2')`,
SRW_TAC [] [JTfield_cases, JTinst_named_cases, substs_typevar_typexpr_def, MAP_11_EQ] THEN
FULL_SIMP_TAC (srw_ss()) [MAP_MAP, Eok_def, MAP_11_ALL_DISTINCT, ETA_THM] THEN 
IMP_RES_TAC lem3 THEN FULL_SIMP_TAC (srw_ss()) [MAP_MAP, LAMBDA_PROD2, ETA_THM] THEN SRW_TAC [] [] THEN
`JTeq E (TE_constr (MAP SND typevar_t_list) (TC_name typeconstr_name))
        (TE_constr (MAP SND typevar_t_list') (TC_name typeconstr_name))`
     by METIS_TAC [lem5] THEN
`Eok E` by METIS_TAC [ok_ok_thm] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [EBok_def] THEN
MATCH_MP_TAC (GEN_ALL teq_substs_same_thm) THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [MAP_11_EQ, ETA_THM, Eok_def, MAP_MAP, substs_typevar_typexpr_def, tp_to_tv_def,
                          is_abbrev_tc_def, teq_fun1]);

end;

local

val lem1 = Q.prove (
`!x. (substs_x_xs case x of substs_x_xs l -> l) = x`,
Cases THEN SRW_TAC [] []);

val lem2 = Q.prove (
`!l1 l2. (MAP (\z. (F_name (FST z),SND z)) l1 = MAP (\z. (F_name (FST z),FST (SND z))) l2) =
         (MAP (\z. (FST z,SND z)) l1 = MAP (\z. (FST z,FST (SND z))) l2)`,
SRW_TAC [] [MAP_pair] THEN METIS_TAC [MAP_11_EQ, field_11]);

val lem3 = Q.prove (
`!a b c d. PERM (a::b++c) d ==> PERM (b++a::c) d`,
SRW_TAC [] [PERM_CONS_EQ_APPEND] THEN METIS_TAC [CONS_PERM, PERM_TRANS, PERM_SYM]);

val lem4 = Q.prove (
`!l1 t. (LENGTH l1 = LENGTH t) /\
        EVERY (\(x1,x2). LENGTH x1 = LENGTH case x2 of substs_x_xs l -> l) (ZIP (l1,t)) ==>
        (LENGTH (FLAT l1) = LENGTH (FLAT (MAP (\x. case x of substs_x_xs l -> l) t)))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []);

val lem5 = Q.prove (
`!(Q:Tsigma -> environment -> environment -> (value_name # expr) list -> bool) 
  select_env select_type (select_pat: 'a -> pattern) (l1:'a list) l2 l3 P S E.
 EVERY (\x. !v substs. P v (select_pat x) (substs_x_xs substs) /\ JTe S E v (select_type x) ==> 
                       Q S E (select_env x) substs) l1 /\ 
 EVERY (\x. P (FST x) (FST (SND x)) (SND (SND x))) l2 /\
 EVERY (\x. JTe S E (FST x) (SND x)) l3 /\
 EVERY (\(t1,t2). JTeq E t1 t2) (ZIP (MAP SND l3,MAP select_type l1)) /\
 (MAP select_pat l1 = MAP (\x. (FST (SND x))) l2) /\
 (MAP FST l2 = MAP FST l3) ==>
 EVERY (\(x1, x2). Q S E x1 (case x2 of substs_x_xs l -> l))
       (ZIP (MAP select_env l1, MAP (SND o SND) l2))`,
NTAC 4 STRIP_TAC THEN Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN Cases_on `l3` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN `JTe S E (FST h'') (select_type h)` by METIS_TAC [teq_thm] THEN 
Cases_on `SND (SND h')` THEN SRW_TAC [] [] THEN METIS_TAC []);

val lem6= SIMP_RULE (srw_ss()) [] (Q.SPEC
`\S E x y. ?E''. PERM x E'' /\
             EVERY (\x. ?t. (FST x = EB_vn (FST (SND x)) (TS_forall (shiftt 0 1 t))) /\
                            JTe S E (SND (SND x)) t)
                   (ZIP (REVERSE E'',y))`
lem5);

val lem8 = Q.prove (
`!l1 l2. 
(LENGTH l1 = LENGTH l2) /\ EVERY (\(x1, x2). LENGTH x1 = LENGTH case x2 of substs_x_xs l -> l) (ZIP (l1,l2)) /\
EVERY (\(x1,x2). ?E''. PERM x1 E'' /\
                       EVERY (\x. ?t. (FST x = EB_vn (FST (SND x)) (TS_forall (shiftt 0 1 t))) /\
                                      JTe S E (SND (SND x)) t)
                             (ZIP (REVERSE E'', case x2 of substs_x_xs l -> l)))
      (ZIP (l1,l2))
==>
?E''.
PERM (FLAT (REVERSE l1)) E'' /\
EVERY (\x. ?t. (FST x = EB_vn (FST (SND x)) (TS_forall (shiftt 0 1 t))) /\
               JTe S E (SND (SND x)) t)
     (ZIP (REVERSE E'', FLAT (MAP (\x. case x of substs_x_xs l -> l) l2)))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
Q.EXISTS_TAC `E'''++E''` THEN SRW_TAC [] [FLAT_APPEND, REVERSE_APPEND] THEN1 
METIS_TAC [PERM_CONG] THEN 
`LENGTH (REVERSE E'') = LENGTH case h' of substs_x_xs l -> l` by METIS_TAC [PERM_LENGTH, LENGTH_REVERSE] THEN
`LENGTH (REVERSE E''') = LENGTH (FLAT (MAP (\x. case x of substs_x_xs l -> l) t))` 
          by METIS_TAC [PERM_LENGTH, LENGTH_REVERSE, LENGTH_FLAT_REVERSE, lem4] THEN
SRW_TAC [] [ZIP_APPEND]);

val INST_TUPLE =
  SIMP_RULE (srw_ss()) [o_DEF] o
  Q.SPECL [`SND o SND`, `FST o SND`, `FST`] o
  INST_TYPE [alpha |-> Type`:pattern # typexpr # environment`];

val INST_CTOR =
  SIMP_RULE (srw_ss()) [o_DEF] o
  Q.SPECL [`FST o SND`, `SND o SND`, `FST`] o
  INST_TYPE [alpha |-> Type`:pattern # environment # typexpr`];

val INST_REC =
  SIMP_RULE (srw_ss()) [o_DEF] o
  Q.SPECL [`FST o SND o SND`, `SND o SND o SND`, `FST o SND`] o
  INST_TYPE [alpha |-> Type`:field_name # pattern # environment # typexpr`];

val lem9 = Q.prove (
`!l1 l2. (MAP FST l1 = MAP FST l2) /\
         EVERY (\x. JTfield E (FST x) (TE_constr t'_list (TC_name typeconstr_name)) (SND (SND x))) l1 /\
         EVERY (\x. JTfield E (FST x) t (SND (SND (SND x)))) l2 /\
         JTeq E (TE_constr t'_list (TC_name typeconstr_name)) t ==>
         EVERY (\(t1,t2). JTeq E t1 t2) 
               (ZIP (MAP SND (MAP SND l1), MAP (\x. SND (SND (SND x))) l2))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [record_arg_types_lem]);

val lem10 = Q.prove (
`!l3 l4 l5 l6.
  PERM (l4 ++ l5) l6 /\
  (MAP (\z. (F_name (FST z),SND z)) l6 = MAP (\z. (F_name (FST z),FST (SND z))) l3) ==>
  ?l1 l2. 
  PERM l3 (l1 ++ l2) /\ (MAP (\x. (FST x, FST (SND x))) l1 = l4)`,
Induct_on `l4` THEN SRW_TAC [] [] THEN1 METIS_TAC [PERM_REFL] THEN
FULL_SIMP_TAC (srw_ss()) [PERM_CONS_EQ_APPEND] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [MAP_split] THEN SRW_TAC [] [] THEN Cases_on `l5'` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`?l1 l2. PERM (l4'++t) (l1 ++ l2) /\ (MAP (\x. (FST x,FST (SND x))) l1 = l4)` by
     METIS_TAC [MAP_APPEND] THEN
Q.EXISTS_TAC `h'::l1` THEN Cases_on `h` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `l2` THEN ONCE_REWRITE_TAC [PERM_SYM] THEN SRW_TAC [] [PERM_CONS_EQ_APPEND] THEN
METIS_TAC [PERM_SYM]);

in

val pat_num_bindings_lem = Q.store_thm ("pat_num_bindings_lem",
`!S E p t E'. JTpat S E p t E' ==> !v substs. JM_match v p (substs_x_xs substs) ==>
            (LENGTH E' = LENGTH substs)`,
RULE_INDUCT_TAC JTpat_ind [JM_match_fun]
[([``"JTpat_construct"``],
  SRW_TAC [] [] THEN REPEAT (Q.PAT_ASSUM `JTconstr_p a b c d` (K ALL_TAC)) THEN 
        REPEAT (Q.PAT_ASSUM `ALL_DISTINCT x` (K ALL_TAC)) THEN 
        REPEAT (POP_ASSUM MP_TAC) THEN
        MAP_EVERY Q.ID_SPEC_TAC [`v_pat_substs_x_list`, `pattern_E_t_list`] THEN
        Induct THEN SRW_TAC [] [] THEN
        Cases_on `v_pat_substs_x_list` THEN FULL_SIMP_TAC list_ss [] THEN
        SRW_TAC [] [SUM_APPEND, LENGTH_FLAT] THEN 
        FULL_SIMP_TAC list_ss [SUM_APPEND, LENGTH_FLAT, ELIM_UNCURRY] THEN
        METIS_TAC [lem1]),
 ([``"JTpat_tuple"``],
  SRW_TAC [] [] THEN REPEAT (Q.PAT_ASSUM `LENGTH x >= y` (K ALL_TAC)) THEN 
        REPEAT (Q.PAT_ASSUM `ALL_DISTINCT x` (K ALL_TAC)) THEN 
        REPEAT (POP_ASSUM MP_TAC) THEN
        MAP_EVERY Q.ID_SPEC_TAC [`v_pat_substs_x_list`, `pattern_t_E_list`] THEN
        Induct THEN SRW_TAC [] [] THEN
        Cases_on `v_pat_substs_x_list` THEN FULL_SIMP_TAC list_ss [] THEN
        SRW_TAC [] [SUM_APPEND, LENGTH_FLAT] THEN 
        FULL_SIMP_TAC list_ss [SUM_APPEND, LENGTH_FLAT, ELIM_UNCURRY] THEN
        METIS_TAC [lem1]),
 ([``"JTpat_record"``],
  SRW_TAC [] [] THEN REPEAT (Q.PAT_ASSUM `LENGTH x >= y` (K ALL_TAC)) THEN
        REPEAT (Q.PAT_ASSUM `ALL_DISTINCT x` (K ALL_TAC)) THEN
        REPEAT (Q.PAT_ASSUM `PERM x y` (K ALL_TAC)) THEN
        REPEAT (POP_ASSUM MP_TAC) THEN
        MAP_EVERY Q.ID_SPEC_TAC [`field_name'_pat_substs_x_v'_list`, `field_name_pattern_E_t_list`] THEN
        Induct THEN SRW_TAC [] [] THEN
        Cases_on `field_name'_pat_substs_x_v'_list` THEN FULL_SIMP_TAC list_ss [] THEN
        SRW_TAC [] [SUM_APPEND, LENGTH_FLAT] THEN
        FULL_SIMP_TAC list_ss [SUM_APPEND, LENGTH_FLAT, ELIM_UNCURRY] THEN
        METIS_TAC [lem1])]
THEN
SRW_TAC [ARITH_ss][] THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC [arithmeticTheory.ADD1, lem1, PERM_LENGTH]);

local

val lem7 = Q.prove (
`!select_env select_type select_pat (l1:'a list) l2.
 (LENGTH l1 = LENGTH l2) /\
 (MAP select_pat l1 = MAP (\x. FST (SND x)) l2) /\
 EVERY (\x. JTpat S E (select_pat x) (select_type x) (select_env x)) l1 /\
 EVERY (\x. JM_match (FST x) (FST (SND x)) (SND (SND x))) l2 ==>
 EVERY (\(x1, x2). LENGTH x1 = LENGTH case x2 of substs_x_xs l -> l) 
       (ZIP (MAP select_env l1, MAP (SND o SND) l2))`,
NTAC 3 STRIP_TAC THEN Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
SRW_TAC [] [] THEN
Cases_on `SND (SND h')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [pat_num_bindings_lem]);

in

val pat_preservation_lem = Q.prove (
`!S E p t E'. JTpat S E p t E' ==> !v substs. JM_match v p (substs_x_xs substs) /\ JTe S E v t ==>
            ?E''. PERM E' E'' /\
               (EVERY (\(EB, subst). ?t. (EB = EB_vn (FST subst) (TS_forall (shiftt 0 1 t))) /\ 
                                         JTe S E (SND subst) t)
                      (ZIP (REVERSE E'', substs)))`,
RULE_INDUCT_TAC JTpat_sind [JM_match_fun, EVERY_DEF, ZIP, domEB_def, JTe_fun, ELIM_UNCURRY]
[([``"JTpat_var"``, ``"JTpat_typed"``, ``"JTpat_construct_any"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [JTe_fun] THEN METIS_TAC []),
 ([``"JTpat_or"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [JTe_fun] THEN METIS_TAC [PERM_LENGTH, PERM_TRANS]),
 ([``"JTpat_alias"``],
  SRW_TAC [] [] THEN 
        FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1] THEN 
        RES_TAC THEN Q.EXISTS_TAC `EB_vn x (TS_forall (shiftt 0 1 t))::E''` THEN 
        `LENGTH (REVERSE E'') = LENGTH x_v_list` by 
               METIS_TAC [LENGTH_REVERSE, PERM_LENGTH, pat_num_bindings_lem] THEN
        SRW_TAC [] [ZIP_APPEND] THEN METIS_TAC []),
 ([``"JTpat_construct"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [JTe_fun] THEN
      `EVERY (\(t1, t2). JTeq E t1 t2) (ZIP (MAP SND e_t_list, MAP (\x. SND (SND x)) pattern_E_t_list))`
                         by METIS_TAC [constr_arg_types_lem, LENGTH_MAP] THEN
      `LENGTH e_t_list = LENGTH pattern_E_t_list` by METIS_TAC [LENGTH_MAP] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      IMP_RES_TAC (INST_CTOR lem6) THEN 
      SRW_TAC [] [MAP_MAP] THEN
      IMP_RES_TAC (INST_CTOR lem7) THEN IMP_RES_TAC lem8 THEN FULL_SIMP_TAC (srw_ss()) [MAP_MAP, o_DEF] THEN
      METIS_TAC [LENGTH_MAP]),
 ([``"JTpat_tuple"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [JTe_fun, teq_fun1, is_abbrev_tc_def] THEN
      `LENGTH e_t_list = LENGTH pattern_t_E_list` by METIS_TAC [LENGTH_MAP] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      IMP_RES_TAC (INST_TUPLE lem6) THEN 
      SRW_TAC [] [MAP_MAP] THEN
      IMP_RES_TAC (INST_TUPLE lem7) THEN IMP_RES_TAC lem8 THEN FULL_SIMP_TAC (srw_ss()) [MAP_MAP, o_DEF] THEN
      METIS_TAC [LENGTH_MAP]),
 ([``"JTpat_record"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [JTe_fun] THEN
      `?field_name_e_t_list_perm1 field_name_e_t_list_perm2. 
            PERM field_name_e_t_list (field_name_e_t_list_perm1 ++ field_name_e_t_list_perm2) /\
            (MAP (\x. (FST x, FST (SND x))) field_name_e_t_list_perm1 = 
             MAP (\x. (FST x, SND (SND (SND x)))) field_name'_pat_substs_x_v'_list)` by
           METIS_TAC [lem10] THEN
      `EVERY (\x. JM_match (FST x) (FST (SND x)) (SND (SND x))) 
             (MAP (\(fn, p, s, v). (v, p, s)) field_name'_pat_substs_x_v'_list)` 
           by SRW_TAC [] [EVERY_MAP, LAMBDA_PROD2] THEN
      `EVERY (\x. JTe S' E (FST x) (SND x)) (MAP SND field_name_e_t_list_perm1)`
           by (SRW_TAC [] [EVERY_MAP, LAMBDA_PROD2] THEN METIS_TAC [PERM_lem]) THEN
      FULL_SIMP_TAC (srw_ss()) [MAP_pair, MAP_11_EQ, field_11, ETA_THM] THEN
      `EVERY (\(t1,t2). JTeq E t1 t2) 
             (ZIP (MAP SND (MAP SND field_name_e_t_list_perm1),
                   MAP (\x. SND (SND (SND x))) field_name_pattern_E_t_list))`
           by METIS_TAC [lem9, PERM_lem] THEN
      `MAP (\x. FST (SND x)) field_name_pattern_E_t_list = 
       MAP (\x. FST (SND x)) (MAP (\(fn, p, s, v). (v, p, s)) field_name'_pat_substs_x_v'_list)` by
           FULL_SIMP_TAC (srw_ss()) [MAP_pair, MAP_MAP, LAMBDA_PROD2] THEN
      `MAP FST (MAP (\(fn, p, s, v). (v, p, s)) field_name'_pat_substs_x_v'_list) = 
       MAP FST (MAP SND field_name_e_t_list_perm1)` by
          SRW_TAC [] [MAP_MAP, LAMBDA_PROD2] THEN
      `LENGTH field_name_pattern_E_t_list = 
       LENGTH (MAP (\(fn,p,s,v). (v,p,s)) field_name'_pat_substs_x_v'_list)` by METIS_TAC [LENGTH_MAP] THEN
      IMP_RES_TAC (INST_REC lem6) THEN 
      SRW_TAC [] [MAP_MAP] THEN
      IMP_RES_TAC (INST_REC lem7) THEN IMP_RES_TAC lem8 THEN 
      FULL_SIMP_TAC (srw_ss()) [MAP_MAP, o_DEF, LAMBDA_PROD2] THEN
      METIS_TAC []),
 ([``"JTpat_cons"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [JTe_fun] THEN
      Cases_on `substs_x2` THEN Cases_on `substs_x1` THEN
      `JTe S' E v2 (TE_constr [t] TC_list)` by METIS_TAC [teq_thm] THEN
      FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN
      `JTe S' E v1 t` by METIS_TAC [teq_thm] THEN
      RES_TAC THEN Q.EXISTS_TAC `E''' ++ E'''''` THEN SRW_TAC [] [] THEN1
      METIS_TAC [PERM_CONG] THEN IMP_RES_TAC pat_num_bindings_lem THEN
      `(LENGTH (REVERSE E''''') = LENGTH l') /\ (LENGTH (REVERSE E''') = LENGTH l)` 
                     by METIS_TAC [PERM_LENGTH, LENGTH_REVERSE] THEN
      SRW_TAC [] [REVERSE_APPEND, ZIP_APPEND])]);
end;

val pat_preservation_thm = Q.store_thm ("pat_preservation_thm",
`!S E p t E'. JTpat S E p t E' ==> !v substs. JM_match v p (substs_x_xs substs) /\ JTe S E v t ==>
            ?E''. PERM E' E'' /\
            (EVERY (\(EB, subst). ?t. (EB = EB_vn (FST subst) (TS_forall (shiftt 0 1 t))) /\ 
                                      JTe S E (SND subst) t)
                   (ZIP (REVERSE E'', substs)))`,
METIS_TAC [pat_preservation_lem, pat_num_bindings_lem]);

end;

val weak_teq_lem1 = Q.prove (
`!E EB t1 t2. JTeq E t1 t2 /\ ~(EB = EB_tv) /\ Eok (EB::E) ==> JTeq (EB::E) t1 t2`,
METIS_TAC [MEM, APPEND, weak_teq_thm]);

val uprim_preservation_lem = Q.prove (
`!uprim e L e'. JRuprim uprim e L e' ==> !S E. closed_env E ==> !t1 t2. JTuprim E uprim (TE_arrow t1 t2) /\
                JTe S E e t1 /\ JTLin S E L ==> ?E''. JTLout S E L E'' /\ JTe S (E''++E) e' t2`,
RULE_INDUCT_TAC JRuprim_ind [JTe_fun, JTconst_cases, JTuprim_cases, JTLin_cases, Eok_def, JTLout_cases]
[([``"Juprim_deref"``], 
  SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN SRW_TAC [] [] THEN METIS_TAC [teq_thm]),
 ([``"Juprim_ref_alloc"``],
  SRW_TAC [] [GSYM LEFT_EXISTS_AND_THM, lookup_def, domEB_def, Eok_def] THEN
      Q.EXISTS_TAC `t1` THEN SRW_TAC [] [] THEN
      `tkind E (TE_constr [t1] TC_ref) /\ Eok (EB_l l t1::E)` 
                    by (SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_ok_thm]) THEN
      `JTeq E (TE_constr [t1] TC_ref) (TE_constr [t1] TC_ref)` by METIS_TAC [JTeq_rules, ok_ok_thm] THEN
      IMP_RES_TAC weak_teq_lem1 THEN FULL_SIMP_TAC (srw_ss()) [])]);

val JTL_nil_lem = Q.store_thm ("JTL_nil_lem",
`!S E E'. JTLin S E Lab_nil /\ (JTLout S E Lab_nil E' = (E' = []))`,
SRW_TAC [] [JTLin_cases, JTLout_cases] THEN METIS_TAC []);

val matching_step_preservation_lem = Q.prove (
`!S E pm t' t pm'. JTpat_matching S E pm t' t /\ JRmatching_step v pm pm' ==> JTpat_matching S E pm' t' t`,
SRW_TAC [] [JRmatching_step_cases] THEN FULL_SIMP_TAC list_ss [JTe_fun] THEN
Cases_on `pattern_e_E_list` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC [LENGTH_MAP]);

local 

val lem3 = Q.prove (
`!E. Eok E ==> JTeq E (TE_constr [] TC_bool) (TE_constr [] TC_bool) /\
               JTeq E (TE_constr [] TC_string) (TE_constr [] TC_string) /\
               JTeq E (TE_constr [] TC_exn) (TE_constr [] TC_exn)`,
SRW_TAC [] [] THEN
`tkind E (TE_constr [] TC_bool) /\ tkind E (TE_constr [] TC_string) /\ tkind E (TE_constr [] TC_exn)`
          by SRW_TAC [] [Eok_def] THEN
METIS_TAC [JTeq_rules]);

val lem1 = Q.prove (
`!exprs E S. JTe S E (FOLDR Expr_and (Expr_constant CONST_true) exprs) (TE_constr [] TC_bool) = 
           EVERY (\e. JTe S E e (TE_constr [] TC_bool)) exprs /\ Eok E`,
Induct THEN SRW_TAC [] [JTe_fun, JTconst_cases] THEN
EQ_TAC THEN SRW_TAC [] [] THEN METIS_TAC [JTeq_rules, lem3]);

val lem2 = Q.prove (
`!l1 l2. (MAP (\z. (F_name (FST z),SND z)) l1 = MAP (\z. (F_name (FST z),FST (SND z))) l2) ==>
         (l1 = MAP (\x. (FST x, FST (SND x))) l2)`,
Induct THEN Cases_on `l2` THEN SRW_TAC [] [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [] THEN
Cases_on `h'` THEN FULL_SIMP_TAC list_ss []);

val lem4 = Q.prove (
`!E t. JTeq E t t = tkind E t`,
METIS_TAC [JTeq_rules, teq_ok_thm]);

val lem5 = Q.prove (
`!v_v'_list e_t_list e_t_list'.
 (MAP FST v_v'_list = MAP FST e_t_list) /\
 (MAP SND v_v'_list = MAP FST e_t_list') /\
 EVERY (\x. JTe S E (FST x) (SND x)) e_t_list' /\
 EVERY (\x. JTe S E (FST x) (SND x)) e_t_list /\
 EVERY (\(t1,t2). JTeq E t1 t2) (ZIP (MAP SND e_t_list,MAP SND e_t_list')) ==>
 EVERY (\z. ?t1'. (?t1''. (?t. (?t'. (t = TE_arrow t' (TE_arrow t' (TE_constr [] TC_bool))) /\ tkind E t') /\
                               JTeq E t (TE_arrow t1'' (TE_arrow t1' (TE_constr [] TC_bool)))) /\ 
                          JTe S E (FST z) t1'') /\ 
                  JTe S E (SND z) t1') 
       v_v'_list`,
Induct THEN SRW_TAC [] [] THEN Cases_on `e_t_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e_t_list'` THEN FULL_SIMP_TAC (srw_ss()) [] THENL
[Q.EXISTS_TAC `SND h''` THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `SND h'` THEN SRW_TAC [] [] THEN
     Q.EXISTS_TAC `TE_arrow (SND h') (TE_arrow (SND h') (TE_constr [] TC_bool))` THEN SRW_TAC [] [] THEN
     METIS_TAC [teq_ok_thm, lem4, lem3, JTeq_rules, ok_ok_thm],
 METIS_TAC [ok_ok_thm]]);

in

val bprim_preservation_lem = Q.prove (
`!e1 bprim e2 L e'. JRbprim e1 bprim e2 L e' ==> !E S. closed_env E ==>
                    !t1 t2 t3. JTbprim E bprim (TE_arrow t1 (TE_arrow t2 t3)) /\
                               JTe S E e1 t1 /\ JTe S E e2 t2 /\ JTLin S E L ==>
                               ?E''. JTLout S E L E'' /\ JTe S (E''++E) e' t3`,
RULE_INDUCT_TAC JRbprim_ind [JTe_fun, JTconst_cases, JTbprim_cases, JTLin_cases, JTLout_cases, Eok_def, 
                             lem1, EVERY_MAP]
[([``"Jbprim_equal_loc"``], 
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [Eok_def] THEN SRW_TAC [] [JTuprim_cases] THEN
      `tkind E (TE_constr [t] TC_ref)` by METIS_TAC [teq_ok_thm] THEN
      FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN
      Q.EXISTS_TAC `t` THEN SRW_TAC [] [] THENL
      [Q.EXISTS_TAC `t` THEN SRW_TAC [] [] THENL
             [Q.EXISTS_TAC `TE_arrow t (TE_arrow t (TE_constr [] TC_bool))` THEN
                    SRW_TAC [] [Eok_def, lem4],
              Q.EXISTS_TAC `TE_constr [t] TC_ref` THEN SRW_TAC [] [Eok_def, lem4] THEN
                    Q.EXISTS_TAC `TE_arrow (TE_constr [t] TC_ref) t` THEN SRW_TAC [] [Eok_def, lem4]],
       Q.EXISTS_TAC `t1` THEN SRW_TAC [] [] THEN
             Q.EXISTS_TAC `TE_arrow (TE_constr [t] TC_ref) t` THEN SRW_TAC [] [] THEN 
             METIS_TAC [JTeq_rules]]),
 ([``"Jbprim_equal_const_true"``, ``"Jbprim_equal_const_false"``, ``"Jbprim_equal_cons_nil"``,
   ``"Jbprim_equal_nil_cons"``, ``"Jbprim_equal_constr_false"``, ``"Jbprim_equal_const_constr_false"``,
   ``"Jbprim_equal_constr_const_false"``],
  METIS_TAC [ok_ok_thm, lem3]),
 ([``"Jbprim_equal_fun"``],
   SRW_TAC [] [JTuprim_cases, JTconstr_p_cases, Eok_def, JTconstr_c_cases] THEN
         Q.EXISTS_TAC `TE_constr [] TC_exn` THEN SRW_TAC [] [] THENL
         [Q.EXISTS_TAC `TE_arrow (TE_constr [] TC_exn) (TE_constr [] TC_bool)` THEN
              SRW_TAC [] [Eok_def, lem4] THEN METIS_TAC [ok_ok_thm],
          Q.EXISTS_TAC `[(Expr_constant (CONST_string "equal: functional value"), TE_constr [] TC_string)]` THEN
              SRW_TAC [] [JTe_fun, JTconst_cases] THEN METIS_TAC [ok_ok_thm, lem3]]),
 ([``"Jbprim_equal_cons"``],
  SRW_TAC [] [lem4, Eok_def, COND_EXPAND_EQ] THEN 
         `tkind E(TE_constr [t] TC_list)` by METIS_TAC [teq_ok_thm] THEN 
         FULL_SIMP_TAC (srw_ss()) [Eok_def] THENL
         [Q.EXISTS_TAC `t'` THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `t` THEN SRW_TAC [] [] THEN
                Q.EXISTS_TAC `TE_arrow t (TE_arrow t (TE_constr [] TC_bool))` THEN SRW_TAC [] [] THEN
                `JTeq E (TE_constr [t] TC_list) (TE_constr [t'] TC_list)` by METIS_TAC [JTeq_rules] THEN
                FULL_SIMP_TAC (srw_ss()) [teq_fun1, is_abbrev_tc_def] THEN
                SRW_TAC [] [Eok_def] THEN
                METIS_TAC [JTeq_rules, lem3, lem4, ok_ok_thm],
          Q.EXISTS_TAC `TE_constr [t'] TC_list` THEN SRW_TAC [] [] THEN
                Q.EXISTS_TAC `TE_constr [t] TC_list` THEN SRW_TAC [] [] THEN 
                Q.EXISTS_TAC `TE_arrow (TE_constr [t] TC_list) 
                                       (TE_arrow (TE_constr [t] TC_list) 
                                                 (TE_constr [] TC_bool))` THEN
                SRW_TAC [] [Eok_def] THEN
                `JTeq E (TE_constr [t] TC_list) (TE_constr [t'] TC_list)` by METIS_TAC [JTeq_rules] THEN
                SRW_TAC [] [] THEN
                METIS_TAC [JTeq_rules, lem3, lem4, ok_ok_thm],
          METIS_TAC [ok_ok_thm]]),
 ([``"Jbprim_equal_tuple"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [Eok_def] THENL 
      [`JTeq E (TE_tuple (MAP SND e_t_list)) (TE_tuple (MAP SND e_t_list'))` by METIS_TAC [JTeq_rules] THEN
             FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN SRW_TAC [] [] THEN
             METIS_TAC [lem5, LENGTH_MAP],
       METIS_TAC [ok_ok_thm]]),
 ([``"Jbprim_equal_constr"``],
  SRW_TAC [] [] THENL
       [`JTeq E t t'` by METIS_TAC [JTeq_rules] THEN
            IMP_RES_TAC constr_arg_types_lem THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
            METIS_TAC [LENGTH_MAP, lem5],
        METIS_TAC [ok_ok_thm]]),
 ([``"Jbprim_equal_rec"``],
  SRW_TAC [] [] THENL
      [IMP_RES_TAC lem2 THEN SRW_TAC [] [EVERY_MAP, EVERY_MEM] THEN
           Q.EXISTS_TAC `SND (SND x)` THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THENL
           [Q.EXISTS_TAC `SND (SND x)` THEN SRW_TAC [] [] THEN
                Q.EXISTS_TAC `TE_arrow (SND (SND x)) (TE_arrow (SND (SND x)) (TE_constr [] TC_bool))` THEN
                SRW_TAC [] [lem4, Eok_def] THEN METIS_TAC [ok_thm, ok_ok_thm],
            MAP_EVERY Q.EXISTS_TAC [`(TE_constr t'_list (TC_name typeconstr_name))`, `SND (SND x)`] THEN
                SRW_TAC [] [lem4] THENL
                [`JTeq E (TE_constr t'_list' (TC_name typeconstr_name')) 
                         (TE_constr t'_list (TC_name typeconstr_name))`
                               by METIS_TAC [JTeq_rules] THEN
                     MAP_EVERY Q.EXISTS_TAC [`field_name'_list'`, `t'_list'`, `field_name_e_t_list'`, 
                                             `typeconstr_name'`] THEN
                     SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [MAP_MAP, lem4, Eok_def],
                 METIS_TAC [ok_thm]]],
       METIS_TAC [ok_ok_thm]]),
 ([``"Jbprim_div0"``], 
  SRW_TAC [] [JTconstr_c_cases, JTuprim_cases, Eok_def] THEN
        Q.EXISTS_TAC `TE_constr [] TC_exn` THEN SRW_TAC [] [lem4, Eok_def] THEN
        Q.EXISTS_TAC `TE_arrow (TE_constr [] TC_exn) (TE_constr [] TC_int)` THEN SRW_TAC [] [lem4, Eok_def]),
 ([``"Jbprim_assign"``],
  SRW_TAC [] [] THEN SRW_TAC [] [lem4, Eok_def] THEN 
        FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN METIS_TAC [teq_thm, JTeq_rules])]);

        
end;

(*
val lem2 = Q.prove (
`!l1 l2 E t. (LENGTH l1 = LENGTH l2) /\ 
             (EVERY (\x.  JTfield E (FST x) t (SND (SND x))) l1) /\
             (EVERY (\x.  JTfield E (FST x) t (SND x)) (ZIP (MAP FST l1, l2))) ==>
             (l2 = MAP (\x. SND (SND x)) l1)`,
Induct THEN Cases_on `l2` THEN SRW_TAC [] [] THEN METIS_TAC [record_arg_types_lem]);

val lem3 = Q.prove (
`!l1 l2. (MAP (\z. (F_name (FST z),FST (SND z))) l1 = MAP (\z. (F_name (FST z),FST (SND z))) l2) =
         (MAP (\z. (FST z,FST (SND z))) l1 = MAP (\z. (FST z,FST (SND z))) l2)`,
Induct THEN Cases_on `l2` THEN SRW_TAC [] []);

val lem4 = Q.prove (
`!l1 l2. (MAP (\z. (F_name (FST (SND (SND z))),FST (SND (SND (SND z))))) l1 =
          MAP (\z. (F_name (FST z),FST (SND z))) l2) =
         (MAP (\z. (FST (SND (SND z)),FST (SND (SND (SND z))))) l1 =
          MAP (\z. (FST z,FST (SND z))) l2)`,
Induct THEN Cases_on `l2` THEN SRW_TAC [] []);

val lem5 = Q.prove (
`!l1 l2 z. (MAP (\z. (FST z,FST (SND z))) l1 = MAP (\z. (FST z,FST (SND z))) l2) /\ MEM z l1 /\
           ALL_DISTINCT (MAP FST l1) ==>
           ?t. list_assoc (FST z) l2 = SOME (FST (SND z),t)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss [list_assoc_def] THEN
Cases_on `h'` THEN SRW_TAC [] [list_assoc_def] THEN Cases_on `r` THEN FULL_SIMP_TAC list_ss [] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MEM_MAP] THEN METIS_TAC []);

e(
FULL_SIMP_TAC list_ss [environment_binding_11] THEN SRW_TAC [] [] THEN
`PERM (MAP FST field_name_e_t_list') (MAP FST field_name_e_t_list)` by METIS_TAC [PERM_SYM, PERM_TRANS] THEN
`?t''list. (LENGTH (MAP FST field_name_e_t_list) = LENGTH t''list) /\
           (PERM (MAP (\x. SND (SND x)) field_name_e_t_list') t''list) /\
           (PERM (ZIP (MAP FST field_name_e_t_list', (MAP (\x. SND (SND x)) field_name_e_t_list'))) 
                 (ZIP (MAP FST field_name_e_t_list, t''list)))` by
     METIS_TAC [EXTEND_PERM, PERM_LENGTH, LENGTH_MAP] THEN
FULL_SIMP_TAC list_ss [ZIP_MAP, MAP_MAP, MAP_ZIP_SAME] THEN
`EVERY (\x. JTfield E (FST x) (TE_constr t_'list (TC_name typeconstr_name)) (SND x))
       (ZIP (MAP FST field_name_e_t_list, t''list))` by 
              (FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN
                       `MEM x (MAP (\p. (FST p,SND (SND p))) field_name_e_t_list')` by
                                       METIS_TAC [EVERY_MEM, PERM_MEM_EQ] THEN
                       FULL_SIMP_TAC list_ss [MEM_MAP]) THEN
`t''list = MAP (\x. SND (SND x)) field_name_e_t_list` by METIS_TAC [lem2] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC list_ss [ZIP_MAP, MAP_MAP, MAP_ZIP_SAME, lem3, EVERY_MEM, lem4] THEN
SRW_TAC [] [] THEN
IMP_RES_TAC lookup_ok_thm THEN FULL_SIMP_TAC list_ss [EBok_def] THEN
FULL_SIMP_TAC list_ss [MAP_11_ALL_DISTINCT2, name_11] THEN
`ALL_DISTINCT (MAP FST field_name_e_t_list') /\ ALL_DISTINCT (MAP FST field_name_e_t_list)` by
        METIS_TAC [PERM_ALL_DISTINCT] THEN
`ALL_DISTINCT (MAP FST fn_v_fn_'v_'v_''list)` by
        ((`MAP FST (MAP (\z. (FST z,FST (SND z))) fn_v_fn_'v_'v_''list) =
           MAP FST (MAP (\z. (FST z,FST (SND z))) field_name_e_t_list)` by METIS_TAC []) THEN 
         FULL_SIMP_TAC list_ss [MAP_MAP, ETA_THM]) THEN 
`ALL_DISTINCT (MAP (\x. FST (SND (SND x))) fn_v_fn_'v_'v_''list)` by
        ((`MAP FST (MAP (\z. (FST (SND (SND z)),FST (SND (SND (SND z))))) fn_v_fn_'v_'v_''list) =
           MAP FST (MAP (\z. (FST z,FST (SND z))) field_name_e_t_list')` by METIS_TAC []) THEN 
         FULL_SIMP_TAC list_ss [MAP_MAP, ETA_THM]) THEN
`ALL_DISTINCT (MAP FST (MAP (\p. (FST p,SND (SND p))) field_name_e_t_list'))` by
               SRW_TAC [] [MAP_MAP, ETA_THM] THEN
`ALL_DISTINCT (MAP FST (MAP (\p. (FST p,FST (SND p))) field_name_e_t_list'))` by
               SRW_TAC [] [MAP_MAP, ETA_THM] THEN
`ALL_DISTINCT (MAP FST (MAP (\p. (FST p,SND (SND p))) field_name_e_t_list))` by
               SRW_TAC [] [MAP_MAP, ETA_THM] THEN 
`ALL_DISTINCT (MAP FST (MAP (\z. (FST z,SND (SND (SND (SND z))))) fn_v_fn_'v_'v_''list))` by
               SRW_TAC [] [MAP_MAP, ETA_THM]);

e(`?t. list_assoc (FST z) field_name_e_t_list = SOME (FST (SND z),t)` by METIS_TAC [lem5]);

e(`?t. (list_assoc (FST z) field_name_e_t_list' = SOME (SND (SND (SND (SND z))), t))`
   by (???));

e(`t = t'` by METIS_TAC [OPTION_MAP_DEF, SND, SOME_11, list_assoc_map, PERM_list_assoc] THEN
METIS_TAC [list_assoc_mem, FST, SND, ok_thm]);
*)


val recfun_is_value = Q.store_thm ("recfun_is_value",
`!lrbs pm. is_value_of_expr (recfun lrbs pm)`,
Cases THEN SRW_TAC [] [is_value_of_expr_def, recfun_def, substs_value_name_letrec_binding_def]);

val recfun_ftv_thm = Q.prove (
`!lrbs pm. (ftv_letrec_bindings lrbs = []) /\ (ftv_pattern_matching pm = []) ==>
           (ftv_expr (recfun lrbs pm) = [])`,
Cases THEN 
SRW_TAC [] [recfun_def, ftv_letrec_binding_def, substs_value_name_letrec_binding_def, FLAT_EQ_EMPTY,
                EVERY_MAP] THEN
MATCH_MP_TAC (List.nth (CONJUNCTS substs_ftv_thm, 4)) THEN SRW_TAC [] [EVERY_MAP, EVERY_MEM] THEN
Cases_on `letrec_binding` THEN SRW_TAC [] [ftv_letrec_binding_def, FLAT_EQ_EMPTY, EVERY_MAP]);

val letrec_lem = Q.prove (
`!l1 l2. (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l1 =
          MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND z))) (SND (SND (SND z)))))))
              l2) =
         (l1 = MAP (\z. (FST z, TE_arrow (FST (SND (SND z))) (SND (SND (SND z))))) l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
Cases_on `h` THEN Cases_on `h'` THEN SRW_TAC [] [shiftt_11]);

local

val lem1 = Q.prove (
`!E t. JTuprim E Uprim_raise t = ?t'. tkind E t' /\ (t = (TE_arrow (TE_constr [] TC_exn) t'))`,
SRW_TAC [] [JTuprim_cases] THEN METIS_TAC []);

val lem2 = Q.prove (
`!l f g. value_env (MAP (\x. EB_vn (f x) (g x)) l)`,
Induct THEN SRW_TAC [] [value_env_def]);

val lem4 = Q.prove (
`!E. mono_value_env E ==> ?x_t_list. E = MAP (\(x, t). EB_vn x (TS_forall (shiftt 0 1 t))) x_t_list`,
recInduct mono_value_env_ind THEN SRW_TAC [] [mono_value_env_def] THEN 
Cases_on `ts` THEN FULL_SIMP_TAC list_ss [mono_ts_def] THEN IMP_RES_TAC shift_has0_thm THEN
Q.EXISTS_TAC `(vn, t'')::x_t_list` THEN SRW_TAC [] []);

val vn_to_x_t_def = Define 
`vn_to_x_t (EB_vn n (TS_forall t)) = (n, t)`;

val lem3 = Q.prove (
`!l1 l2 S. (LENGTH l1 = LENGTH l2) /\
           EVERY (\(EB,subst). ?t. (EB = EB_vn (FST subst) (TS_forall (shiftt 0 1 t))) /\ 
                                   JTe (shiftTsig 0 1 S) (EB_tv::E) (SND subst) t)
                 (ZIP (l1, l2)) ==>
         EVERY (\(EB,(x',v')). (FST (vn_to_x_t EB) = x') /\ 
                               JTe (shiftTsig 0 1 S) (EB_tv::E) v' (idxsubn 0 [] (SND (vn_to_x_t EB))))
               (ZIP (l1, l2))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN
FULL_SIMP_TAC (srw_ss()) [vn_to_x_t_def, sub_shiftt_thm2]);

val lem5 = Q.prove (
`!l1 l2 S. (LENGTH l1 = LENGTH l2) /\
           EVERY (\(EB,subst). ?t. (EB = EB_vn (FST subst) (TS_forall (shiftt 0 1 t))) /\ JTe S E (SND subst) t)
                 (ZIP (l1, l2)) ==>
         EVERY (\(EB,(x',v')). (FST (vn_to_x_t EB) = x') /\ 
                               JTe (shiftTsig 0 1 S) (EB_tv::E) v' (SND (vn_to_x_t EB)))
               (ZIP (l1, l2))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN
FULL_SIMP_TAC (srw_ss()) [vn_to_x_t_def, sub_shiftt_thm2] THEN
IMP_RES_TAC weak_one_tv_thm THEN METIS_TAC [APPEND, num_tv_def, shiftE_def]);

val lem6 = Q.prove (
`!l1 l2. (MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l1 =
          MAP (\z. EB_vn (FST z) (TS_forall (shiftt 0 1 (SND z)))) l2) ==>
         (l1 = l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN 
FULL_SIMP_TAC list_ss [environment_binding_11, typescheme_11] THEN
Cases_on `h` THEN Cases_on `h'` THEN FULL_SIMP_TAC list_ss [shiftt_11]);

val lem8 = Q.prove (
`!l1 l2. (MAP (\z. LRB_simple (FST z) (SND (SND z))) l1 = MAP (\z. LRB_simple (FST z) (FST (SND z))) l2) ==> 
         (MAP FST l1 = MAP FST l2) /\ (MAP (\x. SND (SND x)) l1 = MAP (\x. FST (SND x)) l2)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
Cases_on `h` THEN Cases_on `h'` THEN SRW_TAC [] []);

val lem9 = Q.prove (
`!l1 l2 P. EVERY (\z:value_name # expr # pattern_matching. P (SND (SND z))) l1 /\
           (MAP (\x. SND (SND x)) l1 = MAP (\x. FST (SND x)) l2) ==>
           EVERY (\z:value_name # pattern_matching # typexpr # typexpr. P (FST (SND z))) l2`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss []);

val lem10 = Q.prove (
`!l1 l2. (LENGTH l1 = LENGTH l2) /\ (MAP FST l1 = MAP FST l2) ==>
         EVERY (\p. FST (FST p) = FST (SND p)) (ZIP (l1, l2))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss []);

val lem11 = Q.prove (
`!l1 l2 f P.
  (LENGTH l1 = LENGTH l2) /\ 
  (MAP (\x. SND (SND x)) l1 = MAP (\x. FST (SND x)) l2) /\
  EVERY (\x. f (SND (SND x)) = FST (SND x)) l1 /\ 
  EVERY (\p. P (f (FST (SND p))) (FST (SND (SND p))) (SND (SND (SND p)))) l2 ==>
  EVERY (\p. P (FST (SND (SND p))) (FST (SND (SND (FST p)))) (SND (SND (SND (FST p))))) (ZIP (l2, l1))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []);

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

val lem15 =
(GEN_ALL o SIMP_RULE list_ss [num_tv_def] o Q.SPEC `[EB_tv]`) tkind_weak_thm;

val lem16 = Q.prove (
`!l p. MEM p l /\ ALL_DISTINCT (MAP FST l) ==>
(lookup (MAP (\(x,pm,t1,t2). EB_vn x (TS_forall (shiftt 0 1 (TE_arrow t1 t2)))) l++EB_tv::E) (name_vn (FST p)) =
 SOME (EB_vn (FST p) (TS_forall (shiftt 0 1 (TE_arrow (FST (SND (SND p))) (SND (SND (SND p))))))))`,
SIMP_TAC list_ss [LAMBDA_PROD2] THEN Induct THEN SRW_TAC [] [lookup_def, domEB_def, shiftEB_add_thm] THEN
METIS_TAC [lookup_dom_thm, MEM_MAP]);

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

val lem21 = Q.prove (
`!E up t. JTuprim E up t ==> ?t1 t2. t = TE_arrow t1 t2`,
SRW_TAC [] [JTuprim_cases]);

val lem22 = Q.prove (
`!E bp t. JTbprim E bp t ==> ?t1 t2 t3. t = TE_arrow t1 (TE_arrow t2 t3)`,
SRW_TAC [] [JTbprim_cases]);

val lem23 = Q.prove (
`!S E L E' t t'. JTLout S E L E' /\ JTLin S E L /\ JTeq E t t' ==> JTeq (E'++E) t t'`,
SRW_TAC [] [JTLout_cases, JTLin_cases] THEN SRW_TAC [] [] THEN
IMP_RES_TAC (Q.SPECL [`E`, `EB_l location t''`] weak_teq_lem1) THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN
METIS_TAC [ok_thm]);

val simple_raise_tac = 
  IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC list_ss [Eok_def, lem1] THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC list_ss [Eok_def] THEN 
      FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN SRW_TAC [] [] THEN
      IMP_RES_TAC teq_ok_thm THEN FULL_SIMP_TAC (srw_ss()) [Eok_def] THEN
      METIS_TAC [teq_thm, JTeq_rules];

in

val recfun_pres_thm = Q.store_thm ("recfun_pres_thm",
`!S E lrbs pm t t' x_t_list.
      closed_env E /\
      JTletrec_binding (shiftTsig 0 1 S) (EB_tv::E) lrbs
                                             (MAP (\(x, t). EB_vn x (TS_forall (shiftt 0 1 t))) x_t_list) /\
      JTpat_matching S (MAP (\(x, t). EB_vn x (TS_forall t)) x_t_list ++ E) pm t t' ==>
      JTe S E (recfun lrbs pm) (TE_arrow t t')`,
Cases_on `lrbs` THEN SRW_TAC [] [JTe_fun, recfun_def, substs_value_name_letrec_binding_def] THEN
SRW_TAC [] [MAP_MAP] THEN 
MAP_EVERY Q.EXISTS_TAC [`t`, `t'`] THEN SRW_TAC [] [] THENL
[MATCH_MP_TAC substs_pm_lem THEN Q.EXISTS_TAC `REVERSE x_t_list` THEN
      SRW_TAC [] [MAP_MAP, EVERY_MAP, LENGTH_MAP, ZIP_MAP, MAP_ZIP_SAME, LENGTH_REVERSE,
                  is_value_of_expr_def, is_non_expansive_of_expr_def] THEN
      FULL_SIMP_TAC (srw_ss()) [GSYM MAP_REVERSE] THEN1
      METIS_TAC [LENGTH_MAP, LENGTH_REVERSE] THEN
      FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2, GSYM MAP_REVERSE, letrec_lem] THEN
      FULL_SIMP_TAC (srw_ss()) [MAP_REVERSE, ALL_DISTINCT_REVERSE, MAP_MAP] THEN1
      METIS_TAC [MAP_11_ALL_DISTINCT, name_11] THEN
      SRW_TAC [] [ZIP_MAP, MAP_ZIP_SAME, EVERY_MAP, EVERY_MEM] THEN
      FULL_SIMP_TAC (srw_ss()) [MAP_MAP, MEM_MAP, GSYM MAP_REVERSE, MAP_MAP] THEN
      SRW_TAC [] [JTe_fun] THEN SRW_TAC [] [GSYM MAP_REVERSE, letrec_lem] THEN
      SRW_TAC [] [MAP_REVERSE, REVERSE_EQ, GSYM LEFT_EXISTS_AND_THM, MAP_MAP] THEN
      Q.EXISTS_TAC `MAP (\(vn, pm, t, t'). (vn, pm, shiftt 0 1 t, shiftt 0 1 t'))
                        value_name_pattern_matching_t_t'_list` THEN
      SRW_TAC [] [EVERY_MAP, LAMBDA_PROD2, MAP_MAP] THENL
      [FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN RES_TAC THEN IMP_RES_TAC lem12 THEN
           FULL_SIMP_TAC (srw_ss()) [value_env_map_thm, value_env_num_tv_thm, lem14, shiftTsig_add_thm, 
                                     shiftt_def] THEN
           METIS_TAC [MAP_REVERSE, APPEND, APPEND_ASSOC],
       SRW_TAC [] [JTvalue_name_cases] THEN
           Q.EXISTS_TAC `TE_arrow (FST (SND (SND p'))) (SND (SND (SND p')))` THEN
           SRW_TAC [] [] THENL
           [Q.EXISTS_TAC `TS_forall (TE_arrow (shiftt 0 1 (FST (SND (SND p')))) 
                                    (shiftt 0 1 (SND (SND (SND p')))))` THEN
                SRW_TAC [] [JTinst_cases] THENL
                [SRW_TAC [] [GSYM MAP_REVERSE] THEN 
                     MATCH_MP_TAC (SIMP_RULE (srw_ss()) [LAMBDA_PROD2, shiftt_def] lem16) THEN
                     SRW_TAC [] [MAP_REVERSE, ALL_DISTINCT_REVERSE] THEN 
                     Q.PAT_ASSUM `ALL_DISTINCT a` MP_TAC THEN
                     REPEAT (POP_ASSUM (K ALL_TAC)) THEN Induct_on `value_name_pattern_matching_t_t'_list` THEN
                     SRW_TAC [] [MEM_MAP],
                 FULL_SIMP_TAC (srw_ss()) [EVERY_MEM, Eok_def, idxsub_def, GSYM idxsubn0_thm, 
                                           sub_shiftt_thm2] THEN
                     Q.EXISTS_TAC `[]` THEN SRW_TAC [] [] THEN MATCH_MP_TAC lem15 THEN
                     SRW_TAC [] [Eok_def, GSYM MAP_REVERSE] THEN FULL_SIMP_TAC (srw_ss()) [shiftt_def] THEN
                     METIS_TAC [ok_thm, ok_ok_thm]],
            FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN RES_TAC THEN
                IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2, MAP_REVERSE, shiftt_def] THEN
                `tkind (REVERSE (MAP (\x. EB_vn (FST x) (TS_forall (TE_arrow (shiftt 0 1 (FST (SND (SND x))))
                                                                             (shiftt 0 1 (SND (SND (SND x)))))))
                                     value_name_pattern_matching_t_t'_list) ++ EB_tv::E)
                       (TE_arrow (FST (SND (SND p'))) (SND (SND (SND p'))))`
                                     by SRW_TAC [] [Eok_def] THEN
                METIS_TAC [JTeq_rules]]],
 IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2] THEN
     METIS_TAC [JTeq_rules, value_env_ok_str_thm, value_env_map_thm, APPEND]]);

val matching_preservation_lem = Q.prove (
`!v pattern_matching e' S E t' t.
 JRmatching_success v pattern_matching e' /\ JTe S E v t' /\ JTpat_matching S E pattern_matching t' t /\ 
 closed_env E /\ is_value_of_expr v ==>
 JTe S E e' t`,
SRW_TAC [] [JRmatching_success_cases] THEN FULL_SIMP_TAC (srw_ss()) [JTe_fun] THEN
Cases_on `pattern_e_E_list` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THENL
[IMP_RES_TAC pat_env_lem THEN IMP_RES_TAC lem4 THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        IMP_RES_TAC pat_num_bindings_lem THEN IMP_RES_TAC pat_preservation_thm THEN
        MATCH_MP_TAC substs_lem THEN IMP_RES_TAC lem17 THEN
        Q.EXISTS_TAC `MAP vn_to_x_t (REVERSE E'')` THEN
        SRW_TAC [] [MAP_REVERSE] THEN FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2] THENL
        [IMP_RES_TAC PERM_LENGTH THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_REVERSE] THEN
              METIS_TAC [LENGTH_REVERSE, LENGTH_MAP, PERM_LENGTH],
         SRW_TAC [] [MAP_MAP, lem18] THEN IMP_RES_TAC distinct_pat_env THEN
                METIS_TAC [value_perm_thm, APPEND, value_env_map_thm],
         FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN Cases_on `SND z` THEN 
                 SRW_TAC [] [] THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
                 METIS_TAC [value_nonexpansive_thm],
         IMP_RES_TAC lem19 THEN IMP_RES_TAC distinct_pat_env THEN
                 FULL_SIMP_TAC (srw_ss()) [MAP_MAP, domEB_def, LAMBDA_PROD2, ALL_DISTINCT_REVERSE] THEN
                 METIS_TAC [MAP_11_ALL_DISTINCT, name_11, PERM_ALL_DISTINCT, PERM_MAP, MAP_MAP],
         `LENGTH (REVERSE E'') = LENGTH x_v_list`
                        by METIS_TAC [LENGTH_REVERSE, LENGTH_MAP, PERM_LENGTH] THEN
                 SRW_TAC [] [GSYM MAP_REVERSE, ZIP_MAP, EVERY_MAP] THEN 
                 METIS_TAC [LENGTH_MAP, LENGTH_REVERSE, SIMP_RULE list_ss [LAMBDA_PROD2] lem5, MAP_REVERSE]],
 SRW_TAC [] [lem1, JTconst_cases, JTconstr_c_cases] THEN
       Q.EXISTS_TAC `TE_constr [] TC_exn` THEN
       `tkind E (TE_constr [] TC_exn)` by SRW_TAC [] [Eok_def] THEN
        METIS_TAC [pat_env_lem, ok_thm, value_env_ok_str_thm, APPEND, pat_ok_thm,
                   ok_ok_thm, JTeq_rules]]);

local

val lem1 = Q.prove (
`!x. (substs_x_xs case x of substs_x_xs l -> l) = x`,
Cases THEN SRW_TAC [] []);

in

val JMmatch_tyvars_thm = Q.prove (
`!v p subs. JM_match v p subs ==> !x_v_list. (subs = substs_x_xs x_v_list) ==> (ftv_expr v = []) ==>
            EVERY (\xv. ftv_expr (SND xv) = []) x_v_list`,
RULE_INDUCT_TAC JM_match_ind [ftv_letrec_binding_def, MEM_FLAT, MEM_MAP, EXISTS_MEM, ELIM_UNCURRY,
                              MEM, FLAT_EQ_EMPTY, EVERY_MAP, EVERY_MEM]
[([``"JM_match_alias"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss []),
 ([``"JM_match_construct"``, ``"JM_match_tuple"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `x''` THEN Cases_on `r` THEN Cases_on `r'` THEN
         FULL_SIMP_TAC list_ss [substs_x_case_def] THEN METIS_TAC [FST, SND]),
 ([``"JM_match_record"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `x''` THEN Cases_on `r` THEN Cases_on `r'` THEN
         FULL_SIMP_TAC list_ss [substs_x_case_def] THEN IMP_RES_TAC PERM_MEM_EQ THEN 
         FULL_SIMP_TAC list_ss [MEM_MAP] THEN METIS_TAC [FST, SND, lem1]),
 ([``"JM_match_cons"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THENL
  [Cases_on `subs` THEN FULL_SIMP_TAC list_ss [substs_x_case_def] THEN METIS_TAC [FST, SND],
   Cases_on `subs'` THEN FULL_SIMP_TAC list_ss [substs_x_case_def] THEN METIS_TAC [FST, SND]])]); 

end;

val e_preservation_thm = Q.prove (
`!e L e'. JR_expr e L e' ==> !E S. closed_env E ==> !t. JTe S E e t /\ JTLin S E L ==> 
          ?E''. JTLout S E L E'' /\ JTe S (E''++E) e' t`,
RULE_INDUCT_TAC JR_expr_sind [JTL_nil_lem, JTe_fun, JTconst_fun, ftv_letrec_binding_def]
[([``"JR_expr_uprim"``], 
  SRW_TAC [] [] THEN IMP_RES_TAC lem21 THEN 
      FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN SRW_TAC [] [] THEN
      `JTe S E v t1'` by METIS_TAC [teq_thm, JTeq_rules] THEN IMP_RES_TAC uprim_preservation_lem THEN 
      METIS_TAC [lem23, teq_thm]),
 ([``"JR_expr_bprim"``], 
  SRW_TAC [] [] THEN IMP_RES_TAC lem22 THEN 
      FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN SRW_TAC [] [] THEN
      `JTe S E v1 t1'' /\ JTe S E v2 t2` by METIS_TAC [teq_thm, JTeq_rules] THEN 
      IMP_RES_TAC bprim_preservation_lem THEN METIS_TAC [lem23, teq_thm]),
 ([``"JR_expr_typed_ctx"``],
  SRW_TAC [] []),
 ([``"JR_expr_apply_ctx_arg"``, ``"JR_expr_apply_ctx_fun"``, ``"JR_expr_sequence_ctx_left"``,
   ``"JR_expr_ifthenelse_ctx"``, ``"JR_expr_match_ctx"``, ``"JR_expr_try_ctx"``],
  METIS_TAC [label_weak_thm]),
 ([``"JR_expr_apply_raise1"``, ``"JR_expr_apply_raise2"``, ``"JR_expr_sequence_raise"``, ``"JR_expr_if_raise"``,
   ``"JR_expr_match_raise"``, ``"JR_expr_for_raise1"``, ``"JR_expr_for_raise2"``, ``"JR_expr_cons_raise1"``,
   ``"JR_expr_cons_raise2"``, ``"JR_expr_assert_raise"``],
  SRW_TAC [] [] THEN simple_raise_tac),
 ([``"JR_expr_apply"``],
  simple_raise_tac),
 ([``"JR_expr_let_ctx"``],
  SRW_TAC [] [] THENL
  [RES_TAC THEN Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN DISJ1_TAC THEN Q.EXISTS_TAC `x_t_list` THEN
        METIS_TAC [val_env_label_weak_thm, label_weak_thm, lem2, MAP_REVERSE],
   IMP_RES_TAC nexp_red_thm THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JTL_nil_lem] THEN
        SRW_TAC [] [] THEN DISJ2_TAC THEN
        METIS_TAC [closed_env_tv_lem, ok_thm, ok_ok_thm, MAP_REVERSE]]),
 ([``"JR_expr_let_raise"``],
  SRW_TAC [] [] THENL
  [IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC list_ss [Eok_def, lem1] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [Eok_def] THEN
        FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN SRW_TAC [] [] THEN
        METIS_TAC [value_env_ok_str_thm, lem2, MAP_REVERSE, APPEND, teq_thm, JTeq_rules],
   IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC list_ss [Eok_def, lem1] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [Eok_def, is_non_expansive_of_expr_def,
                               is_binary_prim_app_value_of_expr_def] THEN 
        METIS_TAC [value_env_ok_str_thm, lem2, MAP_REVERSE, APPEND]]),
 ([``"JR_expr_let_subst"``],
  SRW_TAC [] [GSYM MAP_REVERSE] THENL
  [`x_t_list' = x_t_list` by METIS_TAC [REVERSE_EQ, lem6] THEN SRW_TAC [] [] THEN
        IMP_RES_TAC pat_num_bindings_lem THEN IMP_RES_TAC pat_preservation_thm THEN
        MATCH_MP_TAC substs_lem THEN IMP_RES_TAC lem17 THEN
        Q.EXISTS_TAC `MAP vn_to_x_t (REVERSE E'')` THEN
        SRW_TAC [] [MAP_REVERSE] THEN FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2,  value_env_map_thm] THENL
        [IMP_RES_TAC PERM_LENGTH THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_REVERSE] THEN
              METIS_TAC [LENGTH_REVERSE, LENGTH_MAP, PERM_LENGTH],
         SRW_TAC [] [MAP_MAP, lem18] THEN IMP_RES_TAC distinct_pat_env THEN
                METIS_TAC [value_perm_thm, APPEND, value_env_map_thm],
         FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN Cases_on `SND z` THEN 
                 SRW_TAC [] [] THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
                 METIS_TAC [value_nonexpansive_thm],
         IMP_RES_TAC lem19 THEN IMP_RES_TAC distinct_pat_env THEN
                 FULL_SIMP_TAC (srw_ss()) [MAP_MAP, domEB_def, LAMBDA_PROD2, ALL_DISTINCT_REVERSE] THEN
                 METIS_TAC [MAP_11_ALL_DISTINCT, name_11, PERM_ALL_DISTINCT, PERM_MAP, MAP_MAP],
         `LENGTH (REVERSE E'') = LENGTH x_v_list`
                        by METIS_TAC [LENGTH_REVERSE, LENGTH_MAP, PERM_LENGTH] THEN
                 SRW_TAC [] [GSYM MAP_REVERSE, ZIP_MAP, EVERY_MAP] THEN 
                 METIS_TAC [LENGTH_MAP, LENGTH_REVERSE, SIMP_RULE list_ss [LAMBDA_PROD2] lem5, MAP_REVERSE]],
   `x_t_list' = x_t_list` by METIS_TAC [REVERSE_EQ, lem6] THEN SRW_TAC [] [] THEN
        IMP_RES_TAC pat_num_bindings_lem THEN IMP_RES_TAC pat_preservation_thm THEN
        MATCH_MP_TAC substs_lem THEN IMP_RES_TAC lem17 THEN
        Q.EXISTS_TAC `MAP (\(x,t). (x, idxsubn 0 [] t)) (MAP vn_to_x_t (REVERSE E''))` THEN
        SRW_TAC [] [MAP_REVERSE] THEN FULL_SIMP_TAC (srw_ss()) [LAMBDA_PROD2,  value_env_map_thm] THENL
        [IMP_RES_TAC PERM_LENGTH THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_REVERSE] THEN
              METIS_TAC [LENGTH_REVERSE, LENGTH_MAP, PERM_LENGTH],
         SRW_TAC [] [MAP_MAP, lem18] THEN IMP_RES_TAC distinct_pat_env THEN IMP_RES_TAC lem20 THEN
                `ALL_DISTINCT (MAP domEB (MAP (\z. EB_vn (FST z) (TS_forall (SND z))) (REVERSE x_t_list)))`
                        by FULL_SIMP_TAC (srw_ss()) [MAP_MAP, vn_to_x_t_def, domEB_def] THEN
                METIS_TAC [value_perm_thm, APPEND, value_env_map_thm],
         FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN SRW_TAC [] [] THEN Cases_on `SND z` THEN 
                 SRW_TAC [] [] THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
                 METIS_TAC [value_nonexpansive_thm],
         IMP_RES_TAC lem19 THEN IMP_RES_TAC distinct_pat_env THEN
                 FULL_SIMP_TAC (srw_ss()) [MAP_MAP, domEB_def, LAMBDA_PROD2, ALL_DISTINCT_REVERSE] THEN
                 METIS_TAC [MAP_11_ALL_DISTINCT, name_11, PERM_ALL_DISTINCT, PERM_MAP, MAP_MAP],
         `LENGTH (REVERSE E'') = LENGTH x_v_list`
                        by METIS_TAC [LENGTH_REVERSE, LENGTH_MAP, PERM_LENGTH] THEN
                 SRW_TAC [] [GSYM MAP_REVERSE, ZIP_MAP, EVERY_MAP] THEN 
                 METIS_TAC [LENGTH_MAP, LENGTH_REVERSE, SIMP_RULE list_ss [LAMBDA_PROD2] lem3,
                            MAP_REVERSE]]]),
 ([``"JR_expr_let_fail"``],
  SRW_TAC [] [] THENL
  [IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC list_ss [Eok_def, lem1] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC (srw_ss()) [Eok_def, JTconstr_c_cases] THEN
        `tkind E (TE_constr [] TC_exn)` by SRW_TAC [] [Eok_def] THEN
        METIS_TAC [value_env_ok_str_thm, lem2, MAP_REVERSE, APPEND, ok_ok_thm, JTeq_rules],
   IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC list_ss [Eok_def, lem1] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC (srw_ss()) [Eok_def, JTconstr_c_cases, is_binary_prim_app_value_of_expr_def] THEN 
        `tkind E (TE_constr [] TC_exn)` by SRW_TAC [] [Eok_def] THEN
        METIS_TAC [value_env_ok_str_thm, lem2, MAP_REVERSE, APPEND, ok_ok_thm, JTeq_rules]]),
 ([``"JR_expr_letrec"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [FLAT_EQ_EMPTY, EVERY_MAP, REVERSE_EQ, ftv_letrec_binding_def] THEN 
        MATCH_MP_TAC substs_lem THEN SRW_TAC [] [EVERY_MAP] THEN
        Q.EXISTS_TAC `x_t_list` THEN
        IMP_RES_TAC letrec_lem THEN IMP_RES_TAC lem8 THEN FULL_SIMP_TAC list_ss [MAP_MAP] THEN
        SRW_TAC [] [LAMBDA_PROD2] THENL
        [METIS_TAC [LENGTH_MAP],
         FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [recfun_is_value, value_nonexpansive_thm],
        (* FULL_SIMP_TAC list_ss [EVERY_MEM] THEN SRW_TAC [] [] THEN 
                Tactical.REVERSE (`ftv_expr (FST (SND z)) = []` by ALL_TAC) THEN1
                SRW_TAC [] [DISJOINT_def] THEN
                RES_TAC THEN POP_ASSUM (fn x => ONCE_REWRITE_TAC [GSYM x]) THEN 
                MATCH_MP_TAC recfun_ftv_thm THEN 
                SRW_TAC [] [ftv_letrec_binding_def, FLAT_EQ_EMPTY, EVERY_MAP] THEN
                HO_MATCH_MP_TAC lem9 THEN SRW_TAC [] [EVERY_MEM] THEN METIS_TAC [],*)
         METIS_TAC [MAP_11_ALL_DISTINCT2, name_11, MAP_MAP],
         `LENGTH x_e_pattern_matching_list = LENGTH value_name_pattern_matching_t_t'_list` 
                                       by METIS_TAC [LENGTH_MAP] THEN
                 SRW_TAC [] [ZIP_MAP, EVERY_MAP, EVERY_CONJ, lem10] THEN HO_MATCH_MP_TAC lem11 THEN
                 SRW_TAC [] [] THEN
                 Q.EXISTS_TAC `\y. recfun (LRBs_inj (MAP (\z. LRB_simple (FST z) (FST (SND z)))
                                                         value_name_pattern_matching_t_t'_list)) y` THEN
                 SRW_TAC [] [] THEN
                 SRW_TAC [] [EVERY_MEM] THEN MATCH_MP_TAC recfun_pres_thm THEN
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
                 SRW_TAC [] [MAP_REVERSE, MAP_MAP, EVERY_MEM, ELIM_UNCURRY]]]),
 ([``"JR_expr_match_step"``],
  METIS_TAC [matching_step_preservation_lem]),
 ([``"JR_expr_match_success"``],
  METIS_TAC [matching_preservation_lem]),
 ([``"JR_expr_and"``, ``"JR_expr_or"``, ``"JR_expr_while"``],
  METIS_TAC [ok_thm, ok_ok_thm, teq_thm]),
 ([``"JR_expr_for_ctx1"``],
  SRW_TAC [] [] THEN RES_TAC THEN Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN1 METIS_TAC [label_weak_thm] THEN 
        METIS_TAC [value_env_def, APPEND, val_env_label_weak_thm, lem23]),
 ([``"JR_expr_for_ctx2"``],
  SRW_TAC [] [] THEN RES_TAC THEN Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN1 METIS_TAC [label_weak_thm] THEN
        METIS_TAC [value_env_def, APPEND, val_env_label_weak_thm, lem23]),
 ([``"JR_expr_for_to_do"``, ``"JR_expr_for_downto_do"``],
  SRW_TAC [] [] THEN DISJ1_TAC THEN Q.EXISTS_TAC `[(VN_id lowercase_ident, TE_constr [] TC_int)]` THEN 
         SRW_TAC [] [] THEN
         Q.EXISTS_TAC `[(VN_id lowercase_ident, TE_constr [] TC_int)]` THEN 
         SRW_TAC [] [JTpat_fun, Eok_def, shiftt_def] THEN
         Q.EXISTS_TAC `TE_constr [] TC_int` THEN SRW_TAC [] [Eok_def, shiftt_def]),
 ([``"JR_expr_for_to_done"``,  ``"JR_expr_for_downto_done"``], 
  METIS_TAC []),
 ([``"JR_expr_try_catch"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `TE_constr [] TC_exn` THEN SRW_TAC [] [] THEN 
        FULL_SIMP_TAC (srw_ss()) [JTuprim_cases] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC (srw_ss()) [teq_fun1, is_abbrev_tc_def] THENL
        [METIS_TAC [teq_thm, JTeq_rules],
         Q.EXISTS_TAC `pattern_e_E_list++[(P_any, Expr_apply (Expr_uprim Uprim_raise) v, [])]` THEN
             SRW_TAC [] [JTpat_fun, JTe_fun] THEN SRW_TAC [] [Eok_def] THENL
             [METIS_TAC [ok_ok_thm],
              SRW_TAC [] [JTuprim_cases] THEN METIS_TAC [teq_thm, JTeq_rules],
              DECIDE_TAC]]),
 ([``"JR_expr_tuple_ctx"``],
  SRW_TAC [] [] THEN
    `?l1 et l2. (e_list = MAP FST l1) /\ (e = FST et) /\ (v_list = MAP FST l2) /\
                (e_t_list = l1++[et]++l2)` by (FULL_SIMP_TAC list_ss [MAP_split] THEN
                                               Cases_on `l5'` THEN FULL_SIMP_TAC list_ss [] THEN
                                               METIS_TAC []) THEN
        FULL_SIMP_TAC list_ss [EVERY_APPEND, FLAT_EQ_EMPTY] THEN SRW_TAC [] [] THEN RES_TAC THEN
        Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `l1++[(e', SND et)]++l2` THEN
        SRW_TAC [] [EVERY_MEM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [label_weak_thm, lem23]),
 ([``"JR_expr_tuple_raise"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MAP_split] THEN Cases_on `l5'` THEN FULL_SIMP_TAC list_ss [] THEN 
        Cases_on `h` THEN
        SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_APPEND] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [JTe_fun, JTuprim_cases, typexpr_11, unary_prim_distinct] THEN
        SRW_TAC [] [Eok_def, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        simple_raise_tac),
 ([``"JR_expr_constr_ctx"``],
  SRW_TAC [] [] THEN
  `?l1 et l2. (e_list = MAP FST l1) /\ (e = FST et) /\ (v_list = MAP FST l2) /\
             (e_t_list = l1++[et]++l2)` by (FULL_SIMP_TAC list_ss [MAP_split] THEN
                                            Cases_on `l5'` THEN FULL_SIMP_TAC list_ss [] THEN
                                            METIS_TAC []) THEN
        FULL_SIMP_TAC list_ss [EVERY_APPEND, FLAT_EQ_EMPTY] THEN SRW_TAC [] [] THEN RES_TAC THEN
        Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `l1++[(e', SND et)]++l2` THEN
        SRW_TAC [] [EVERY_MEM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [label_weak_thm, label_constr_p_weak_thm, lem23]),
 ([``"JR_expr_constr_raise"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MAP_split] THEN Cases_on `l5'` THEN FULL_SIMP_TAC list_ss [] THEN 
        Cases_on `h` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_APPEND] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [JTe_fun, JTuprim_cases, typexpr_11, unary_prim_distinct] THEN
        SRW_TAC [] [Eok_def, EVERY_MAP] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        Q.EXISTS_TAC `t1` THEN SRW_TAC [] [] THEN
        Q.EXISTS_TAC `TE_arrow (TE_constr [] TC_exn) t` THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN
        METIS_TAC [teq_ok_thm, JTeq_rules]),
 ([``"JR_expr_cons_ctx1"``, ``"JR_expr_cons_ctx2"``],
  METIS_TAC [label_weak_thm, lem23]),
 ([``"JR_expr_record_ctx"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MAP_split] THEN SRW_TAC [] [GSYM MAP_split] THEN Cases_on `l5'` THEN
        FULL_SIMP_TAC list_ss [EVERY_APPEND, FLAT_EQ_EMPTY] THEN SRW_TAC [] [] THEN RES_TAC THEN
        Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN
        MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`, `l4'++[(FST h, e', SND (SND h))]++l5`, 
                                `typeconstr_name`, `kind`] THEN
        SRW_TAC [] [EVERY_MEM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [label_weak_thm, label_field_weak_thm, label_lookup_weak_thm, name_distinct, lem23]),
 ([``"JR_expr_record_raise"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MAP_split] THEN SRW_TAC [] [GSYM MAP_split] THEN Cases_on `l5'` THEN
        FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `r` THEN
        FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JTe_fun] THEN 
        IMP_RES_TAC field_constr_p_ok_thm THEN FULL_SIMP_TAC list_ss [lem1] THEN SRW_TAC [] [] THEN
        simple_raise_tac),
 ([``"JR_expr_record_with_ctx1"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MAP_split] THEN SRW_TAC [] [GSYM MAP_split] THEN Cases_on `l5'` THEN
        FULL_SIMP_TAC list_ss [EVERY_APPEND, FLAT_EQ_EMPTY] THEN SRW_TAC [] [] THEN RES_TAC THEN
        Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN
        Q.EXISTS_TAC `l4'++[(FST h, e', SND (SND h))]++l5` THEN
        SRW_TAC [] [EVERY_MEM] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [label_weak_thm, label_field_weak_thm, lem23]),
 ([``"JR_expr_record_with_raise1"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MAP_split] THEN SRW_TAC [] [GSYM MAP_split] THEN Cases_on `l5'` THEN
        FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `r` THEN
        FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JTe_fun] THEN
        IMP_RES_TAC field_constr_p_ok_thm THEN FULL_SIMP_TAC list_ss [lem1] THEN SRW_TAC [] [] THEN
        Q.EXISTS_TAC `t1` THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `TE_arrow (TE_constr [] TC_exn) t` THEN
        SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN
        METIS_TAC [JTeq_rules, teq_ok_thm]),
 ([``"JR_expr_record_with_ctx2"``],
  SRW_TAC [] [] THEN RES_TAC THEN Q.EXISTS_TAC `E''` THEN SRW_TAC [] [] THEN 
        Q.EXISTS_TAC `field_name_e_t_list` THEN
        SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN
        METIS_TAC [label_field_weak_thm, label_weak_thm, lem23]),
 ([``"JR_expr_record_raise_ctx2"``], 
  SRW_TAC [] [] THEN
        Q.EXISTS_TAC `t1` THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `t''` THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC (srw_ss()) [is_abbrev_tc_def, teq_fun1] THEN
        METIS_TAC [JTeq_rules, ok_thm]),
 ([``"JR_expr_record_with_many"``],
  SRW_TAC [] [] THEN Cases_on `field_name_e_t_list` THEN FULL_SIMP_TAC list_ss [] THEN 
        MAP_EVERY Q.EXISTS_TAC [`t''`, `t'`] THEN
        SRW_TAC [] [] THENL [ALL_TAC, METIS_TAC [LENGTH_MAP]] THEN
        FULL_SIMP_TAC list_ss [MAP_split] THEN SRW_TAC [] [GSYM MAP_split] THEN Cases_on `l5'` THEN
        FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN 
        MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`, 
                                `l4'++[(FST h, FST (SND h), SND (SND h'))]++l5`,
                                `typeconstr_name`, `kind`] THEN
        SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN
        METIS_TAC [teq_thm, record_arg_types_lem, JTeq_rules]),
 ([``"JR_expr_record_with_1"``],
  SRW_TAC [] [] THEN Cases_on `field_name_e_t_list` THEN FULL_SIMP_TAC list_ss [] THEN
        FULL_SIMP_TAC list_ss [MAP_split] THEN SRW_TAC [] [GSYM MAP_split] THEN Cases_on `l5'` THEN
        FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
        MAP_EVERY Q.EXISTS_TAC [`field_name'_list`, `t'_list`,
                                `l4'++[(FST h, FST (SND h), SND (SND h'))]++l5`,
                                `typeconstr_name`, `kind`] THEN
        SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN
        METIS_TAC [teq_thm, record_arg_types_lem, JTeq_rules]),
 ([``"JR_expr_record_access_ctx"``],
  METIS_TAC [label_field_weak_thm, lem23]),
 ([``"JR_expr_record_access_raise"``],
  SRW_TAC [] [] THEN IMP_RES_TAC ok_thm THEN FULL_SIMP_TAC list_ss [Eok_def, lem1] THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC list_ss [Eok_def] THEN
        Q.EXISTS_TAC `t1` THEN SRW_TAC [] [] THEN
        Q.EXISTS_TAC `TE_arrow (TE_constr [] TC_exn) t` THEN SRW_TAC [] [] THEN
        FULL_SIMP_TAC (srw_ss()) [teq_fun1, is_abbrev_tc_def] THEN
        METIS_TAC [teq_ok_thm, JTeq_rules]),
 ([``"JR_expr_record_access"``],
  FULL_SIMP_TAC list_ss [MAP_split] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EVERY_APPEND] THEN
        Cases_on `l5'` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
        METIS_TAC [teq_thm, record_arg_types_lem, JTeq_rules]),
 ([``"JR_expr_assert_ctx"``],
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [JR_expr_fun] THEN METIS_TAC [label_weak_thm, lem23]),
 ([``"JR_expr_assert_false"``],
  SRW_TAC [] [JTconstr_c_cases, JTuprim_cases] THEN Q.EXISTS_TAC `TE_constr [] TC_exn` THEN SRW_TAC [] [] THEN
        `tkind E (TE_constr [] TC_exn)` by (SRW_TAC [] [Eok_def] THEN METIS_TAC [ok_ok_thm]) THEN
        `tkind E (TE_arrow (TE_constr [] TC_exn) t)` by (SRW_TAC [] [Eok_def] THEN METIS_TAC [teq_ok_thm]) THEN
        METIS_TAC [ok_ok_thm, JTeq_rules, teq_ok_thm])]);

end; 


val e_preservation_thm = 
  save_thm ("e_preservation_thm", SIMP_RULE list_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] 
                                    e_preservation_thm);

val _ = export_theory ();

