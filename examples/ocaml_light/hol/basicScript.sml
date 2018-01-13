open HolKernel boolLib bossLib IndDefLib IndDefRules listTheory optionTheory relationTheory pairTheory 
open rich_listTheory combinTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory shiftTheory;

val _ = new_theory "basic";

val OPTION_MAP_I = Q.prove (
`!x. OPTION_MAP (\y . y) x = x`,
Cases THEN SRW_TAC [] []);

val domEB_def = Define 
`(domEB EB_tv = name_tv) /\
 (domEB (EB_vn value_name typescheme) = name_vn value_name) /\
 (domEB (EB_cc constr_name typeconstr) = name_cn constr_name) /\
 (domEB (EB_pc constr_name type_params_opt t_list typeconstr) = name_cn constr_name) /\
 (domEB (EB_td typeconstr_name kind) = name_tcn typeconstr_name) /\
 (domEB (EB_ta type_params_opt typeconstr_name t) = name_tcn typeconstr_name) /\
 (domEB (EB_tr typeconstr_name kind field_name_list) = name_tcn typeconstr_name) /\
 (domEB (EB_fn field_name type_params_opt typeconstr_name typexpr) = name_fn field_name) /\
 (domEB (EB_l location t) = name_l location)`;

val domEB_thm = Q.prove (
`!EB name. JdomEB EB name = (domEB EB = name)`,
Cases THEN SRW_TAC [] [JdomEB_cases, domEB_def, clause_name_def] THEN METIS_TAC [typexprs_nchotomy]);

val domE_thm = Q.prove (
`!E names. JdomE E names = (MAP domEB E = names)`,
Induct THENL
[SRW_TAC [] [Once JdomE_cases, clause_name_def] THEN METIS_TAC [],
 SRW_TAC [] [Once JdomE_cases, domEB_thm, clause_name_def] THEN METIS_TAC []]);             

val lookup_def = Define
`(lookup [] name = NONE) /\
 (lookup (EB::E) name = 
    if domEB EB = name then 
      SOME EB
    else OPTION_MAP (\EB2. shiftEB 0 (if domEB EB = name_tv then 1 else 0) EB2) (lookup E name))`;

val lookup_append_thm = Q.store_thm ("lookup_append_thm",
`!E1 E2 name. lookup (E1++E2) name =
                case lookup E1 name of
                   NONE -> OPTION_MAP (\EB. shiftEB 0 (num_tv E1) EB) (lookup E2 name)
                || SOME EB -> SOME EB`,
Induct THEN SRW_TAC [] [lookup_def, num_tv_def, OPTION_MAP_I, shiftEB_add_thm] THEN
Cases_on `lookup E1 name` THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `lookup E2 name` THEN
SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [num_tv_def, shiftEB_add_thm] THEN
FULL_SIMP_TAC list_ss [domEB_def] THEN SRW_TAC [] []);

val lookup_dom_thm = Q.store_thm ("lookup_dom_thm",
`!E name. (MEM name (MAP domEB E) = ?EB. lookup E name = SOME EB) /\
          (~MEM name (MAP domEB E) = (lookup E name = NONE))`,
Induct THEN SRW_TAC [] [lookup_def] THEN METIS_TAC [NOT_SOME_NONE]);

val lookup_thm = Q.prove (
`!E name EB. Jlookup_EB E name EB = (lookup E name = SOME EB)`,
Induct THENL [
SRW_TAC [] [Once Jlookup_EB_cases, lookup_def, clause_name_def],
SIMP_TAC list_ss [Once Jlookup_EB_cases] THEN Cases THEN
       SRW_TAC [] [lookup_def, domE_thm, domEB_thm, clause_name_def] THEN EQ_TAC THEN
       SRW_TAC [] [domEB_def] THEN 
       FULL_SIMP_TAC list_ss [domEB_def, name_distinct, name_11, shiftEB_add_thm]]);

val idx_bound_def = Define
`(idx_bound [] idx = F) /\
 (idx_bound (EB_tv::E) 0 = T) /\
 (idx_bound (EB_tv::E) (SUC n2) = idx_bound E n2) /\
 (idx_bound (_::E) n = idx_bound E n)`; 

val idx_bound_thm = Q.prove (
`!E idx num. Jidx_bound E idx = idx_bound E idx`,
Induct THENL [
SRW_TAC [] [Once Jidx_bound_cases, idx_bound_def],
SRW_TAC [] [Once Jidx_bound_cases, idx_bound_def, clause_name_def] THEN
Cases_on `h` THEN SRW_TAC [] [idx_bound_def, domEB_thm, domEB_def] THEN
Cases_on `idx` THEN SRW_TAC [] [idx_bound_def] THEN FULL_SIMP_TAC list_ss [arithmeticTheory.ADD1]]);

val Slookup_thm = Q.prove (
`!st l v. JSlookup st l v = (list_assoc l st = SOME v)`,
Induct THEN ONCE_REWRITE_TAC [JSlookup_cases] THEN SRW_TAC [] [list_assoc_def, clause_name_def] THEN
Cases_on `h` THEN SRW_TAC [] [list_assoc_def]);

val recfun_def = Define
`recfun (LRBs_inj letrec_bindings) pattern_matching =
  (substs_value_name_expr
    (MAP (\letrec_binding. case letrec_binding of
                             LRB_simple x pattern_matching ->
                               (x , Expr_letrec (LRBs_inj letrec_bindings)
                                                (Expr_ident x)))
         letrec_bindings)
    (Expr_function pattern_matching))`;

val recfun_thm = Q.prove (
`!letrec_bindings pattern_matching expr. Jrecfun letrec_bindings pattern_matching expr =
                                         (recfun letrec_bindings pattern_matching = expr)`,
Cases THEN SRW_TAC [] [Jrecfun_cases, recfun_def, clause_name_def] THEN EQ_TAC THEN SRW_TAC [] [] THENL
[SRW_TAC [] [MAP_MAP, 
                 Q.prove (`!x. (case (\(a, b). LRB_simple a b) x of LRB_simple a b -> P a b) =
                               (case x of (a, b) -> P a b)`, 
                          Cases THEN SRW_TAC [] []),
                 LAMBDA_PROD],
 Q.EXISTS_TAC `MAP (\x. case x of LRB_simple a b -> (a, b)) l'` THEN
   SRW_TAC [] [MAP_MAP, 
                   Q.prove (`!x f. ((\(x_ ,pattern_matching_). f x_)
                                    case x of LRB_simple a b -> (a,b)) = 
                                   case x of LRB_simple a b -> f a`,
                            Cases THEN SRW_TAC [] [])] THEN
   Induct_on `l'` THEN SRW_TAC [] [] THENL [Cases_on `h` THEN SRW_TAC [] [], METIS_TAC []]]);

val funval_def = Define
`(funval (Expr_uprim unary_prim) = T) /\
 (funval (Expr_bprim binary_prim) = T) /\
 (funval (Expr_apply (Expr_bprim binary_prim) v) = is_value_of_expr v) /\
 (funval (Expr_function pattern_matching) = T) /\
 (funval _ = F)`;

val funval_thm = Q.prove (
`!v. Jfunval v = funval v`,
Cases THEN SRW_TAC [] [funval_def, Jfunval_cases, clause_name_def] THEN
Cases_on `e'` THEN SRW_TAC [] [funval_def, Jfunval_cases]);

val tp_to_tv_def = Define
`tp_to_tv (TP_var tv) = tv`;

val tp_to_tv_thm = Q.store_thm ("tp_to_tv_thm",
`TP_var (tp_to_tv v) = v`,
Cases_on `v` THEN SRW_TAC [] [tp_to_tv_def]);

val lrbs_to_lrblist_def = Define
`lrbs_to_lrblist (LRBs_inj x) = x`;

val lrbs_to_lrblist_thm = Q.store_thm ("lrbs_to_lrblist_thm",
`!x. LRBs_inj (lrbs_to_lrblist x) = x`,
Cases THEN SRW_TAC [] [lrbs_to_lrblist_def]);

val patexp_to_pelist_def = Define
`patexp_to_pelist (PE_inj x y) = (x, y)`;

val patexp_to_pelist_thm = Q.store_thm ("patexp_to_pelist_thm",
`!x. PE_inj (FST (patexp_to_pelist x)) (SND (patexp_to_pelist x)) = x`,
Cases THEN SRW_TAC [] [patexp_to_pelist_def]);

val tpo_to_tps_def = Define
`tpo_to_tps (TPS_nary tps) = tps`;

val tpo_to_tps_thm = Q.store_thm ("tpo_to_tps_thm",
`!tpo. TPS_nary (tpo_to_tps tpo) = tpo`,
Cases THEN SRW_TAC [] [tpo_to_tps_def]);

val field_to_fn_def = Define
`field_to_fn (F_name f) = f`;

val field_to_fn_thm = Q.store_thm ("field_to_fn_thm",
`!f. F_name (field_to_fn f) = f`,
Cases THEN SRW_TAC [] [field_to_fn_def]);

val t_size_def = Define
`(t_size (TE_var v) = 2:num) /\
 (t_size (TE_idxvar a b) = 1) /\
 (t_size TE_any = 1) /\
 (t_size (TE_arrow t1 t2) = 1 + t_size t1 + t_size t2) /\
 (t_size (TE_tuple tlist) = 1 + t1_size tlist) /\
 (t_size (TE_constr tlist tc) = 1 + t1_size tlist) /\
 (t1_size [] = 1) /\
 (t1_size (t1::tlist) = t_size t1 + t1_size tlist)`;

val ts_size_def = Define
`(ts_size (TS_forall t) = 1 + (t_size t))`;

val EB_size_def = Define
`(EB_size EB_tv = 1) /\
 (EB_size (EB_vn x ts) = 2 + ts_size ts) /\
 (EB_size (EB_cc cn tc) = 3) /\
 (EB_size (EB_pc cn (TPS_nary tplist) (typexprs_inj tlist) tc) = 4 + LENGTH tplist + t1_size tlist) /\
 (EB_size (EB_fn fn (TPS_nary tplist) tcn t) = 4 + LENGTH tplist + t_size t) /\
 (EB_size (EB_td tcn k) = 3) /\
 (EB_size (EB_tr tcn k fnlist) = 4 + LENGTH fnlist) /\
 (EB_size (EB_ta (TPS_nary tplist) tcn t) = 2 + LENGTH tplist + t_size t) /\
 (EB_size (EB_l l t) = 2 + t_size t)`;

val E_size_def = Define
`(E_size [] = 0) /\
 (E_size (EB::E) = EB_size EB + E_size E)`;

local
  val lem1 = Q.prove (
  `!t. 0 < t1_size t`,
  Induct THEN SRW_TAC [ARITH_ss] [t_size_def]);

  val lem2 = Q.prove (
  `!t l. MEM t l ==> t_size t < t1_size l`,
  Induct_on `l` THEN SRW_TAC [] [t_size_def] THEN RES_TAC THEN ASSUME_TAC (Q.SPEC `l` lem1) THEN
  DECIDE_TAC);

  val lem3 = Q.prove (
  `!t. 0 < t_size t`,
  Induct THEN SRW_TAC [ARITH_ss] [t_size_def]);
in

val Eok_def = tDefine "Eok"
`(Eok [] = T) /\
 (Eok (EB_tv::E) = Eok E) /\
 (Eok (EB_vn value_name ts::E) = tsok E ts) /\
 (Eok (EB_cc constr_name TC_exn::E) =
    Eok E /\ ~MEM (name_cn constr_name) (MAP domEB E)) /\
 (Eok (EB_cc constr_name (TC_name typeconstr_name)::E) =
    Eok E /\ (?kind. lookup E (name_tcn typeconstr_name) = SOME (EB_td typeconstr_name kind)) /\
    ~MEM (name_cn constr_name) (MAP domEB E)) /\
 (Eok (EB_cc constr_name tc::E) = F) /\
 (Eok (EB_pc constr_name (TPS_nary []) (typexprs_inj t_list) TC_exn::E) =
    EVERY (tkind E) t_list /\
    ~MEM (name_cn constr_name) (MAP domEB E) /\
    LENGTH t_list >= 1) /\
 (Eok (EB_pc constr_name (TPS_nary vars) (typexprs_inj t_list) (TC_name typeconstr_name)::E) =
    EVERY (\t. ntsok E vars t) t_list /\
    (lookup E (name_tcn typeconstr_name) = SOME (EB_td typeconstr_name (LENGTH vars))) /\
    ~MEM (name_cn constr_name) (MAP domEB E) /\
    LENGTH t_list >= 1) /\
 (Eok (EB_pc constr_name params (typexprs_inj t_list) tc::E) = F) /\
 (Eok (EB_fn field_name (TPS_nary vars) typeconstr_name t::E) =
    ntsok E vars t /\
    ~MEM (name_fn field_name) (MAP domEB E) /\
    ?field_name_list. (lookup E (name_tcn typeconstr_name) =
                       SOME (EB_tr typeconstr_name (LENGTH vars) field_name_list)) /\
                      MEM field_name field_name_list) /\
 (Eok (EB_td typeconstr_name kind::E) = 
    Eok E /\ 
    ~MEM (name_tcn typeconstr_name) (MAP domEB E)) /\
 (Eok (EB_ta (TPS_nary vars) typeconstr_name t::E) =
    ~MEM (name_tcn typeconstr_name) (MAP domEB E) /\ ntsok E vars t) /\
 (Eok (EB_tr typeconstr_name kind field_name_list::E) =
    Eok E /\
    ~MEM (name_tcn typeconstr_name) (MAP domEB E) /\
    ALL_DISTINCT (MAP name_fn field_name_list)) /\ 
 (Eok (EB_l location t::E) = 
    tkind E t /\
    ~MEM (name_l location) (MAP domEB E)) /\

 (typeconstr_kind E (TC_name typeconstr_name) = 
   if Eok E then
     case lookup E (name_tcn typeconstr_name) of
        NONE -> NONE
     || SOME (EB_td tcn kind) -> SOME kind
     || SOME (EB_ta (TPS_nary type_params_opt) tcn t) -> 
          if ALL_DISTINCT type_params_opt then
            SOME (LENGTH type_params_opt)
          else
            NONE
     || SOME (EB_tr tcn kind field_name_list) ->
          SOME kind
   else
     NONE) /\
 (typeconstr_kind E TC_int = if Eok E then SOME 0 else NONE) /\
 (typeconstr_kind E TC_char = if Eok E then SOME 0 else NONE) /\
 (typeconstr_kind E TC_string = if Eok E then SOME 0 else NONE) /\
 (typeconstr_kind E TC_float = if Eok E then SOME 0 else NONE) /\
 (typeconstr_kind E TC_bool = if Eok E then SOME 0 else NONE) /\
 (typeconstr_kind E TC_unit = if Eok E then SOME 0 else NONE) /\
 (typeconstr_kind E TC_exn = if Eok E then SOME 0 else NONE) /\
 (typeconstr_kind E TC_list = if Eok E then SOME 1 else NONE) /\
 (typeconstr_kind E TC_option = if Eok E then SOME 1 else NONE) /\
 (typeconstr_kind E TC_ref = if Eok E then SOME 1 else NONE) /\

 (tsok E (TS_forall t) = tkind (EB_tv::E) t) /\

 (ntsok E vars t =
   ALL_DISTINCT vars /\
   tkind E (substs_typevar_typexpr (MAP (\tp. (tp_to_tv tp, TE_constr [] TC_unit)) vars) t)) /\

 (tkind E (TE_var typevar) = F) /\
 (tkind E (TE_idxvar idx n) = 
    Eok E /\ idx_bound E idx) /\
 (tkind E TE_any = F) /\
 (tkind E (TE_arrow t1 t2) = 
   tkind E t1 /\ tkind E t2) /\
 (tkind E (TE_tuple t_list) = 
   EVERY (tkind E) t_list /\ LENGTH t_list >= 2) /\
 (tkind E (TE_constr t_list typeconstr) =
   (typeconstr_kind E typeconstr = SOME (LENGTH t_list)) /\ EVERY (tkind E) t_list)`
(WF_REL_TAC `inv_image ($< LEX $<) 
                       (\a. (sum_size (E_size) 
                             (sum_size (\(x,y). E_size x) 
                              (sum_size (\(x,y). E_size x + ts_size y)
                               (sum_size (\(x,y,z). E_size x + t_size z)
                                (\(x,y). E_size x))))) a,
                            (sum_size (\x. 0)
                             (sum_size (\(x,y). 1)
                              (sum_size (\x. 0)
                               (sum_size (\(x,y,z). 0)
                                (\(x,y). t_size y))))) a)` THEN
 SRW_TAC [ARITH_ss] [LENGTH_REVERSE, E_size_def, EB_size_def, t_size_def, ts_size_def, lem1, lem3] THEN
 IMP_RES_TAC lem2 THEN SRW_TAC [ARITH_ss] [EB_size_def, ts_size_def]);

val Eok_ind = fetch "-" "Eok_ind";

end;

val lookup_name_thm = Q.store_thm ("lookup_name_thm",
`!E.
(!tv EB. (lookup E name_tv = SOME EB) ==> (EB = EB_tv)) /\
(!vn EB. (lookup E (name_vn vn) = SOME EB) ==> ?ts. EB = EB_vn vn ts) /\
(!cn EB. (lookup E (name_cn cn) = SOME EB) ==> (?typeconstr. EB = EB_cc cn typeconstr) \/
                                               ?typ tlist typeconstr. EB = EB_pc cn typ tlist typeconstr) /\
(!tcn EB. (lookup E (name_tcn tcn) = SOME EB) ==> (?kind. EB = EB_td tcn kind) \/
                                                  (?tpo t. EB = EB_ta tpo tcn t) \/
                                                  ?k fnl. EB = EB_tr tcn k fnl) /\
(!fn EB. (lookup E (name_fn fn) = SOME EB) ==> ?tpo tcn t. EB = EB_fn fn tpo tcn t) /\
(!l EB. (lookup E (name_l l) = SOME EB) ==> ?t. EB = EB_l l t)`,
Induct THEN SRW_TAC [] [lookup_def, domEB_def, shiftEB_add_thm] THEN RES_TAC THEN SRW_TAC [] [shiftEB_def] THEN
Cases_on `EB` THEN 
FULL_SIMP_TAC list_ss [domEB_def, name_11, name_distinct] THEN METIS_TAC []);


local
val SIMP = SIMP_RULE bool_ss [clause_name_def, EVERY_MAP, EVERY_CONJ, ETA_THM, LAMBDA_PROD2, lookup_thm, 
                              domE_thm, idx_bound_thm];
val JTEok_rules2 = SIMP JTEok_rules;
val JTEok_cases2 = SIMP JTEok_cases;

in
val Eok_thm = Q.prove (
`(!E. JTEok E = Eok E) /\
 (!E tc k. JTtypeconstr E tc k = (typeconstr_kind E tc = SOME k)) /\
 (!E ts k. JTts E ts k = tsok E ts /\ (k = 0)) /\
 (!E tps t k. JTtsnamed E (TPS_nary tps) t k = ntsok E tps t /\ (k = 0)) /\
 (!E t k. JTt E t k = tkind E t /\ (k = 0))`,
HO_MATCH_MP_TAC Eok_ind THEN
 SRW_TAC [ARITH_ss] [Eok_def, domE_thm, lookup_thm, JTEok_rules2] THEN
   ONCE_REWRITE_TAC [JTEok_cases2] THEN SRW_TAC [ARITH_ss] [EVERY_MEM]
THENL
[
 EQ_TAC THEN SRW_TAC [] [] THEN1 METIS_TAC [] THEN
    Cases_on `ts` THEN SRW_TAC [] [] THEN Cases_on `t` THEN SRW_TAC [] [], 
 METIS_TAC [],
 EQ_TAC THEN SRW_TAC [] [] THEN 
   FULL_SIMP_TAC list_ss [MAP_MAP, MAP_REVERSE] THENL
   [Cases_on `tv_list` THEN 
          FULL_SIMP_TAC list_ss [MAP_MAP, MAP_REVERSE] THEN METIS_TAC [],
    METIS_TAC [],
    METIS_TAC [],
    Cases_on `tv_list` THEN FULL_SIMP_TAC list_ss [],
    Q.EXISTS_TAC `MAP tp_to_tv (v30::v31)` THEN 
            SRW_TAC [] [MAP_MAP, MAP_REVERSE, tp_to_tv_thm, MAP_I] THEN METIS_TAC []],
 EQ_TAC THEN SRW_TAC [] [] THEN 
    FULL_SIMP_TAC list_ss [MAP_MAP, MAP_REVERSE] THEN
    SRW_TAC [] [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN
    Q.EXISTS_TAC `MAP tp_to_tv tps` THEN
    SRW_TAC [] [MAP_MAP, MAP_I, tp_to_tv_thm],
 EQ_TAC THEN SRW_TAC [] [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN
    Q.EXISTS_TAC `MAP tp_to_tv tps` THEN
    SRW_TAC [] [MAP_MAP, MAP_I, tp_to_tv_thm],
 Cases_on `lookup E (name_tcn typeconstr_name)` THEN SRW_TAC [] [] 
    THEN IMP_RES_TAC lookup_name_thm THEN SRW_TAC [] [] THEN 
    FULL_SIMP_TAC list_ss [name_11, name_distinct] THEN
    Cases_on `tpo` THEN SRW_TAC [ARITH_ss] [clause_name_def, JTtps_kind_cases],
 EQ_TAC THEN SRW_TAC [] [],
 EQ_TAC THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [MAP_MAP, tp_to_tv_def] THEN1 METIS_TAC [] THEN
     Q.EXISTS_TAC `MAP tp_to_tv tps` THEN SRW_TAC [] [tp_to_tv_def, MAP_MAP, tp_to_tv_thm, MAP_I],
 EQ_TAC THEN SRW_TAC [] [] THEN SRW_TAC [] [] THEN Cases_on `idx_bound E idx` THEN FULL_SIMP_TAC list_ss [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC []]);
end;

val idxsub_def = ottDefine "idxsub"
`(idxsub tl (TE_var v) = TE_var v) /\
 (idxsub tl (TE_idxvar 0 n) = if n < LENGTH tl then EL n tl else TE_constr [] TC_unit) /\
 (idxsub tl (TE_idxvar (SUC n) n') = TE_idxvar n n') /\
 (idxsub tl TE_any = TE_any) /\
 (idxsub tl (TE_arrow t1 t2) = TE_arrow (idxsub tl t1) (idxsub tl t2)) /\
 (idxsub tl (TE_tuple tl') = TE_tuple (MAP (idxsub tl) tl')) /\
 (idxsub tl (TE_constr tl' tcn) = TE_constr (MAP (idxsub tl) tl') tcn)`;

val idxsubn0_thm = Q.store_thm ("idxsubn0_thm",
`(!t tl. idxsubn 0 tl t = idxsub tl t) /\
 (!tl' tl. MAP (idxsubn 0 tl) tl' = MAP (idxsub tl) tl')`,
Induct THEN SRW_TAC [] [idxsubn_def, idxsub_def, GSYM ETA_THM] THEN1
(Cases_on `n` THEN SRW_TAC [] [idxsub_def]) THEN METIS_TAC []);

local

val JTidxsub_fun = structural_cases [typexpr_11, typexpr_distinct]
                                   1
                                   [get_terms ftv_typexpr_def]
                                   JTidxsub_cases;
val lem1 = Q.prove (
`!tl t t'. JTidxsub tl t t' ==> (t' = idxsub tl t)`,
RULE_INDUCT_TAC JTidxsub_ind [idxsub_def, LAMBDA_PROD2, EVERY_MAP, MAP_MAP, GSYM arithmeticTheory.ADD1]
[([``"JTinxsub_idx0"``, ``"JTinxsub_idx1"``], 
  SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [EL_APPEND1, EL_APPEND2]),
 ([``"JTinxsub_tuple"``, ``"JTinxsub_tc"``],
  Induct THEN SRW_TAC [] [])]);

val lem2 = Q.prove (
`!tl t t'. (t' = idxsub tl t) ==> JTidxsub tl t t'`,
HO_MATCH_MP_TAC (fetch "-" "idxsub_ind") THEN 
SRW_TAC [] [JTidxsub_fun, idxsub_def, clause_name_def, EVERY_MAP, LAMBDA_PROD2] THENL
[DISJ1_TAC THEN MAP_EVERY Q.EXISTS_TAC [`LASTN (LENGTH tl - n - 1) tl`, `FIRSTN n tl`] THEN
          SRW_TAC [ARITH_ss] [LENGTH_FIRSTN] THEN METIS_TAC [FIRSTN_EL_LASTN],
 DISJ2_TAC THEN DECIDE_TAC,
 DECIDE_TAC,
 Q.EXISTS_TAC `MAP (\t. (t, idxsub tl t)) tl'` THEN SRW_TAC [] [MAP_MAP, MAP_I, EVERY_MAP, EVERY_MEM],
 Q.EXISTS_TAC `MAP (\t. (t, idxsub tl t)) tl'` THEN 
       SRW_TAC [] [MAP_MAP, MAP_I, EVERY_MAP, EVERY_MEM]]);

in

val idxsub_thm = Q.prove (
`!tl t t'. JTidxsub tl t t' = (t' = idxsub tl t)`,
METIS_TAC [lem1, lem2]);

end;



val SIMP1 = SIMP_RULE bool_ss [EVERY_MAP, EVERY_CONJ, ETA_THM, LAMBDA_PROD2, lookup_thm, Slookup_thm,
                               idx_bound_thm, domE_thm, recfun_thm, funval_thm, Eok_thm, idxsub_thm];
val SIMP2 = SIMP_RULE bool_ss [EVERY_MAP, EVERY_CONJ, ETA_THM, LAMBDA_PROD2, lookup_thm, Slookup_thm,
                               idx_bound_thm, domE_thm, recfun_thm, funval_thm, Eok_thm, clause_name_def,
                               idxsub_thm];

val JM_matchP_cases = save_thm ("JM_matchP_cases", SIMP2 JM_matchP_cases);
val _ = save_thm ("JM_matchP_sind", SIMP1 (derive_strong_induction (JM_matchP_rules, JM_matchP_ind)));
val _ = save_thm ("JM_matchP_ind", SIMP1 JM_matchP_ind);
val _ = save_thm ("JM_matchP_rules", SIMP2 JM_matchP_rules);

val JM_match_cases = save_thm ("JM_match_cases", SIMP2 JM_match_cases);
val _ = save_thm ("JM_match_sind", SIMP1 (derive_strong_induction (JM_match_rules, JM_match_ind)));
val _ = save_thm ("JM_match_ind", SIMP1 JM_match_ind);
val _ = save_thm ("JM_match_rules", SIMP2 JM_match_rules);

val JRB_dbehaviour_cases = save_thm ("JRB_dbehaviour_cases", SIMP2 JRB_dbehaviour_cases);
val _ = save_thm ("JRB_dbehaviour_ind", SIMP1 JRB_dbehaviour_ind);
val _ = save_thm ("JRB_dbehaviour_rules", SIMP2 JRB_dbehaviour_rules);

val JRB_ebehaviour_cases = save_thm ("JRB_ebehaviour_cases", SIMP2 JRB_ebehaviour_cases);
val _ = save_thm ("JRB_ebehaviour_ind", SIMP1 JRB_ebehaviour_ind);
val _ = save_thm ("JRB_ebehaviour_rules", SIMP2 JRB_ebehaviour_rules);

val JR_expr_cases = save_thm ("JR_expr_cases", SIMP2 JR_expr_cases);
val _ = save_thm ("JR_expr_sind", SIMP1 (derive_strong_induction (JR_expr_rules, JR_expr_ind)));
val _ = save_thm ("JR_expr_ind", SIMP1 JR_expr_ind);
val _ = save_thm ("JR_expr_rules", SIMP2 JR_expr_rules);

val JRbprim_cases = save_thm ("JRbprim_cases", SIMP2 JRbprim_cases);
val _ = save_thm ("JRbprim_ind", SIMP1 JRbprim_ind);
val _ = save_thm ("JRbprim_rules", SIMP2 JRbprim_rules);

val JRdefn_cases = save_thm ("JRdefn_cases", SIMP2 JRdefn_cases);
val _ = save_thm ("JRdefn_sind", SIMP1 (derive_strong_induction (JRdefn_rules, JRdefn_ind)));
val _ = save_thm ("JRdefn_ind",	 SIMP1 JRdefn_ind);
val _ = save_thm ("JRdefn_rules", SIMP2 JRdefn_rules);

val JRmatching_step_cases = save_thm ("JRmatching_step_cases", SIMP2 JRmatching_step_cases);
val _ = save_thm ("JRmatching_step_ind", SIMP1 JRmatching_step_ind);
val _ = save_thm ("JRmatching_step_rules", SIMP2 JRmatching_step_rules);

val JRmatching_success_cases = save_thm ("JRmatching_success_cases", SIMP2 JRmatching_success_cases);
val _ = save_thm ("JRmatching_success_ind", SIMP1 JRmatching_success_ind);
val _ = save_thm ("JRmatching_success_rules", SIMP2 JRmatching_success_rules);

val JRstore_cases = save_thm ("JRstore_cases", SIMP2 JRstore_cases);
val _ = save_thm ("JRstore_ind", SIMP1 JRstore_ind);
val _ = save_thm ("JRstore_rules", SIMP2 JRstore_rules);

val JRtop_cases = save_thm ("JRtop_cases", SIMP2 JRtop_cases);
val _ = save_thm ("JRtop_ind",	 SIMP1 JRtop_ind);
val _ = save_thm ("JRtop_rules", SIMP2 JRtop_rules);

val JRuprim_cases = save_thm ("JRuprim_cases", SIMP2 JRuprim_cases);
val _ = save_thm ("JRuprim_ind", SIMP1 JRuprim_ind);
val _ = save_thm ("JRuprim_rules", SIMP2 JRuprim_rules);

val JTbprim_cases = save_thm ("JTbprim_cases", SIMP2 JTbprim_cases);
val _ = save_thm ("JTbprim_ind", SIMP1 JTbprim_ind);
val _ = save_thm ("JTbprim_rules", SIMP2 JTbprim_rules);

val JTconst_cases = save_thm ("JTconst_cases", SIMP2 JTconst_cases);
val _ = save_thm ("JTconst_ind", SIMP1 JTconst_ind);
val _ = save_thm ("JTconst_rules", SIMP2 JTconst_rules);

val JTconstr_c_cases = save_thm ("JTconstr_c_cases", SIMP2 JTconstr_c_cases);
val _ = save_thm ("JTconstr_c_ind", SIMP1 JTconstr_c_ind);
val _ = save_thm ("JTconstr_c_rules", SIMP2 JTconstr_c_rules);

val JTconstr_decl_cases = save_thm ("JTconstr_decl_cases", SIMP2 JTconstr_decl_cases);
val _ = save_thm ("JTconstr_decl_ind", SIMP1 JTconstr_decl_ind);
val _ = save_thm ("JTconstr_decl_rules", SIMP2 JTconstr_decl_rules);

val JTconstr_p_cases = save_thm ("JTconstr_p_cases", SIMP2 JTconstr_p_cases);
val _ = save_thm ("JTconstr_p_ind", SIMP1 JTconstr_p_ind);
val _ = save_thm ("JTconstr_p_rules", SIMP2 JTconstr_p_rules);

val JTdefinition_cases = save_thm ("JTdefinition_cases", SIMP2 JTdefinition_cases);
val _ = save_thm ("JTdefinition_ind", SIMP1 JTdefinition_ind);
val _ = save_thm ("JTdefinition_rules", SIMP2 JTdefinition_rules);

val JTdefinitions_cases = save_thm ("JTdefinitions_cases", SIMP2 JTdefinitions_cases);
val _ = save_thm ("JTdefinitions_sind",
                  SIMP1 (derive_strong_induction (JTdefinitions_rules, JTdefinitions_ind)));
val _ = save_thm ("JTdefinitions_ind", SIMP1 JTdefinitions_ind);
val _ = save_thm ("JTdefinitions_rules", SIMP2 JTdefinitions_rules);

val JTe_cases = save_thm ("JTe_cases", SIMP2 JTe_cases);
val _ = save_thm ("JTe_sind", SIMP1 (derive_strong_induction (JTe_rules, JTe_ind)));
val _ = save_thm ("JTe_ind", SIMP1 JTe_ind);
val _ = save_thm ("JTe_rules", SIMP2 JTe_rules);

val JTeq_cases = save_thm ("JTeq_cases", SIMP2 JTeq_cases);
val _ = save_thm ("JTeq_ind", SIMP1 JTeq_ind);
val _ = save_thm ("JTeq_rules", SIMP2 JTeq_rules);

val JTfield_decl_cases = save_thm ("JTfield_decl_cases", SIMP2 JTfield_decl_cases);
val _ = save_thm ("JTfield_decl_ind", SIMP1 JTfield_decl_ind);
val _ = save_thm ("JTfield_decl_rules", SIMP2 JTfield_decl_rules);

val JTfield_cases = save_thm ("JTfield_cases", SIMP2 JTfield_cases);
val _ = save_thm ("JTfield_ind", SIMP1 JTfield_ind);
val _ = save_thm ("JTfield_rules", SIMP2 JTfield_rules);

val JTinst_cases = save_thm ("JTinst_cases", SIMP2 JTinst_cases);
val _ = save_thm ("JTinst_ind", SIMP1 JTinst_ind);
val _ = save_thm ("JTinst_rules", SIMP2 JTinst_rules);

val JTinst_named_cases = save_thm ("JTinst_named_cases", SIMP2 JTinst_named_cases);
val _ = save_thm ("JTinst_named_ind", SIMP1 JTinst_named_ind);
val _ = save_thm ("JTinst_named_rules", SIMP2 JTinst_named_rules);

val JTinst_any_cases = save_thm ("JTinst_any_cases", SIMP2 JTinst_any_cases);
val _ = save_thm ("JTinst_any_ind", SIMP1 JTinst_any_ind);
val _ = save_thm ("JTinst_any_rules", SIMP2 JTinst_any_rules);

val JTLin_cases = save_thm ("JTLin_cases", SIMP2 JTLin_cases);
val _ = save_thm ("JTLin_ind", SIMP1 JTLin_ind);
val _ = save_thm ("JTLin_rules", SIMP2 JTLin_rules);

val JTLout_cases = save_thm ("JTLout_cases", SIMP2 JTLout_cases);
val _ = save_thm ("JTLout_ind", SIMP1 JTLout_ind);
val _ = save_thm ("JTLout_rules", SIMP2 JTLout_rules);

val JTpat_cases = save_thm ("JTpat_cases", SIMP2 JTpat_cases);
val _ = save_thm ("JTpat_sind", SIMP1 (derive_strong_induction (JTpat_rules, JTpat_ind)));
val _ = save_thm ("JTpat_ind", SIMP1 JTpat_ind);
val _ = save_thm ("JTpat_rules", SIMP2 JTpat_rules);

val JTstore_cases = save_thm ("JTstore_cases", SIMP2 JTstore_cases);
val _ = save_thm ("JTstore_sind", SIMP1 (derive_strong_induction (JTstore_rules, JTstore_ind)));
val _ = save_thm ("JTstore_ind", SIMP1 JTstore_ind);
val _ = save_thm ("JTstore_rules", SIMP2 JTstore_rules);

val JTtype_definition_cases = save_thm ("JTtype_definition_cases", SIMP2 JTtype_definition_cases);
val _ = save_thm ("JTtype_definition_ind", SIMP1 JTtype_definition_ind);
val _ = save_thm ("JTtype_definition_rules", SIMP2 JTtype_definition_rules);

val JTtypedef_cases = save_thm ("JTtypedef_cases", SIMP2 JTtypedef_cases);
val _ = save_thm ("JTtypedef_ind", SIMP1 JTtypedef_ind);
val _ = save_thm ("JTtypedef_rules", SIMP2 JTtypedef_rules);

val JTuprim_cases = save_thm ("JTuprim_cases", SIMP2 JTuprim_cases);
val _ = save_thm ("JTuprim_ind", SIMP1 JTuprim_ind);
val _ = save_thm ("JTuprim_rules", SIMP2 JTuprim_rules);

val JTvalue_name_cases = save_thm ("JTvalue_name_cases", SIMP2 JTvalue_name_cases);
val _ = save_thm ("JTvalue_name_ind", SIMP1 JTvalue_name_ind);
val _ = save_thm ("JTvalue_name_rules", SIMP2 JTvalue_name_rules);

val JTtop_cases = save_thm ("JTtop_cases", SIMP2 JTtop_cases);
val _ = save_thm ("JTtop_ind", SIMP1 JTtop_ind);
val _ = save_thm ("JTtop_rules", SIMP2 JTtop_rules);

val JTprog_cases = save_thm ("JTprog_cases", SIMP2 JTprog_cases);
val _ = save_thm ("JTprog_ind", SIMP1 JTprog_ind);
val _ = save_thm ("JTprog_rules", SIMP2 JTprog_rules);

val is_binary_prim_app_value_of_expr_thm = Q.prove (
`!e. is_binary_prim_app_value_of_expr e = (?bp. e = Expr_bprim bp)`,
Cases THEN SRW_TAC [] [is_binary_prim_app_value_of_expr_def]);

val _ = save_thm ("is_value_of_expr_def", 
                  PURE_REWRITE_RULE [is_binary_prim_app_value_of_expr_thm] is_value_of_expr_def);

val expr_terms = get_terms is_value_of_expr_def;
val pattern_matching_terms = [``PM_pm pat_exp_list``];
val let_binding_terms = [``LB_simple pattern expr``];
val letrec_binding_terms = [``LRBs_inj letrec_binding_list``];
val _ = save_thm ("JTe_fun",
                  structural_cases [expr_11, expr_distinct, pattern_matching_11,
                                    let_binding_11, letrec_bindings_11]
                               2
                               [expr_terms, pattern_matching_terms, let_binding_terms, letrec_binding_terms]
                               JTe_cases);

val _ = save_thm ("JR_expr_fun",
                  structural_cases [expr_11, expr_distinct]
                               0
                               [expr_terms]
                               JR_expr_cases);

val _ = save_thm ("JTpat_fun",
                  structural_cases [pattern_11, pattern_distinct]
                               2
                               [get_terms ftv_pattern_def]
                               JTpat_cases);

val _ = save_thm ("JTconst_fun",
                  structural_cases [constant_11, constant_distinct]
                               1
                               [[``CONST_int n``, ``CONST_float f``, ``CONST_char c``, ``CONST_string s``,
                                 ``CONST_constr constr``, ``CONST_true``, ``CONST_false``, ``CONST_unit``,
                                 ``CONST_nil``]]
                               JTconst_cases);

val JM_matchP_fun = save_thm ("JM_matchP_fun",
                  structural_cases [pattern_11, pattern_distinct] 
                                   1
                                   [get_terms ftv_pattern_def]
                                   JM_matchP_cases);

val JM_match_fun = save_thm ("JM_match_fun",
                  structural_cases [pattern_11, pattern_distinct] 
                                   1
                                   [get_terms ftv_pattern_def]
                                   JM_match_cases);

val JTdefinition_fun = save_thm ("JTdefinition_fun",
                  structural_cases [definition_11, definition_distinct]
                               1
                               [[``D_let lb``,
                                 ``D_letrec lrbs``,
                                 ``D_type td``,
                                 ``D_exception ed``]]
                               JTdefinition_cases);

val JTdefinitions_fun = save_thm ("JTdefinitions_fun",
       structural_cases [definitions_11, definitions_distinct]
                        1 [[``Ds_nil``, ``Ds_cons d ds``]]
                        JTdefinitions_cases);

val JTprog_fun = save_thm ("JTprog_fun",
       structural_cases [program_11, program_distinct]
                        1 [[``Prog_defs ds``,
                            ``Prog_raise v``]]
                        JTprog_cases);

val JRdefn_fun = save_thm ("JRdefn_fun",
                  structural_cases [definitions_11, definitions_distinct, definition_11, definition_distinct,
                                    program_11, program_distinct]
                               1
                               [[``Prog_defs Ds_nil``,
                                 ``Prog_defs (Ds_cons (D_let lb) ds)``,
                                 ``Prog_defs (Ds_cons (D_letrec lrbs) ds)``,
                                 ``Prog_defs (Ds_cons (D_type td) ds)``,
                                 ``Prog_defs (Ds_cons (D_exception ed) ds)``,
                                 ``Prog_raise v``]]
                               JRdefn_cases);

val JTstore_fun = save_thm ("JTstore_fun", SIMP_RULE list_ss []
                  (structural_cases [list_11, list_distinct]
                               1
                               [[``[]:store``,
                                 ``(l, v)::(store:store)``]]
                               JTstore_cases));

val JTinst_any_fun = save_thm ("JTinst_any_fun",
                     structural_cases [typexpr_11, typexpr_distinct]
                                      2
                                      [get_terms ftv_typexpr_def]
                                      JTinst_any_cases);


val JTeq_fun = save_thm ("JTeq_fun",
                     structural_cases [typexpr_11, typexpr_distinct]
                                      1
                                      [get_terms ftv_typexpr_def]
                                      JTeq_cases);

(* This otherwise useless definition is accompanied by a nice induction principle. *)
val Eok2_def = Define
`(Eok2 [] = T) /\
 (Eok2 (EB_tv::E) = Eok2 E) /\
 (Eok2 (EB_vn value_name (TS_forall t)::E) = Eok2 E) /\
 (Eok2 (EB_cc constr_name TC_exn::E) = Eok2 E) /\
 (Eok2 (EB_cc constr_name (TC_name typeconstr_name)::E) = Eok2 E) /\ 
 (Eok2 (EB_cc constr_name tc::E) = F) /\
 (Eok2 (EB_pc constr_name (TPS_nary []) (typexprs_inj t_list) TC_exn::E) = Eok2 E) /\
 (Eok2 (EB_pc constr_name (TPS_nary vars) (typexprs_inj t_list) (TC_name typeconstr_name)::E) = Eok2 E) /\
 (Eok2 (EB_pc constr_name params (typexprs_inj t_list) tc::E) = F) /\
 (Eok2 (EB_fn field_name (TPS_nary vars) typeconstr_name t::E) = Eok2 E) /\
 (Eok2 (EB_td typeconstr_name kind::E) = Eok2 E) /\ 
 (Eok2 (EB_ta tps typeconstr_name t::E) = Eok2 E) /\
 (Eok2 (EB_tr typeconstr_name kind field_name_list::E) = Eok2 E) /\
 (Eok2 (EB_l location t::E) = Eok2 E)`;

val is_abbrev_tc_def = Define `
(is_abbrev_tc E (TE_constr _ (TC_name tcn)) =
  case lookup E (name_tcn tcn) of
     SOME (EB_ta x y z) -> T
  || _ -> F) /\
(is_abbrev_tc E _ = F)`;

val is_abbrev_tc_cases = Q.store_thm ("is_abbrev_tc_cases",
`!E t. is_abbrev_tc E t = ?ts tcn tps t'. (t = TE_constr ts (TC_name tcn)) /\
                                          (lookup E (name_tcn tcn) = SOME (EB_ta (TPS_nary tps) tcn t'))`,
Cases_on `t` THEN SRW_TAC [] [is_abbrev_tc_def] THEN
Cases_on `t'` THEN SRW_TAC [] [is_abbrev_tc_def] THEN
Cases_on `lookup E (name_tcn t'')` THEN SRW_TAC [] [is_abbrev_tc_def] THEN
Cases_on `x` THEN SRW_TAC [] [is_abbrev_tc_def] THEN
IMP_RES_TAC lookup_name_thm THEN
FULL_SIMP_TAC list_ss [environment_binding_11, environment_binding_distinct, type_params_opt_nchotomy]);

val is_record_tc_def = Define `
(is_record_tc E (TE_constr _ (TC_name tcn)) =
  case lookup E (name_tcn tcn) of
     SOME (EB_tr x y z) -> T
  || _ -> F) /\
(is_record_tc E _ = F)`;

val is_record_tc_cases = Q.store_thm ("is_record_tc_cases",
`!E t. is_record_tc E t = (?ts tcn k fns. (t = TE_constr ts (TC_name tcn)) /\
                                          (lookup E (name_tcn tcn) = SOME (EB_tr tcn k fns)))`,
Cases_on `t` THEN SRW_TAC [] [is_record_tc_def] THEN
Cases_on `t'` THEN SRW_TAC [] [is_record_tc_def] THEN
Cases_on `lookup E (name_tcn t'')` THEN SRW_TAC [] [is_record_tc_def] THEN
Cases_on `x` THEN SRW_TAC [] [is_abbrev_tc_def] THEN
IMP_RES_TAC lookup_name_thm THEN
FULL_SIMP_TAC list_ss [environment_binding_11, environment_binding_distinct]);

val is_constr_tc_def = Define `
(is_constr_tc E (TE_constr _ (TC_name tcn)) =
  case lookup E (name_tcn tcn) of
     SOME (EB_td x y) -> T
  || _ -> F) /\
(is_constr_tc E (TE_constr [] TC_exn) = T) /\
(is_constr_tc E (TE_constr [t] TC_option) = T) /\
(is_constr_tc E _ = F)`;

val is_constr_tc_cases = Q.store_thm ("is_constr_tc_cases",
`!E t. is_constr_tc E t = (?ts tcn k. (t = TE_constr ts (TC_name tcn)) /\
                                      (lookup E (name_tcn tcn) = SOME (EB_td tcn k))) \/
                          (?t'. t = TE_constr [t'] TC_option) \/
                          (t = TE_constr [] TC_exn)`,
Cases_on `t` THEN SRW_TAC [] [is_constr_tc_def] THEN
Cases_on `t'` THEN SRW_TAC [] [is_constr_tc_def] THEN
Cases_on `l` THEN SRW_TAC [] [is_constr_tc_def] THEN
TRY (Cases_on `lookup E (name_tcn t'')` THEN SRW_TAC [] [is_constr_tc_def]) THEN
TRY (Cases_on `t` THEN SRW_TAC [] [is_constr_tc_def]) THEN
TRY (Cases_on `t'` THEN SRW_TAC [] [is_constr_tc_def]) THEN
Cases_on `x` THEN SRW_TAC [] [is_abbrev_tc_def] THEN
IMP_RES_TAC lookup_name_thm THEN
FULL_SIMP_TAC list_ss [environment_binding_11, environment_binding_distinct]);

val JM_match_lem = Q.prove (
`!e p s. JM_match e p s ==> JM_matchP e p`,
RULE_INDUCT_TAC JM_match_ind [JM_matchP_fun, ELIM_UNCURRY, EVERY_MAP, EVERY_MEM]
[([``"JM_match_construct"``, ``"JM_match_tuple"``],
  SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\x. (FST x, FST (SND x))) v_pat_substs_x_list` THEN
        SRW_TAC [] [MAP_MAP, ETA_THM] THEN FULL_SIMP_TAC list_ss [MEM_MAP]),
 ([``"JM_match_record"``],
  SRW_TAC [] [] THEN
      MAP_EVERY Q.EXISTS_TAC [`fn_v''_list`,
                              `MAP (\(a, b, c, d). (a, b, d)) field_name'_pat_substs_x_v'_list`,
                              `field_name_v_list`] THEN
      SRW_TAC [] [LAMBDA_PROD2, MAP_MAP] THEN FULL_SIMP_TAC list_ss [MEM_MAP])]);

local

val lem1 = Q.prove (
`!l1 l2 P.
 (LENGTH l1 = LENGTH l2) /\
 EVERY (\x. P (FST x) (FST (SND x)) (substs_x_xs (SND (SND x)))) (ZIP (MAP FST l1,ZIP (MAP SND l1,l2))) ==>
 EVERY (\x. P (FST (FST x)) (SND (FST x)) (SND x)) (ZIP (l1,MAP substs_x_xs l2))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss []);

val lem2 = Q.prove (
`!l1 l2 f g. (LENGTH l1 = LENGTH l2) ==>
             (MAP (\x. (f (FST x),g (FST x))) (ZIP (l1,l2)) =
              MAP (\z. (f z, g z)) l1)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss []);

val lem3 = Q.prove (
`!l1 l2 P.
 (LENGTH l1 = LENGTH l2) /\
 EVERY (\x. P (SND (FST x)) (SND (FST (SND x))) (substs_x_xs (SND (SND x))))
       (ZIP (MAP (\z. (F_name (FST z),SND (SND z))) l1,
             ZIP (MAP (\z. (F_name (FST z),FST (SND z))) l1,l2))) ==>
 EVERY (\x. P (SND (SND (FST x))) (FST (SND (FST x))) (substs_x_xs (SND x))) (ZIP (l1,l2))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss []);

in

val JM_matchP_lem = Q.prove (
`(!p e. JM_matchP e p ==> ?s. JM_match e p (substs_x_xs s) /\ EVERY is_value_of_expr (MAP SND s)) /\
 (!plist elist. (LENGTH plist = LENGTH elist) /\ EVERY (UNCURRY JM_matchP) (ZIP (elist, plist)) ==>
                ?slist. (LENGTH plist = LENGTH slist) /\ EVERY is_value_of_expr (MAP SND (FLAT slist)) /\
                        EVERY (\(e, p, s). JM_match e p (substs_x_xs s))
                              (ZIP (elist, (ZIP (plist, slist))))) /\
 (!fplist felist. (LENGTH felist = LENGTH fplist) /\
                  EVERY (\((f:field,e),(f':field,p)). JM_matchP e p) (ZIP (felist, fplist)) ==>
                  ?slist. (LENGTH fplist = LENGTH slist) /\ EVERY is_value_of_expr (MAP SND (FLAT slist)) /\
                          EVERY (\((f,e), (f,p), s). JM_match e p (substs_x_xs s))
                                (ZIP (felist, (ZIP (fplist, slist))))) /\
 (!(fp:field#pattern) (fe:field#expr). JM_matchP (SND fe) (SND fp) ==>
          ?s. JM_match (SND fe) (SND fp) (substs_x_xs s) /\ EVERY is_value_of_expr (MAP SND s))`,
Induct THEN SRW_TAC [] [JM_match_fun, JM_matchP_fun, EVERY_MAP] THEN
FULL_SIMP_TAC list_ss [EVERY_MAP, ELIM_UNCURRY] THENL
[RES_TAC THEN Q.EXISTS_TAC `s++[(v,e)]` THEN SRW_TAC [] [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 Q.PAT_ASSUM `!elist. P elist ==> Q elist` (MP_TAC o Q.SPEC `MAP FST (v_pat_list:(expr#pattern) list)`) THEN
       SRW_TAC [] [ZIP_MAP_ID] THEN Q.EXISTS_TAC `FLAT slist` THEN SRW_TAC [] [] THEN
       Q.EXISTS_TAC `MAP (\((v, p), s). (v, p, s)) (ZIP (v_pat_list, MAP substs_x_xs slist))` THEN
       SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP] THEN
       SRW_TAC [] [GSYM MAP_MAP, MAP_FST_ZIP, MAP_SND_ZIP, GSYM EVERY_MAP] THEN
       SRW_TAC [] [MAP_MAP, MAP_I, EVERY_MAP, lem1],
  Q.PAT_ASSUM `!elist. P elist ==> Q elist` (MP_TAC o Q.SPEC `MAP FST (v_pat_list:(expr#pattern) list)`) THEN
       SRW_TAC [] [ZIP_MAP_ID] THEN Q.EXISTS_TAC `FLAT slist` THEN SRW_TAC [] [] THEN
       Q.EXISTS_TAC `MAP (\((v, p), s). (v, p, s)) (ZIP (v_pat_list, MAP substs_x_xs slist))` THEN
       SRW_TAC [] [MAP_MAP, LAMBDA_PROD2, EVERY_MAP] THEN
       SRW_TAC [] [GSYM MAP_MAP, MAP_FST_ZIP, MAP_SND_ZIP, GSYM EVERY_MAP] THEN
       SRW_TAC [] [MAP_MAP, MAP_I, EVERY_MAP, lem1],
 Q.PAT_ASSUM `!felist. P felist ==> Q felist`
             (MP_TAC o Q.SPEC `MAP (\(fn, p:pattern, v:expr). (F_name fn, v)) field_name'_pat_v'_list`) THEN
       SRW_TAC [] [MAP_MAP, MAP_ZIP_SAME, ZIP_MAP, EVERY_MAP, LAMBDA_PROD2] THEN
       Q.EXISTS_TAC `FLAT slist` THEN SRW_TAC [] [] THEN
       MAP_EVERY Q.EXISTS_TAC [`fn_v''_list`,
                               `MAP (\((f, p, v), s). (f, p, substs_x_xs s, v))
                                    (ZIP (field_name'_pat_v'_list, slist))`,
                               `field_name_v_list`] THEN
       SRW_TAC [] [ETA_THM, MAP_MAP, LAMBDA_PROD2, EVERY_MAP, MAP_SND_ZIP, lem2] THEN
       SRW_TAC [] [GSYM EVERY_MAP, GSYM MAP_MAP, MAP_FST_ZIP] THEN
       SRW_TAC [] [EVERY_MAP, lem3],
 RES_TAC THEN Q.EXISTS_TAC `s'++s` THEN SRW_TAC [] [] THEN
       MAP_EVERY Q.EXISTS_TAC [`substs_x_xs s'`, `substs_x_xs s`] THEN SRW_TAC [] [],
 Cases_on `elist` THEN FULL_SIMP_TAC list_ss [] THEN Q.EXISTS_TAC `[]` THEN SRW_TAC [] [],
 Cases_on `elist` THEN FULL_SIMP_TAC list_ss [] THEN
       Q.PAT_ASSUM `!elist. P elist ==> ?slist. (LENGTH elist = LENGTH slist) /\ Q elist slist`
               (MP_TAC o Q.SPEC `t`) THEN
       SRW_TAC [] [] THEN RES_TAC THEN Q.EXISTS_TAC `s::slist` THEN SRW_TAC [] [],
 Cases_on `felist` THEN FULL_SIMP_TAC list_ss [] THEN Q.EXISTS_TAC `[]` THEN SRW_TAC [] [],
 Cases_on `felist` THEN FULL_SIMP_TAC list_ss [] THEN
       Q.PAT_ASSUM `!felist'. P felist' ==> ?slist. (LENGTH fplist = LENGTH slist) /\ Q felist' slist`
               (MP_TAC o Q.SPEC `t`) THEN
       SRW_TAC [] [] THEN RES_TAC THEN Q.EXISTS_TAC `s::slist` THEN SRW_TAC [] []]);

end;

val JM_match_is_val_thm = Q.store_thm ("JM_match_is_val_thm",
`!e p s. JM_match e p s ==> !s'. (s = substs_x_xs s') ==> EVERY is_value_of_expr (MAP SND s')`,
RULE_INDUCT_TAC JM_match_ind [EVERY_MAP, ELIM_UNCURRY, MAP_MAP]
[([``"JM_match_tuple"``, ``"JM_match_construct"``],
  SRW_TAC [] [EVERY_MEM, MEM_FLAT, EXISTS_MAP, EXISTS_MEM] THEN
       Cases_on `x'` THEN FULL_SIMP_TAC list_ss [] THEN
       Cases_on `r` THEN FULL_SIMP_TAC list_ss [] THEN
       Cases_on `r'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [SND]),
 ([``"JM_match_record"``],
  SRW_TAC [] [EVERY_MEM, MEM_FLAT, EXISTS_MAP, EXISTS_MEM] THEN
       Cases_on `x'` THEN FULL_SIMP_TAC list_ss [] THEN
       Cases_on `r` THEN FULL_SIMP_TAC list_ss [] THEN
       Cases_on `r'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       Cases_on `q''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [FST, SND]),
 ([``"JM_match_cons"``],
  SRW_TAC [] [EVERY_MEM] THEN
       Cases_on `s` THEN Cases_on `s'` THEN FULL_SIMP_TAC (srw_ss()) [])]);

val JM_matchP_thm = Q.store_thm ("JM_matchP_thm",
`!p e. JM_matchP e p = ?s. JM_match e p (substs_x_xs s)`,
METIS_TAC [JM_matchP_lem, JM_match_lem, JM_match_is_val_thm]);


val _ = export_theory();
