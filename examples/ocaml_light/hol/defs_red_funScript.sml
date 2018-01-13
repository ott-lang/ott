open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory reduction_funTheory matching_funTheory;

val _ = new_theory "defs_red_fun";

val defns_red_def = Define
`(defns_red (defs, Prog_raise _) = Stuck) /\
 (defns_red (defs, Prog_defs Ds_nil) = Stuck) /\
 (defns_red (defs, Prog_defs (Ds_cons (D_let (LB_simple pat e)) defs')) =
   if is_definitions_value_of_definitions defs then
     if is_raise e then
       (case e of
           Expr_apply e1 v -> Step (defs, Prog_raise v)
        || _ -> Stuck)
     else if ~is_value_of_expr e then
       result_map (\e'. (defs, Prog_defs (Ds_cons (D_let (LB_simple pat e')) defs')))
                  (red e)
     else
       case pat_match pat e of
          SOME substs -> Step (defs, Prog_defs (substs_value_name_definitions 
                                                  (MAP (\(x, v). (x, remv_tyvar_expr v)) substs)
                                                  defs'))
       || NONE -> Step (defs, Prog_raise (Expr_constant (CONST_constr C_matchfailure)))
   else Stuck) /\
 (defns_red (defs, Prog_defs (Ds_cons (D_letrec lrbs) defs')) =
   if is_definitions_value_of_definitions defs then
     Step (defs, Prog_defs
                   (substs_value_name_definitions
                     (MAP (\lb. (case lb of LRB_simple vn pm -> (vn, remv_tyvar_expr (recfun lrbs pm))))
                          (lrbs_to_lrblist lrbs))
                     defs'))
   else Stuck) /\
 (defns_red (defs, Prog_defs (Ds_cons (D_type type_definition) defs')) =
   if is_definitions_value_of_definitions defs then
     Step (definitions_snoc defs (D_type type_definition),  Prog_defs defs')
   else Stuck) /\
 (defns_red (defs, Prog_defs (Ds_cons (D_exception exception_definition) defs')) =
   if is_definitions_value_of_definitions defs then
     Step (definitions_snoc defs (D_exception exception_definition),  Prog_defs defs')
   else
     Stuck)`;

val defns_red_ind = fetch "-" "defns_red_ind";

local

val lem6 = Q.prove (
`!lb f g. f (case lb of LRB_simple vn pm -> g vn pm) = case lb of LRB_simple vn pm -> f (g vn pm)`,
Cases THEN SRW_TAC [] []);

in

val defns_red_thm = Q.store_thm ("defns_red_thm",
`!ds_values ds l ds_values' ds'. (UNCURRY JRdefn) (ds_values, ds) l ds_values' ds' = 
        (interp_result (defns_red (ds_values, ds)) l = SOME (ds_values', ds'))`,
HO_MATCH_MP_TAC defns_red_ind THEN
SRW_TAC [] [JRdefn_fun, defns_red_def, interp_result_def, COND_EXPAND_EQ, interp_map_thm, raise_cases,
            is_value_of_expr_def, JM_matchP_thm] THEN EQ_TAC THEN SRW_TAC [] [] THENL
[FULL_SIMP_TAC (srw_ss()) [JR_expr_fun, JRuprim_cases] THEN METIS_TAC [no_value_red_thm],
 METIS_TAC [raise_cases, raise_not_JR_thm],
 METIS_TAC [red_thm],
 METIS_TAC [red_thm],
 Cases_on `pat_match pat e` THEN SRW_TAC [] [interp_result_def] THEN METIS_TAC [no_value_red_thm],
 IMP_RES_TAC match_thm THEN SRW_TAC [] [interp_result_def, LAMBDA_PROD2],
 Cases_on `pat_match pat e` THEN SRW_TAC [] [interp_result_def]  THEN METIS_TAC [match_thm, NOT_SOME_NONE],
 Cases_on `pat_match pat e` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, COND_EXPAND_EQ] THEN
     SRW_TAC [] [is_value_of_expr_def, LAMBDA_PROD2] THENL
         [METIS_TAC [match_thm, NOT_SOME_NONE],
          METIS_TAC [match_thm, pat_match_is_val_thm, EVERY_MAP]],
 SRW_TAC [] [lrbs_to_lrblist_def, MAP_MAP] THEN
        MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) THEN
        SRW_TAC [] [MAP_EQ] THEN FULL_SIMP_TAC list_ss [EVERY_MEM],
 Q.EXISTS_TAC `MAP (\lb. case lb of LRB_simple vn pm -> (vn,recfun lrbs pm, pm))
                   (lrbs_to_lrblist lrbs)` THEN 
     SRW_TAC [] [MAP_MAP, EVERY_MAP, lem6] THENL
         [Cases_on `lrbs` THEN SRW_TAC [] [lrbs_to_lrblist_def] THEN
              Induct_on `l'` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN
              SRW_TAC [] [],
          MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) THEN
              SRW_TAC [] [MAP_EQ] THEN Cases_on `lb` THEN SRW_TAC [] [],
          SRW_TAC [] [EVERY_MEM] THEN Cases_on `lb` THEN SRW_TAC [] [] THEN
              MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) THEN
              Cases_on `lrbs` THEN SRW_TAC [] [lrbs_to_lrblist_def] THEN 
              POP_ASSUM (K ALL_TAC) THEN Induct_on `l'` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN
              Cases_on `h` THEN SRW_TAC [] []]]);
 
end;

val store_assign_def = Define
`(store_assign loc expr [] = NONE) /\
 (store_assign loc expr ((l1, e1)::st) =
   if loc = l1 then
     SOME ((l1,expr)::st)
   else
     OPTION_MAP (\st. (l1,e1)::st) (store_assign loc expr st))`;

val top_red_def = Define 
`top_red allocator (st, dvs, prog) =
  if is_definitions_value_of_definitions dvs then
    case defns_red (dvs, prog) of
       Stuck -> NONE
    || Step d -> SOME (st,d)
    || StepAlloc get_results vl ->
         if is_value_of_expr vl then
           let l = allocator st in
              SOME ((l, remv_tyvar_expr vl)::st, get_results (Expr_location l))
         else
           NONE
    || StepLookup get_results loc ->
         (case list_assoc loc st of
             NONE -> NONE
          || SOME e ->
               if is_value_of_expr e then
                 SOME (st, get_results e)
               else
                 NONE)
    || StepAssign r loc expr ->
         if is_value_of_expr expr then
           OPTION_MAP (\st. (st, r)) (store_assign loc (remv_tyvar_expr expr) st)
         else
           NONE
  else
    NONE`;

val good_allocator_def = Define
`good_allocator allocator = !st. ~MEM (allocator st) (MAP FST st)`;

val good_alloc_thm = Q.prove (
`!st alloc v. good_allocator alloc ==> ~(list_assoc (alloc st) st = SOME v)`,
SRW_TAC [] [good_allocator_def] THEN CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN 
IMP_RES_TAC list_assoc_mem THEN FULL_SIMP_TAC list_ss [MEM_MAP] THEN METIS_TAC [FST, SND]);

val store_assign1_thm = Q.prove (
`!st n e st'. (store_assign n e st = SOME st') ==>
              ?st1 e' st2. (st = st1++[(n, e')]++st2) /\ (st' = st1++[(n,e)]++st2) /\
                           (!v. ~(list_assoc n st1 = SOME v))`,
Induct THEN SRW_TAC [] [store_assign_def, list_assoc_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC list_ss [COND_EXPAND_EQ, store_assign_def, list_assoc_def] THEN Cases_on `st'` THEN 
FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THENL
[Q.EXISTS_TAC `[]` THEN SRW_TAC [] [list_assoc_def],
 RES_TAC THEN SRW_TAC [] [] THEN METIS_TAC [APPEND, APPEND_ASSOC, list_assoc_def]]);

val store_assign2_thm = Q.prove (
`!l e st1 e' st2. (!v. ~(list_assoc l st1 = SOME v)) ==>
                  (store_assign l e (st1++[(l, e')]++st2) = SOME (st1++[(l, e)]++st2))`,
Induct_on `st1` THEN SRW_TAC [] [list_assoc_def, store_assign_def] THEN Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [list_assoc_def, store_assign_def] THEN SRW_TAC [] [] THEN METIS_TAC []);

val max_alloc_def = Define
`(max_alloc [] = 0:num) /\
 (max_alloc ((l,_)::st) =
   let l' = max_alloc st in
     if l >= l' then
       l + 1
     else l')`;

local

val lem1 = Q.prove (
`!st l'. MEM l' (MAP FST st) ==> (max_alloc st) > l'`,
Induct THEN SRW_TAC [] [max_alloc_def] THEN Cases_on `h` THEN SRW_TAC [] [max_alloc_def, LET_DEF] THEN
RES_TAC THEN DECIDE_TAC);

in

val max_alloc_good_thm = Q.prove (
`good_allocator max_alloc`,
SRW_TAC [] [good_allocator_def] THEN CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN IMP_RES_TAC lem1 THEN
DECIDE_TAC);

end;

val top_red1_thm = Q.prove (
`!alloc st dvs prog st' dvs' prog'.
   good_allocator alloc /\ (top_red alloc (st, dvs, prog) = SOME (st', dvs', prog')) ==>
   JRtop dvs prog st dvs' prog' st'`,
SRW_TAC [] [JRtop_cases, top_red_def, SIMP_RULE list_ss [ELIM_UNCURRY] defns_red_thm] THEN 
Cases_on `defns_red (dvs,prog)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `prog` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [defns_red_def, interp_result_def, JRstore_cases] THENL
[Q.EXISTS_TAC `Lab_nil` THEN SRW_TAC [] [],
 Q.EXISTS_TAC `Lab_alloc e (alloc st)` THEN SRW_TAC [] [interp_result_def] THEN 
     FULL_SIMP_TAC (srw_ss()) [LET_DEF, list_assoc_mem, COND_EXPAND_EQ, good_alloc_thm],
 Cases_on `list_assoc n st` THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ] THEN
     Q.EXISTS_TAC `Lab_deref n x` THEN SRW_TAC [] [interp_result_def],
 FULL_SIMP_TAC list_ss [COND_EXPAND_EQ] THEN Q.EXISTS_TAC `Lab_assign n e` THEN 
     SRW_TAC [] [interp_result_def] THEN METIS_TAC [store_assign1_thm]]);

val top_red2_thm = Q.prove (
`!st dvs prog st' dvs' prog'. 
  JRtop dvs prog st dvs' prog' st' ==> 
  ?alloc. good_allocator alloc /\ (top_red alloc (st, dvs, prog) = SOME (st', dvs', prog'))`,
SRW_TAC [] [JRtop_cases, top_red_def, SIMP_RULE list_ss [ELIM_UNCURRY] defns_red_thm, LET_DEF] THEN 
Cases_on `defns_red (dvs,prog)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `prog` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [defns_red_def, interp_result_def, JRstore_cases, COND_EXPAND_EQ] THEN 
SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [interp_result_def, COND_EXPAND_EQ] THEN 
SRW_TAC [] [] THENL
[METIS_TAC [max_alloc_good_thm],
 Q.EXISTS_TAC `\st'. if st' = st then l else max_alloc st'` THEN SRW_TAC [] [good_allocator_def] THEN
     Cases_on `st' = st` THEN SRW_TAC [] [] THENL
     [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN IMP_RES_TAC mem_list_assoc THEN METIS_TAC [],
      METIS_TAC [max_alloc_good_thm, good_allocator_def]],
 METIS_TAC [max_alloc_good_thm],
 Q.EXISTS_TAC `max_alloc` THEN SRW_TAC [] [] THEN METIS_TAC [max_alloc_good_thm, store_assign2_thm],
 METIS_TAC []]);

val top_red_thm = Q.store_thm ("top_red_thm",
`!st dvs prog st' dvs' prog'. 
  JRtop dvs prog st dvs' prog' st' = 
  ?alloc. good_allocator alloc /\ (top_red alloc (st, dvs, prog) = SOME (st', dvs', prog'))`,
METIS_TAC [top_red2_thm, top_red1_thm]);

val top_red_max_alloc_thm = Q.store_thm ("top_red_max_alloc_thm",
`!st dvs prog st' dvs' prog'.
   (top_red max_alloc (st, dvs, prog) = SOME (st', dvs', prog')) ==>
   JRtop dvs prog st dvs' prog' st'`,
METIS_TAC [top_red_thm, max_alloc_good_thm]);

val _ = export_theory();
