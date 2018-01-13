open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open sortingTheory wordsTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory matching_funTheory;

val _ = new_theory "reduction_fun";

val UNZIP_LEM = Q.prove (
`!l1 l2 l3. (UNZIP l1 = (l2, l3)) = (l2 = MAP FST l1) /\ (l3 = MAP SND l1)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN SRW_TAC [] [] THEN Cases_on `l3` THEN SRW_TAC [] [] THEN
METIS_TAC [FST, SND]);

val ZIP_LEM = Q.prove (
`!l1 l2 l3 x. (MAP SND l1 = l2++x::l3) = ?l2' x' l3'. (LENGTH l2' = LENGTH l2) /\ (LENGTH l3' = LENGTH l3) /\
                                                      (l1 = ZIP (l2', l2) ++ (x',x) :: ZIP (l3', l3))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l2` THEN SRW_TAC [] [] THEN EQ_TAC THEN SRW_TAC [] [] THENL
[Q.EXISTS_TAC `[]` THEN SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [] THEN 
     Q.EXISTS_TAC `MAP FST l1` THEN SRW_TAC [] [ZIP_MAP_ID],
 Cases_on `l2'` THEN FULL_SIMP_TAC list_ss [],
 Cases_on `l2'` THEN FULL_SIMP_TAC list_ss [MAP_SND_ZIP],
 FULL_SIMP_TAC list_ss [MAP_SND_ZIP] THEN
    Q.PAT_ASSUM `!l2 l3'' x''. (t ++ x::l3 = l2 ++ x''::l3'') = P l2 l3'' x''` 
                (MP_TAC o Q.SPECL [`t`, `l3`, `x`]) THEN 
    SRW_TAC [] [] THEN Q.EXISTS_TAC `FST h::l2''` THEN SRW_TAC [] [] THEN METIS_TAC [],
 Cases_on `l2'` THEN FULL_SIMP_TAC list_ss [],
 Cases_on `l2'` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []]);


val is_raise_def = Define
`(is_raise (Expr_apply expr1 expr2) = (expr1 = Expr_uprim Uprim_raise) /\ is_value_of_expr expr2) /\
 (is_raise _ = F)`;

val value_not_raise_thm = Q.store_thm ("value_not_raise_thm",
`!e. (is_value_of_expr e ==> ~is_raise e) /\ (is_raise e ==> ~is_value_of_expr e)`,
recInduct is_value_of_expr_ind THEN SRW_TAC [] [is_value_of_expr_def, is_raise_def]);

val _ = Hol_datatype
`result = Stuck
        | Step of 'a
        | StepAlloc of (expr -> 'a) => expr
        | StepLookup of (expr -> 'a) => location 
        | StepAssign of 'a => location => expr`;

val result_map_def = Define 
`(result_map f Stuck = Stuck) /\
 (result_map f (Step expr) = Step (f expr)) /\
 (result_map f (StepAlloc get_result alloc_expr) =
    StepAlloc (\l. f (get_result l)) alloc_expr) /\
 (result_map f (StepLookup get_result lookup_lab) =
    StepLookup (\e. f (get_result e)) lookup_lab) /\
 (result_map f (StepAssign result_expr assign_lab assign_expr) =
    StepAssign (f result_expr) assign_lab assign_expr)`;

val interp_result_def = Define
`(interp_result (Step e) l = if l = Lab_nil then SOME e else NONE) /\
 (interp_result (StepAlloc get_result alloc_expr1) (Lab_alloc alloc_expr2 new_loc) =
    if alloc_expr1 = alloc_expr2 then
       SOME (get_result (Expr_location new_loc))
    else
       NONE) /\
 (interp_result (StepLookup get_result lookup_lab1) (Lab_deref lookup_lab2 result_expr) =
    if is_value_of_expr result_expr /\ (lookup_lab1 = lookup_lab2) then
       SOME (get_result result_expr)
    else
       NONE) /\
 (interp_result (StepAssign result assign_loc1 assign_expr1) (Lab_assign assign_loc2 assign_expr2) =
    if (assign_loc1 = assign_loc2) /\ (assign_expr1 = assign_expr2) then
       SOME result
    else
       NONE) /\
 (interp_result _ _ = NONE)`;

val eval_uprim_def = Define
`(eval_uprim Uprim_not v = 
    if v = Expr_constant (CONST_true) then
       Step (Expr_constant (CONST_false))
    else if v = Expr_constant (CONST_false) then
       Step (Expr_constant (CONST_true))
    else Stuck) /\
 (eval_uprim Uprim_minus v = 
    case v of
       Expr_constant (CONST_int n) -> Step (Expr_constant (CONST_int (0w - n)))
    || _ -> Stuck) /\
 (eval_uprim Uprim_ref v =
    StepAlloc (\e. e) v) /\
 (eval_uprim Uprim_deref v = 
    case v of
       Expr_location l -> StepLookup (\e. e) l
    || _ -> Stuck) /\
 (eval_uprim Uprim_raise v = 
    Stuck)`;

val b_int_primop_def = Define
`b_int_primop oper v1 v2 = 
  case v1 of 
     Expr_constant (CONST_int n1) ->
       (case v2 of
           Expr_constant (CONST_int n2) ->
              Step (Expr_constant (CONST_int (oper n1 n2)))
        || _ -> Stuck)
  || _ -> Stuck`;

val is_const_constr_def = Define
`(is_const_constr (CONST_constr _) = T) /\
 (is_const_constr _ = F)`;

val non_funval_equal_def = Define
`(non_funval_equal (Expr_constant c) (Expr_constant c') =
    if c = c' then 
       Step (Expr_constant CONST_true)
    else
       Step (Expr_constant CONST_false)) /\
 (non_funval_equal (Expr_location l) (Expr_location l') =
    Step (Expr_apply (Expr_apply (Expr_bprim Bprim_equal) 
                                 (Expr_apply (Expr_uprim Uprim_deref) (Expr_location l)))
                     (Expr_apply (Expr_uprim Uprim_deref) (Expr_location l')))) /\
 (non_funval_equal (Expr_cons v1 v2) (Expr_cons v1' v2') =
    Step (Expr_and (Expr_apply (Expr_apply (Expr_bprim Bprim_equal) v1) v1')
                   (Expr_apply (Expr_apply (Expr_bprim Bprim_equal) v2) v2'))) /\
 (non_funval_equal (Expr_cons v1 v2) (Expr_constant const) = 
    if (const = CONST_nil) then
       Step (Expr_constant CONST_false)
    else
       Stuck) /\
 (non_funval_equal (Expr_constant const) (Expr_cons v1' v2') = 
    if const = CONST_nil then
       Step (Expr_constant CONST_false)
    else
       Stuck) /\
 (non_funval_equal (Expr_tuple vs) (Expr_tuple vs') = 
    if ~(LENGTH vs >= 2) \/ ~(LENGTH vs = LENGTH vs') then
       Stuck
    else
       Step (FOLDR Expr_and 
                   (Expr_constant CONST_true) 
                   (MAP2 (\v v'. Expr_apply (Expr_apply (Expr_bprim Bprim_equal) v) v') vs vs'))) /\
 (non_funval_equal (Expr_construct ctor vs) (Expr_construct ctor' vs') =
    if ~(ctor = ctor') then
       Step (Expr_constant CONST_false)
    else if ~(LENGTH vs = LENGTH vs') then
       Stuck
    else 
       Step (FOLDR Expr_and
                   (Expr_constant CONST_true)
                   (MAP2 (\v v'. Expr_apply (Expr_apply (Expr_bprim Bprim_equal) v) v') vs vs'))) /\
 (non_funval_equal (Expr_construct ctor vs) (Expr_constant const) =
    if is_const_constr const then
      Step (Expr_constant CONST_false)
    else
      Stuck) /\
 (non_funval_equal (Expr_constant const) (Expr_construct ctor' vs') =
    if is_const_constr const then
      Step (Expr_constant CONST_false)
    else
      Stuck) /\
 (non_funval_equal (Expr_record field_exprs) (Expr_record field_exprs') =
    if ~(PERM (MAP (\x. field_to_fn (FST x)) field_exprs) 
              (MAP (\x. field_to_fn (FST x)) field_exprs')) then
       Stuck
    else
       Step (FOLDR Expr_and (Expr_constant CONST_true)
                   (MAP (\(field, v).
                        Expr_apply (Expr_apply (Expr_bprim Bprim_equal) v) 
                                   (Expr_field (Expr_record field_exprs') field))
                        field_exprs))) /\
 (non_funval_equal _ _ = Stuck)`;

val eval_bprim_def = Define
`(eval_bprim Bprim_equal v1 v2 = 
    if funval v1 then
       Step (Expr_apply (Expr_uprim Uprim_raise) 
                        (Expr_construct C_invalidargument 
                                        [Expr_constant (CONST_string "equal: functional value")]))
    else
       non_funval_equal v1 v2) /\
 (eval_bprim Bprim_plus v1 v2 = b_int_primop $+ v1 v2) /\
 (eval_bprim Bprim_minus v1 v2 = b_int_primop $- v1 v2) /\
 (eval_bprim Bprim_times v1 v2 = b_int_primop $* v1 v2) /\
 (eval_bprim Bprim_div v1 v2 = 
    if v2 = Expr_constant (CONST_int 0w) then
       case v1 of
          Expr_constant (CONST_int n) ->
              Step (Expr_apply (Expr_uprim Uprim_raise) (Expr_constant (CONST_constr C_div_by_0)))
       || _ -> Stuck
    else
       b_int_primop $/ v1 v2) /\
 (eval_bprim Bprim_assign v1 v2 =
    case v1 of
       Expr_location l -> StepAssign (Expr_constant CONST_unit) l v2
    || _ -> Stuck)`;

val do_1override_def = Define
`(do_1override fn1 v1 [] = NONE) /\
 (do_1override fn1 v1 ((fn2,v2)::record) =
    if fn1 = fn2 then
       SOME ((fn1, v1)::record)
    else
       OPTION_MAP (\r. (fn2, v2)::r) (do_1override fn1 v1 record))`;

val eval_override_def = Define
`(eval_override v [] [] = Stuck) /\
 (eval_override v1 [fn1] [v] =
    case v1 of 
      Expr_record fn_expr_list -> 
         (case do_1override fn1 v fn_expr_list of
             NONE -> Stuck
          || SOME x -> Step (Expr_record x))
   || _ -> Stuck) /\
 (eval_override v1 (fn1::foverrides)  (v::voverrides) =
    case v1 of 
      Expr_record fn_expr_list -> 
         (case do_1override fn1 v fn_expr_list of
             NONE -> Stuck
          || SOME x -> Step (Expr_override (Expr_record x) (ZIP (foverrides, voverrides))))
   || _ -> Stuck)`;


val eval_apply_def = Define
`eval_apply v1 v2 = 
   case v1 of
      Expr_uprim up -> eval_uprim up v2
   || Expr_function pm -> Step (Expr_match v2 pm)
   || Expr_apply v3 v4 -> 
        (case v3 of
            Expr_bprim bp -> eval_bprim bp v4 v2
         || _ -> Stuck)
   || _ -> Stuck`;

val eval_field_def = Define
`eval_field field v = 
   case v of
      Expr_record fn_expr_list -> 
         (case list_assoc field fn_expr_list of
             SOME x -> Step x
          || NONE -> Stuck)
   || _ -> Stuck`;

val eval_ite_def = Define
`eval_ite expr2 expr3 v1 = 
   if v1 = Expr_constant CONST_true then
      Step expr2
   else if v1 = Expr_constant CONST_false then
      Step expr3
   else
      Stuck`;

val eval_while_def = Define
`eval_while e1 e2 = 
   Step (Expr_ifthenelse e1 (Expr_sequence e2 (Expr_while e1 e2)) (Expr_constant CONST_unit))`;

val eval_for_def = Define
`eval_for x for_dirn expr3 v2 v1 =
   case v1 of
     Expr_constant (CONST_int n1) -> 
        (case v2 of
            Expr_constant (CONST_int n2) ->
               (case for_dirn of
                   FD_upto -> 
                     if n1 <= n2 then
                        Step (Expr_sequence (Expr_let (LB_simple (P_var x) v1) expr3)
                                            (Expr_for x (Expr_constant (CONST_int (n1 + 1w))) for_dirn v2
                                                      expr3))
                     else
                        Step (Expr_constant CONST_unit)
                || FD_downto ->
                     if n2 <= n1 then
                        Step (Expr_sequence (Expr_let (LB_simple (P_var x) v1) expr3)
                                            (Expr_for x (Expr_constant (CONST_int (n1 - 1w))) for_dirn v2
                                                      expr3))
                     else
                        Step (Expr_constant CONST_unit))
         || _ -> Stuck)
   || _ -> Stuck`;

val eval_match_def = Define
`(eval_match (PM_pm []) v = Stuck) /\
 (eval_match (PM_pm [PE_inj p e]) v = 
    Step (case pat_match p v of
             NONE -> Expr_apply (Expr_uprim Uprim_raise) (Expr_constant (CONST_constr C_matchfailure))
          || SOME substs -> substs_value_name_expr substs e)) /\
 (eval_match (PM_pm (PE_inj p e::pelist)) v = 
    Step (case pat_match p v of
             NONE -> Expr_match v (PM_pm pelist)
          || SOME substs -> substs_value_name_expr substs e))`;


val eval_try_def = Define
`eval_try expr pattern_matching = 
   case expr of
      Expr_apply e1 e2 -> 
        if e1 = Expr_uprim Uprim_raise then 
           (case pattern_matching of
               PM_pm pe_list -> Step (Expr_match e2 (PM_pm (pe_list ++ [PE_inj P_any expr]))))
        else
           Stuck 
   || _ -> Stuck`;

val eval_let_def = Define
`eval_let pattern expr2 v1 = 
  Step (case pat_match pattern v1 of
           SOME substs -> substs_value_name_expr substs expr2
        || NONE -> Expr_apply (Expr_uprim Uprim_raise) (Expr_constant (CONST_constr C_matchfailure)))`;

val eval_letrec_def = Define
`eval_letrec letrec_bindings expr =
   Step (substs_value_name_expr (MAP (\lb. (case lb of LRB_simple vn pm -> (vn, recfun letrec_bindings pm)))
                                     (lrbs_to_lrblist letrec_bindings)) expr)`;

val eval_assert_def = Define
`eval_assert v =
   if v = Expr_constant CONST_true then
      Step (Expr_constant CONST_unit)
   else if v = Expr_constant CONST_false then
      Step (Expr_apply (Expr_uprim Uprim_raise) (Expr_constant (CONST_constr C_assertfailure)))
   else
      Stuck`;

local

val lem1 = Q.prove (
`!exprs1 exprs2. letrec_binding4_size (exprs1 ++ exprs2) = 
                 letrec_binding4_size exprs1 + letrec_binding4_size exprs2`,
Induct THEN SRW_TAC [] [letrec_binding_size_def] THEN DECIDE_TAC);

val lem2 = Q.prove (
`!exprs. letrec_binding4_size (REVERSE exprs) = letrec_binding4_size exprs`,
Induct THEN SRW_TAC [] [letrec_binding_size_def, lem1] THEN DECIDE_TAC);

val lem3 = Q.prove (
`!field_exprs exprs fields. ((fields,exprs) = UNZIP field_exprs) ==>
                    letrec_binding4_size exprs <= letrec_binding3_size field_exprs`,
Induct THEN SRW_TAC [] [letrec_binding_size_def] THEN Cases_on `UNZIP field_exprs` THEN
SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [letrec_binding_size_def] THEN DECIDE_TAC);

in

val red_def = tDefine "red"
`(red (Expr_uprim unary_prim) = Stuck) /\
 (red (Expr_bprim binary_prim) = Stuck) /\
 (red (Expr_ident value_name) = Stuck) /\
 (red (Expr_constant constant) = Stuck) /\
 (red (Expr_typed expr typexpr) = Step expr) /\
 (red (Expr_tuple exprs) = red_list (REVERSE exprs) Expr_tuple (\v. Stuck) []) /\
 (red (Expr_construct constr exprs) = red_list (REVERSE exprs) (Expr_construct constr) (\x. Stuck) []) /\
 (red (Expr_cons expr1 expr2) = red_2 expr1 expr2 Expr_cons (\v1 v2. Stuck)) /\ 
 (red (Expr_record field_exprs) = 
   let (fields, exprs) = UNZIP field_exprs in
     red_list (REVERSE exprs) (\es. Expr_record (ZIP (fields, es))) (\v. Stuck) []) /\
 (red (Expr_override expr field_exprs) = 
   red_1 expr (\e. Expr_override e field_exprs) 
              (\v. let (fields, exprs) = UNZIP field_exprs in
                     red_list (REVERSE exprs)
                              (\es. Expr_override v (ZIP (fields, es)))
                              (eval_override v fields)
                              [])) /\
 (red (Expr_apply expr1 expr2) = 
   red_2 expr1 expr2 Expr_apply eval_apply) /\
 (red (Expr_and expr1 expr2) = Step (Expr_ifthenelse expr1 expr2 (Expr_constant CONST_false))) /\
 (red (Expr_or expr1 expr2) = Step (Expr_ifthenelse expr1 (Expr_constant CONST_true) expr2)) /\
 (red (Expr_field expr field) = red_1 expr (\e. Expr_field e field) (eval_field field)) /\
 (red (Expr_ifthenelse expr1 expr2 expr3) = 
    red_1 expr1 (\e. Expr_ifthenelse e expr2 expr3) (eval_ite expr2 expr3)) /\
 (red (Expr_while expr1 expr2) = eval_while expr1 expr2) /\
 (red (Expr_for value_name expr1 for_dirn expr2 expr3) = 
    red_2 expr2 expr1 (\e2 e1. Expr_for value_name e1 for_dirn e2 expr3)
                      (eval_for value_name for_dirn expr3)) /\
 (red (Expr_sequence expr1 expr2) = red_1 expr1 (\e. Expr_sequence e expr2) (\v. Step expr2)) /\
 (red (Expr_match expr pattern_matching) = 
    red_1 expr (\e. Expr_match e pattern_matching) (eval_match pattern_matching)) /\
 (red (Expr_function pattern_matching) = Stuck) /\
 (red (Expr_try expr pattern_matching) = 
    if is_raise expr then
      eval_try expr pattern_matching
    else if is_value_of_expr expr then
      Step expr
    else
      result_map (\e. Expr_try e pattern_matching) (red expr)) /\
 (red (Expr_let (LB_simple pattern expr1) expr2) = 
     red_1 expr1 (\e1. Expr_let (LB_simple pattern e1) expr2) (eval_let pattern expr2)) /\
 (red (Expr_letrec letrec_bindings expr) = eval_letrec letrec_bindings expr) /\
 (red (Expr_assert expr) = 
    red_1 expr Expr_assert eval_assert) /\
 (red (Expr_location location) = Stuck) /\

 (red_1 expr pack1 eval1 = 
    if is_raise expr then
      Step expr
    else if ~is_value_of_expr expr then
      result_map pack1 (red expr)
    else
      eval1 expr) /\

 (red_2 expr1 expr2 pack2 eval2 =
   if is_raise expr2 then
      Step expr2
    else if ~is_value_of_expr expr2 then 
      result_map (pack2 expr1) (red expr2)
    else if is_raise expr1 then
      Step expr1
    else if ~is_value_of_expr expr1 then
      result_map (\e. pack2 e expr2) (red expr1)
    else
      eval2 expr1 expr2) /\

 (red_list [] packl evall acc = evall acc) /\
 (red_list (expr::exprs) packl evall acc = 
    if is_raise expr then
      Step expr
    else if ~is_value_of_expr expr then
      result_map (\e. packl (REVERSE exprs++[e]++acc)) (red expr)
    else
      red_list exprs packl evall (expr::acc))`
(WF_REL_TAC `inv_image ((\x:num y. x < y) LEX (\x:num y. x < y))
               ((sum_case (\e. (expr_size e, 0))
                (sum_case (\(e, f, g). (expr_size e, 1))
                (sum_case (\(e1, e2, f, g). (expr_size e1 + expr_size e2, 1))
                          (\(e, f, g). (letrec_binding4_size e, 1))))))`
 THEN
 SRW_TAC [ARITH_ss] [lem2, METIS_PROVE [] ``!f. (\x y. f x y) = f``] THEN 
 SRW_TAC [] [prim_recTheory.WF_LESS] THEN IMP_RES_TAC lem3 THEN DECIDE_TAC);

val red_ind = fetch "-" "red_ind";

end;

val interp_map_thm = Q.store_thm ("interp_map_thm",
`!result label f. interp_result (result_map f result) label = OPTION_MAP f (interp_result result label)`,
Cases THEN Cases THEN SRW_TAC [] [interp_result_def, result_map_def]);

val eval_ite_thm = Q.prove (
`!e2 e3 e l. (interp_result (eval_ite expr2 expr3 e) l = SOME e') =
             (e = Expr_constant CONST_true) /\ (expr2 = e') /\ (l = Lab_nil) \/
             (e = Expr_constant CONST_false) /\ (expr3 = e') /\ (l = Lab_nil)`,
SRW_TAC [] [eval_ite_def, interp_result_def, COND_EXPAND_EQ] THEN METIS_TAC []);


val raise_stuck_thm = Q.prove (
`!e. is_raise e ==> (red e = Stuck)`,
Cases THEN SRW_TAC [] [is_raise_def, red_def, result_map_def, eval_apply_def, eval_uprim_def] THEN
METIS_TAC [value_not_raise_thm]);

val no_value_red_thm = Q.store_thm ("no_value_red_thm",
`!e L e'. is_value_of_expr e ==> ~JR_expr e L e'`,
recInduct is_value_of_expr_ind THEN SRW_TAC [] [is_value_of_expr_def, JR_expr_fun] THEN
CCONTR_TAC THEN FULL_SIMP_TAC list_ss [is_value_of_expr_def, expr_11, expr_distinct, JR_expr_fun] THEN
METIS_TAC []);

val raise_not_JR_thm = Q.store_thm ("raise_not_JR_thm",
`!e. is_raise e ==> !l e'. ~JR_expr e l e'`,
Cases_on `e` THEN SRW_TAC [] [is_raise_def, JR_expr_fun, JRuprim_cases] THEN 
FULL_SIMP_TAC list_ss [no_value_red_thm] THEN METIS_TAC [value_not_raise_thm, is_raise_def]);

local

val lem1 = Q.prove (
`!es f acc. EVERY is_value_of_expr es ==> (red_list es f (\v. Stuck) acc = Stuck)`,
Induct THEN SRW_TAC [] [red_def, o_DEF, value_not_raise_thm]);

val lem2 = Q.prove (
`!fel fl el P. EVERY (\(f,e). P e) fel /\ (UNZIP fel = (fl,el)) ==> EVERY P el`,
Induct THEN SRW_TAC [] [] THEN SRW_TAC [] [] THENL
[Cases_on `h` THEN FULL_SIMP_TAC list_ss [],
 RES_TAC THEN POP_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `FST (UNZIP fel)` THEN SRW_TAC [] []]);

in

val value_stuck_thm = Q.prove (
`!e. is_value_of_expr e ==> (red e = Stuck)`,
recInduct is_value_of_expr_ind THEN 
SRW_TAC [] [is_value_of_expr_def, red_def, value_not_raise_thm, eval_apply_def] THEN
SRW_TAC [] [red_def, result_map_def] THEN FULL_SIMP_TAC list_ss [o_DEF] THENL
[METIS_TAC [lem1, EVERY_REVERSE],
 METIS_TAC [lem1, EVERY_REVERSE],
 METIS_TAC [lem1, lem2, EVERY_REVERSE],
 Cases_on `expr1` THEN FULL_SIMP_TAC list_ss [is_raise_def] THEN SRW_TAC [] []]);

end;

val FOLDR_MAP = Q.prove (
`!f e g l. FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l`,
Induct_on `l` THEN SRW_TAC [] []);

val raise_cases = Q.store_thm ("raise_cases",
`!e. is_raise e = ?v. is_value_of_expr v /\ (e = Expr_apply (Expr_uprim Uprim_raise) v)`,
Cases THEN SRW_TAC [] [is_raise_def] THEN METIS_TAC []);

val uprim_red_thm = Q.prove (
`!u e l e'. is_value_of_expr e ==> 
            (JRuprim u e l e' = (interp_result (eval_uprim u e) l = SOME e'))`,
Cases THEN SRW_TAC [] [JRuprim_cases] THEN SRW_TAC [] [interp_result_def, eval_uprim_def, COND_EXPAND_EQ] THENL
[METIS_TAC [],
 METIS_TAC [],
 Cases_on `e` THEN SRW_TAC [] [interp_result_def] THEN Cases_on `c` THEN SRW_TAC [] [interp_result_def] THEN
       METIS_TAC [],
 Cases_on `l` THEN SRW_TAC [] [interp_result_def] THEN METIS_TAC [],
 Cases_on `e` THEN SRW_TAC [] [interp_result_def] THEN Cases_on `l` THEN SRW_TAC [] [interp_result_def] THEN
       METIS_TAC []]);

local

val TAC = 
Cases_on `e1` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, is_value_of_expr_def] THEN
Cases_on `c` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def] THEN
Cases_on `e2` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, is_value_of_expr_def] THEN
Cases_on `c` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, COND_EXPAND_EQ] THEN METIS_TAC [];

in

val bprim_red_thm = Q.prove (
`!e1 b e2 l e'. is_value_of_expr e1 /\ is_value_of_expr e2 ==>
                (JRbprim e1 b e2 l e' = (interp_result (eval_bprim b e1 e2) l = SOME e'))`,
Cases_on `b` THEN SRW_TAC [] [JRbprim_cases] THEN 
SRW_TAC [] [interp_result_def, funval_def, eval_bprim_def, COND_EXPAND_EQ, b_int_primop_def] THENL
[Cases_on `e1` THEN FULL_SIMP_TAC (srw_ss()) [funval_def] THEN METIS_TAC [],
 Cases_on `e1` THEN 
      FULL_SIMP_TAC (srw_ss()) [funval_def, is_value_of_expr_def, non_funval_equal_def, interp_result_def] THEN
      Cases_on `e2` THEN FULL_SIMP_TAC list_ss [funval_def, is_value_of_expr_def] THEN
      SRW_TAC [] [non_funval_equal_def, interp_result_def, COND_EXPAND_EQ, o_DEF] THENL
      [METIS_TAC [],
       METIS_TAC [],
       Cases_on `c` THEN FULL_SIMP_TAC (srw_ss()) [is_const_constr_def] THEN METIS_TAC [],
       Cases_on `c` THEN FULL_SIMP_TAC (srw_ss()) [is_const_constr_def] THEN METIS_TAC [],
       METIS_TAC [],
       METIS_TAC [LENGTH_MAP],
       METIS_TAC [LENGTH_MAP],
       FULL_SIMP_TAC list_ss [MAP2_ZIP, LAMBDA_PROD2] THEN
                 METIS_TAC [MAP_FST_ZIP, MAP_SND_ZIP, EVERY_MAP, ZIP_MAP_ID, LENGTH_ZIP],
       Cases_on `c'` THEN FULL_SIMP_TAC (srw_ss()) [is_const_constr_def] THEN METIS_TAC [], 
       Cases_on `c'` THEN FULL_SIMP_TAC (srw_ss()) [is_const_constr_def] THEN METIS_TAC [], 
       METIS_TAC [],
       METIS_TAC [LENGTH_MAP],
       FULL_SIMP_TAC list_ss [MAP2_ZIP, LAMBDA_PROD2] THEN
                 METIS_TAC [MAP_FST_ZIP, MAP_SND_ZIP, EVERY_MAP, ZIP_MAP_ID, LENGTH_ZIP],
       METIS_TAC [],
       METIS_TAC [],
       CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN 
                 FULL_SIMP_TAC list_ss [MAP_MAP, field_to_fn_def] THEN METIS_TAC [],
       EQ_TAC THEN SRW_TAC [] [] THEN1 SRW_TAC [] [MAP_MAP, LAMBDA_PROD2] THEN
               MAP_EVERY Q.EXISTS_TAC [`MAP (\z. (field_to_fn (FST z), SND z)) l''`,
                                       `MAP (\z. (field_to_fn (FST z), SND z)) l'`] THEN
               FULL_SIMP_TAC (srw_ss()) [MAP_MAP, field_to_fn_thm, MAP_I, LAMBDA_PROD2, EVERY_MAP],
       METIS_TAC []],
 TAC,
 TAC,
 TAC,
 Cases_on `e1` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, is_value_of_expr_def] THEN
      Cases_on `c` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, COND_EXPAND_EQ] THEN METIS_TAC [],
 TAC,
 Cases_on `e1` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, is_value_of_expr_def] THEN
 Cases_on `l` THEN SRW_TAC [] [interp_result_def] THEN METIS_TAC []]); 

end;

val list_get_next_def = Define
`(list_get_next [] = NONE) /\
 (list_get_next (e::es) = 
   if ~is_value_of_expr e then
      SOME ([], e, es)
   else
      OPTION_MAP (\(vs, e', es). (e::vs, e', es)) (list_get_next es))`;

val get_next_NONE_thm = Q.prove (
`!es. (list_get_next es = NONE) = EVERY is_value_of_expr es`,
Induct THEN SRW_TAC [] [list_get_next_def] THEN METIS_TAC []);

val get_next_SOME_thm = Q.prove (
`!es x. (list_get_next es = SOME x) = 
        ?v_list e e_list. (es = v_list++[e]++e_list) /\ EVERY is_value_of_expr v_list /\
                          ~is_value_of_expr e /\ (x = (v_list, e, e_list))`,
Induct THEN SRW_TAC [] [list_get_next_def] THENL
[Cases_on `x` THEN Cases_on `r` THEN Cases_on `q` THEN SRW_TAC [] [] THEN METIS_TAC [],
 EQ_TAC THEN SRW_TAC [] [] THEN SRW_TAC [] [] THEN Cases_on `v_list` THEN FULL_SIMP_TAC list_ss [] THEN
      SRW_TAC [] [] THEN Q.EXISTS_TAC `(t, e, e_list)` THEN SRW_TAC [] []]);

val lem1 = Q.prove (
`(!v. ~is_value_of_expr v \/ ~(e1 = Expr_apply (Expr_uprim Uprim_raise) v)) ==>
 ~(e1 = Expr_apply (Expr_uprim Uprim_raise) v') \/ ~(l = Lab_nil) \/
    ~(e' = Expr_apply (Expr_uprim Uprim_raise) v') \/ ~is_value_of_expr v'`,
METIS_TAC []);

val lem2 = Q.prove (
`!x y z. x++[y]++z = x++y::z`,
METIS_TAC [APPEND, APPEND_ASSOC]);

val lem3 = Q.prove (
`!e_list e_list' e e' v_list v_list'. 
    EVERY is_value_of_expr v_list /\ EVERY is_value_of_expr v_list' /\
    ~is_value_of_expr e /\ ~is_value_of_expr e' ==> 
    ((v_list++e::e_list = v_list'++e'::e_list') = (e_list = e_list') /\ (e = e') /\ (v_list = v_list'))`,
Induct_on `v_list` THEN SRW_TAC [] [] THEN Cases_on `v_list'` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []);

val lem4 = Q.prove (
`!ctor.
 (!l e'. (if is_raise e then
             (e' = e) /\ (l = Lab_nil)
          else
             ?e1'. (e' = ctor (REVERSE (v_list ++ [e1'] ++ e_list))) /\ JR_expr e l e1') =
         (interp_result (red_list (v_list ++ [e] ++ e_list) ctor (\v. Stuck) []) l = SOME e')) /\
 (REVERSE exprs = v_list ++ [e] ++ e_list) /\
 EVERY is_value_of_expr v_list /\
 ~is_value_of_expr e 
 ==>
 ((?v_list e_list e e''.
        (exprs = e_list ++ [e] ++ v_list) /\
        (e' = ctor (e_list ++ [e''] ++ v_list)) /\
        EVERY is_value_of_expr v_list /\ JR_expr e l e'') \/
  (?v_list e_list v.
        (exprs =
         e_list ++ [Expr_apply (Expr_uprim Uprim_raise) v] ++ v_list) /\
        (l = Lab_nil) /\ (e' = Expr_apply (Expr_uprim Uprim_raise) v) /\
        is_value_of_expr v /\ EVERY is_value_of_expr v_list)
   =
  (interp_result (red_list (v_list ++ [e] ++ e_list) ctor (\v. Stuck) []) l = SOME e'))`,
SRW_TAC [] [] THEN EQ_TAC THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC list_ss [COND_EXPAND_EQ, REVERSE_APPEND, lem2] THENL
[`EVERY is_value_of_expr (REVERSE v_list')` by METIS_TAC [EVERY_REVERSE] THEN
     `~is_value_of_expr e''` by METIS_TAC [no_value_red_thm] THEN
     FULL_SIMP_TAC list_ss [lem3] THEN SRW_TAC [] [] THEN
     `~is_raise e` by METIS_TAC [raise_not_JR_thm] THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC [],
 `EVERY is_value_of_expr (REVERSE v_list')` by METIS_TAC [EVERY_REVERSE] THEN
     `~is_value_of_expr (Expr_apply (Expr_uprim Uprim_raise) v)` by SRW_TAC [] [is_value_of_expr_def] THEN
     FULL_SIMP_TAC list_ss [lem3] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [is_raise_def] THEN
     METIS_TAC [],
 Cases_on `is_raise e` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THENL
     [FULL_SIMP_TAC list_ss [raise_cases] THEN DISJ2_TAC THEN 
          MAP_EVERY Q.EXISTS_TAC [`REVERSE v_list`, `REVERSE e_list`, `v`] THEN
          SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [lem2, REVERSE_EQ_SYM, REVERSE_APPEND, EVERY_REVERSE] THEN
          METIS_TAC [],
     DISJ1_TAC THEN MAP_EVERY Q.EXISTS_TAC [`REVERSE v_list`, `REVERSE e_list`, `e`] THEN
          FULL_SIMP_TAC list_ss [lem2, REVERSE_EQ_SYM, REVERSE_APPEND, EVERY_REVERSE]]]);

val lem5 = Q.prove (
`!l1 f x l2 fn_v_list fn'_v'_list e'.
  ~MEM (F_name f) (MAP FST l1) /\ ~MEM (F_name f) (MAP (\z. F_name (FST z)) fn_v_list) /\
  (l1 ++ (F_name f,x)::l2 = MAP (\z. (F_name (FST z),SND z)) fn_v_list ++ [(F_name f,e')] ++
                            MAP (\z. (F_name (FST z),SND z)) fn'_v'_list) ==>
  (x = e')`,
Induct THEN SRW_TAC [] [] THEN Cases_on `fn_v_list` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []);

(*val lem6 = Q.prove (
`(!lb g. FST (case lb of LRB_simple vn pm -> g vn pm) = case lb of LRB_simple vn pm -> FST (g vn pm)) /\
 (!lb g. SND (case lb of LRB_simple vn pm -> g vn pm) = case lb of LRB_simple vn pm -> SND (g vn pm))`,
CONJ_TAC THEN Cases THEN SRW_TAC [] []);
*)
val lem6 = Q.prove (
`!lb f g. f (case lb of LRB_simple vn pm -> g vn pm) = case lb of LRB_simple vn pm -> f (g vn pm)`,
Cases THEN SRW_TAC [] []);

val lem7 = Q.prove (
`!h t' pat_e_list. (h::t' = MAP (\z. PE_inj (FST z) (SND z)) pat_e_list) = 
              (pat_e_list = (case h of PE_inj a b -> (a, b))::MAP (\x. case x of PE_inj a b -> (a, b)) t')`,
Induct_on `t'` THEN SRW_TAC [] [] THENL
[Cases_on `h` THEN Cases_on `pat_e_list` THEN SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [] THEN 
     METIS_TAC [],
 Cases_on `pat_e_list` THEN Cases_on `h'` THEN SRW_TAC [] [] THEN Cases_on `h''` THEN SRW_TAC [] [] THEN
     Cases_on `h` THEN SRW_TAC [] [] THEN METIS_TAC []]);

val lem8 = Q.prove (
`(!pe g. FST (case pe of PE_inj p e -> g p e) = case pe of PE_inj p e -> FST (g p e)) /\
 (!pe g. SND (case pe of PE_inj p e -> g p e) = case pe of PE_inj p e -> SND (g p e))`,
CONJ_TAC THEN Cases THEN SRW_TAC [] []);

val lem9 = Q.prove (
`!h. PE_inj (case h of PE_inj a b -> a) (case h of PE_inj a b -> b) = h`,
Cases_on `h` THEN SRW_TAC [] []);

val lem10 = Q.prove (
`!l1 l2 fn v v'. ~MEM fn (MAP FST l1) ==>
 (interp_result (eval_override (Expr_record (MAP (\z. (F_name (FST z),SND z)) (l1 ++ [(fn, v)] ++ l2)))
                               [F_name fn] [v']) Lab_nil = 
  SOME (Expr_record (MAP (\z. (F_name (FST z),SND z)) (l1 ++ [(fn, v')] ++ l2))))`,
SRW_TAC [] [eval_override_def, interp_result_def] THEN Induct_on `l1` THEN
SRW_TAC [] [do_1override_def, interp_result_def] THEN
Cases_on `do_1override (F_name fn) v' (MAP (\z. (F_name (FST z),SND z)) l1 ++ [(F_name fn,v)] ++ 
                                       MAP (\z. (F_name (FST z),SND z)) l2)` THEN
FULL_SIMP_TAC (srw_ss()) [interp_result_def]);

val lem11 = Q.prove (
`!l3 l1 l2 fn v v'. ~MEM fn (MAP FST l1) /\ LENGTH l3 >= 1 ==>
 (interp_result (eval_override (Expr_record (MAP (\z. (F_name (FST z),SND z)) (l1 ++ [(fn, v)] ++ l2)))
                               (F_name fn::MAP (\z. F_name (FST z)) l3)
                               (v'::MAP SND l3)) Lab_nil = 
  SOME (Expr_override (Expr_record (MAP (\z. (F_name (FST z),SND z)) (l1 ++ [(fn,v')] ++ l2)))
                      (MAP (\z. (F_name (FST z),SND z)) l3)))`,
Induct THEN SRW_TAC [] [] THEN Cases_on `l3` THEN FULL_SIMP_TAC list_ss [] THEN
    SRW_TAC [] [eval_override_def, interp_result_def] THEN Induct_on `l1` THEN
    SRW_TAC [] [do_1override_def, interp_result_def] THEN
    Cases_on `do_1override (F_name fn) v' (MAP (\z. (F_name (FST z),SND z)) l1 ++ [(F_name fn,v)] ++ 
                                           MAP (\z. (F_name (FST z),SND z)) l2)` THEN
    FULL_SIMP_TAC (srw_ss()) [interp_result_def] THEN
    FULL_SIMP_TAC (srw_ss()) [eval_override_def, interp_result_def, ZIP_MAP, MAP_MAP, MAP_ZIP_SAME]);

val lem12 = Q.prove (
`!l fn v x. (do_1override fn v l = SOME x) ==>
            ?r1 r2 v'. (l = r1 ++ [(fn,v')] ++ r2) /\ (x = r1 ++ [(fn,v)] ++ r2) /\ ~MEM fn (MAP FST r1)`,
Induct THEN SRW_TAC [] [do_1override_def] THEN Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss ()) [do_1override_def, COND_EXPAND_EQ] THEN SRW_TAC [] [] THENL
[Q.EXISTS_TAC `[]` THEN SRW_TAC [] [],
 RES_TAC THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `(q,r)::r1` THEN SRW_TAC [] []]);

val lem13 = Q.prove (
`!l2 l3 l e e'. (LENGTH l2 >= 2) /\
                (LENGTH l2 = LENGTH l3) /\
                (interp_result (eval_override e l2 l3) l = SOME e') ==>
                ?r1 r2 v. (e = Expr_record (r1++[(HD l2, v)]++r2)) /\
                          (e' = Expr_override (Expr_record (r1++[(HD l2, HD l3)]++r2))
                                              (ZIP (TL l2, TL l3))) /\
                          ~MEM (HD l2) (MAP FST r1) /\
                          (l = Lab_nil)`,
Induct THEN Cases_on `l3` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC list_ss [eval_override_def, interp_result_def] THEN
Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] THEN
Cases_on `t` THEN FULL_SIMP_TAC list_ss [eval_override_def] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def] THEN 
FULL_SIMP_TAC list_ss [COND_EXPAND_EQ] THEN
Cases_on `do_1override h' h l'` THEN FULL_SIMP_TAC (srw_ss ()) [interp_result_def, COND_EXPAND_EQ] THEN
SRW_TAC [] [] THEN METIS_TAC [lem12]);


val red_thm = Q.store_thm ("red_thm",
`(!e l e'. JR_expr e l e' = (interp_result (red e) l = SOME e')) /\
 (!e pack eval l e'. 
   (if is_raise e then
       (l = Lab_nil) /\ (e' = e)
    else if ~is_value_of_expr e then
       ?e1'. (e' = pack e1') /\ JR_expr e l e1'
    else   
       (interp_result (eval e) l = SOME e'))
   = 
   (interp_result (red_1 e pack eval) l = SOME e')) /\
 (!e1 e2 pack eval l e'. 
   (if is_raise e2 then
       (l = Lab_nil) /\  (e' = e2)
    else if ~is_value_of_expr e2 then
       ?e2'. (e' = pack e1 e2') /\ JR_expr e2 l e2'
    else if is_raise e1 then
       (l = Lab_nil) /\ (e' = e1)
    else if ~is_value_of_expr e1 then
       ?e1'. (e' = pack e1' e2) /\ JR_expr e1 l e1'
    else
       (interp_result (eval e1 e2) l = SOME e')) 
   =
   (interp_result (red_2 e1 e2 pack eval) l = SOME e')) /\
 (!es pack eval acc l e'.
   (case list_get_next es of
       NONE -> (interp_result (eval (REVERSE es++acc)) l = SOME e')
    || SOME (v_list, e, e_list) ->
         if is_raise e then
            (e' = e) /\ (l = Lab_nil)
         else
            ?e1'. (e' = pack (REVERSE (v_list++[e1']++e_list)++acc)) /\ JR_expr e l e1')
   =
   (interp_result (red_list es pack eval acc) l = SOME e'))`,
HO_MATCH_MP_TAC red_ind THEN REPEAT CONJ_TAC THENL
[(* Expr_uprim unary_prim *) 
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ],
 (* Expr_bprim binary_prim *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ],
 (* Expr_ident value_name *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ],
 (* Expr_constant constant *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ],
 (* Expr_typed expr typexpr *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ] THEN METIS_TAC [],
 (* Expr_tuple exprs *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ] THEN
       Cases_on `list_get_next (REVERSE exprs)` THEN 
       FULL_SIMP_TAC (srw_ss()) [get_next_NONE_thm, get_next_SOME_thm] THENL
       [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [EVERY_REVERSE] THEN SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND, is_value_of_expr_def] THEN METIS_TAC [no_value_red_thm],
        SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [lem4]],
 (* Expr_construct constr exprs *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ] THEN
       Cases_on `list_get_next (REVERSE exprs)` THEN
       FULL_SIMP_TAC (srw_ss()) [get_next_NONE_thm, get_next_SOME_thm] THENL
       [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [EVERY_REVERSE] THEN SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND, is_value_of_expr_def] THEN METIS_TAC [no_value_red_thm],
        SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [lem4]],
 (* Expr_cons e1 e2 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THEN METIS_TAC [],
 (* Expr_record field_exprs *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ] THEN
       FULL_SIMP_TAC list_ss [UNZIP_LEM] THEN SRW_TAC [] [] THEN
       Cases_on `list_get_next (REVERSE (MAP SND field_exprs))` THEN
       FULL_SIMP_TAC (srw_ss()) [get_next_NONE_thm, get_next_SOME_thm] THENL
       [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [EVERY_REVERSE] THEN SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND, is_value_of_expr_def] THEN METIS_TAC [no_value_red_thm],
        SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ] THEN EQ_TAC THEN SRW_TAC [] [] THEN
            FULL_SIMP_TAC (srw_ss()) [MAP_MAP, REVERSE_APPEND, lem2, ETA_THM] THENL
            [`~is_value_of_expr expr` by METIS_TAC [no_value_red_thm] THEN
                 `EVERY is_value_of_expr (REVERSE (MAP SND fn'_v_list))` 
                          by METIS_TAC [EVERY_MAP, EVERY_REVERSE] THEN
                 FULL_SIMP_TAC list_ss [lem3] THEN SRW_TAC [] [] THEN
                 `~is_raise e` by METIS_TAC [raise_not_JR_thm] THEN 
                 FULL_SIMP_TAC list_ss [ZIP_APPEND, ZIP_MAP, MAP_ZIP_SAME, MAP_MAP] THEN METIS_TAC [],
             `~is_value_of_expr (Expr_apply (Expr_uprim Uprim_raise) v)` 
                            by SRW_TAC [] [is_value_of_expr_def] THEN
                 `EVERY is_value_of_expr (REVERSE (MAP SND fn'_v_list))` 
                          by METIS_TAC [EVERY_MAP, EVERY_REVERSE] THEN
                 FULL_SIMP_TAC list_ss [lem3] THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [is_raise_def] THEN
                 METIS_TAC [],
             Cases_on `is_raise e` THEN 
                 FULL_SIMP_TAC list_ss [REVERSE_EQ_SYM, ZIP_LEM, REVERSE_APPEND, lem2] THENL
                 [FULL_SIMP_TAC list_ss [raise_cases] THEN DISJ2_TAC THEN
                      MAP_EVERY Q.EXISTS_TAC [`ZIP (MAP field_to_fn l3',REVERSE v_list)`,
                                              `ZIP (MAP field_to_fn l2',REVERSE e_list)`,
                                              `field_to_fn x'`,
                                              `v`] THEN 
                      SRW_TAC [] [ZIP_MAP, MAP_MAP, field_to_fn_thm, MAP_I, EVERY_MAP] THEN
                      FULL_SIMP_TAC list_ss [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN
                      SRW_TAC [] [GSYM EVERY_MAP, MAP_SND_ZIP, EVERY_REVERSE],
                  DISJ1_TAC THEN
                      MAP_EVERY Q.EXISTS_TAC [`ZIP (MAP field_to_fn l3',REVERSE v_list)`,
                                              `ZIP (MAP field_to_fn l2',REVERSE e_list)`,
                                              `field_to_fn x'`,
                                              `e`] THEN
                      RES_TAC THEN Q.EXISTS_TAC `e1'` THEN SRW_TAC [] [] THEN
                      SRW_TAC [] [ZIP_MAP, MAP_MAP, field_to_fn_thm, MAP_I, EVERY_MAP, MAP_FST_ZIP,
                                  ZIP_APPEND] THEN
                      SRW_TAC [] [GSYM EVERY_MAP, MAP_SND_ZIP, EVERY_REVERSE]]]],
 (* Expr_override e field_exprs *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THENL
       [EQ_TAC THEN SRW_TAC [] [] THEN Q.EXISTS_TAC `MAP (\x. (field_to_fn (FST x), SND x)) field_exprs` THEN
            SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I],
        EQ_TAC THEN SRW_TAC [] [] THENL
            [METIS_TAC [],
             FULL_SIMP_TAC (srw_ss()) [interp_map_thm, is_value_of_expr_def, o_DEF, EXISTS_MAP] THEN 
                 FULL_SIMP_TAC list_ss [EXISTS_MEM, EVERY_MEM] THEN METIS_TAC [],
             FULL_SIMP_TAC (srw_ss()) [interp_map_thm, is_value_of_expr_def, o_DEF, EXISTS_MAP] THEN 
                 FULL_SIMP_TAC list_ss [EXISTS_MEM, EVERY_MEM] THEN METIS_TAC [],
             DISJ1_TAC THEN Q.EXISTS_TAC `MAP (\x. (field_to_fn (FST x), SND x)) field_exprs` THEN
                 SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I]],
        FULL_SIMP_TAC (srw_ss()) [UNZIP_LEM, is_value_of_expr_def, GSYM raise_cases] THEN SRW_TAC [] [] THEN
            Cases_on `list_get_next (REVERSE (MAP SND field_exprs))` THEN
            FULL_SIMP_TAC (srw_ss()) [get_next_NONE_thm, get_next_SOME_thm] THEN
            `~is_raise e` by METIS_TAC [raise_cases] THENL
            [EQ_TAC THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_REVERSE, is_value_of_expr_def] THENL
                 [METIS_TAC [no_value_red_thm],
                  `~MEM field_name (MAP FST fn_v_list)` by FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
                      FULL_SIMP_TAC list_ss [MAP_MAP] THEN IMP_RES_TAC lem11 THEN FULL_SIMP_TAC list_ss [] THEN 
                      METIS_TAC [],
                      `~MEM field_name (MAP FST fn_v_list)` by FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
                          IMP_RES_TAC lem10 THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC [],
                      RES_TAC THEN Cases_on `field_exprs` THEN1 
                          FULL_SIMP_TAC list_ss [eval_override_def, interp_result_def] THEN
                          Cases_on `t` THEN FULL_SIMP_TAC list_ss [] THEN NTAC 3 DISJ2_TAC THENL
                          [FULL_SIMP_TAC list_ss [eval_override_def] THEN
                               Cases_on `e` THEN FULL_SIMP_TAC (srw_ss ()) [interp_result_def] THEN 
                               Cases_on `do_1override (FST h) (SND h) l'` THEN
                               FULL_SIMP_TAC list_ss [interp_result_def, COND_EXPAND_EQ] THEN SRW_TAC [] [] THEN
                               IMP_RES_TAC lem12 THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
                               MAP_EVERY Q.EXISTS_TAC [`MAP (\x. (field_to_fn (FST x), SND x)) r2`,
                                                       `MAP (\x. (field_to_fn (FST x), SND x)) r1`,
                                                       `field_to_fn (FST h)`,
                                                       `v'`,
                                                       `SND h`] THEN
                                   SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I, ZIP_MAP, MAP_ZIP_SAME, 
                                               EVERY_MAP] THEN
                                   FULL_SIMP_TAC list_ss [is_value_of_expr_def, EVERY_MAP, LAMBDA_PROD2] THEN
                                   SRW_TAC [] [MEM_MAP, field_to_fn_11] THEN FULL_SIMP_TAC list_ss [MEM_MAP],
                              IMP_RES_TAC lem13 THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN
                                  MAP_EVERY Q.EXISTS_TAC [`MAP (\x. (field_to_fn (FST x), SND x)) (h'::t')`,
                                                          `MAP (\x. (field_to_fn (FST x), SND x)) r2`,
                                                          `MAP (\x. (field_to_fn (FST x), SND x)) r1`,
                                                          `field_to_fn (FST h)`,
                                                          `v`,
                                                          `SND h`] THEN
                                  SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I, ZIP_MAP, MAP_ZIP_SAME, 
                                              EVERY_MAP] THEN
                                  FULL_SIMP_TAC list_ss [is_value_of_expr_def, EVERY_MAP, LAMBDA_PROD2] THEN
                                  SRW_TAC [] [MEM_MAP, field_to_fn_11] THEN FULL_SIMP_TAC list_ss [MEM_MAP]]],
             SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ] THEN EQ_TAC THEN SRW_TAC [] [] THEN
                 FULL_SIMP_TAC (srw_ss()) [MAP_MAP, REVERSE_APPEND, lem2, ETA_THM] THENL
                 [`~is_value_of_expr e''' /\ ~is_raise e'''`
                                       by METIS_TAC [no_value_red_thm, raise_not_JR_thm] THEN
                      `EVERY is_value_of_expr (REVERSE (MAP SND fn'_v_list))` 
                                   by METIS_TAC [EVERY_MAP, EVERY_REVERSE] THEN
                      FULL_SIMP_TAC list_ss [lem3] THEN SRW_TAC [] [] THEN
                      FULL_SIMP_TAC list_ss [ZIP_APPEND, ZIP_MAP, MAP_ZIP_SAME, MAP_MAP] THEN METIS_TAC [],
                  `~is_value_of_expr (Expr_apply (Expr_uprim Uprim_raise) v)` 
                                   by SRW_TAC [] [is_value_of_expr_def] THEN
                      `EVERY is_value_of_expr (REVERSE (MAP SND fn'_v_list))` 
                                   by METIS_TAC [EVERY_MAP, EVERY_REVERSE] THEN
                      FULL_SIMP_TAC list_ss [lem3] THEN SRW_TAC [] [] THEN 
                      FULL_SIMP_TAC list_ss [is_raise_def] THEN METIS_TAC [],
                  METIS_TAC [EVERY_MAP, EVERY_APPEND, EVERY_REVERSE, EVERY_DEF],
                  METIS_TAC [EVERY_MAP, EVERY_APPEND, EVERY_REVERSE, EVERY_DEF],
             Cases_on `is_raise e''` THEN 
                 FULL_SIMP_TAC list_ss [REVERSE_EQ_SYM, ZIP_LEM, REVERSE_APPEND, lem2] THENL
                 [FULL_SIMP_TAC list_ss [raise_cases] THEN DISJ2_TAC THEN DISJ1_TAC THEN
                      MAP_EVERY Q.EXISTS_TAC [`ZIP (MAP field_to_fn l3',REVERSE v_list)`,
                                              `ZIP (MAP field_to_fn l2',REVERSE e_list)`,
                                              `field_to_fn x'`,
                                              `v`] THEN 
                      SRW_TAC [] [ZIP_MAP, MAP_MAP, field_to_fn_thm, MAP_I, EVERY_MAP] THEN
                      FULL_SIMP_TAC list_ss [] THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN
                      SRW_TAC [] [GSYM EVERY_MAP, MAP_SND_ZIP, EVERY_REVERSE],
                  DISJ1_TAC THEN
                      MAP_EVERY Q.EXISTS_TAC [`ZIP (MAP field_to_fn l3',REVERSE v_list)`,
                                              `ZIP (MAP field_to_fn l2',REVERSE e_list)`,
                                              `field_to_fn x'`,
                                              `e''`] THEN
                      RES_TAC THEN Q.EXISTS_TAC `e1'` THEN SRW_TAC [] [] THEN
                      SRW_TAC [] [ZIP_MAP, MAP_MAP, field_to_fn_thm, MAP_I, EVERY_MAP, MAP_FST_ZIP,
                                  ZIP_APPEND] THEN
                      SRW_TAC [] [GSYM EVERY_MAP, MAP_SND_ZIP, EVERY_REVERSE]]]]],
 (* Expr_apply e1 e2 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THENL
      [METIS_TAC [],
       METIS_TAC [],
       METIS_TAC [],
       METIS_TAC [is_value_of_expr_def],
       FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [eval_apply_def] THEN Cases_on `e1` THEN 
             FULL_SIMP_TAC (srw_ss()) [interp_result_def, lem1, is_value_of_expr_def, COND_EXPAND_EQ] THEN
             METIS_TAC [uprim_red_thm, bprim_red_thm]],
 (* Expr_and expr1 expr2 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ] THEN METIS_TAC [],
 (* Expr_or expr1 expr2 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ] THEN METIS_TAC [],
 (* Expr_field e field *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THEN Cases_on `field` THEN SRW_TAC [] [] THENL
       [METIS_TAC [],
        FULL_SIMP_TAC (srw_ss()) [interp_map_thm] THEN EQ_TAC THEN SRW_TAC [] [] THEN
                  FULL_SIMP_TAC list_ss [is_value_of_expr_def, EXISTS_MAP] THEN 
                  METIS_TAC [EVERY_NOT_EXISTS],
        SRW_TAC [] [eval_field_def] THEN
              Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, is_value_of_expr_def] THEN
              Cases_on `list_assoc (F_name f') l'` THEN SRW_TAC [] [interp_result_def] THENL
              [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN IMP_RES_TAC list_assoc_not_mem THEN
                   FULL_SIMP_TAC list_ss [] THEN METIS_TAC [],
               FULL_SIMP_TAC list_ss [list_assoc_split] THEN SRW_TAC [] [] THEN
                   EQ_TAC THEN SRW_TAC [] [] THENL
                   [`~MEM (F_name f') (MAP (\z. F_name (FST z)) fn_v_list)` by 
                        FULL_SIMP_TAC (srw_ss ()) [MEM_MAP] THEN
                        METIS_TAC [lem5],
                    MAP_EVERY Q.EXISTS_TAC [`MAP (\z. (field_to_fn (FST z), SND z)) l2`,
                                            `MAP (\z. (field_to_fn (FST z), SND z)) l1`] THEN
                        SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I, lem2, EVERY_MAP] THEN 
                        FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND, LAMBDA_PROD2, MEM_MAP, EVERY_MAP, 
                                                  EVERY_MEM] THEN
                        METIS_TAC [field_to_fn_def, field_to_fn_thm]]]],
 (* Expr_ifthenelse e expr2 expr3 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THENL
      [METIS_TAC [],
       METIS_TAC [is_value_of_expr_def],
       SRW_TAC [] [eval_ite_def, interp_result_def, COND_EXPAND_EQ] THEN METIS_TAC []],
 (* Expr_while expr1 expr2 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, eval_while_def] THEN METIS_TAC [],
 (* Expr_for value_name e2 for_dirn e1 expr3 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THENL
      [METIS_TAC [],
       METIS_TAC [is_value_of_expr_def],
       METIS_TAC [],
       METIS_TAC [is_value_of_expr_def],
       FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [eval_for_def] THEN 
             Cases_on `e2` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, lem1, is_value_of_expr_def] THEN
             Cases_on `c` THEN SRW_TAC [] [interp_result_def, lem1] THEN
             Cases_on `e1` THEN FULL_SIMP_TAC (srw_ss()) [interp_result_def, lem1, is_value_of_expr_def] THEN
             Cases_on `c` THEN SRW_TAC [] [interp_result_def, lem1] THEN
             Cases_on `for_dirn` THEN SRW_TAC [] [interp_result_def] THEN 
             FULL_SIMP_TAC list_ss [WORD_GREATER] THEN
             METIS_TAC [WORD_LESS_OR_EQ, WORD_LESS_ANTISYM, WORD_LESS_EQ_CASES]], 
 (* Expr_sequence e expr2 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THEN METIS_TAC [],
 (* Expr_match e pattern_matching *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THENL
       [METIS_TAC [],
        METIS_TAC [is_value_of_expr_def],
        Cases_on `pattern_matching` THEN Cases_on `l'` THEN
            FULL_SIMP_TAC (srw_ss()) [JRmatching_step_cases, JRmatching_success_cases, JM_matchP_thm, 
                                      eval_match_def, interp_result_def] THEN1 METIS_TAC [] THEN
            Cases_on `h` THEN Cases_on `t` THEN SRW_TAC [] [eval_match_def, interp_result_def, match_thm] THEN
            Cases_on `pat_match p' e` THEN SRW_TAC [] [lem7, lem8, lem9, MAP_MAP, MAP_I] THENL
            [METIS_TAC [],
             METIS_TAC [pat_match_is_val_thm, EVERY_MAP],
             SRW_TAC [ARITH_ss] [] THEN METIS_TAC [],
             METIS_TAC [pat_match_is_val_thm, EVERY_MAP]]],
 (* Expr_function pattern_matching *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ],
 (* Expr_try e pattern_matching *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases, interp_map_thm] THENL
       [SRW_TAC [] [eval_try_def, interp_result_def] THEN Cases_on `pattern_matching` THEN 
                SRW_TAC [] [interp_result_def] THEN EQ_TAC THEN SRW_TAC [] [] THEN 
                FULL_SIMP_TAC (srw_ss()) [is_value_of_expr_def], 
        METIS_TAC [],
        METIS_TAC []],
 (* Expr_let (LB_simple pattern e) expr2 *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THENL
       [METIS_TAC [],
        METIS_TAC [],
        SRW_TAC [] [eval_let_def, interp_result_def, JM_matchP_thm, match_thm] THEN
            Cases_on `pat_match pattern e` THEN SRW_TAC [] [] THEN
             METIS_TAC [pat_match_is_val_thm, EVERY_MAP]],
 (* Expr_letrec letrec_bindings expr *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, eval_letrec_def] THEN EQ_TAC THEN SRW_TAC [] [] THENL
   [SRW_TAC [] [lrbs_to_lrblist_def, MAP_MAP] THEN
        MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) THEN
        SRW_TAC [] [MAP_EQ] THEN FULL_SIMP_TAC list_ss [EVERY_MEM],
    Q.EXISTS_TAC `MAP (\lb. case lb of LRB_simple vn pm -> (vn,recfun letrec_bindings pm, pm))
                      (lrbs_to_lrblist letrec_bindings)` THEN 
        SRW_TAC [] [MAP_MAP, EVERY_MAP, lem6] THENL
        [Cases_on `letrec_bindings` THEN SRW_TAC [] [lrbs_to_lrblist_def] THEN
             Induct_on `l'` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `h` THEN
             SRW_TAC [] [],
        MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) THEN
             SRW_TAC [] [MAP_EQ] THEN Cases_on `lb` THEN SRW_TAC [] [],
        SRW_TAC [] [EVERY_MEM] THEN Cases_on `lb` THEN SRW_TAC [] [] THEN
             MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) THEN
             Cases_on `letrec_bindings` THEN SRW_TAC [] [lrbs_to_lrblist_def] THEN 
             POP_ASSUM (K ALL_TAC) THEN Induct_on `l'` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [] THEN                  Cases_on `h` THEN SRW_TAC [] []]],
 (* Expr_assert e *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ, raise_not_JR_thm, value_not_raise_thm,
               no_value_red_thm, raise_cases] THENL
       [METIS_TAC [],
        METIS_TAC [is_value_of_expr_def],
        SRW_TAC [] [eval_assert_def, interp_result_def, COND_EXPAND_EQ] THEN METIS_TAC []],
 (* Expr_location location *)
   SRW_TAC [] [red_def, interp_result_def, JR_expr_fun, COND_EXPAND_EQ],
 (* red_1 *)
   SRW_TAC [] [red_def, interp_result_def, COND_EXPAND_EQ, interp_map_thm] THEN METIS_TAC [],
 (* red_2 *)
   SRW_TAC [] [red_def, interp_result_def, COND_EXPAND_EQ, interp_map_thm] THEN METIS_TAC [],
 (* red_list *)
   SRW_TAC [] [red_def, interp_result_def, COND_EXPAND_EQ, interp_map_thm, LET_THM, list_get_next_def],
 (* red_list *)
   SRW_TAC [] [red_def, interp_result_def, COND_EXPAND_EQ, interp_map_thm, LET_THM, list_get_next_def] THENL
       [METIS_TAC [],
        METIS_TAC [],
        METIS_TAC [value_not_raise_thm],
        Cases_on `list_get_next es` THEN FULL_SIMP_TAC (srw_ss()) [lem2] THEN
             Cases_on `x` THEN Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [lem2]]]
);


val _ = export_theory ();

