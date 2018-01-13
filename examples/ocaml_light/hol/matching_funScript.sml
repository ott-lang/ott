open bossLib HolKernel boolLib listTheory rich_listTheory optionTheory combinTheory arithmeticTheory pairTheory;
open sortingTheory wordsTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory basicTheory;

val _ = new_theory "matching_fun";

val ALL_DISTINCT_MAP = Q.prove (
`!l f. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT l`,
Induct THEN SRW_TAC [] [MEM_MAP] THEN METIS_TAC []);

val list_assoc_MAP_11 = Q.prove (
`!l f k. (!x x'. (f x = f x') = (x = x')) ==>
         (list_assoc (f k) (MAP (\x. (f (FST x), SND x)) l) = list_assoc k l)`,
Induct THEN SRW_TAC [] [list_assoc_def] THEN Cases_on `h` THEN SRW_TAC [] [list_assoc_def] THEN
FULL_SIMP_TAC list_ss []);

val MEM_SPLIT = Q.prove (
`!x l. MEM x l = ?l1 l2. l = l1++x::l2`,
Induct_on `l` THEN SRW_TAC [] [] THEN EQ_TAC THEN SRW_TAC [] [] THENL
[METIS_TAC [APPEND],
 METIS_TAC [APPEND],
 Cases_on `l1` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []]);

val pat_match_def = tDefine "pat_match"
`(pat_match (P_var vn) e = SOME [(vn, e)]) /\
 (pat_match P_any e = SOME []) /\
 (pat_match (P_constant constant) e = 
    if (e = Expr_constant constant) then
       SOME []
    else
       NONE) /\
 (pat_match (P_alias pat vn) e = 
    OPTION_MAP (\s. s++[(vn, e)]) (pat_match pat e)) /\
 (pat_match (P_typed pat t) e = pat_match pat e) /\
 (pat_match (P_or pat1 pat2) e = 
    case pat_match pat1 e of
       SOME s -> SOME s
    || NONE -> pat_match pat2 e) /\
 (pat_match (P_construct c plist) e =
    case e of
       Expr_construct c' elist -> 
         if ~(c' = c) then
            NONE
         else
            pat_match_list plist elist 
    || _ -> NONE) /\
 (pat_match (P_construct_any c) e = 
    case e of
       Expr_construct c' elist ->
         if (c = c') then
            SOME []
         else
            NONE
    || _ -> NONE) /\
 (pat_match (P_tuple plist) e =
    case e of
       Expr_tuple elist ->
         pat_match_list plist elist 
    || _ -> NONE) /\
 (pat_match (P_record fplist) e = 
    case e of 
       Expr_record felist -> 
         if ~ALL_DISTINCT (MAP FST felist) \/ ~(ALL_DISTINCT (MAP FST fplist)) then
            NONE
         else
            pat_match_rec_list fplist felist 
    || _ -> NONE) /\
 (pat_match (P_cons pat1 pat2) e =
    case e of
       Expr_cons e1 e2 ->
          (case pat_match pat1 e1 of
              SOME s1 ->
                (case pat_match pat2 e2 of
                    SOME s2 -> SOME (s1++s2)
                 || NONE -> NONE)
           || NONE -> NONE)
    || _ -> NONE) /\

 (pat_match_list [] [] = SOME []) /\
 (pat_match_list (p::plist) (e::elist) = 
    case pat_match p e of
       SOME s1 ->
         (case pat_match_list plist elist of
             SOME s2 -> SOME (s1++s2)
          || NONE -> NONE)
    || NONE -> NONE) /\
 (pat_match_list _ _ = NONE) /\

 (pat_match_rec_list [] _ = SOME []) /\
 (pat_match_rec_list ((f, p)::fplist) felist =
    case list_assoc f felist of
       SOME e -> 
         (case pat_match p e of
             SOME s1 -> 
               (case pat_match_rec_list fplist felist of
                   SOME s2 -> SOME (s1++s2)
                || NONE -> NONE)
          || NONE -> NONE)
    || NONE -> NONE)`
  (WF_REL_TAC `measure (sum_case (pattern_size o FST)
                       (sum_case (pattern1_size o FST)
                                 (pattern2_size o FST)))`);

val pat_match_ind = fetch "-" "pat_match_ind";

val pat_match_is_val_thm = Q.store_thm ("pat_match_is_val_thm",
`(!p e s. is_value_of_expr e /\ (pat_match p e = SOME s) ==> EVERY is_value_of_expr (MAP SND s)) /\
 (!pl el s. EVERY is_value_of_expr el /\ (pat_match_list pl el = SOME s) ==>
            EVERY is_value_of_expr (MAP SND s)) /\
 (!fpl fel s. EVERY is_value_of_expr (MAP SND fel) /\ (pat_match_rec_list fpl fel = SOME s) ==>
              EVERY is_value_of_expr (MAP SND s))`,
HO_MATCH_MP_TAC pat_match_ind THEN 
SRW_TAC [] [pat_match_def, is_value_of_expr_def, EVERY_MAP] THEN
SRW_TAC [] [] THENL
[Cases_on `pat_match p e` THEN FULL_SIMP_TAC (srw_ss()) [],
 Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ, is_value_of_expr_def] THEN METIS_TAC [],
 Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ, is_value_of_expr_def] THEN METIS_TAC [EVERY_DEF],
 Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ, is_value_of_expr_def] THEN METIS_TAC [],
 Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ, is_value_of_expr_def, LAMBDA_PROD2] THEN 
        METIS_TAC [],
 Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [COND_EXPAND_EQ, is_value_of_expr_def] THEN
        Cases_on `pat_match p e'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `pat_match p' e0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [EVERY_APPEND],
 Cases_on `pat_match p e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `pat_match_list pl el` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [EVERY_APPEND],
 Cases_on `list_assoc f fel` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `pat_match p x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
        Cases_on `pat_match_rec_list fpl fel` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
        IMP_RES_TAC list_assoc_mem THEN FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [SND]]);

local

val lem1 = Q.prove (
`!s. (substs_x_xs case s of substs_x_xs l -> l) = s`,
Cases THEN SRW_TAC [] []);

val lem2 = Q.prove (
`!l1 l2 l3. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) /\ 
            EVERY (\x. JM_match (FST x) (FST (SND x)) (substs_x_xs (SND (SND x)))) (ZIP (l1,ZIP (l2,l3))) ==>
            EVERY (\x. JM_match (FST x) (FST (SND x)) (SND (SND x))) (ZIP (l1,ZIP (l2,MAP substs_x_xs l3)))`,
Induct THEN Cases_on `l2` THEN Cases_on `l3` THEN FULL_SIMP_TAC list_ss []);

val lem3 = Q.prove (
`!l. EVERY (\x. P (SND (SND (SND x))) (FST (SND x)) (FST (SND (SND x)))) l /\ MEM p l /\ 
     ALL_DISTINCT (MAP FST l) ==>
case list_assoc (FST p) (MAP (\z. (FST z,SND (SND (SND z)))) l ++ fn_v''_list) of
   NONE -> F
|| SOME e -> P e (FST (SND p)) (FST (SND (SND p)))`,
Induct THEN SRW_TAC [] [list_assoc_def] THEN FULL_SIMP_TAC list_ss [] THEN
Cases_on `list_assoc (FST h) (MAP (\z. (FST z,SND (SND (SND z)))) l ++ fn_v''_list)` THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN METIS_TAC []);

val field_to_fn_11 = Q.store_thm ("field_to_fn_11",
`!x x'. (field_to_fn x = field_to_fn x') = (x = x')`,
Cases THEN Cases THEN SRW_TAC [] [field_to_fn_def]);
 
val lem4 = Q.prove (
`!fplist slist l.
 EVERY (\z. is_value_of_expr (SND z)) l /\
 ALL_DISTINCT (MAP FST l) /\
 ALL_DISTINCT (MAP FST fplist) /\
 (LENGTH slist = LENGTH fplist) /\
 EVERY (\z. case list_assoc (FST (FST z)) l of
               NONE -> F
            || SOME e -> JM_match e (SND (FST z)) (substs_x_xs (SND z)))
       (ZIP (fplist,slist)) ==>
 ?fn_v''_list field_name'_pat_substs_x_v'_list field_name_v_list.
      (l = MAP (\z. (F_name (FST z),SND z)) field_name_v_list) /\
      (fplist =
       MAP (\z. (F_name (FST z),FST (SND z)))
         field_name'_pat_substs_x_v'_list) /\
      (FLAT slist =
       FLAT
         (MAP (\x. case x of substs_x_xs l' -> l')
            (MAP (UNCURRY (\field_name_'. UNCURRY (\pat_. FST)))
               field_name'_pat_substs_x_v'_list))) /\
      EVERY (\z. is_value_of_expr (SND z)) fn_v''_list /\
      EVERY (\z. is_value_of_expr (SND (SND (SND z))))
        field_name'_pat_substs_x_v'_list /\
      EVERY (\z. is_value_of_expr (SND z)) field_name_v_list /\
      PERM
        (MAP (\z. (FST z,SND (SND (SND z))))
           field_name'_pat_substs_x_v'_list ++ fn_v''_list)
        field_name_v_list /\
      EVERY
        (\x. JM_match (SND (SND (SND x))) (FST (SND x)) (FST (SND (SND x))))
        field_name'_pat_substs_x_v'_list /\
      ALL_DISTINCT (MAP (\z. name_fn (FST z)) field_name_v_list)`,
Induct THEN SRW_TAC [] [] THEN Cases_on `slist` THEN FULL_SIMP_TAC list_ss [] THENL
[MAP_EVERY Q.EXISTS_TAC [`MAP (\x. (field_to_fn (FST x), (SND x))) l`,
                         `MAP (\x. (field_to_fn (FST x), (SND x))) l`] THEN
     SRW_TAC [] [MAP_MAP, field_to_fn_thm, MAP_I, EVERY_MAP] THEN
     METIS_TAC [MAP_11_ALL_DISTINCT, name_11, field_to_fn_11],
 Cases_on `list_assoc (FST h) l` THEN FULL_SIMP_TAC list_ss [] THEN 
     Q.PAT_ASSUM `!slist l'. P slist l' ==> Q slist l'` (MP_TAC o Q.SPECL [`t`, `l`]) THEN 
     SRW_TAC [] [] THEN
     IMP_RES_TAC list_assoc_mem THEN FULL_SIMP_TAC list_ss [EVERY_MAP, MAP_MAP] THEN
     Cases_on `h` THEN Cases_on `q` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
     `MEM (f',x) (MAP (\z. (FST z,SND z)) field_name_v_list)` by 
                  (FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN METIS_TAC []) THEN
     FULL_SIMP_TAC (srw_ss()) [MAP_I] THEN IMP_RES_TAC PERM_MEM_EQ THEN FULL_SIMP_TAC list_ss [] THEN1
     (FULL_SIMP_TAC list_ss [MEM_MAP] THEN METIS_TAC []) THEN
     FULL_SIMP_TAC list_ss [MEM_SPLIT] THEN 
     MAP_EVERY Q.EXISTS_TAC [`l1''++l2''`, 
                             `(f', r, substs_x_xs h', x)::
                              field_name'_pat_substs_x_v'_list`,
                             `field_name_v_list`] THEN
     SRW_TAC [] [field_to_fn_thm] THEN FULL_SIMP_TAC list_ss [EVERY_MAP] THEN
     METIS_TAC [PERM_REFL, CONS_PERM, APPEND, PERM_SYM, PERM_TRANS]]);


val list_TAC = 
 Cases_on `e` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [is_value_of_expr_def, ETA_THM, ELIM_UNCURRY] THEN
     EQ_TAC THEN SRW_TAC [] [] THENL
     [FULL_SIMP_TAC list_ss [LENGTH_MAP] THEN
          Q.PAT_ASSUM `!s. f ==> ((?slist. P slist) = g)`
                (MP_TAC o GSYM o
                 Q.SPEC `FLAT (MAP (\x. case SND (SND x) of substs_x_xs l -> l)
                                   (v_pat_substs_x_list: (expr#pattern#substs_x) list))`) THEN
          SRW_TAC [] [MAP_MAP] THEN
          Q.EXISTS_TAC `MAP (\x. case SND (SND x) of substs_x_xs l -> l)
                            (v_pat_substs_x_list: (expr#pattern#substs_x) list)` THEN
          SRW_TAC [] [ZIP_MAP, LENGTH_MAP, LENGTH_ZIP, MAP_ZIP_SAME] THEN
          SRW_TAC [] [MAP_MAP, EVERY_MAP, lem1],
      RES_TAC THEN SRW_TAC [] [] THEN
          Q.EXISTS_TAC `ZIP (l,ZIP (plist,MAP substs_x_xs slist))` THEN
          SRW_TAC [] [MAP_FST_ZIP, LENGTH_ZIP, GSYM MAP_MAP, GSYM EVERY_MAP, MAP_SND_ZIP] THEN
          SRW_TAC [] [MAP_MAP, lem1, MAP_I, lem2]];

in

val match_thm = Q.store_thm ("match_thm",
`(!p e s. is_value_of_expr e ==> (JM_match e p (substs_x_xs s) = (pat_match p e = SOME s))) /\
 (!plist elist s. EVERY is_value_of_expr elist ==>
      ((LENGTH plist = LENGTH elist) /\
        (?slist. (LENGTH slist = LENGTH elist) /\ (s = FLAT slist) /\
                 EVERY (\(e, p, s). JM_match e p (substs_x_xs s)) (ZIP (elist, ZIP (plist, slist))))
       =
       (pat_match_list plist elist = SOME s))) /\
 (!fplist felist s. EVERY is_value_of_expr (MAP SND felist) ==>
      ((?slist. (LENGTH slist = LENGTH fplist) /\ (s = FLAT slist) /\
                EVERY (\((f, p), s). 
                           case list_assoc f felist of NONE -> F || SOME e -> JM_match e p (substs_x_xs s)) 
                      (ZIP (fplist, slist)))
       =
       (pat_match_rec_list fplist felist = SOME s)))`,
HO_MATCH_MP_TAC pat_match_ind THEN SRW_TAC [] [pat_match_def, JM_match_fun, is_value_of_expr_def] THEN
IMP_RES_TAC pat_match_is_val_thm THEN FULL_SIMP_TAC list_ss [EVERY_MAP] THENL
[METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 METIS_TAC [],
 SRW_TAC [] [JM_matchP_thm] THEN Cases_on `pat_match p e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [], 
 list_TAC,
 Cases_on `e` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC list_ss [is_value_of_expr_def] THEN METIS_TAC [],
 list_TAC,
 Cases_on `e` THEN SRW_TAC [] [] THENL
     [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [EVERY_MAP, MAP_MAP] THEN SRW_TAC [] [] THEN
          METIS_TAC [MAP_11_ALL_DISTINCT, name_11, field_11],
      CCONTR_TAC THEN FULL_SIMP_TAC list_ss [EVERY_MAP, MAP_MAP] THEN SRW_TAC [] [] THEN
          `PERM (MAP FST (MAP (\z. (FST z,SND (SND (SND z)))) 
                              field_name'_pat_substs_x_v'_list ++ fn_v''_list))
                (MAP FST field_name_v_list)` by METIS_TAC [PERM_MAP] THEN
          FULL_SIMP_TAC list_ss [MAP_MAP] THEN
          IMP_RES_TAC PERM_ALL_DISTINCT THEN FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND] THEN
          METIS_TAC [MAP_11_ALL_DISTINCT, name_11, field_11], 
      FULL_SIMP_TAC list_ss [is_value_of_expr_def, LAMBDA_PROD2] THEN POP_ASSUM (MP_TAC o GSYM) THEN
          SRW_TAC [] [] THEN EQ_TAC THEN SRW_TAC [] [] THENL
          [Q.EXISTS_TAC `MAP (\x. case FST (SND (SND x)) of substs_x_xs l -> l)
                             (field_name'_pat_substs_x_v'_list:(field_name#pattern#substs_x#expr) list)` THEN
               SRW_TAC [] [ELIM_UNCURRY, MAP_MAP, ZIP_MAP, MAP_ZIP_SAME] THEN
               SRW_TAC [] [EVERY_MAP, EVERY_MEM, lem1, list_assoc_MAP_11] THEN
               FULL_SIMP_TAC (srw_ss()) [MAP_MAP, MAP_11_ALL_DISTINCT, ETA_THM] THEN
               `PERM (MAP FST (MAP (\z. (FST z,SND (SND (SND z))))
                                   field_name'_pat_substs_x_v'_list ++ fn_v''_list)) 
                     (MAP FST field_name_v_list)` 
                                  by METIS_TAC [PERM_MAP] THEN
               `ALL_DISTINCT (MAP FST (MAP (\z. (FST z,SND (SND (SND z))))
                                           field_name'_pat_substs_x_v'_list ++ fn_v''_list))`
                                  by METIS_TAC [PERM_ALL_DISTINCT, MAP_MAP, FST, MAP_APPEND] THEN 
               METIS_TAC [lem3, PERM_list_assoc], 
           METIS_TAC [lem4]]],
 Cases_on `e` THEN SRW_TAC [] [] THEN Cases_on `pat_match p e'` THEN SRW_TAC [] [] THENL
     [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `substs_x1` THEN FULL_SIMP_TAC list_ss [] THEN
          METIS_TAC [],
      Cases_on `pat_match p' e0` THEN SRW_TAC [] [] THENL
          [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `substs_x2` THEN FULL_SIMP_TAC list_ss [] THEN
               METIS_TAC [],
           FULL_SIMP_TAC list_ss [is_value_of_expr_def] THEN 
               EQ_TAC THEN SRW_TAC [] [] THENL
                   [Cases_on `substs_x1` THEN Cases_on `substs_x2` THEN SRW_TAC [] [] THEN METIS_TAC [],
                    MAP_EVERY Q.EXISTS_TAC [`substs_x_xs x`, `substs_x_xs x'`] THEN SRW_TAC [] []]]],
 Cases_on `s` THEN SRW_TAC [] [] THENL 
        [Q.EXISTS_TAC `[]` THEN SRW_TAC [] [], 
         Cases_on `slist` THEN SRW_TAC [] []],
 Cases_on `pat_match p e` THEN SRW_TAC [] [] THENL
     [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN Cases_on `slist` THEN 
          FULL_SIMP_TAC list_ss [] THEN METIS_TAC [],
      Cases_on `pat_match_list plist elist` THEN SRW_TAC [] [] THENL
          [CCONTR_TAC THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `slist` THEN
               FULL_SIMP_TAC list_ss [EVERY_MEM, EXISTS_MEM] THEN METIS_TAC [],
           EQ_TAC THEN SRW_TAC [] [] THENL
               [Cases_on `slist` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC [],
                METIS_TAC [],
                POP_ASSUM (MP_TAC o Q.SPEC `x'`) THEN SRW_TAC [] [] THEN 
                    Q.EXISTS_TAC `x::slist` THEN SRW_TAC [] []]]],
 Cases_on `s` THEN SRW_TAC [] [] THENL 
        [Q.EXISTS_TAC `[]` THEN SRW_TAC [] [], 
         Cases_on `slist` THEN SRW_TAC [] []],
 Cases_on `list_assoc f felist` THEN SRW_TAC [] [] THENL
     [Cases_on `slist` THEN SRW_TAC [] [],
      Cases_on `pat_match p x` THEN SRW_TAC [] [] THENL
          [CCONTR_TAC THEN Cases_on `slist` THEN FULL_SIMP_TAC list_ss [] THEN 
               REPEAT (POP_ASSUM MP_TAC) THEN SRW_TAC [] [EVERY_MEM] THEN
               METIS_TAC [SND, list_assoc_mem],
           Cases_on `pat_match_rec_list fplist felist` THEN SRW_TAC [] [] THENL
               [CCONTR_TAC THEN Cases_on `slist` THEN FULL_SIMP_TAC list_ss [] THEN 
                    REPEAT (POP_ASSUM MP_TAC) THEN SRW_TAC [] [EVERY_MEM, o_DEF] THEN
                    METIS_TAC [],
                EQ_TAC THEN SRW_TAC [] [] THENL
                    [Cases_on `slist` THEN FULL_SIMP_TAC list_ss [] THEN
                         REPEAT (POP_ASSUM MP_TAC) THEN SRW_TAC [] [EVERY_MEM] THEN 
                         METIS_TAC [SND, list_assoc_mem],
                     POP_ASSUM (MP_TAC o Q.SPEC `x''`) THEN SRW_TAC [] [] THEN
                         Q.EXISTS_TAC `x'::slist` THEN SRW_TAC [] [] THEN
                         FULL_SIMP_TAC list_ss [EVERY_MEM] THEN METIS_TAC [SND, list_assoc_mem]]]]]]);

end;
val _ = export_theory ();
