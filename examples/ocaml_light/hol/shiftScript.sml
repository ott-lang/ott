open HolKernel boolLib bossLib IndDefLib IndDefRules listTheory optionTheory relationTheory pairTheory
open rich_listTheory combinTheory arithmeticTheory;
open ottTheory ottLib caml_typedefTheory;
open utilTheory;

val _ = new_theory "shift";

val shiftt_add_thm = Q.store_thm ("shiftt_add_thm",
`(!t. (shiftt m 0 t = t) /\
      (!x y. shiftt m (x + y) t = shiftt m x (shiftt m y t))) /\
 (!tl. (MAP (shiftt m 0) tl = tl) /\
       (!x y. (MAP (shiftt m (x + y)) tl = MAP (shiftt m x o shiftt m y) tl)))`,
Induct THEN SRW_TAC [ARITH_ss] [shiftt_def, MAP_MAP] THEN METIS_TAC []);

val shiftts_add_thm = Q.store_thm ("shiftts_add_thm",
`!ts. (shiftts m 0 ts = ts) /\
      (!x y. shiftts m (x + y) ts = shiftts m x (shiftts m y ts))`,
Cases THEN SRW_TAC [] [shiftts_def, shiftt_add_thm]);

val shifttes_add_thm = Q.store_thm ("shifttes_add_thm",
`!tes. (shifttes m 0 tes = tes) /\
       (!x y. shifttes m (x + y) tes = shifttes m x (shifttes m y tes))`,
Cases THEN SRW_TAC [] [shifttes_def, shiftt_add_thm, MAP_MAP_o]);

val shiftEB_add_thm = Q.store_thm ("shiftEB_add_thm",
`!EB. (shiftEB m 0 EB = EB) /\
      (!x y. shiftEB m (x + y) EB = shiftEB m x (shiftEB m y EB))`,
Cases THEN SRW_TAC [] [shiftEB_def, shiftt_add_thm, shifttes_add_thm, shiftts_add_thm]);

val shiftTsig_add_thm = Q.store_thm ("shiftTsig_add_thm",
`!S. (shiftTsig m 0 S = S) /\
     (!x y. shiftTsig m x (shiftTsig m y S) = shiftTsig m (x + y) S)`,
Induct THEN SRW_TAC [] [shiftTsig_def, shiftt_add_thm, MAP_MAP, LAMBDA_PROD2]);

(*
val shiftE_add_thm = Q.store_thm ("shiftE_add_thm",
`!E m. (shiftE m 0 E = E) /\
       (!x y. shiftE m (x + y) E = shiftE m x (shiftE m y E))`,
Induct THEN SRW_TAC [] [shiftE_def] THEN Cases_on `h` THEN
SRW_TAC [] [shiftEB_def, shiftE_def,  shiftt_add_thm, shifttes_add_thm, shiftts_add_thm]);
*)

val num_tv_append_thm = Q.store_thm ("num_tv_append_thm",
`!E1 E2. num_tv (E1++E2) = num_tv E1 + num_tv E2`,
Induct THEN SRW_TAC [] [num_tv_def] THEN Cases_on `h` THEN SRW_TAC [ARITH_ss] [num_tv_def]);

val shiftE_append_thm = Q.store_thm ("shiftE_append_thm",
`!E1 E2 m n. shiftE m n (E1++E2) = shiftE (m + num_tv E2) n E1 ++ shiftE m n E2`,
Induct THEN SRW_TAC [ARITH_ss] [shiftE_def, num_tv_append_thm]);

val is_src_t_shift_thm = Q.store_thm ("is_src_t_shift_thm",
`(!t. is_src_typexpr_of_typexpr t ==> !m n. (shiftt m n t = t)) /\
 (!tl. EVERY is_src_typexpr_of_typexpr tl ==> (!m n. MAP (\t. shiftt m n t) tl = tl))`,
Induct THEN SRW_TAC [] [shiftt_def, is_src_typexpr_of_typexpr_def] THEN METIS_TAC []);

val shiftt_com_lem = Q.store_thm ("shiftt_com_lem",
`(!t n m l. shiftt (m + n + l) l (shiftt m l t) = shiftt m l (shiftt (m + n) l t)) /\
 (!tl n m l. MAP (\t. shiftt (m + n + l) l (shiftt m l t)) tl = MAP (\t. shiftt m l (shiftt (m + n) l t)) tl)`,
Induct THEN SRW_TAC [] [shiftt_def, MAP_MAP, COND_EXPAND_EQ] THEN DECIDE_TAC);

val shiftts_com_lem  = Q.store_thm ("shiftts_com_lem",
`!t n m l. shiftts (m + n + l) l (shiftts m l t) = shiftts m l (shiftts (m + n) l t)`,
Cases THEN SRW_TAC [] [shiftts_def] THEN METIS_TAC [ADD_ASSOC, ADD_COMM, shiftt_com_lem]);

val shifttes_com_lem  = Q.store_thm ("shifttes_com_lem",
`!ts n m l. shifttes (m + n + l) l (shifttes m l ts) = shifttes m l (shifttes (m + n) l ts)`,
Cases THEN SRW_TAC [] [shifttes_def, shiftt_com_lem, MAP_MAP]);

val shiftEB_com_lem = Q.store_thm ("shiftEB_com_lem",
`!EB n m l. shiftEB (m + n + l) l (shiftEB m l EB) = shiftEB m l (shiftEB (m + n) l EB)`,
Cases THEN SRW_TAC [] [shiftEB_def, shifttes_com_lem, shiftts_com_lem, shiftt_com_lem]);

val subst_shiftt_com_lem = Q.store_thm ("subst_shiftt_com_lem",
`(!t substs m n. shiftt m n (substs_typevar_typexpr substs t) =
                 substs_typevar_typexpr (MAP (\(tv, t'). (tv, shiftt m n t')) substs) (shiftt m n t)) /\
 (!tl substs m n. MAP (\t. shiftt m n (substs_typevar_typexpr substs t)) tl =
                  MAP (\t. substs_typevar_typexpr (MAP (\(tv, t'). (tv, shiftt m n t')) substs) (shiftt m n t))
                      tl)`,
Induct THEN SRW_TAC [] [substs_typevar_typexpr_def, shiftt_def, MAP_MAP] THEN
Cases_on `list_assoc t substs` THEN SRW_TAC [] [LAMBDA_PROD2, shiftt_def, list_assoc_map]);

val shiftTsig_com_lem = Q.store_thm ("shiftTsig_com_lem",
`!subst n m l. shiftTsig (m + n + l) l (shiftTsig m l subst) = shiftTsig m l (shiftTsig (m + n) l subst)`,
Induct THEN SRW_TAC [] [shiftTsig_def, LAMBDA_PROD2, MAP_MAP, shiftt_com_lem]);

val shiftt_11 = Q.store_thm ("shiftt_11",
`(!r r' n. (shiftt n 1 r = shiftt n 1 r') = (r = r')) /\
 (!rl rl' n. (MAP (\r. shiftt n 1 r) rl = MAP (\r. shiftt n 1 r) rl') = (rl = rl'))`,
Induct THEN SRW_TAC [] [shiftt_def] THENL
[Cases_on `r'`,
 Cases_on `r'`,
 Cases_on `r'`,
 Cases_on `r'`,
 Cases_on `r''`,
 Cases_on `r'`,
 Cases_on `r'`,
 Cases_on `rl'`,
 Cases_on `rl'`]
 THEN FULL_SIMP_TAC list_ss [shiftt_def] THEN SRW_TAC [] [] THEN DECIDE_TAC);

val idxsubn_def = ottDefine "idxsubn"
`(idxsubn n tl (TE_var v) = TE_var v) /\
 (idxsubn n tl (TE_idxvar n' n'') =
    if n' = n then
      (if n'' < LENGTH tl then EL n'' tl else TE_constr [] TC_unit)
    else if n' < n then
      TE_idxvar n' n''
    else
      TE_idxvar (n' - 1) n'') /\
 (idxsubn n tl TE_any = TE_any) /\
 (idxsubn n tl (TE_arrow t1 t2) = TE_arrow (idxsubn n tl t1) (idxsubn n tl t2)) /\
 (idxsubn n tl (TE_tuple tl') = TE_tuple (MAP (idxsubn n tl) tl')) /\
 (idxsubn n tl (TE_constr tl' tcn) = TE_constr (MAP (idxsubn n tl) tl') tcn)`;

val idxsubnts_def = Define
`idxsubnts n tl (TS_forall t) = TS_forall (idxsubn (n+1) (MAP (shiftt 0 1) tl) t)`;

val idxsubntes_def = Define
`idxsubntes n tl (typexprs_inj tes) = typexprs_inj (MAP (idxsubn n tl) tes)`;

val idxsubnEB_def = Define
`(idxsubnEB n tl EB_tv = EB_tv) /\
 (idxsubnEB n tl (EB_vn vn ts) = EB_vn vn (idxsubnts n tl ts)) /\
 (idxsubnEB n tl (EB_cc cn tc) = EB_cc cn tc) /\
 (idxsubnEB n tl (EB_pc cn tpo tes tc) = EB_pc cn tpo (idxsubntes n tl tes) tc) /\
 (idxsubnEB n tl (EB_fn fn tpo tcn t) = EB_fn fn tpo tcn (idxsubn n tl t)) /\
 (idxsubnEB n tl (EB_td tcn k) = EB_td tcn k) /\
 (idxsubnEB n tl (EB_tr tcn k fnl) = EB_tr tcn k fnl) /\
 (idxsubnEB n tl (EB_ta tpo tcn t) = EB_ta tpo tcn (idxsubn n tl t)) /\
 (idxsubnEB n tl (EB_l l t) = EB_l l (idxsubn n tl t))`;

val idxsubnE_def = Define
`(idxsubnE n tl [] = []) /\
 (idxsubnE n tl (EB::E) = idxsubnEB (n + num_tv E) (MAP (shiftt 0 (n + num_tv E)) tl) EB::idxsubnE n tl E)`;

val sub_shiftt_thm = Q.store_thm ("sub_shiftt_thm",
`(!t n m tl. idxsubn n tl (shiftt n (m + 1) t) = shiftt n m t) /\
 (!tl' n m tl. MAP (\t. idxsubn n tl (shiftt n (m + 1) t)) tl' = MAP (shiftt n m) tl')`,
Induct THEN SRW_TAC [ARITH_ss] [shiftt_def, idxsubn_def, MAP_MAP] THEN METIS_TAC []);

val sub_shiftt_thm2 = Q.store_thm ("sub_shiftt_thm2",
`(!t n m tl. idxsubn n tl (shiftt n 1 t) = t) /\
 (!tl' n m tl. MAP (\t. idxsubn n tl (shiftt n 1 t)) tl' = tl')`,
Induct THEN SRW_TAC [ARITH_ss] [shiftt_def, idxsubn_def, MAP_MAP]);

val sub_shifttes_thm = Q.store_thm ("sub_shifttes_thm",
`!tes n tl. idxsubntes n tl (shifttes n 1 tes) = tes`,
Cases THEN SRW_TAC [ARITH_ss] [idxsubntes_def, shifttes_def, sub_shiftt_thm2, MAP_MAP, MAP_I]);

val sub_shiftts_thm = Q.store_thm ("sub_shiftts_thm",
`!ts n tl. idxsubnts n tl (shiftts n 1 ts) = ts`,
Cases THEN SRW_TAC [] [idxsubnts_def, shiftts_def, sub_shiftt_thm2]);

val sub_shiftEB_thm = Q.store_thm ("sub_shiftEB_thm",
`!EB n tl. idxsubnEB n tl (shiftEB n 1 EB) = EB`,
Cases THEN SRW_TAC [] [idxsubnEB_def, shiftEB_def, sub_shiftt_thm2, sub_shifttes_thm, sub_shiftts_thm]);

val idxsubnE_num_tv_thm = Q.store_thm ("idxsubnE_num_tv_thm",
`!E n tl. num_tv (idxsubnE n tl E) = num_tv E`,
Induct THEN SRW_TAC [] [num_tv_def, idxsubnE_def] THEN Cases_on `h` THEN 
SRW_TAC [] [num_tv_def, idxsubnE_def, idxsubnEB_def]);

local

val lem1 = Q.prove (
`(!t. (ftv_typexpr t = []) ==> (substs_typevar_typexpr substs t = t)) /\
 (!tl. EVERY (\t. ftv_typexpr t = []) tl ==> (MAP (substs_typevar_typexpr substs) tl = tl))`,
Induct THEN SRW_TAC [] [ftv_typexpr_def, substs_typevar_typexpr_def, FLAT_EQ_EMPTY, EVERY_MAP] THEN
METIS_TAC []);

in

val idxsubn_subst_com_lem = Q.store_thm ("idxsubn_subst_com_lem",
`(!t substs n tl. EVERY (\t. ftv_typexpr t = []) tl ==>
                  (idxsubn n tl (substs_typevar_typexpr substs t) =
                   substs_typevar_typexpr (MAP (\(tv, t'). (tv, idxsubn n tl t')) substs) (idxsubn n tl t))) /\
 (!tl substs n tl'. EVERY (\t. ftv_typexpr t = []) tl' ==>
                    (MAP (\t. idxsubn n tl' (substs_typevar_typexpr substs t)) tl =
           MAP (\t. substs_typevar_typexpr (MAP (\(tv, t'). (tv, idxsubn n tl' t')) substs) (idxsubn n tl' t))
                      tl))`,
Induct THEN SRW_TAC [] [ftv_typexpr_def, idxsubn_def, substs_typevar_typexpr_def, MAP_MAP] THENL
[Cases_on `list_assoc t substs` THEN SRW_TAC [] [list_assoc_map, idxsubn_def, LAMBDA_PROD2],
 FULL_SIMP_TAC list_ss [EVERY_EL] THEN METIS_TAC [lem1]]);

end;

val src_t_idxsubn_thm = Q.store_thm ("src_t_idxsubn_thm",
`(!t x y. is_src_typexpr_of_typexpr t ==> (idxsubn x y t = t)) /\
 (!tl x y. EVERY is_src_typexpr_of_typexpr tl ==> (MAP (idxsubn x y) tl = tl))`,
Induct THEN SRW_TAC [] [idxsubn_def, is_src_typexpr_of_typexpr_def] THEN METIS_TAC []);

val idxsubnE_append_thm = Q.store_thm ("idxsubnE_append_thm",
`!E1 E2 n tl. idxsubnE n tl (E1++E2) = idxsubnE (num_tv E2 + n) tl E1 ++ idxsubnE n tl E2`,
Induct THEN SRW_TAC [ARITH_ss] [idxsubnE_def, num_tv_def, num_tv_append_thm]);

val shift_idxsubn_com_thm = Q.store_thm ("shift_idxsubn_com_thm",
`(!t y z tl. shiftt 0 y (idxsubn z tl t) = idxsubn (y + z) (MAP (shiftt 0 y) tl) (shiftt 0 y t)) /\
 (!tl' y z tl. MAP (\t. shiftt 0 y (idxsubn z tl t)) tl' =
                   MAP (\t. idxsubn (y + z) (MAP (shiftt 0 y) tl) (shiftt 0 y t)) tl')`,
Induct THEN SRW_TAC [ARITH_ss] [idxsubn_def, shiftt_def, EL_MAP, COND_EXPAND_EQ, MAP_MAP]);

val no_num_tv_thm = Q.store_thm ("no_num_tv_thm",
`!E. ~MEM EB_tv E ==> (num_tv E = 0)`,
Induct THEN SRW_TAC [] [num_tv_def] THEN Cases_on `h` THEN SRW_TAC [] [num_tv_def]);

val _ = export_theory();
