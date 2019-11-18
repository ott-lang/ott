open HolKernel boolLib Parse bossLib pairTheory optionTheory stringTheory;

val _ = new_theory "ott";

val list_minus_def = Define
`(list_minus [] ys = [])  /\
 (list_minus (x::xs) ys = (if ~(MEM x ys) then x::(list_minus xs ys) else list_minus xs ys))`;

val list_minus_thm = Q.store_thm ("list_minus_thm",
`!l x. MEM x (list_minus l l') = (MEM x l /\ ~MEM x l')`,
Induct THEN RW_TAC list_ss [list_minus_def] THEN METIS_TAC []);

val list_minus_append = Q.store_thm ("list_minus_append",
`!l1 l2 l3. list_minus (l1++l2) l3 = list_minus l1 l3 ++ list_minus l2 l3`,
Induct THEN RW_TAC list_ss [list_minus_def]);

val list_assoc_def = Define
`(list_assoc x [] = NONE)  /\
 (list_assoc x ((x',y')::xys) = (if x=x' then SOME y' else list_assoc x xys))`;

val list_assoc_mem = Q.store_thm ("list_assoc_mem",
`!l x y. (list_assoc x l = SOME y) ==> MEM (x,y) l`,
Induct THEN RW_TAC list_ss [list_assoc_def] THEN
Cases_on `h` THEN RW_TAC list_ss [list_assoc_def] THEN
Cases_on `x = q` THEN FULL_SIMP_TAC list_ss [list_assoc_def]);

val list_assoc_not_mem = Q.store_thm ("list_assoc_not_mem",
`!l x y. (list_assoc x l = NONE) ==> ~MEM (x,y) l`,
Induct THEN FULL_SIMP_TAC list_ss [list_assoc_def] THEN Cases_on `h` THEN RW_TAC list_ss [list_assoc_def]);

val list_assoc_split = Q.store_thm ("list_assoc_split",
`!l x y. (list_assoc x l = SOME y) = ?l1 l2. (l = l1++(x,y)::l2) /\ ~MEM x (MAP FST l1)`,
Induct THEN RW_TAC list_ss [list_assoc_def] THEN Cases_on `h` THEN RW_TAC list_ss [list_assoc_def] THEN
EQ_TAC THEN RW_TAC list_ss [] THENL
[MAP_EVERY Q.EXISTS_TAC [`[]`, `l`] THEN RW_TAC list_ss [],
 Cases_on `l1` THEN FULL_SIMP_TAC list_ss [] THEN RW_TAC list_ss [] THEN FULL_SIMP_TAC list_ss [],
 MAP_EVERY Q.EXISTS_TAC [`(q,r)::l1`, `l2`] THEN RW_TAC list_ss [],
 Cases_on `l1` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []]);

val list_assoc_append = Q.store_thm ("list_assoc_append",
`!l1 l2 x. list_assoc x (l1++l2) =
              case list_assoc x l1 of
                 SOME y => SOME y
               | NONE => list_assoc x l2`,
Induct THEN RW_TAC list_ss [list_assoc_def] THEN Cases_on `h` THEN RW_TAC list_ss [list_assoc_def]);

val mem_list_assoc = Q.store_thm ("mem_list_assoc",
`!l x. MEM x (MAP FST l) ==> ?y. list_assoc x l = SOME y`,
Induct THEN RW_TAC list_ss [list_assoc_def] THEN Cases_on `h` THEN RW_TAC list_ss [list_assoc_def]);

val not_mem_list_assoc = Q.store_thm ("not_mem_list_assoc",
`!l x. ~MEM x (MAP FST l) ==> (list_assoc x l = NONE)`,
Induct THEN RW_TAC list_ss [list_assoc_def] THEN Cases_on `h` THEN RW_TAC list_ss [list_assoc_def] THEN
METIS_TAC [FST]);

val list_assoc_distinct_reverse = Q.store_thm ("list_assoc_distinct_reverse",
`!l. ALL_DISTINCT (MAP FST l) ==> !x. list_assoc x (REVERSE l) = list_assoc x l`,
Induct THEN RW_TAC list_ss [list_assoc_def, list_assoc_append] THEN Cases_on `h` THEN
RW_TAC list_ss [list_assoc_def] THEN FULL_SIMP_TAC list_ss [] THENL
[METIS_TAC [not_mem_list_assoc, option_case_def],
 Cases_on `list_assoc x l` THEN RW_TAC list_ss []]);

val list_assoc_map = Q.store_thm ("list_assoc_map",
`!l x f. (list_assoc x (MAP (\z. (FST z, f (SND z))) l) = OPTION_MAP f (list_assoc x l))`,
Induct THEN RW_TAC list_ss [list_assoc_def] THEN Cases_on `h` THEN RW_TAC list_ss [list_assoc_def] THEN
METIS_TAC [FST]);

val mono_every_id_thm = Q.store_thm ("mono_every_id_thm",
`(!x. P x ==> Q x) ==> EVERY (\x. x) (MAP P l) ==> EVERY (\x. x) (MAP Q l)`,
Induct_on `l` THEN RW_TAC list_ss [] THEN METIS_TAC []);

val _ = IndDefLib.export_mono "mono_every_id_thm";

val filter_size = Q.store_thm ("filter_size",
`!l f size. list_size size (FILTER f l) <= list_size size l`,
Induct THEN RW_TAC list_ss [listTheory.list_size_def] THEN
Q.PAT_ASSUM `!f' size. g f' size` (STRIP_ASSUME_TAC o (Q.SPECL [`f`, `size`])) THEN
DECIDE_TAC);

val clause_name = Define `clause_name (x:string) = T`;

val _ = export_theory();
