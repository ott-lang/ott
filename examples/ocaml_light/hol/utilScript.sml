open HolKernel boolLib bossLib listTheory sortingTheory combinTheory wordsTheory pairTheory optionTheory;
open rich_listTheory;
open ottTheory;

val _ = new_theory "util";

val LAMBDA_PROD2 = Q.store_thm ("LAMBDA_PROD2",
`(\(x,y). P x y) = (\z. P (FST z) (SND z))`,
RW_TAC list_ss [FUN_EQ_THM] THEN Cases_on `z` THEN RW_TAC list_ss []);

val MAP_I = Q.store_thm ("MAP_I",
`!l. MAP (\x. x) l = l`,
Induct THEN RW_TAC list_ss []);

val MAP_MAP = save_thm ("MAP_MAP", SIMP_RULE list_ss [o_DEF] MAP_MAP_o);

val DISJOINT_def = Define
`(DISJOINT [] l = T) /\
 (DISJOINT (h::l1) l2 = ~(MEM h l2) /\ DISJOINT l1 l2)`;

val DISJOINT_RIGHT = Q.store_thm ("DISJOINT_RIGHT",
`!l1 h l2. (DISJOINT l1 [] = T) /\
           (DISJOINT l1 (h::l2) = ~(MEM h l1) /\ DISJOINT l1 l2)`,
Induct THEN RW_TAC list_ss [DISJOINT_def] THEN METIS_TAC []);

val DISJOINT_APPEND = Q.store_thm ("DISJOINT_APPEND",
`(!l1 l2 l3. DISJOINT (l1++l2) l3 = DISJOINT l1 l3 /\ DISJOINT l2 l3) /\
 (!l1 l2 l3. DISJOINT l1 (l2++l3) = DISJOINT l1 l2 /\ DISJOINT l1 l3)`,
STRIP_TAC THEN Induct THEN RW_TAC list_ss [DISJOINT_def] THEN METIS_TAC []);

val DISJOINT_MEM = Q.store_thm ("DISJOINT_MEM",
`!l1 l2. DISJOINT l1 l2 = EVERY (\y. ~MEM y l2) l1`,
Induct THEN RW_TAC list_ss [DISJOINT_def]);

val DISJOINT_REVERSE = Q.store_thm ("DISJOINT_REVERSE",
`!l1 l2. DISJOINT l1 l2 = DISJOINT (REVERSE l1) l2`,
Induct THEN RW_TAC list_ss [DISJOINT_def, DISJOINT_APPEND] THEN METIS_TAC []);

val ALL_DISTINCT_APPEND = Q.store_thm ("ALL_DISTINCT_APPEND",
`!l1 l2. ALL_DISTINCT (l1++l2) =
        ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\ DISJOINT l1 l2`,
Induct THEN RW_TAC list_ss [DISJOINT_def] THEN EQ_TAC THEN RW_TAC list_ss [EVERY_CONJ, EVERY_MEM]);

val COND_EXPAND_EQ = Q.store_thm ("COND_EXPAND_EQ",
`!b t1 t2 v. ((if b then t1 else t2) = v) = (b /\ (t1 = v)) \/ (~b /\ (t2 = v))`,
METIS_TAC []);

val MAP2_MAP = Q.store_thm ("MAP2_MAP",
`!l1 l2 f g h. (LENGTH l1 = LENGTH l2) ==>
               (MAP2 f (MAP g l1) (MAP h l2) = MAP2 (\x y. f (g x) (h y)) l1 l2)`,
Induct THEN Cases_on `l2` THEN RW_TAC list_ss []);

val MAP2_ELIM = Q.store_thm ("MAP2_ELIM",
`!l f. MAP2 (\x y. f x y) l l = MAP (\x. f x x) l`,
Induct THEN RW_TAC list_ss []);

val MAP_EQ = Q.store_thm ("MAP_EQ",
`!l f g. (MAP f l = MAP g l) = !a. MEM a l ==> (f a = g a)`,
Induct THEN RW_TAC list_ss [] THEN METIS_TAC []);

val MAP_MAP2 = Q.store_thm ("MAP_MAP2",
`!l1 l2 f g. (LENGTH l1 = LENGTH l2) ==> (MAP f (MAP2 g l1 l2) = MAP2 (\x y. f (g x y)) l1 l2)`,
Induct THEN Cases_on `l2` THEN RW_TAC list_ss []);

val MAP2_IGNORE = Q.store_thm ("MAP2_IGNORE",
`(!l1 l2 f. (LENGTH l1 = LENGTH l2) ==> (MAP2 (\x y. f x) l1 l2 = MAP f l1)) /\
 (!l1 l2 f. (LENGTH l1 = LENGTH l2) ==> (MAP2 (\x y. f y) l1 l2 = MAP f l2))`,
CONJ_TAC THEN Induct THEN Cases_on `l2` THEN RW_TAC list_ss []);

val MAP2_LENGTH = Q.store_thm ("MAP2_LENGTH",
`!l1 l2 f. (LENGTH l1 = LENGTH l2) ==> (LENGTH (MAP2 f l1 l2) = LENGTH l1)`,
Induct THEN Cases_on `l2` THEN RW_TAC list_ss []);

val EVERY_MAP2 = Q.store_thm ("EVERY_MAP2",
`!l1 l2 f g. (LENGTH l1 = LENGTH l2) ==>
             (EVERY f (MAP2 g l1 l2) = EVERY (\x. x) (MAP2 (\x y. f (g x y)) l1 l2))`,
Induct THEN Cases_on `l2` THEN RW_TAC list_ss []);

val LENGTH_NIL_ALT = Q.store_thm ("LENGTH_NIL_ALT",
`!l. (0 = LENGTH l) = (l = [])`,
METIS_TAC [LENGTH_NIL]);

val LENGTH_1 = Q.store_thm ("LENGTH_1",
`!l. (1 = LENGTH l) = (?x. l = [x])`,
Induct THEN RW_TAC list_ss [LENGTH_NIL]);

val EXTEND_PERM = Q.store_thm ("EXTEND_PERM",
`!l1 l2. PERM l1 l2 ==> !l3. (LENGTH l3 = LENGTH l1) ==>
         ?l4. (LENGTH l2 = LENGTH l4) /\ PERM l3 l4 /\ PERM (ZIP (l1, l3)) (ZIP (l2, l4))`,
HO_MATCH_MP_TAC PERM_IND THEN RW_TAC list_ss [LENGTH_NIL] THENL
[Q.EXISTS_TAC `[]` THEN RW_TAC list_ss [PERM_REFL],
 Cases_on `l3` THEN FULL_SIMP_TAC list_ss [] THEN RES_TAC THEN Q.EXISTS_TAC `h::l4` THEN
         RW_TAC list_ss [PERM_CONS_IFF],
 Cases_on `l3` THEN FULL_SIMP_TAC list_ss [] THEN Cases_on `t` THEN FULL_SIMP_TAC list_ss [] THEN
         RES_TAC THEN Q.EXISTS_TAC `h'::h::l4` THEN RW_TAC list_ss [PERM_SWAP_AT_FRONT],
 METIS_TAC [PERM_TRANS, PERM_LENGTH]]);

val PERM_MAP = Q.store_thm ("PERM_MAP",
`!l1 l2. PERM l1 l2 ==> !f. PERM (MAP f l1) (MAP f l2)`,
HO_MATCH_MP_TAC PERM_IND THEN RW_TAC list_ss [PERM_REFL, PERM_CONS_IFF, PERM_SWAP_AT_FRONT] THEN
   METIS_TAC [PERM_TRANS]);

val ZIP_MAP_ID = Q.store_thm ("ZIP_MAP_ID",
`!l. ZIP (MAP FST l, MAP SND l) = l`,
Induct THEN RW_TAC list_ss []);

val MAP3_def = Define
`(MAP3 f [] [] [] = []) /\
 (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3 :: MAP3 f t1 t2 t3)`;

val MAP_MAP3 = Q.store_thm ("MAP_MAP3",
`!l1 l2 l3 f g. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
                (MAP f (MAP3 g l1 l2 l3) = MAP3 (\x y z. f (g x y z)) l1 l2 l3)`,
Induct THEN Cases_on `l2` THEN Cases_on `l3` THEN RW_TAC list_ss [MAP3_def]);

val EVERY_MAP3 = Q.store_thm ("EVERY_MAP3",
`!l1 l2 l3 f g. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
                (EVERY f (MAP3 g l1 l2 l3) = EVERY (\x. x) (MAP3 (\x y z. f (g x y z)) l1 l2 l3))`,
Induct THEN Cases_on `l2` THEN Cases_on `l3` THEN RW_TAC list_ss [MAP3_def]);

val MAP3_IGNORE = Q.store_thm ("MAP3_IGNORE",
`(!l1 l2 l3 f. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
               (MAP3 (\x y z. f x y) l1 l2 l3 = MAP2 f l1 l2)) /\
 (!l1 l2 l3 f. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
               (MAP3 (\x y z. f y z) l1 l2 l3 = MAP2 f l2 l3)) /\
 (!l1 l2 l3 f. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
               (MAP3 (\x y z. f x z) l1 l2 l3 = MAP2 f l1 l3))`,
REPEAT CONJ_TAC THEN Induct THEN Cases_on `l2` THEN Cases_on `l3` THEN RW_TAC list_ss [MAP3_def]);


val MEM_FLAT = Q.store_thm ("MEM_FLAT",
`!l x. MEM x (FLAT l) = EXISTS (\l'. MEM x l') l`,
Induct THEN RW_TAC list_ss []);


val label_def = Define
`label x = T`;

val EXISTS_REVERSE = Q.store_thm ("EXISTS_REVERSE",
`!l P. EXISTS P (REVERSE l) = EXISTS P l`,
RW_TAC list_ss [MEM_REVERSE, EXISTS_MEM]);

val EVERY_REVERSE = Q.store_thm ("EVERY_REVERSE",
`!l P. EVERY P (REVERSE l) = EVERY P l`,
RW_TAC list_ss [MEM_REVERSE, EVERY_MEM]);

val REVERSE_EQ_SYM_IMP = Q.prove (
`!l1 l2. (REVERSE l1 = l2) ==> (l1 = REVERSE l2)`,
RW_TAC list_ss [] THEN METIS_TAC [REVERSE_REVERSE]);

val REVERSE_EQ_SYM = Q.store_thm ("REVERSE_EQ_SYM",
`!l1 l2. (REVERSE l1 = l2) = (l1 = REVERSE l2)`,
METIS_TAC [REVERSE_EQ_SYM_IMP]);

val EXISTS_FIRST_SPLIT = Q.store_thm ("EXISTS_FIRST_SPLIT",
`!l P. EXISTS P l ==> ?l1 l2 y. (l = l1 ++ [y] ++ l2) /\ ~EXISTS P l1 /\ P y`,
Induct THEN RW_TAC list_ss [] THEN FULL_SIMP_TAC list_ss [o_DEF] THENL
[MAP_EVERY Q.EXISTS_TAC [`[]`, `l`, `h`] THEN RW_TAC list_ss [],
 Cases_on `P h` THEN RW_TAC list_ss [] THEN1
             (MAP_EVERY Q.EXISTS_TAC [`[]`, `l`, `h`] THEN RW_TAC list_ss []) THEN
      RES_TAC THEN MAP_EVERY Q.EXISTS_TAC [`h::l1`, `l2`, `y`] THEN RW_TAC list_ss []]);

val EXISTS_LAST_SPLIT = Q.store_thm ("EXISTS_LAST_SPLIT",
`!l P. EXISTS P l ==> ?l1 l2 y. (l = l1 ++ [y] ++ l2) /\ ~EXISTS P l2 /\ P y`,
RW_TAC list_ss [o_DEF] THEN
`?l1 l2 y. (REVERSE l = l1 ++ [y] ++ l2) /\ ~EXISTS P l1 /\ P y` by
                 METIS_TAC [EXISTS_REVERSE, EXISTS_FIRST_SPLIT] THEN
FULL_SIMP_TAC list_ss [REVERSE_EQ_SYM, REVERSE_APPEND, o_DEF] THEN
MAP_EVERY Q.EXISTS_TAC [`REVERSE l2`, `REVERSE l1`, `y`] THEN RW_TAC list_ss [EVERY_REVERSE] THEN
METIS_TAC [APPEND, APPEND_ASSOC]);

val MAP_11_EQ = Q.store_thm ("MAP_11_EQ",
`!l1 l2 f g h. (!x x'. (f x = f x') = (x = x')) ==>
               ((MAP (\x. f (g x)) l1 = MAP (\x. f (h x)) l2) =
                (MAP (\x. g x) l1 = MAP (\x. h x) l2))`,
Induct THEN Cases_on `l2` THEN RW_TAC list_ss []);

val MAP_11_ALL_DISTINCT = Q.store_thm ("MAP_11_ALL_DISTINCT",
`!l f g. (!x x'. (f x = f x') = (x = x')) ==>
         (ALL_DISTINCT (MAP (\x. f (g x)) l) = ALL_DISTINCT (MAP g l))`,
Induct THEN RW_TAC list_ss [MEM_MAP]);

val MAP_11_ALL_DISTINCT2 = Q.store_thm ("MAP_11_ALL_DISTINCT2",
`!l f. (!x x'. (f x = f x') = (x = x')) ==>
       (ALL_DISTINCT (MAP f l) = ALL_DISTINCT l)`,
Induct THEN RW_TAC list_ss [MEM_MAP]);

val MAP_FST_SND_EQ = Q.store_thm ("MAP_FST_SND_EQ",
`!l1 l2. ((MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2)) = (l1 = l2)`,
Induct THEN Cases_on `l2` THEN RW_TAC list_ss [] THEN Cases_on `h` THEN Cases_on `h'` THEN
RW_TAC list_ss [] THEN METIS_TAC []);

val MAP_ZIP_SAME = Q.store_thm ("MAP_ZIP_SAME",
`!l f. MAP (\x. f (FST x) (SND x)) (ZIP (l, l)) = MAP (\x. f x x) l`,
Induct THEN RW_TAC list_ss []);

val PERM_ALL_DISTINCT = Q.store_thm ("PERM_ALL_DISTINCT",
`!l1 l2. PERM l1 l2 ==> (ALL_DISTINCT l1 = ALL_DISTINCT l2)`,
RW_TAC list_ss [PERM_DEF, ALL_DISTINCT_FILTER] THEN
EQ_TAC THEN RW_TAC list_ss [] THEN
`!x. MEM x (FILTER ($= x) l1) = MEM x (FILTER ($= x) l2)` by METIS_TAC [] THEN
FULL_SIMP_TAC list_ss [MEM_FILTER]);

local

val lem1 = Q.prove (
`!l1 l2. PERM l1 l2 ==>
         ALL_DISTINCT (MAP FST l1) ==>
         PERM l1 l2 /\ !x. list_assoc x l1 = list_assoc x l2`,
HO_MATCH_MP_TAC PERM_IND THEN
RW_TAC list_ss [PERM_REFL, PERM_MONO, PERM_SWAP_AT_FRONT, PERM_TRANS] THENL
[Cases_on `x` THEN RW_TAC list_ss [list_assoc_def],
 Cases_on `x` THEN Cases_on `y` THEN RW_TAC list_ss [list_assoc_def] THEN FULL_SIMP_TAC list_ss [],
 METIS_TAC [PERM_ALL_DISTINCT, PERM_MAP, PERM_TRANS],
 METIS_TAC [PERM_ALL_DISTINCT, PERM_MAP, PERM_TRANS]]);

val lem2 = Q.prove (
`!l1 l2. ALL_DISTINCT (MAP FST l1) /\ ALL_DISTINCT (MAP FST l2) /\
         (!x. list_assoc x l1 = list_assoc x l2) ==>
         PERM l1 l2`,
Induct THEN RW_TAC list_ss [list_assoc_def, PERM_CONS_EQ_APPEND] THENL
[Cases_on `l2` THEN RW_TAC list_ss [PERM_REFL] THEN Cases_on `h` THEN
               FULL_SIMP_TAC list_ss [list_assoc_def] THEN METIS_TAC [NOT_SOME_NONE],
 Cases_on `h` THEN FULL_SIMP_TAC list_ss [list_assoc_def] THEN
         `?l3 l4. (l2 = l3++(q,r)::l4) /\ ~MEM q (MAP FST l3)` by METIS_TAC [list_assoc_split] THEN
         MAP_EVERY Q.EXISTS_TAC [`l3`, `l4`] THEN RW_TAC list_ss [] THEN
         FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, DISJOINT_RIGHT, list_assoc_append, list_assoc_def] THEN
         Q.PAT_ASSUM `!l2'. P l2' ==> PERM l1 l2'` MATCH_MP_TAC THEN
         RW_TAC list_ss [ALL_DISTINCT_APPEND, list_assoc_append] THEN
         Cases_on `x = q` THEN RW_TAC list_ss [not_mem_list_assoc] THEN METIS_TAC []]);
in

val PERM_list_assoc = Q.store_thm ("PERM_list_assoc",
`!l1 l2. ALL_DISTINCT (MAP FST l1) /\ ALL_DISTINCT (MAP FST l2) ==>
         (PERM l1 l2 = (!x. list_assoc x l1 = list_assoc x l2))`,
METIS_TAC [lem1, lem2]);

end;

val MAP_split = Q.store_thm ("MAP_split",
`!l1 l2 l3 f. (l1++l2 = MAP f l3) = ?l4 l5. (l3 = l4++l5) /\ (l1 = MAP f l4) /\ (l2 = MAP f l5)`,
Induct THEN RW_TAC list_ss [] THEN Cases_on `l3` THEN RW_TAC list_ss [] THEN EQ_TAC THEN
RW_TAC list_ss [] THENL
[MAP_EVERY Q.EXISTS_TAC [`h'::l4`, `l5`] THEN RW_TAC list_ss [],
 Cases_on `l4` THEN FULL_SIMP_TAC list_ss [],
 Cases_on `l4` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []]);

val MAP_pair = Q.store_thm ("MAP_pair",
`!l1 l2 f g h i. (MAP (\x. (f x, g x)) l1 = MAP (\x. (h x, i x)) l2) =
                 (MAP f l1 = MAP h l2) /\ (MAP g l1 = MAP i l2)`,
Induct THEN Cases_on `l2` THEN RW_TAC list_ss [] THEN METIS_TAC []);

val ZIP_APPEND = Q.store_thm ("ZIP_APPEND",
`!l1 l2 l3 l4. (LENGTH l1 = LENGTH l3) /\ (LENGTH l2 = LENGTH l4) ==>
               (ZIP (l1++l2, l3++l4) = ZIP (l1, l3) ++ ZIP (l2, l4))`,
Induct THEN RW_TAC list_ss [] THEN Cases_on `l3` THEN FULL_SIMP_TAC list_ss []);

local

val lem1 = Q.prove (
`!l1 l2 l3 l4. (LENGTH l1 = LENGTH l3) ==>
               ((l1++l2 = l3++l4) = (l1 = l3) /\ (l2 = l4))`,
Induct THEN RW_TAC list_ss [] THEN Cases_on `l3` THEN FULL_SIMP_TAC list_ss [] THEN METIS_TAC []);

val lem2 = Q.prove (
`!l1 l2 l3 l4. (LENGTH l2 = LENGTH l4) /\ (l1++l2 = l3++l4) ==> (LENGTH l1 = LENGTH l3)`,
RW_TAC list_ss [] THEN `LENGTH (l1++l2) = LENGTH (l3++l4)` by METIS_TAC [] THEN
FULL_SIMP_TAC list_ss [LENGTH_APPEND]);

in

val APPEND_LENGTH_11 = Q.store_thm ("APPEND_LENGTH_11",
`!l1 l2 l3 l4. (LENGTH l1 = LENGTH l3) \/ (LENGTH l2 = LENGTH l4) ==>
               ((l1++l2 = l3++l4) = (l1 = l3) /\ (l2 = l4))`,
METIS_TAC [lem1, lem2]);

end;

val REVERSE_EQ = Q.store_thm ("REVERSE_EQ",
`!l1 l2. (REVERSE l1 = REVERSE l2) = (l1 = l2)`,
Induct THEN RW_TAC list_ss [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss [] THEN
METIS_TAC [APPEND_LENGTH_11, LENGTH, list_11]);

val NOT_MEM_EMPTY = Q.store_thm ("NOT_MEM_EMPTY",
`!l. (!x. ~MEM x l) = (l = [])`,
Induct THEN RW_TAC list_ss [] THEN METIS_TAC []);

val FLAT_MAP_SING = Q.store_thm ("FLAT_MAP_SING",
`!l f. FLAT (MAP (\x. [f x]) l) = MAP f l`,
Induct THEN RW_TAC list_ss []);

val EVERY_FILTER = Q.store_thm ("EVERY_FILTER",
`!l f g. EVERY f l ==> EVERY f (FILTER g l)`,
METIS_TAC [EVERY_MEM, MEM_FILTER]);

val FLAT_EQ_EMPTY = Q.store_thm ("FLAT_EQ_EMPTY",
`!l. (FLAT l = []) = EVERY (\x. x = []) l`,
Induct THEN RW_TAC list_ss []);

val ALL_DISTINCT_REVERSE = Q.store_thm ("ALL_DISTINCT_REVERSE",
`!l. ALL_DISTINCT (REVERSE l) = ALL_DISTINCT l`,
Induct THEN RW_TAC list_ss [ALL_DISTINCT_APPEND, DISJOINT_RIGHT] THEN METIS_TAC []);

val DISTINCT_INJ = Q.store_thm ("DISTINCT_INJ",
`!l i j. ALL_DISTINCT l ==> i < LENGTH l /\ j < LENGTH l ==> (EL i l = EL j l) ==> (i = j)`,
Induct THEN RW_TAC list_ss [] THEN Cases_on `i` THEN Cases_on `j` THEN RW_TAC list_ss [] THEN
FULL_SIMP_TAC list_ss [] THEN METIS_TAC [MEM_EL]);

val MAP_FST_ZIP = Q.store_thm ("MAP_FST_ZIP",
`!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP FST (ZIP (l1, l2)) = l1)`,
Induct THEN RW_TAC list_ss [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss []);

val MAP_SND_ZIP = Q.store_thm ("MAP_SND_ZIP",
`!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP SND (ZIP (l1, l2)) = l2)`,
Induct THEN RW_TAC list_ss [] THEN Cases_on `l2` THEN FULL_SIMP_TAC list_ss []);

val MEM_SPLIT = Q.store_thm ("MEM_SPLIT",
`!l x. MEM x (MAP FST l) = ?l1 l2 y. l = l1 ++ [(x,y)] ++ l2`,
Induct THEN SRW_TAC [] [] THEN Cases_on `h` THEN SRW_TAC [] [] THEN
EQ_TAC THEN SRW_TAC [] [] THEN1 METIS_TAC [APPEND] THEN1
METIS_TAC [APPEND] THEN Cases_on `l1` THEN FULL_SIMP_TAC list_ss [] THEN
METIS_TAC []);

val FIRSTN_EL_LASTN = Q.store_thm ("FIRSTN_EL_LASTN",
`!tl n. (n < LENGTH tl) ==> (tl = FIRSTN n tl ++ [EL n tl] ++ LASTN (LENGTH tl - (n + 1)) tl)`,
Induct THEN SRW_TAC [] [LASTN_CONS, LASTN_LENGTH_ID] THEN Cases_on `n` THEN
FULL_SIMP_TAC (srw_ss()) [FIRSTN] THEN SRW_TAC [ARITH_ss] [arithmeticTheory.ADD1] THEN
`LENGTH tl - (n' + 1) <= LENGTH tl` by DECIDE_TAC THEN METIS_TAC [APPEND, LASTN_APPEND2]);

val REMOVE_1_def = Define
`(REMOVE_1 v [] = NONE) /\
 (REMOVE_1 v (h::t) =
    if h = v then
       SOME t
    else
       OPTION_MAP (\x. h::x) (REMOVE_1 v t))`;

val REMOVE_1_NONE = Q.store_thm ("REMOVE_1_NONE",
`!l v. (REMOVE_1 v l = NONE) = ~MEM v l`,
Induct THEN SRW_TAC [] [REMOVE_1_def]);

val REMOVE_1_SOME = Q.store_thm ("REMOVE_1_SOME",
`!l v l'. (REMOVE_1 v l = SOME l') =
          ?l1 l2. ~MEM v l1 /\ (l' = l1 ++ l2) /\ (l = l1++v::l2)`,
Induct THEN SRW_TAC [] [REMOVE_1_def] THEN EQ_TAC THEN SRW_TAC [] [] THENL
[MAP_EVERY Q.EXISTS_TAC [`[]`, `l`] THEN SRW_TAC [] [],
 Cases_on `l1` THEN FULL_SIMP_TAC list_ss [],
 MAP_EVERY Q.EXISTS_TAC [`h::l1`, `l2`] THEN SRW_TAC [] [],
 Cases_on `l1` THEN FULL_SIMP_TAC list_ss [] THEN SRW_TAC [] [] THEN METIS_TAC []]);

local

(* Copied from sortingScript.sml *)
val FILTER_EQ_CONS_APPEND = Q.prove
(`!M N x. FILTER ($= x) M ++ x::N = x::FILTER ($= x) M ++ N`,
 Induct THEN SRW_TAC [][]);

in

val PERM_EVAL = Q.store_thm ("PERM_EVAL",
`(PERM [] l = (l = [])) /\
 (PERM (h::t) l =
   case (REMOVE_1 h l) of
      NONE -> F
   || SOME l' -> PERM t l')`,
SRW_TAC [] [PERM_NIL, PERM_CONS_EQ_APPEND] THEN
Cases_on `REMOVE_1 h l` THEN FULL_SIMP_TAC list_ss [REMOVE_1_NONE, REMOVE_1_SOME] THEN1
METIS_TAC [MEM_APPEND, MEM] THEN EQ_TAC THEN SRW_TAC [] [] THENL
[FULL_SIMP_TAC list_ss [PERM_DEF] THEN SRW_TAC [] [] THEN
    `FILTER ($= x) (l1 ++ h::l2) = FILTER ($= x) (M ++ h::N)` by METIS_TAC [] THEN
    FULL_SIMP_TAC list_ss [FILTER_APPEND, FILTER] THEN Cases_on `x=h` THEN
    FULL_SIMP_TAC list_ss [FILTER_EQ_CONS_APPEND],
 METIS_TAC []]);

end;


val _ = export_theory ();
