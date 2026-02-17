open HolKernel boolLib Parse bossLib;
open pairTheory optionTheory stringTheory;

val _ = new_theory "ott";

Definition list_minus_def:
 (list_minus [] ys = [])
 /\
 (list_minus (x::xs) ys =
   if ~MEM x ys then x::(list_minus xs ys) else list_minus xs ys)
End

Theorem list_minus_thm:
 !l x. MEM x (list_minus l l') <=> (MEM x l /\ ~MEM x l')
Proof
 Induct >> RW_TAC list_ss [list_minus_def] >> METIS_TAC []
QED

Theorem list_minus_append:
 !l1 l2 l3. list_minus (l1++l2) l3 = list_minus l1 l3 ++ list_minus l2 l3
Proof
 Induct >> RW_TAC list_ss [list_minus_def]
QED

Definition list_assoc_def:
 (list_assoc x [] = NONE)
 /\
 (list_assoc x ((x',y')::xys) = if x=x' then SOME y' else list_assoc x xys)
End

Theorem list_assoc_mem:
 !l x y. list_assoc x l = SOME y ==> MEM (x,y) l
Proof
 Induct >> RW_TAC list_ss [list_assoc_def] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def] >>
 Cases_on `x = q` >> FULL_SIMP_TAC list_ss [list_assoc_def]
QED

Theorem list_assoc_not_mem:
 !l x y. list_assoc x l = NONE ==> ~MEM (x,y) l
Proof
 Induct >> FULL_SIMP_TAC list_ss [list_assoc_def] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def]
QED

Theorem list_assoc_split:
 !l x y. list_assoc x l = SOME y <=>
  ?l1 l2. (l = l1++(x,y)::l2) /\ ~MEM x (MAP FST l1)
Proof
 Induct >> RW_TAC list_ss [list_assoc_def] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def] >>
 EQ_TAC >> RW_TAC list_ss [] >| [
  MAP_EVERY Q.EXISTS_TAC [`[]`, `l`] >> RW_TAC list_ss [],
  Cases_on `l1` >> FULL_SIMP_TAC list_ss [] >>
  RW_TAC list_ss [] >> FULL_SIMP_TAC list_ss [],
  MAP_EVERY Q.EXISTS_TAC [`(q,r)::l1`, `l2`] >> RW_TAC list_ss [],
  Cases_on `l1` >> FULL_SIMP_TAC list_ss [] >> METIS_TAC []
 ]
QED

Theorem list_assoc_append:
 !l1 l2 x. list_assoc x (l1++l2) =
   case list_assoc x l1 of
   | SOME y => SOME y
   | NONE => list_assoc x l2
Proof
 Induct >> RW_TAC list_ss [list_assoc_def] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def]
QED

Theorem mem_list_assoc:
 !l x. MEM x (MAP FST l) ==> ?y. list_assoc x l = SOME y
Proof
 Induct >> RW_TAC list_ss [list_assoc_def] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def]
QED

Theorem not_mem_list_assoc:
 !l x. ~MEM x (MAP FST l) ==> list_assoc x l = NONE
Proof
 Induct >> RW_TAC list_ss [list_assoc_def] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def] >>
 METIS_TAC [FST]
QED

Theorem list_assoc_distinct_reverse:
 !l. ALL_DISTINCT (MAP FST l) ==>
  !x. list_assoc x (REVERSE l) = list_assoc x l
Proof
 Induct >> RW_TAC list_ss [list_assoc_def,list_assoc_append] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def] >>
 FULL_SIMP_TAC list_ss [] >| [
  METIS_TAC [not_mem_list_assoc, option_case_def],
  Cases_on `list_assoc x l` >> RW_TAC list_ss []
 ]
QED

Theorem list_assoc_map:
 !l x f. list_assoc x (MAP (\z. (FST z, f (SND z))) l) =
  OPTION_MAP f (list_assoc x l)
Proof
 Induct >> RW_TAC list_ss [list_assoc_def] >>
 Cases_on `h` >> RW_TAC list_ss [list_assoc_def] >>
 METIS_TAC [FST]
QED

Theorem mono_every_id_thm:
 (!x. P x ==> Q x) ==> EVERY (\x. x) (MAP P l) ==> EVERY (\x. x) (MAP Q l)
Proof
 Induct_on `l` >> RW_TAC list_ss [] >> METIS_TAC []
QED

val _ = IndDefLib.export_mono "mono_every_id_thm";

Theorem filter_size:
 !l f size. list_size size (FILTER f l) <= list_size size l
Proof
 Induct >> RW_TAC list_ss [listTheory.list_size_def] >>
 Q.PAT_ASSUM `!f' size. g f' size` (STRIP_ASSUME_TAC o (Q.SPECL [`f`, `size`])) >>
 DECIDE_TAC
QED

Definition clause_name_def:
 clause_name (x:string) = T
End

val _ = export_theory ();
