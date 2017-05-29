(* A supplemental list library to help ott users *)

(* Definitions used by ott-generated output *)
Require Export Ott.ott_list_core.

(* Support library (non-list-related content) *)
Require Export Ott.ott_list_support.

(* Supplemental lemmas and tactics about basic functions (length, map, rev) *)
Require Export Ott.ott_list_base.

(* The take and drop functions, and lemmas and tactics about them
   (n = take n l ++ drop n l) /\ (length (take n l) = n) *)
Require Export Ott.ott_list_takedrop.

(* Supplemental lemmas about taking the nth element of a list *)
Require Export Ott.ott_list_nth.

(* Lemmas about [In], [list_mem] and [list_minus] *)
Require Export Ott.ott_list_mem.

(* Lemmas about [flat_map] *)
Require Export Ott.ott_list_flat_map.

(* Lemmas and tactics about [Forall_list], [Exists_list], [forall_list]
   and [exists_list] *)
Require Export Ott.ott_list_predicate.

(* The repeat function, and lemmas about it
   (length (repeat n x) = n) /\ (forall y, In y (repeat n x) -> x = y) *)
Require Export Ott.ott_list_repeat.

(* The [disjoint] function (test that two lists have no common element),
   the [all_distinct] function (test that a list has no repeated element),
   and lemmas about them *)
Require Export Ott.ott_list_distinct.
