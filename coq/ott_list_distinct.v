(*** Lists with no repetition ***)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ring.
Require Import ott_list_core.
Require Import ott_list_base.
Require Import ott_list_nth.
Require Import ott_list_mem.



Section All_distinct.
Set Implicit Arguments.
Variable A : Set.
Variable eq_dec : forall (x y:A), {x=y} + {x<>y}.

Notation one_distinct := (fun x xs => negb (list_mem eq_dec x xs)).

Fixpoint all_distinct (xs:list A) : bool :=
  match xs with
    | nil => true
    | x::xt => andb (one_distinct x xt) (all_distinct xt)
  end.
Fixpoint disjoint (xs ys:list A) {struct xs} : bool :=
  match xs with
    | nil => true
    | x::xt => andb (one_distinct x ys) (disjoint xt ys)
  end.



Ltac destruct_andb :=
  repeat match goal with
           | H : Is_true (?a && ?b) |- _ =>
               (* N.B. [andb_prop2] is called [andb_prop_elim] after V8.1 *)
               destruct (andb_prop2 a b H); clear H
         end.

Lemma one_distinct_eq_fold_right :
  forall x0 xs,
    one_distinct x0 xs =
    fold_right (fun x b => if eq_dec x x0 then false else b) true xs.
Proof.
  induction xs; simpl in * . reflexivity.
  destruct (eq_dec a x0); simpl in *; congruence.
Qed.
Lemma disjoint_eq_fold_right :
  forall xs ys,
    disjoint xs ys = fold_right (fun x => andb (one_distinct x ys)) true xs.
Proof. intros; induction xs; simpl in *; congruence. Qed.

Lemma one_distinct_app :
  forall x xs ys,
    one_distinct x (xs++ys) = one_distinct x xs && one_distinct x ys.
Proof.
  intros; induction xs; simpl in * . reflexivity.
  destruct (eq_dec a x); auto with bool.
Qed.
Lemma all_distinct_app :
  forall xs ys,
    all_distinct (xs++ys) =
    all_distinct xs && all_distinct ys && disjoint xs ys.
Proof.
  intros; induction xs; simpl in * . ring.
  rewrite one_distinct_app. rewrite IHxs. ring.
Qed.

Lemma one_distinct_app_left :
  forall x xs ys,
    Is_true (one_distinct x (xs++ys)) -> Is_true (one_distinct x xs).
Proof.
  intros; simpl in * .
  simplify_lists. apply Is_true_eq_left. assert (H' := Is_true_eq_true _ H).
  unfold negb in * . destruct (list_mem eq_dec x xs); auto.
Qed.
Lemma all_distinct_app_left :
  forall xs ys, Is_true (all_distinct (xs++ys)) -> Is_true (all_distinct xs).
Proof.
  intros. rewrite all_distinct_app in H.
  destruct_andb; assumption.
Qed.
Lemma one_distinct_app_right :
  forall x xs ys,
    Is_true (one_distinct x (xs++ys)) -> Is_true (one_distinct x xs).
Proof.
  intros; simpl in * .
  simplify_lists. apply Is_true_eq_left. assert (H' := Is_true_eq_true _ H).
  unfold negb in * . destruct (list_mem eq_dec x xs); auto.
Qed.
Lemma all_distinct_app_right :
  forall xs ys, Is_true (all_distinct (xs++ys)) -> Is_true (all_distinct xs).
Proof.
  intros. rewrite all_distinct_app in H.
  destruct_andb; assumption.
Qed.

Lemma disjoint_nil_left : forall xs, disjoint nil xs = true.
Proof. reflexivity. Qed.
Lemma disjoint_nil_right : forall xs, disjoint xs nil = true.
Proof. induction xs; simpl; congruence. Qed.
Lemma disjoint_comm :
  forall xs ys, disjoint xs ys = disjoint ys xs.
Proof.
  induction xs; intros; simpl in * .
  rewrite disjoint_nil_right; reflexivity.
  induction ys; simpl in * . rewrite IHxs; reflexivity.
  rewrite <- IHys; repeat rewrite IHxs; simpl.
  destruct (eq_dec a0 a); destruct (eq_dec a a0); try subst a0.
  reflexivity. elim n; reflexivity. elim n; reflexivity. ring.
Qed.
Lemma disjoint_app_distr_left :
  forall xs ys zs, disjoint xs (ys++zs) = disjoint xs ys && disjoint xs zs.
Proof.
  intros. induction xs; simpl in * . reflexivity.
  rewrite IHxs; rewrite one_distinct_app. ring.
Qed.
Lemma disjoint_app_distr_right :
  forall xs ys zs, disjoint (xs++ys) zs = disjoint xs zs && disjoint ys zs.
Proof.
  intros. rewrite disjoint_comm. rewrite disjoint_app_distr_left.
  do 2 rewrite (disjoint_comm zs). reflexivity.
Qed.

Lemma rev_one_distinct :
  forall x xs, one_distinct x (rev xs) = one_distinct x xs.
Proof.
  intros; induction xs; simpl in * . reflexivity.
  rewrite one_distinct_app; rewrite IHxs; simpl.
  destruct (eq_dec a x); ring.
Qed.
Lemma rev_disjoint_right :
  forall xs ys, disjoint xs (rev ys) = disjoint xs ys.
Proof.
  intros; induction xs; simpl in * . reflexivity.
  rewrite rev_one_distinct; rewrite IHxs; reflexivity.
Qed.
Lemma rev_disjoint_left :
  forall xs ys, disjoint (rev xs) ys = disjoint xs ys.
Proof.
  intros; induction xs; simpl in * . reflexivity.
  rewrite disjoint_app_distr_right; simpl. rewrite IHxs; ring.
Qed.
Lemma rev_all_distinct :
  forall xs, all_distinct (rev xs) = all_distinct xs.
Proof.
  intros; induction xs; simpl in * . reflexivity.
  rewrite all_distinct_app; simpl. rewrite IHxs.
  rewrite rev_disjoint_left; rewrite disjoint_comm; simpl; ring.
Qed.

Lemma all_distinct_indices_aux :
  forall xs i j,
    i <= j ->
    Is_true (all_distinct xs) ->
    nth_error xs i = nth_error xs j ->
    i < length xs ->
    i = j.
Proof.
  intros xs i j Ineq.
  replace j with (i + (j-i)). 2: solve [auto with arith].
  generalize (j-i); clear Ineq j; intros k Distinct Nths Bound.
  destruct k. solve [auto with arith]. elimtype False.
  generalize dependent xs; induction i; intros; destruct xs; simpl in * .
  omega.
  destruct (andb_prop2 _ _ Distinct) as [Notin _]; clear Distinct Bound.
  generalize dependent k; induction xs; intros; simpl in * .
  destruct k; discriminate.
  destruct (eq_dec a0 a). exact Notin.
  destruct k; simpl in *; [injection Nths | idtac]; solve [eauto].
  omega.
  eapply IHi; eauto. destruct_andb; assumption.
  omega.
Qed.
Lemma all_distinct_indices :
  forall xs i j,
    Is_true (all_distinct xs) ->
    nth_error xs i = nth_error xs j ->
    i < length xs ->
    i = j.
Proof.
  intros. destruct (le_ge_dec i j).
  eapply all_distinct_indices_aux; eauto.
  symmetry. eapply all_distinct_indices_aux; eauto. omega.
Qed.

End All_distinct.

Notation one_distinct := (fun eq_dec x xs => negb (list_mem eq_dec x xs)).

Hint Rewrite one_distinct_app all_distinct_app : lists.
Hint Rewrite disjoint_nil_left disjoint_nil_right : lists.
Hint Rewrite disjoint_app_distr_left disjoint_app_distr_right : lists.
Hint Rewrite rev_one_distinct rev_disjoint_right rev_disjoint_left
             rev_all_distinct : lists.
