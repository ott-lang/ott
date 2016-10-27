(*** Constant list ***)

Require Import Arith.
Require Import List.
Require Import Omega.
Require Import ott_list_support.
Require Import ott_list_base.
Require Import ott_list_nth.
Import List_lib_Arith.



Section Lists.

Variables A B C : Set.
Implicit Types x : A.
Implicit Types y : B.
Implicit Types z : C.
Implicit Types xs l : list A.
Implicit Types ys : list B.
Implicit Types zs : list C.
Implicit Types f : A -> B.
Implicit Types g : B -> C.
Implicit Types m n : nat.
Set Implicit Arguments.

Fixpoint repeat n x {struct n} : list A :=
  match n with
    | 0 => nil
    | S m => x :: repeat m x
  end.

Lemma repeat_length : forall n x, length (repeat n x) = n.
Proof.
  induction n; intros. reflexivity. simpl. rewrite IHn. reflexivity.
Qed.

Lemma repeat_app :
  forall n m x, repeat (n + m) x = repeat n x ++ repeat m x.
Proof.
  induction n; simpl; intros. reflexivity. rewrite IHn. reflexivity.
Qed.

Lemma repeat_S : forall n x, repeat (S n) x = repeat n x ++ x::nil.
Proof.
  intros. replace (S n) with (n+1). 2: omega.
  rewrite repeat_app. reflexivity.
Qed.

Lemma nth_error_repeat :
  forall m n x,
    nth_error (repeat n x) m = if le_lt_dec n m then error else value x.
Proof.
  induction m; destruct n; intros; try reflexivity.
  simpl repeat. simpl nth_error. rewrite IHm.
  symmetry. apply le_lt_dec_S.
Qed.

Lemma nth_repeat :
  forall m n x,
    nth m (repeat n x) x = x.
Proof.
  induction m; destruct n; intros; try reflexivity.
  simpl. rewrite IHm. reflexivity.
Qed.

Lemma nth_safe_repeat :
  forall m n x H,
    nth_safe (repeat n x) m H = x.
Proof.
  intros. assert (value (nth_safe (repeat n x) m H) = value x).
  rewrite nth_safe_eq_nth_error. rewrite nth_error_repeat.
  rewrite repeat_length in H.
  destruct (le_lt_dec n m). elimtype False; omega. reflexivity.
  injection H0. tauto.
Qed.

End Lists.



Hint Rewrite repeat_length repeat_app repeat_S : lists.
Hint Rewrite nth_error_repeat nth_repeat nth_safe_repeat : lists.
