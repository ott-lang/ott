(*** Membership predicates ***)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ring.
Require Import ott_list_base.
Require Import ott_list_core.
Require Import ott_list_nth.
Set Implicit Arguments.



(*** Membership predicate ***)

Section In.
Variable A : Set.
Implicit Types x : A.
Implicit Types xs l : list A.

(* Speed up proofs by providing trivial consequences of [List.in_or_app] that
   do not require eauto. *)
Lemma In_left_app :
  forall l l' a, In a l -> In a (l ++ l').
Proof. auto with datatypes. Qed.
Lemma In_right_app :
  forall l l' a, In a l -> In a (l ++ l').
Proof. auto with datatypes. Qed.

Lemma not_in_app_or :
  forall l l' a, ~In a (l ++ l') -> ~In a l /\ ~In a l'.
Proof. unfold not; auto with datatypes. Qed.
Lemma not_in_or_app :
  forall l l' a, ~In a l /\ ~In a l' -> ~In a (l ++ l').
Proof. unfold not; destruct 1; intros. pose (in_app_or _ _ _ H1). tauto. Qed.

Lemma nth_error_In :
  forall l n x, nth_error l n = Some x -> In x l.
Proof.
  intros; generalize dependent l; induction n; destruct l; intros;
    simpl in *; simplify_eq H; auto.
Qed.

Lemma nth_safe_In :
  forall l n H, In (nth_safe l n H) l.
Proof.
  intros. eapply nth_error_In. rewrite nth_safe_eq_nth_error. eauto.
Qed.

End In.

Hint Resolve In_left_app In_right_app : datatypes.
Hint Resolve not_in_app_or not_in_or_app : datatypes.
Hint Resolve nth_error_In nth_safe_In : datatypes.



(*** Membership predicate and map ***)

Lemma image_In_map :
  forall (A B:Set) x l (f:A->B),
    In x l -> In (f x) (map f l).
Proof.
  intros. induction l; simpl in * . tauto. destruct H; subst; tauto.
Qed.

Lemma In_map_exists :
  forall (A B:Set) l y (f:A->B),
    In y (map f l) -> exists x, y = f x /\ In x l.
Proof.
  intros. induction l; simpl in * . tauto. destruct H. eauto. firstorder.
Qed.

Ltac elim_In_map H x Eq Mem :=
  let tmp := fresh "tmp" in (
    try rename H into tmp;
    elim (In_map_exists _ _ _ tmp); intro x; destruct 1 as [Eq Mem];
    try clear tmp
  ).

Ltac elim_all_In_map :=
  repeat match goal with
           | H : In ?y (map ?f ?l) |- _ =>
             let Eq := fresh "Eq" with tmp := fresh "tmp" in (
               rename H into tmp;
               elim (In_map_exists _ _ _ tmp); intro; destruct 1 as [Eq Mem];
               clear tmp
             )
         end.



(*** Membership function ***)

Section list_mem.
Variable A : Set.
Variable (eq_dec : forall (a b:A), {a=b} + {a<>b}).
Implicit Types x : A.
Implicit Types xs l : list A.

Ltac case_eq foo :=
  generalize (refl_equal foo);
  pattern foo at -1;
  case foo.

Notation list_mem := (list_mem eq_dec).

Lemma list_mem_implies_In :
  forall x l, Is_true (list_mem x l) -> In x l.
Proof.
  intros. induction l. assumption. simpl in *; destruct (eq_dec a x); tauto.
Qed.
Lemma list_mem_false_implies_not_In :
  forall x l, list_mem x l = false -> ~In x l.
Proof.
  intros. induction l; simpl in * . tauto.
  destruct (eq_dec a x). discriminate. tauto.
Qed.
Lemma case_list_mem_In :
  forall x l, if list_mem x l then In x l else ~In x l.
Proof.
  intros; induction l; simpl in * . tauto.
  destruct (eq_dec a x). tauto. destruct (list_mem x l); tauto.
Qed.
Lemma list_mem_eq_In_dec :
  forall x l, list_mem x l = if In_dec eq_dec x l then true else false.
Proof.
  intros. assert (If := case_list_mem_In x l).
  destruct (list_mem x l); destruct (In_dec eq_dec x l); tauto.
Qed.

Lemma In_implies_list_mem :
  forall x l, In x l -> Is_true (list_mem x l).
Proof.
  intros. induction l. assumption.
  simpl in *; destruct (eq_dec a x); simpl; tauto.
Qed.
Lemma not_In_implies_list_mem_false :
  forall x l, ~In x l -> list_mem x l = false.
Proof.
  intros. induction l; simpl in * . tauto. destruct (eq_dec a x); tauto.
Qed.

Lemma list_mem_app :
  forall x l l', list_mem x (l++l') = list_mem x l || list_mem x l'.
Proof.
  intros; repeat rewrite list_mem_eq_In_dec;
    repeat match goal with |- context C [In_dec ?eq_dec_ ?x_ ?l_] =>
             destruct (In_dec eq_dec_ x_ l_)
           end;
    intros; try ring; elimtype False;
    (let a := type of i in (generalize dependent i; fold (~a)));
    auto with datatypes.
Qed.

Lemma nth_error_mem :
  forall l n x, nth_error l n = Some x -> Is_true (list_mem x l).
Proof. intros; apply In_implies_list_mem. eapply nth_error_In; eauto. Qed.
Lemma nth_safe_mem :
  forall l n H, Is_true (list_mem (nth_safe l n H) l).
Proof. intros; apply In_implies_list_mem. apply nth_safe_In; auto. Qed.

End list_mem.

Hint Rewrite list_mem_app : lists.



(*** Removing an element ***)

Section list_minus.
Variable A : Set.
Variable (eq_dec : forall (a b:A), {a=b} + {a<>b}).
Implicit Types x : A.
Implicit Types xs l : list A.

Notation list_minus := (list_minus eq_dec).

Lemma not_In_list_minus_self :
  forall l x, ~In x (list_minus l (x::nil)).
Proof.
  induction l; intros; simpl in * . tauto.
  destruct (eq_dec x a); simpl in *; firstorder.
Qed.

Lemma In_list_plus :
  forall x l l', In x (list_minus l l') -> In x l.
Proof.
  induction l; intros; simpl in * . assumption.
  destruct (list_mem eq_dec a l'); simpl in *; firstorder.
Qed.

Lemma In_list_minus_other :
  forall l x x', x' <> x -> In x l -> In x (list_minus l (x'::nil)).
Proof.
  induction l; intros; simpl in * . assumption.
  destruct (eq_dec x' a); subst; simpl in * .
  apply IHl; tauto.
  destruct H0. tauto. auto.
Qed.

End list_minus.

Hint Resolve In_list_plus : In_list_plus.
Hint Resolve In_list_minus_other : datatypes.
