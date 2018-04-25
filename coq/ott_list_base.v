(* Additional definitions and lemmas on lists *)

Require Import Arith.
Require Import List.
Require Import Omega.
Require Import Wf_nat.
Require Import Ott.ott_list_support.



(*** Tactic definitions ***)

(* Tactic definitions do not survive their section, so tactics that are
   exported must come outside of any section. *)

Ltac reverse_list l l' :=
  let Rev := fresh "Rev" with tmp := fresh "l" in (
    set (tmp := rev l) in *;
    assert (Rev : l = rev tmp);
      [rewrite <- (rev_involutive l); reflexivity |
       clearbody tmp; subst l; rename tmp into l']
  ).



(*** Start of the Lists section ***)

Section Lists.

Variables A B C : Type.
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




(*** Length ***)

Definition lt_length (A:Type) := ltof _ (@length A).
Definition well_founded_lt_length (A:Type) := (well_founded_ltof _ (@length A)).

Lemma length_app : forall l l', length (l ++ l') = length l + length l'.
Proof.
  induction l; simpl; auto.
Qed.




(*** Reverse ***)

Lemma length_rev : forall l, length (rev l) = length l.
Proof.
  induction l; auto.
  simpl. rewrite length_app. rewrite IHl. simpl. rewrite plus_comm. auto.
Qed.

Definition rev_rev := rev_involutive.

Lemma rev_inj : forall l l', rev l = rev l' -> l = l'.
Proof.
  intros. rewrite <- (rev_involutive l). rewrite <- (rev_involutive l').
  apply (f_equal (@rev A)). assumption.
Qed.



(*** Concatenation ***)

Lemma rev_app : forall l l', rev (l++l') = rev l' ++ rev l.
Proof (@distr_rev A).

Lemma app_inj_prefix : forall l l1 l2, l++l1 = l++l2 -> l1 = l2.
Proof.
  intros. induction l. assumption.
  simpl in H. injection H; intros. auto.
Qed.

Lemma app_inj_suffix : forall l l1 l2, l1++l = l2++l -> l1 = l2.
Proof.
  intros. reverse_list l1 l1. reverse_list l2 l2. reverse_list l l.
  apply (f_equal (@rev A)). apply app_inj_prefix with (l := l).
  apply rev_inj. repeat rewrite rev_app. assumption.
Qed.

Lemma app_inj_prefix_length_prefix :
  forall l0 l1 l0' l1',
    length l0 = length l0' -> l0++l1 = l0'++l1' -> l0 = l0'.
Proof.
  intros. generalize dependent l0'; induction l0; intros.
  destruct l0'; simpl in *; [congruence | discriminate].
  destruct l0'. discriminate. injection H0; intros.
  rewrite (IHl0 l0'); auto. congruence.
Qed.
Lemma app_inj_prefix_length_suffix :
  forall l0 l1 l0' l1',
    length l0 = length l0' -> l0++l1 = l0'++l1' -> l1 = l1'.
Proof.
  intros. rewrite (app_inj_prefix_length_prefix _ _ _ _ H H0) in H0.
  eapply app_inj_prefix; eauto.
Qed.
Lemma app_inj_suffix_length_prefix :
  forall l0 l1 l0' l1',
    length l1 = length l1' -> l0++l1 = l0'++l1' -> l0 = l0'.
Proof.
  intros. eapply app_inj_prefix_length_prefix. 2: eexact H0.
  assert (Eq := f_equal (@length A) H0).
  repeat rewrite length_app in Eq. omega.
Qed.
Lemma app_inj_suffix_length_suffix :
  forall l0 l1 l0' l1',
    length l1 = length l1' -> l0++l1 = l0'++l1' -> l1 = l1'.
Proof.
  intros. rewrite (app_inj_suffix_length_prefix _ _ _ _ H H0) in H0.
  eapply app_inj_prefix; eauto.
Qed.



(*** Map ***)

Lemma length_map : forall f l, length (map f l) = length l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma nth_map : forall n f l x, nth n (map f l) (f x) = f (nth n l x).
Proof.
  intros until l. generalize n; clear n.
  induction l; simpl; destruct n; auto.
Qed.

Lemma nth_ok_map : forall n f l x, nth_ok n (map f l) (f x) = nth_ok n l x.
Proof.
  intros until l. generalize n; clear n.
  induction l; simpl; destruct n; auto.
Qed.

Lemma nth_error_map :
  forall n f l, nth_error (map f l) n = map_error f (nth_error l n).
Proof.
  intros until l. generalize n; clear n.
  induction l; simpl; destruct n; simpl; auto.
Qed.

Lemma map_app : forall f l l', map f (l ++ l') = map f l ++ map f l'.
Proof.
  induction l; auto. intro l'. simpl. rewrite (IHl l'). auto.
Qed.

Lemma map_map : forall f g l, map g (map f l) = map (compose g f) l.
Proof.
  induction l; auto. simpl. rewrite IHl. reflexivity.
Qed.

Lemma map_identity : forall l, map (fun x => x) l = l.
Proof. induction l; simpl; congruence. Qed.

Lemma map_extensionality :
  forall f f' l, (forall x, f x = f' x) -> map f l = map f' l.
Proof. intros; induction l; simpl; try rewrite H; congruence. Qed.

Lemma map_rev : forall f l, map f (rev l) = rev (map f l).
Proof.
  induction l; auto.
  simpl. rewrite map_app. rewrite IHl. reflexivity.
Qed.



(*** End of the Lists section ***)

End Lists.
Arguments lt_length [A] _ _.

Hint Resolve length_app length_map length_rev : datatypes.
Hint Rewrite length_app length_map length_rev : lists.
Hint Rewrite rev_app rev_unit rev_rev : lists.
Hint Rewrite app_ass : lists.
Hint Rewrite <- app_nil_end app_comm_cons : lists.
Hint Rewrite map_app map_map map_rev map_identity : lists.
Hint Rewrite app_inj_prefix_length_prefix app_inj_prefix_length_suffix
             app_inj_suffix_length_prefix app_inj_suffix_length_suffix
             app_inj_prefix app_inj_suffix : app_inj.



(* Look for equations in the context that prove that some lists are empty,
   and substitute them away. *)
Ltac eliminate_nil :=
  repeat
    match goal with
      | H : nil = ?l1 ++ ?l2 |- _ => symmetry in H
      | H : ?l1 ++ ?l2 = nil |- _ =>
        destruct (app_eq_nil l1 l2 H); try clear H
      | H : nil = ?l |- _ => symmetry in H
      | H : ?l = nil |- _ => subst l
    end.

(* Simplify all hypotheses involving the list [l]. *)
Ltac simplify_list l :=
  generalize dependent l; intro;
  autorewrite with lists; unfold compose; simpl;
  intros.

(* Simplify all hypotheses involving lists. *)
Ltac simplify_lists :=
  repeat match goal with l:list _ |- _ =>
           generalize dependent l; intro;
             autorewrite with lists; unfold compose; simpl;
               generalize dependent l
         end;
  intros.

(* For every hypothesis that is an equality between lists, add a hypothesis
   stating that their lengths are equal. *)
Ltac equate_list_lengths :=
  let eq' := fresh "eq" in (
    pose (eq' := eq);
    repeat match goal with
             | H:(@eq (list ?T) ?lhs ?rhs) |- _ =>
               generalize (f_equal (@length T) H);
               fold eq' in H
           end;
    unfold eq' in *; clear eq';
    autorewrite with lists; simpl; intros
  ).

