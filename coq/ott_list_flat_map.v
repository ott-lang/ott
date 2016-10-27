(*** Flattening and mapping ***)

Require Import Arith.
Require Import List.
Require Import ott_list_core.
Require Import ott_list_support.
Require Import ott_list_base.



Section Flat_map.
Variables A B C : Set.
Implicit Types x : A.
Implicit Types y : B.
Implicit Types l xs : list A.
Implicit Types ys : list B.
Implicit Types xss : list (list A).
Implicit Types yss : list (list B).
Implicit Types f : A -> B.
Implicit Types g : B -> C.
Implicit Types F : A -> list B.
Implicit Types G : B -> list C.
Set Implicit Arguments.

Lemma std_eq_flat_map :
  forall F l, List.flat_map F l = flat_map F l.
Proof. induction l; simpl; congruence. Qed.

Lemma length_flat_map :
  forall F l,
    length (flat_map F l) = fold_right plus 0 (map (fun x => length (F x)) l).
Proof. induction l; simpl; autorewrite with lists; congruence. Qed.

Lemma flat_map_app :
  forall F l l', flat_map F (l ++ l') = flat_map F l ++ flat_map F l'.
Proof. intros; induction l; simpl; autorewrite with lists; congruence. Qed.

Lemma flat_map_map :
  forall f G l, flat_map G (map f l) = flat_map (compose G f) l.
Proof.
  intros; induction l; simpl; autorewrite with lists;
    unfold compose in *; congruence.
Qed.

Lemma map_flat_map :
  forall F g l, map g (flat_map F l) = flat_map (compose (map g) F) l.
Proof.
  intros; induction l; simpl; autorewrite with lists;
    unfold compose in *; congruence.
Qed.

Lemma flat_map_identity : forall l, flat_map (fun x => x::nil) l = l.
Proof. induction l; simpl; congruence. Qed.

Lemma flat_map_extensionality :
  forall F F' l, (forall x, F x = F' x) -> flat_map F l = flat_map F' l.
Proof. intros; induction l; simpl; try rewrite H; congruence. Qed.

Lemma flat_map_rev :
  forall F l, flat_map F (rev l) = rev (flat_map (compose (@rev _) F) l).
Proof.
  intros; induction l; simpl. reflexivity.
  unfold compose in *; autorewrite with lists;
    rewrite flat_map_app; simpl; autorewrite with lists. congruence.
Qed.

Definition flatten := flat_map (fun xs => xs).
Lemma unfold_flatten : flatten = flat_map (fun xs => xs).
Proof refl_equal _.

Lemma In_flat_map_intro :
  forall F l x y,
    In x l -> In y (F x) -> In y (flat_map F l).
Proof.
  intros; induction l; simpl in *; destruct H.
  subst; auto with datatypes. auto with datatypes.
Qed.

Lemma In_flat_map_elim :
  forall F l y,
    In y (flat_map F l) ->
    exists x, In x l /\ In y (F x).
Proof.
  intros; induction l; simpl in * . solve [elim H].
  destruct (in_app_or _ _ _ H). subst; eauto with datatypes. firstorder.
Qed.

End Flat_map.

Hint Rewrite std_eq_flat_map
             length_flat_map flat_map_app flat_map_map map_flat_map
             flat_map_identity flat_map_extensionality
             flat_map_rev
             unfold_flatten
             : lists.
Hint Resolve In_flat_map_intro In_flat_map_elim : lists.
