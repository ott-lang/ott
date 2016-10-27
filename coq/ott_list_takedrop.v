(* Additional definitions and lemmas on lists *)

Require Import Arith.
Require Import Max.
Require Import Min.
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



(*** Prefix and suffix extraction ***)

Fixpoint take n l {struct l} : list A :=
  match n, l with
    | 0, _ => nil
    | _, nil => nil
    | S m, h::t => h :: (take m t)
  end.

Lemma take_0 : forall l, take 0 l = nil.
Proof. destruct l; reflexivity. Qed.
Lemma take_nil : forall n, take n nil = nil.
Proof. destruct n; reflexivity. Qed.

Lemma take_all :
  forall l n, length l <= n -> take n l = l.
Proof.
  induction l; destruct n; intros; try reflexivity.
  solve [inversion H].
  simpl in * . apply (f_equal2 (@cons A)). reflexivity. apply IHl. omega.
Qed.

Lemma take_length :
  forall l n, length (take n l) = min n (length l).
Proof.
  induction l; destruct n; intros; simpl; try rewrite IHl; reflexivity.
Qed.

Lemma take_some_length :
  forall l n, n <= length l -> length (take n l) = n.
Proof.
  intros. rewrite take_length. auto with arith.
Qed.

Lemma take_nth :
  forall l m n,
    nth_error (take m l) n = if le_lt_dec m n then error else nth_error l n.
Proof.
  intros until n. generalize dependent l. generalize dependent m.
  induction n; intros; simpl.
  destruct m; destruct l; reflexivity.
  destruct l; simpl.
  destruct (le_lt_dec m (S n)); destruct m; reflexivity.
  destruct m. reflexivity.
  rewrite IHn. symmetry. apply le_lt_dec_S.
Qed.

Lemma take_take :
  forall l m n, take m (take n l) = take (min m n) l.
Proof.
  induction l; intros; simpl.
  destruct (min m n); destruct n; repeat rewrite take_nil; reflexivity.
  destruct n; destruct m; try reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Fixpoint drop n l {struct l} : list A :=
  match n, l with
    | 0, _ => l
    | _, nil => nil
    | S m, h::t => drop m t
  end.

Lemma drop_0 : forall l, drop 0 l = l.
Proof. destruct l; reflexivity. Qed.
Lemma drop_nil : forall n, drop n nil = nil.
Proof. destruct n; reflexivity. Qed.

Lemma drop_all :
  forall l n, length l <= n -> drop n l = nil.
Proof.
  induction l; destruct n; intros; try reflexivity.
  solve [inversion H].
  simpl in * . apply IHl. omega.
Qed.

Lemma drop_length : forall l n, length (drop n l) = length l - n.
Proof.
  induction l; destruct n; intros; simpl; try rewrite IHl; reflexivity.
Qed.

Lemma match_drop :
  forall l n, match drop n l with
                | nil => length l <= n
                | _::_ => length l > n
              end.
Proof.
  intros. destruct (le_gt_dec (length l) n) as [Le | Gt].
  rewrite drop_all; assumption.
  generalize (conj (refl_equal (length (drop n l))) (refl_equal (drop n l))).
  pattern (drop n l) at 1 3.
  case (drop n l); intros; rewrite drop_length in H; destruct H; simpl in * .
  elimtype False; omega.
  rewrite <- H0. assumption.
Qed.

Lemma drop_nth :
  forall l m n, nth_error (drop m l) n = nth_error l (m + n).
Proof.
  induction l; intros.
  rewrite drop_nil. repeat rewrite nth_error_nil. reflexivity.
  destruct m; simpl; auto.
Qed.

Lemma drop_drop :
  forall l m n, drop m (drop n l) = drop (n + m) l.
Proof.
  intros; generalize dependent l. induction n; simpl; intros.
  rewrite drop_0. reflexivity.
  destruct l; simpl; [destruct m | rewrite IHn]; reflexivity.
Qed.

Lemma take_app_drop : forall l n, take n l ++ drop n l = l.
Proof.
  intros l n; generalize dependent l; induction n; intros.
  rewrite take_0; rewrite drop_0; reflexivity.
  induction l; simpl. reflexivity.
  rewrite IHn. reflexivity.
Qed.

Lemma take_app_exact :
  forall l l' n, length l = n -> take n (l ++ l') = l.
Proof.
  induction l; intros; subst n; simpl in * .
  rewrite take_0. reflexivity.
  rewrite IHl; reflexivity.
Qed.

Lemma drop_app_exact :
  forall l l' n, length l = n -> drop n (l ++ l') = l'.
Proof.
  induction l; intros; subst n; simpl in * .
  rewrite drop_0. reflexivity.
  rewrite IHl; reflexivity.
Qed.

Lemma take_app_long :
  forall l l' n, n <= length l -> take n (l ++ l') = take n l.
Proof.
  intros.
  set (tmp := l) in |- * at 2. rewrite <- (take_app_drop l n). subst tmp.
  rewrite app_ass. rewrite take_app_exact. reflexivity.
  apply take_some_length. assumption.
Qed.

Lemma drop_app_long :
  forall l l' n, n <= length l -> drop n (l ++ l') = drop n l ++ l'.
Proof.
  intros.
  set (tmp := l) in |- * at 2. rewrite <- (take_app_drop l n). subst tmp.
  rewrite app_ass. rewrite drop_app_exact. reflexivity.
  apply take_some_length. assumption.
Qed.

Lemma take_app_short :
  forall l l' n, take (length l + n) (l ++ l') = l ++ take n l'.
Proof. intros. induction l; simpl; congruence. Qed.

Lemma drop_app_short :
  forall l l' n, drop (length l + n) (l ++ l') = drop n l'.
Proof. intros. induction l; simpl; congruence. Qed.

Lemma take_from_app :
  forall l l', take (length l) (l ++ l') = l.
Proof.
  intros. replace (length l) with (length l + 0). 2: omega.
  rewrite take_app_short. rewrite take_0.
  symmetry. apply app_nil_end.
Qed.

Lemma drop_from_app :
  forall l l', drop (length l) (l ++ l') = l'.
Proof.
  intros. replace (length l) with (length l + 0). 2: omega.
  rewrite drop_app_short. apply drop_0.
Qed.

Lemma take_take_app :
  forall l l' n, n <= length l -> take n (take n l ++ l') = take n l.
Proof.
  intros. rewrite take_app_long. rewrite take_take.
  destruct (min_dec n n) as [Eq | Eq]; rewrite Eq; reflexivity.
  rewrite take_some_length; trivial.
Qed.

Lemma drop_take_app :
  forall l l' n, n <= length l -> drop n (take n l ++ l') = l'.
Proof.
  intros. rewrite drop_app_exact. reflexivity.
  apply take_some_length. assumption.
Qed.



(*** End of the Lists section ***)

End Lists.

Hint Rewrite take_0 take_nil take_length take_nth take_take : take_drop.
Hint Rewrite take_all : take_drop_short.
Hint Rewrite take_some_length : take_drop_long.
Hint Rewrite drop_0 drop_nil drop_length drop_nth drop_drop : take_drop.
Hint Rewrite drop_all : take_drop_short.
Hint Rewrite take_app_drop : take_drop.
Hint Rewrite take_app_exact drop_app_exact : take_drop_exact.
Hint Rewrite take_app_long drop_app_long : take_drop_long.
Hint Rewrite take_app_short drop_app_short : take_drop.
Hint Rewrite take_from_app drop_from_app : take_drop.
Hint Rewrite take_take_app drop_take_app : take_drop_long.

(* Break the list [original] into two pieces [prefix] and [suffix]
   at the location indicated by [cut_point]. [cut_point] indicates
   the number of elements to retain in [prefix]; it may also be
   a list whose length is used. This tactic leaves either one or two
   goals. The first goal has a hypothesis stating that the length of
   [prefix] is [cut_point]. The second goal has [original] left
   unchanged and an additional hypothesis stating that
   [length original < cut_point]; the tactic tries refuting this by
   calling omega. *)
Ltac cut_list original cut_point prefix suffix :=
  let l := fresh "whole" with Ineq := fresh "Ineq" with
      Eq := fresh "Decomposition" with Eql := fresh "Eqlen" with
      p := fresh "prefix" with s := fresh "suffix" with
      n := match type of cut_point with
             | nat => cut_point
             | list _ => constr:(length cut_point)
             | _ => fail "cut_list: unrecognised cut_point type"
           end in (
    destruct (le_lt_dec n (length original)) as [Ineq | Ineq]; [
      (**length original >= n, so length prefix = n**)
      assert (Eql := take_some_length original Ineq); clear Ineq;
      generalize dependent original; intro l;
      assert (Eq := take_app_drop l n);
      set (p := (take n l)) in *; set (s := (drop n l)) in *;
      clearbody p s; subst l;
      (*We've done the cutting, now we try to do some simplifications*)
      autorewrite with lists take_drop; intros;
      rename p into prefix; rename s into suffix
    | (**length original < n**)
      try (equate_list_lengths; elimtype False; omega) ]
  ).

(* Look for equations between lists that can be simplified.
   [?p ++ ?s = ?p' ++ ?s'] is simplified into [?p = ?p'] and [?s = ?s'] *)
Ltac parallel_split :=
  let eq' := fresh "eq" with tmp := fresh "tmp" with
      EqPrefix := fresh "Eql" with EqSuffix := fresh "Eql" in (
    pose (eq' := eq);
    repeat match goal with
             | H : app ?p ?s = app ?p' ?s' |- _ =>
               (
                 assert (tmp : length p = length p');
                   [equate_list_lengths; omega | idtac];
                 assert (EqPrefix := app_inj_prefix_length_prefix _ _ _ _ tmp H);
                 rewrite <- EqPrefix in H;
                 assert (EqSuffix := app_inj_prefix _ _ _ H);
                 clear tmp H
               ) || (
                 assert (tmp : length s = length s');
                   [equate_list_lengths; omega | idtac];
                 assert (EqSuffix := app_inj_prefix_length_suffix _ _ _ _ tmp H);
                 rewrite <- EqSuffix in H;
                 assert (EqPrefix := app_inj_suffix _ _ _ H);
                 clear tmp H
               ) || fold eq' in H
             | H : cons ?a ?l = cons ?a' ?l' |- _ =>
               injection H; intro; clear H; intro H
           end;
    unfold eq' in *; clear eq'
  ).
(* Ad-hoc obsolete tactic (superceded by [parallel_split]) *)
Ltac parallel_split_maps :=
  repeat match goal with
           | H : map ?f ?p ++ map ?f ?s = ?p' ++ ?s' |- _ =>
             assert (Eqlen' : length (map f p) = length p');
               [equate_list_lengths; omega | idtac];
             assert (EqPrefix := app_inj_prefix_length_prefix _ _ _ _ Eqlen' H);
             rewrite <- EqPrefix in H;
             assert (EqSuffix := app_inj_prefix _ _ _ H);
             clear Eqlen' H
           | H : _ ++ _ = map _ _ ++ map _ _ |- _ => symmetry in H
         end.




(*** The End. ***)
