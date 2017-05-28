Require Import Arith.
Require Import Omega.
Require Import List.
Require Import ott_list_support.
Require Import ott_list_base.



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

Ltac case_eq foo :=
  generalize (refl_equal foo);
  pattern foo at -1;
  case foo.



(*** Nth element ***)

Unset Implicit Arguments.

Fixpoint nth_safe l n {struct l} : n < length l -> A :=
  match l as l1, n as n1 return n1 < length l1 -> A with
    | h::t, 0 => fun H => h
    | h::t, S m => fun H => nth_safe t m (le_S_n _ _ H)
    | nil, _ => fun H => match le_Sn_O _ H with end
  end.
Implicit Arguments nth_safe [].

Lemma nth_safe_eq_nth_error :
  forall l n H, value (nth_safe l n H) = nth_error l n.
Proof.
  induction l; intro n; pose (F := le_Sn_O n); destruct n; try (contradiction || tauto).
  simpl length; intro H. 
  simpl nth_error; rewrite <- (IHl n (le_S_n _ _ H)).
  reflexivity.
Qed.

Lemma nth_safe_proof_irrelevance :
  forall l n H H', nth_safe l n H = nth_safe l n H'.
Proof.
  intros. assert (value (nth_safe l n H) = value (nth_safe l n H')).
  transitivity (nth_error l n);
    apply nth_safe_eq_nth_error || (symmetry; apply nth_safe_eq_nth_error).
  injection H0; trivial.
Qed.

Lemma nth_safe_cons :
  forall x l n H,
    nth_safe (x::l) (S n) H = nth_safe l n (le_S_n (S n) (length l) H).
Proof. intros. reflexivity. Qed.

Lemma nth_safe_app :
  forall l l' n (H:n<length l),
    exists H', nth_safe l n H = nth_safe (l++l') n H'.
Proof.
  induction l; intros. solve [contradiction (le_Sn_O n H)].
  destruct n.
  simpl length. assert (H' : 0 < S (length (l ++ l')));
                  [solve [auto with arith] | exists H'; reflexivity].
  simpl app. simpl length.
  elim (IHl l' n (le_S_n (S n) (length l) H)); intros. rename x into H'.
  exists (le_n_S (S n) (length (l ++ l')) H').
  rewrite (nth_safe_cons a l n H). rewrite H0.
  pose (H'' := le_S_n _ _ (le_n_S _ _ H')).
  rewrite (nth_safe_proof_irrelevance (l++l') n H' H'').
  unfold H''. rewrite <- (nth_safe_cons a (l++l') n (le_n_S _ _ H')).
  reflexivity.
Qed.

Set Implicit Arguments.

Lemma nth_error_in :
  forall l n H, nth_error l n = value (nth_safe l n H).
Proof. symmetry. apply nth_safe_eq_nth_error. Qed.

Lemma nth_error_nil : forall n, nth_error (@nil A) n = error.
Proof. destruct n; reflexivity. Qed.

Lemma nth_error_out :
  forall l n, length l <= n -> nth_error l n = error.
Proof.
  induction l; intros n H. solve [apply nth_error_nil].
  simpl in H. destruct n. assert False; [omega | intuition].
  simpl. apply IHl. omega.
Qed.

Lemma nth_error_app_prefix :
  forall l l' n H, nth_error (l++l') n = value (nth_safe l n H).
Proof.
  intros.
  assert (H' : n < length (l ++ l')).
  rewrite (length_app l l'). solve [auto with arith].
  transitivity (value (nth_safe (l++l') n H')).
  solve [apply nth_error_in].
  assert ((nth_safe l n H) = (nth_safe (l ++ l') n H')).
  elim (nth_safe_app l l' n H). intros.
  rewrite H0. apply nth_safe_proof_irrelevance.
  rewrite H0. reflexivity.
Qed.

Lemma nth_error_app_suffix :
  forall l l' n, nth_error (l++l') (length l + n) = nth_error l' n.
Proof.
  induction l; intros; simpl; auto.
Qed.

Lemma nth_error_dec :
  forall l n, nth_error l n = match le_lt_dec (length l) n with
                                | left _ => error
                                | right H => value (nth_safe l n H)
                              end.
Proof.
  intros l n; generalize l; clear l. induction n; destruct l; try reflexivity.
  simpl nth_error. simpl length. rewrite (IHn l); clear IHn.
  decompose sum (lt_eq_lt_dec (length l) n);
    destruct (le_lt_dec (length l) n);
    destruct (le_lt_dec (S (length l)) (S n));
    reflexivity ||
    (assert False; [omega | intuition]) ||
    simpl.
  match match goal with |- ?g => g end with value ?lhs = value ?rhs =>
    assert (Eq : lhs=rhs)
  end. apply nth_safe_proof_irrelevance. rewrite Eq; reflexivity.
Qed.

Lemma nth_error_length :
  forall l n, match nth_error l n with
                | Some _ => n < length l
                | None => n >= length l
              end.
Proof.
  induction l; intros; destruct n; try solve [compute; auto with arith].
  simpl. pose (H := IHl n).
  case_eq (nth_error l n); intros;
    rewrite H0 in H; auto with arith.
Qed.

Lemma nth_error_value :
  forall l n x, nth_error l n = value x -> n < length l.
Proof. intros; assert (L := nth_error_length l n). rewrite H in L; exact L. Qed.
Lemma nth_error_error :
  forall l n, nth_error l n = error -> n >= length l.
Proof. intros; assert (L := nth_error_length l n). rewrite H in L; exact L. Qed.

Lemma nth_eq_nth_safe :
  forall l n default,
    nth n l default = match le_lt_dec (length l) n with
                        | left _ => default
                        | right H => nth_safe l n H
                      end.
Proof.
  induction l; destruct n; reflexivity || intros. simpl nth; simpl length.
  destruct (le_lt_dec (S (length l)) (S n));
    case_eq (le_lt_dec (length l) n); intros;
    [idtac | elimtype False; omega | elimtype False; omega | idtac];
    pose (H' := IHl n default); rewrite H in H'; rewrite H'.
  reflexivity. simpl; apply nth_safe_proof_irrelevance.
Qed.

Lemma nth_eq_nth_error :
  forall l n default,
    nth n l default = match nth_error l n with
                        | Some x => x
                        | None => default
                      end.
Proof.
  induction l; destruct n; intros; try reflexivity. simpl; apply IHl.
Qed.

End Lists.

Implicit Arguments nth_safe [A].
Implicit Arguments nth_safe_eq_nth_error [A].
Implicit Arguments nth_safe_proof_irrelevance [A].
Implicit Arguments nth_safe_cons [A].
Implicit Arguments nth_safe_app [A].

Hint Rewrite nth_map nth_ok_map nth_error_map : lists.
Hint Rewrite nth_error_nil : lists.
Hint Rewrite nth_error_in nth_error_out using omega : list_nth_error.
Hint Rewrite nth_error_dec : list_nth_dec.
Hint Resolve nth_error_value nth_error_error : datatypes.
