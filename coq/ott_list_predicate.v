(*** Predicates on a list ***)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ott.ott_list_base.
Require Import Ott.ott_list_core.
Require Import Ott.ott_list_takedrop.



Section List_predicate_inductive.
(* Properties of [Forall_list] and [Exists_list] *)

Variables A : Type.
Implicit Types x : A.
Implicit Types xs l : list A.
Implicit Types p : A -> bool.
Implicit Types P : A -> Prop.
Set Implicit Arguments.

Lemma not_Exists_list_nil : forall P, ~(Exists_list P nil).
Proof. intros P H; inversion H. Qed.
Hint Resolve not_Exists_list_nil : core.

Lemma Forall_list_dec :
  forall P (dec : forall x, {P x} + {~P x}) l,
    {Forall_list P l} + {~Forall_list P l}.
Proof.
  induction l; simpl in * . solve [auto].
  destruct (dec a); [destruct IHl | idtac]; auto;
    right; intro; inversion_clear H; tauto.
Qed.

Lemma Exists_list_dec :
  forall P (dec : forall x, {P x} + {~P x}) l,
    {Exists_list P l} + {~Exists_list P l}.
Proof.
  induction l; simpl in * . solve [auto].
  destruct (dec a); [idtac | destruct IHl]; auto;
    right; intro; inversion_clear H; tauto.
Qed.

Lemma Forall_Exists_list_dec :
  forall P Q (dec : forall x, {P x} + {Q x}) l,
    {Forall_list P l} + {Exists_list Q l}.
Proof.
  induction l; simpl in * . solve [auto].
  destruct (dec a); destruct IHl; auto.
Qed.

Lemma Forall_list_In :
  forall P x l, In x l -> Forall_list P l -> P x.
Proof.
  induction l; intros; simpl in *; destruct H;
    inversion H0; subst; auto.
Qed.

Lemma In_Forall_list :
  forall P l, (forall x, In x l -> P x) -> Forall_list P l.
Proof.
  induction l; constructor; firstorder.
Qed.

Lemma exists_In_Exists_list :
  forall P l, Exists_list P l -> exists x, In x l /\ P x.
Proof.
  induction 1.
  exists x; simpl; tauto.
  elim IHExists_list; intros. exists x0; simpl; tauto.
Qed.

Lemma Forall_list_app_left :
  forall P l l', Forall_list P (l++l') -> Forall_list P l.
Proof.
  intros; induction l; simpl in * . auto.
  inversion_clear H. auto.
Qed.
Lemma Forall_list_app_right :
  forall P l l', Forall_list P (l++l') -> Forall_list P l'.
Proof.
  induction l; intros. auto. inversion_clear H; auto.
Qed.
Lemma app_Forall_list :
  forall P l l', Forall_list P l -> Forall_list P l' -> Forall_list P (l++l').
Proof.
  intros; induction l; simpl in * . assumption.
  inversion_clear H. auto.
Qed.
Hint Resolve app_Forall_list Forall_list_app_left Forall_list_app_right : core.

Lemma Exists_list_app_or :
  forall P l l', Exists_list P (l++l') ->
    Exists_list P l \/ Exists_list P l'.
Proof.
  intros; induction l; simpl in * . solve [auto].
  inversion_clear H. solve [auto].
  destruct (IHl H0); solve [auto].
Qed.
Lemma app_Exists_list_left :
  forall P l l', Exists_list P l -> Exists_list P (l++l').
Proof.
  intros; induction l; inversion_clear H; simpl; auto.
Qed.
Lemma app_Exists_list_right :
  forall P l l', Exists_list P l' -> Exists_list P (l++l').
Proof.
  intros; induction l; simpl; auto.
Qed.
Hint Resolve Exists_list_app_or app_Exists_list_left app_Exists_list_right : core.

Lemma rev_Forall_list :
  forall P l, Forall_list P l -> Forall_list P (rev l).
Proof. induction 1; simpl; auto. Qed.
Lemma rev_Exists_list :
  forall P l, Exists_list P l -> Exists_list P (rev l).
Proof. induction 1; simpl; auto. Qed.
Lemma Forall_list_rev :
  forall P l, Forall_list P (rev l) -> Forall_list P l.
Proof.
  intros. rewrite <- (rev_involutive l). apply rev_Forall_list; assumption.
Qed.
Lemma Exists_list_rev :
  forall P l, Exists_list P (rev l) -> Exists_list P l.
Proof.
  intros. rewrite <- (rev_involutive l). apply rev_Exists_list; assumption.
Qed.

Lemma take_Forall_list :
  forall P n l, Forall_list P l -> Forall_list P (take n l).
Proof.
  intros; generalize dependent n; induction l; intros;
    inversion_clear H; destruct n; simpl; auto.
Qed.
Lemma drop_Forall_list :
  forall P n l, Forall_list P l -> Forall_list P (drop n l).
Proof.
  intros; generalize dependent n; induction l; intros;
    inversion_clear H; destruct n; simpl; auto.
Qed.
Lemma Forall_list_take_drop :
  forall P n l,
    Forall_list P (take n l) -> Forall_list P (drop n l) -> Forall_list P l.
Proof. intros; rewrite <- (take_app_drop l n); auto. Qed.

Lemma take_drop_Exists_list :
  forall P n l, Exists_list P l ->
    Exists_list P (take n l) \/ Exists_list P (drop n l).
Proof. intros; rewrite <- (take_app_drop l n) in H; auto. Qed.
Lemma Exists_list_take :
  forall P n l, Exists_list P (take n l) -> Exists_list P l.
Proof. intros; rewrite <- (take_app_drop l n); auto. Qed.
Lemma Exists_list_drop :
  forall P n l, Exists_list P (drop n l) -> Exists_list P l.
Proof. intros; rewrite <- (take_app_drop l n); auto. Qed.

Lemma Forall_list_implies :
  forall (P Q:A->Prop) xs,
    (forall x, In x xs -> P x -> Q x) ->
    Forall_list P xs -> Forall_list Q xs.
Proof. induction 2; firstorder. Qed.
Lemma Exists_list_implies :
  forall (P Q:A->Prop) xs,
    (forall x, In x xs -> P x -> Q x) ->
    Exists_list P xs -> Exists_list Q xs.
Proof. induction 2; firstorder. Qed.

End List_predicate_inductive.

Hint Resolve not_Exists_list_nil : lists.
Hint Resolve In_Forall_list : lists.
Hint Resolve Forall_list_app_left Forall_list_app_right : lists.
Hint Resolve app_Forall_list Exists_list_app_or : lists.
Hint Resolve app_Exists_list_left app_Exists_list_right : lists.
Hint Resolve rev_Forall_list rev_Exists_list : lists.
Hint Resolve Forall_list_rev Exists_list_rev : lists.
Hint Resolve take_Forall_list drop_Forall_list Forall_list_take_drop
             take_drop_Exists_list Exists_list_take Exists_list_drop
             : take_drop.
Hint Resolve Forall_list_implies Exists_list_implies : lists.



Section List_predicate_fold.
(* Properties of [forall_list] and [exists_list] *)

Variables A : Type.
Implicit Types x : A.
Implicit Types xs l : list A.
Implicit Types p : A -> bool.
Implicit Types P : A -> Prop.
Set Implicit Arguments.

Lemma forall_list_eq_fold_left_map :
  forall p l,
    forall_list p l = fold_left andb (map p l) true.
Proof.
  unfold forall_list; intros. generalize true.
  induction l; intros; simpl in * . reflexivity.
  rewrite IHl. reflexivity.
Qed.
Lemma forall_list_eq_fold_right_map :
  forall p l,
    forall_list p l = fold_right andb true (map p l).
Proof.
  intros. rewrite forall_list_eq_fold_left_map.
  apply fold_symmetric; auto with bool.
Qed.
Lemma forall_list_eq_fold_left :
  forall p l,
    forall_list p l = fold_left (fun b z => b && p z) l true.
Proof. auto. Qed.
Lemma forall_list_eq_fold_right :
  forall p l,
    forall_list p l = fold_right (fun z b => b && p z) true l.
Proof.
  intros; rewrite forall_list_eq_fold_right_map.
  induction l; simpl. reflexivity. rewrite IHl. auto with bool.
Qed.

Lemma exists_list_eq_fold_left_map :
  forall p l,
    exists_list p l = fold_left orb (map p l) false.
Proof.
  unfold exists_list; intros. generalize false.
  induction l; intros; simpl in * . reflexivity.
  rewrite IHl. reflexivity.
Qed.
Lemma exists_list_eq_fold_right_map :
  forall p l,
    exists_list p l = fold_right orb false (map p l).
Proof.
  intros. rewrite exists_list_eq_fold_left_map.
  apply fold_symmetric; auto with bool.
Qed.
Lemma exists_list_eq_fold_left :
  forall p l,
    exists_list p l = fold_left (fun b z => b || p z) l false.
Proof. auto. Qed.
Lemma exists_list_eq_fold_right :
  forall p l,
    exists_list p l = fold_right (fun z b => b || p z) false l.
Proof.
  intros; rewrite exists_list_eq_fold_right_map.
  induction l; simpl. reflexivity. rewrite IHl. auto with bool.
Qed.

Lemma forall_list_extensionality :
  forall p p' l, (forall x, p x = p' x) -> forall_list p l = forall_list p' l.
Proof.
  intros; repeat rewrite forall_list_eq_fold_right.
  induction l; simpl. reflexivity. rewrite IHl; rewrite H. reflexivity.
Qed.

Lemma exists_list_extensionality :
  forall p p' l, (forall x, p x = p' x) -> exists_list p l = exists_list p' l.
Proof.
  intros; repeat rewrite exists_list_eq_fold_right.
  induction l; simpl. reflexivity. rewrite IHl; rewrite H. reflexivity.
Qed.

End List_predicate_fold.



Section List_predicate_relationship.

Variables A : Type.
Implicit Types x : A.
Implicit Types xs l : list A.
Implicit Types p : A -> bool.
Implicit Types P : A -> Prop.
Set Implicit Arguments.

(* TODO: lemmas relating Forall_list and forall_list, Exists_list
   and exists_list, forall_list and exists_list. *)

Lemma Forall_if_implies_if_forall :
  forall P p l,
    Forall_list (fun z => if p z then P z else ~P z) l ->
    if forall_list p l then Forall_list P l else ~Forall_list P l.
Proof.
  intros; rewrite forall_list_eq_fold_right.
  induction H; simpl in * . apply Forall_nil.
  destruct (fold_right (fun (z : A) (b : bool) => b && p z) true l).
  destruct (p x); simpl. apply Forall_cons; assumption.
  intro No; inversion No; tauto.
  simpl; intro No; inversion No; tauto.
Qed.

End List_predicate_relationship.



(*** More about maps ***)

Section List_predicate_map.

Variables A B C : Type.
Implicit Types x : A.
Implicit Types y : B.
Implicit Types z : C.
Implicit Types xs l : list A.
Implicit Types ys : list B.
Implicit Types zs : list C.
Implicit Types f : A -> B.
Implicit Types g : B -> C.
Implicit Types P : A -> Prop.
Implicit Types Q : B -> Prop.
Implicit Types R : C -> Prop.
Implicit Types m n : nat.
Set Implicit Arguments.

Lemma map_take :
  forall f l n, map f (take n l) = take n (map f l).
Proof.
  intros. generalize dependent n; induction l; intros.
  destruct n; reflexivity.
  destruct n. reflexivity. simpl; rewrite IHl; reflexivity.
Qed.

Lemma map_drop :
  forall f l n, map f (drop n l) = drop n (map f l).
Proof.
  intros. generalize dependent n; induction l; intros.
  destruct n; reflexivity.
  destruct n. reflexivity. simpl; rewrite IHl; reflexivity.
Qed.

Lemma Forall_list_implies_map :
  forall P Q f l,
    (forall x, P x -> Q (f x)) ->
    Forall_list P l -> Forall_list Q (map f l).
Proof. induction 2; simpl; auto with lists. Qed.
Lemma Exists_list_implies_map :
  forall P Q f l,
    (forall x, P x -> Q (f x)) ->
    Exists_list P l -> Exists_list Q (map f l).
Proof. induction 2; simpl; auto with lists. Qed.

Lemma Forall_list_map_implies :
  forall P Q f l,
    (forall x, Q (f x) -> P x) ->
    Forall_list Q (map f l) -> Forall_list P l.
Proof.
  intros. induction l; simpl in * . apply Forall_nil.
  inversion_clear H0. auto with lists.
Qed.
Lemma Exists_list_map_implies :
  forall P Q f l,
    (forall x, Q (f x) -> P x) ->
    Exists_list Q (map f l) -> Exists_list P l.
Proof.
  intros. induction l; simpl in *;
    inversion_clear H0; auto with lists.
Qed.

Lemma Forall_list_map_intro :
  forall Q f l,
    Forall_list (fun x => Q (f x)) l -> Forall_list Q (map f l).
Proof. induction 1; simpl; auto with lists. Qed.
Lemma Exists_list_map_intro :
  forall Q f l,
    Exists_list (fun x => Q (f x)) l -> Exists_list Q (map f l).
Proof. induction 1; simpl; auto with lists. Qed.

Lemma Forall_list_map_elim :
  forall Q f l,
    Forall_list Q (map f l) -> Forall_list (fun x => Q (f x)) l.
Proof.
  intros. induction l; simpl in * . apply Forall_nil.
  inversion_clear H. auto with lists.
Qed.
Lemma Exists_list_map_elim :
  forall Q f l,
    Exists_list Q (map f l) -> Exists_list (fun x => Q (f x)) l.
Proof.
  intros. induction l; simpl in *;
    inversion_clear H; auto with lists.
Qed.

End List_predicate_map.

Hint Rewrite map_take map_drop : take_drop.
Hint Resolve Forall_list_implies_map Exists_list_implies_map : lists.
Hint Resolve Forall_list_map_implies Exists_list_map_implies : lists.
Hint Resolve Forall_list_map_intro Exists_list_map_intro : lists.
Hint Resolve Forall_list_map_elim Exists_list_map_elim : lists.

(* Simplify hypotheses and goals involving [Forall_list]. Simplifications
   involve rewriting [Forall_list ?P ?l] into equivalent statements
   where [?l] is simpler. Recognised ``complex'' constructors for [?l]
   are [nil], [cons], [app], [map], [rev]. In the goal, only
   simplifications that do not solve or split the goal are considered.
 *)
Ltac simplify_Forall_list :=
  let tmp := fresh "tmp" in (
    repeat match goal with
             | H : Forall_list ?P nil |- _ => clear H
             | H : Forall_list ?P (cons ?a ?l) |- _ =>
               inversion_clear H;
               match goal with H':_ |- _ => rename H' into H end
             | H : Forall_list ?P (app ?l0 ?l1) |- _ =>
               rename H into tmp;
               assert (H := Forall_list_app_right l0 l1 tmp);
               generalize H; clear H;
               assert (H := Forall_list_app_left l0 l1 tmp);
               intro; match goal with H':_ |- _ =>
                        move H' after tmp; simpl in H'
                      end;
               move H after tmp; clear tmp; simpl in H
             | H : Forall_list ?P (map ?f ?l) |- _ =>
               (*apply Forall_list_map_elim in H*) (*>=V8.1 only*)
               rename H into tmp;
               assert (H := Forall_list_map_elim f l tmp);
               move H after tmp; clear tmp; simpl in H
             | H : Forall_list ?P (rev ?l) |- _ =>
               rename H into tmp;
               assert (tmp := Forall_list_rev l H);
               move H after tmp; clear tmp; simpl in H
           end;
    repeat ((apply Forall_list_map_intro ||
             apply rev_Forall_list
            ); simpl)
  ).

