(* Helper lemmas for {{coq-equality}} homs. *)

Require Import List.
Set Implicit Arguments.



(* Help construct equality decision procedures (for {{coq-equality}}
   homs). We provide a transparent version of [List.list_eq_dec] from
   the Coq standard library. This transparent version is needed for
   types that contain a recursive call inside a list. Note that at the
   time of writing ott does not generate a workable proof in this case:
   you have to set up the induction manually and call [list_eq_dec] on
   your own (TODO: point to an example --- it's systematic but not easy). *)
Lemma list_eq_dec :
  forall (A:Set) (* should be Type in coq >= V8.1 *)
         (eq_dec : forall (x y:A), {x = y} + {x <> y}),
    forall (x y:list A), {x = y} + {x <> y}.
Proof.
  induction x as [| a l IHl]; destruct y as [| a0 l0]; auto with datatypes.
  destruct (eq_dec a a0) as [e| e].
  destruct (IHl l0) as [e'| e'].
  left; rewrite e; rewrite e'; trivial.
  right; red in |- *; intro.
  apply e'; injection H; trivial.
  right; red in |- *; intro.
  apply e; injection H; trivial.
Defined.

(* While the Coq built-in "decide equality" tactic can decide equality on
   pairs on its own, adding the following lemmas in the hint database helps
   when lists of pairs are involved. *)
Lemma pair_eq_dec :
  forall (A B:Set) (* should be Type in coq >= V8.1 *)
         (eqA:forall a a0:A, {a=a0}+{a<>a0})
         (eqB:forall b b0:B, {b=b0}+{b<>b0})
         (x y:A*B), {x=y}+{x<>y}.
Proof. intros until 2; decide equality; auto. Qed.
Hint Resolve pair_eq_dec : ott_coq_equality.

(* With the following hint, the default {{coq-equality}} proof handles
   grammar types containing lists provided that no recursive call appears
   in a list. *)
Hint Resolve list_eq_dec : ott_coq_equality.

