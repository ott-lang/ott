(* Additional definitions and lemmas on lists *)

Require Import Arith.
Require Import Omega.



(*** Support definitions and lemmas ***)

Module List_lib_Arith.

Lemma le_lt_dec_S :
  forall n m A (x y:A),
    (if le_lt_dec (S n) (S m) then x else y) =
    (if le_lt_dec n m then x else y).
Proof.
  intros. destruct (le_lt_dec n m); destruct (le_lt_dec (S n) (S m)).
  reflexivity. elimtype False; omega. elimtype False; omega. reflexivity.
Qed.

End List_lib_Arith.



Section functions.
  Set Implicit Arguments.
  Variables A B C D : Type.
  Definition compose (g:B->C) (f:A->B) x := g (f x).
  Definition compose2 (h:B->C->D) (f:A->B) (g:A->C) x y := h (f x) (g y).
End functions.
Hint Unfold compose compose2 : core.



Section option.
  Set Implicit Arguments.
  Variables A B : Type.

  Definition map_option (f:A->B) (xo:option A) : option B :=
    match xo with
      | Some x => Some (f x)
      | None => None
    end.
  Definition map_error := map_option.

  Definition fold_option (f:A->B->B) (xo:option A) (y:B) : B :=
    match xo with
      | Some x => f x y
      | None => y
    end.
  Definition fold_error := fold_option.
End option.
Hint Unfold map_option map_error fold_option fold_error : core.
