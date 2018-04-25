(* Miscellaneous non-caml-specific things used by caml. *)

Require Import Arith.
Require Ascii.
Require Import Bool.
Require Import List.
Require String.
Require Import ZArith.
Set Implicit Arguments.

Hint Resolve Ascii.ascii_dec bool_dec String.string_dec : ott_coq_equality.



Section ZArith_extra.

Lemma positive_eq_dec: forall (x y : positive), {x = y} + {x <> y}.
Proof.
  intros. destruct (Z.eq_dec (Zpos x) (Zpos y)).
  injection e; auto.
  assert (x <> y). intro. rewrite H in n; auto. auto.
Qed.

End ZArith_extra.

Hint Resolve positive_eq_dec : ott_coq_equality.



(* Coq 8.1 has NoDup
Section Permutes.
Variable A : Set.

(* Here are two definitions for a predicate stating that two lists are
   permutations of each other. The best definition might not be either
   of these. In any case, these definitions and lemmas about them
   should go into a separate module. Note that Coq includes a
   Permutation library, but it only handles ordered types. *)

Inductive inserts (a:A) : list A -> list A -> Prop :=
  | Inserts_here : forall l, inserts a l (a::l)
  | Inserts_further :
    forall a0 l l', inserts a l l' -> inserts a (a0::l) (a0::l').
Inductive Permutes : list A -> list A -> Prop :=
  | Permutes_nil : Permutes nil nil
  | Permutes_cons :
    forall a l l', Permutes l l' -> inserts a l l' -> Permutes (a::l) l'.

Lemma inserts_equiv_app :
  forall a l l',
    inserts a l l' <->
    exists l0, exists l1, (l = l0 ++ l1 /\ l' = l0 ++ a::l1).
Admitted.
Definition Permutes_mutual_containment (l l':list A) :=
  (forall x, In x l -> In x l') /\
  (forall x, In x l' -> In x l) /\
  length l = length l'.
Lemma Permutes_equiv_mutual_containment :
  forall l l', Permutes l l' <-> Permutes_mutual_containment l l'.
Admitted.

End Permutes.
*)



(*
Section Specialized_lists_support_hacks.
(* Provide various definitions to support both standard and specialized
   lists. The notations defined here will be used in standard list mode,
   and shadowed in specialized list mode. *)
(* Also force the use of standard library list types for
   [environment_binding] lists and [environment] lists. Note that coq
   homs in the ott source must be consistent with this choice. *)
(* We do this here, before the types [typevar] and [environment]
   are even defined, because some of these functions are used in
   auxiliary functions such as substitutions. *)
Set Implicit Arguments.

Definition identity (A:Set) (x:A) := x.
Definition nth_error' (A:Set) (n:nat) (l:list A) := @nth_error A l n.

Definition map_list_environment_binding := map.
Definition make_list_environment_binding := identity.
Definition unmake_list_environment_binding := identity.
Definition nth_list_environment_binding := nth_error'.
Definition app_list_environment_binding := app.

Definition map_list_environment := map.
Definition make_list_environment := identity.
Definition unmake_list_environment := identity.
Definition nth_list_environment := nth_error'.
Definition app_list_environment := app.

End Specialized_lists_support_hacks.
(* Notations do not survive the end of sections *)
Notation Nil_list_typevar := nil (only parsing).
Notation Nil_list_environment_binding := nil (only parsing).
Notation Cons_list_environment_binding := cons (only parsing).
Notation Nil_list_environment := nil (only parsing).
Notation Cons_list_environment := cons (only parsing).
Notation Nil_list_type_param := nil (only parsing).
Notation Cons_list_type_param := cons (only parsing).
Notation Nil_list_typexpr := nil (only parsing).
Notation Cons_list_typexpr := cons (only parsing).
Notation make_list_value_name_expr := (fun x => x) (only parsing).
Notation make_list_pat_exp := (fun x => x) (only parsing).
Notation Nil_list_value_name_expr := nil (only parsing).
Notation Cons_list_value_name_expr := (fun x e => cons (x,e)) (only parsing).
*)
