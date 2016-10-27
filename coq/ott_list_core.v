(* Definitions that are used by ott-generated output (when using non-expanded lists) *)

Require Import Bool.
Require Import List.
Set Implicit Arguments.



Section list_predicates.
Variable (A : Set). (* should be Type in coq >= V8.1 *)

(* Test whether a predicate [p] holds for every element of a list [l]. *)
Definition forall_list (p:A->bool) (l:list A) :=
  fold_left (fun b (z:A) => b && p z) l true.

(* Test whether a predicate [p] holds for some element of a list [l]. *)
Definition exists_list (p:A->bool) (l:list A) :=
  fold_left (fun b (z:A) => b || p z) l false.

(* Assert that a property holds for every element of a list *)
Inductive Forall_list (P:A->Prop) : list A -> Prop :=
  | Forall_nil : Forall_list P nil
  | Forall_cons :
    forall x l, P x -> Forall_list P l -> Forall_list P (x::l).
(* Assert that a property holds for some element of a list *)
Inductive Exists_list (P:A->Prop) : list A -> Prop :=
  | Exists_head : forall x l, P x -> Exists_list P (x::l)
  | Exists_tail : forall x l, Exists_list P l -> Exists_list P (x::l).

End list_predicates.
Hint Constructors Forall_list Exists_list.



Section list_mem.
(* Functions about membership in a list, with equality between a list
   element and a potential member being decided by [eq_dec]. *)
Variable (A : Set). (* should be Type in coq >= V8.1 *)
Variable (eq_dec : forall (a b:A), {a=b} + {a<>b}).

(* Test whether [x] appears in [l]. *)
Fixpoint list_mem (x:A) (l:list A) {struct l} : bool :=
  match l with
  | nil => false
  | cons h t => if eq_dec h x then true else list_mem x t
end.

(* Remove any element of [l1] that is present in [l2]. *)
Fixpoint list_minus (l1 l2:list A) {struct l1} : list A :=
  match l1 with
  | nil => nil
  | cons h t =>
    if (list_mem h l2) then list_minus t l2 else cons h (list_minus t l2)
end.
End list_mem.



Section Flat_map_definition.
Variables (A B : Set). (* should be Type in coq >= V8.1 *)
Variable (f : A -> list B).
(* This definition is almost the same as the one in the standard library of
   Coq V8.0 or V8.1. The difference is that this version has the shape
    fun A B f => (fix flat_map l := _)
   while the standard library has
    fun A B => (fix flat_map f l := _)
   Our version has the advantage of making recursive definitions such as
    fix foo x := match x with ... | List xs => flat_map foo xs end
   well-founded.
 *)
Fixpoint flat_map (l:list A) {struct l} : list B :=
  match l with
    | nil => nil
    | cons x t => (f x) ++ (flat_map t)
  end.
End Flat_map_definition.



(* Provide helper lemmas for {{coq-equality}} homs. *)
Require Export ott_list_eq_dec.
