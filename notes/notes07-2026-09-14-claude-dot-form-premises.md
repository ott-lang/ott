# A dot form's index bound is generated unconstrained, and the rules it guards
are vacuous

Claude: this note is written by Claude (Opus 5), 2026-09-14, from proving - and
failing to prove - the metatheory of `tests/test7.ott` in
`notes/notes06-2026-09-14-claude-test7-metatheory/`.  Every claim below is
machine-checked, in Lean and in Coq; the proof scripts are named where they
live.  Nothing has been changed in the sources.

## The bug

A rule whose premise ranges over the elements of a dot form generates a
quantifier whose bound is a fresh argument of the constructor, with nothing
tying it to the list the dot form stands for.  Instantiating that bound with
zero discharges the premise, so the rule fires with nothing established.

`tests/test7.ott` has

```
r G |- {k1:S1 , .. , km:Sm} <: {l1:T1,..,ln:Tn}
```

with the premise `forall i isin 1 -- m . G |- ki Si <:f { l1 : T1 , .. , ln :
Tn }`.  In the source, `m` is the length of the record on the left.  The
generated Lean is

```lean
| SA_Rcd : ∀ (l_T_list k_S_list : List (label × Typ)) (G5 : TypEnv) (i m : index),
    (∀ i, 1 ≤ i ∧ i ≤ m → SAf G5 … k_S_list[i-1]! … l_T_list) →
    SA G5 (Ty_Rec k_S_list) (Ty_Rec l_T_list)
```

where `m` is a constructor argument like any other.  With `m := 0`:

```lean
theorem sa_rcd_vacuous (G : TypEnv) (k_S_list l_T_list : List (label × Typ)) :
    SA G (Ty_Rec k_S_list) (Ty_Rec l_T_list) := by
  refine SA.SA_Rcd l_T_list k_S_list G 0 0 ?_
  intro i hi
  exact absurd (Nat.le_trans hi.1 hi.2) (by simp)
```

*Any record type is a subtype of any other, in any context.*  That is
`sa_rcd_vacuous` in `test7_proofs.mng`.

The Coq output has the same hole.  There the rule carries two extra premises
from the indexed projections, `nth_list_label_T (i - 1) k_S_list = Some t101`,
which need a non-empty left record to satisfy, so the statement is weaker by
exactly that much:

```coq
Lemma sa_rcd_vacuous : forall G5 l T k_S_list l_T_list,
  SA G5 (Ty_Rec (Cons_list_label_T l T k_S_list)) (Ty_Rec l_T_list).
Proof.
  intros.
  eapply SA_Rcd with (i := 1) (m := 0) (t101 := (l,T)) (t102 := (l,T)).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - intros i [H1 H2]. exfalso. lia.
Qed.
```

## The same thing from the other end: a dot form with no elements

`TyCh_Rcd`'s only premise quantifies over the fields of the record being typed.
For the empty record there are none, so the rule has no premises at all - not
even that the context is well formed:

```lean
theorem ty_empty_rec (G : TypEnv) : Ty G (t_Rec []) (Ty_Rec []) := by
  have h := Ty.TyCh_Rcd [] G (by intro x hx; simp at hx)
  simpa using h
```

and in Coq, `ty_empty_rec` proved by `apply TyCh_Rcd; intros; simpl in *;
contradiction`.  Both are checked.

## What follows

For `tests/test7.ott` these two together sink type soundness.  The empty record
can be coerced by the vacuous subtyping to a record type that claims a field,
and then projected at it:

```lean
theorem ty_stuck : Ty G_empty (t_Proj (t_Rec []) "l") Ty_Top
theorem stuck_no_step : ¬ ∃ t2, reduce (t_Proj (t_Rec []) "l") t2
theorem progress_fails : ¬ Progress
```

all proved in `test7_proofs.mng`.  Typing and subtyping also fail to maintain a
well-formed context, by the same empty-dot-form route
(`typingOk_fails`, `subOk_fails`).

This is not a fact about records or about F<:.  Any rule with a premise over a
dot form has it: the quantifier is guarded by a bound that the instantiator
chooses.

## Where it comes from, and what would fix it

The bound comes from `extract_quantified_proof_assistant_vars` in
`src/grammar_pp.ml`, which puts the dot form's lower and upper bounds into the
list of variables to quantify at the head of the rule, and from the dotted
premise printer, which emits `1 <= i /\ i <= m -> ...` using them.  Nothing
relates `m` to the list, because at that point the list is just another
quantified variable.

Two changes would fix the two halves, and they are independent.

1. **Tie the bound to the list.**  Emit `m = length l` as a premise, or emit
   the quantifier as a membership in the list rather than an index range - Lean
   already has the bounded form `∀ x ∈ l, P x` for the non-indexed case
   (`pp_symterm_node_body`'s `formula_dots` arm), and it is exactly this shape.
   Where the index is used for a projection as well, `nth`-style premises are
   needed and the Coq backend already emits them; the Lean backend uses
   `l[i-1]!` instead, which is the separate problem recorded in
   `notes02-2026-09-14`.

2. **Do not let a rule end up with no premises.**  A rule whose only premise is
   a dot form is vacuous when the list is empty.  Requiring the context
   well-formedness premise that the paper rules carry - `G |- ok` - would be
   enough here, and is what the other leaf rules of the same judgement already
   have (`SA_Top`, `SA_Refl_TVar`, `TyCh_Var`, `GT_Top`).  That is arguably a
   fix to `tests/test7.ott` rather than to Ott, but the pattern is general
   enough to be worth a warning: a generated rule with no premises at all,
   where the source had one, is almost certainly not what the author meant.

The second is also why the first alone is not enough: with `m = length
k_S_list` the empty record still subtypes anything, because the premise is then
vacuous by the list being empty rather than by the bound being chosen small.
Width subtyping for records does want the other direction quantified, which is
what `SAf` is for; the rule as written says nothing about the right-hand record
when the left is empty, and that is correct - the error is only that it says
nothing about *typing contexts* either.

## Relation to the other notes

`notes03-2026-09-14` records a related but distinct defect in the Coq output of
the same rule: the `nth_...` premises are hoisted to the top of the constructor
while the index they mention is bound inside the body, so `SA_Rcd` and `M_Rcd`
state something other than their source rules.  `notes02-2026-09-14` records
the Lean encoding of the same projection.  All three should be settled
together: they are the same rule, seen from three sides.
