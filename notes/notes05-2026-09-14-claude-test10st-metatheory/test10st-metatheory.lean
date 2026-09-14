/- Claude: this file is written by Claude (Opus 5), 2026-09-14.  It states, and
   does not prove, the usual syntactic type soundness results for the simply
   typed lambda calculus as Ott generates it from tests/test10st.ott.  Every
   proof is `sorry`; the point is to say what the generated definitions ought to
   satisfy, and to record two places where the statement has to be weaker than
   one might first write it because of how the definitions are generated.

   "make" in this directory generates test10st.lean from
   ../../tests/test10st.ott and checks this file against it.  A successful run
   reports "declaration uses 'sorry'" for each result below and nothing else. -/

import test10st

open Term Typ

/-! ## Values -/

/-- The subrule predicate `is_v_of_t` is `Bool`-valued, so a proposition about
    values has to compare it with `true`.  (If the Lean backend is changed to
    generate `Prop`-valued subrule predicates, as the Coq one does when lists
    are expanded, this definition goes away and `IsValue` is `is_v_of_t`.) -/
def IsValue (t : Term) : Prop := is_v_of_t t = true

/-- A value is exactly an abstraction, by the definition of `is_v_of_t`. -/
theorem isValue_iff_lam {t : Term} :
    IsValue t ↔ ∃ x t', t = t_Lam x t' := by
  sorry

/-! ## Canonical forms -/

/-- A value of function type is an abstraction. -/
theorem canonical_forms_arrow {Γ : G} {v : Term} {T1 T2 : Typ} :
    GtT Γ v (T_arrow T1 T2) → IsValue v → ∃ x t, v = t_Lam x t := by
  sorry

/-! ## Closed terms

    `tsubst_t` does not rename bound variables: its abstraction clause stops at
    a binder of the same name but does nothing about the free variables of the
    term being substituted.  So substitution captures, and the results below
    are stated for closed terms, where capture cannot arise.  See the remark at
    the end of this file. -/

/-- A term is closed when it has no free term variables. -/
def Closed (t : Term) : Prop := fv_t t = []

/-! ## Substitution -/

/-- Substituting a closed term of the right type for the variable at the head
    of the context preserves typing.  The closedness hypothesis is what stands
    in for capture-avoidance. -/
theorem substitution {Γ : G} {x : termvar} {v t : Term} {T1 T : Typ} :
    GtT ((x, T1) :: Γ) t T → GtT Γ v T1 → Closed v →
    GtT Γ (tsubst_t v x t) T := by
  sorry

/-! ## Preservation -/

/-- Reduction preserves typing, for closed terms.  `reduce` substitutes only
    values, and a value appearing in a closed term is closed, so the
    substitution lemma above applies at every use. -/
theorem preservation {t t' : Term} {T : Typ} :
    GtT [] t T → reduce t t' → GtT [] t' T := by
  sorry

/-- Reduction preserves closedness. -/
theorem reduce_closed {t t' : Term} : Closed t → reduce t t' → Closed t' := by
  sorry

/-! ## Progress -/

/-- A closed well-typed term is either a value or reduces.  The empty context
    is what rules out `t_Var`: `bound x T []` unfolds to `False`. -/
theorem progress {t : Term} {T : Typ} :
    GtT [] t T → IsValue t ∨ ∃ t', reduce t t' := by
  sorry

/-! ## Multi-step reduction -/

/-- The reflexive transitive closure of `reduce`. -/
inductive Reduces : Term → Term → Prop where
  | refl (t : Term) : Reduces t t
  | step {t t' t'' : Term} : reduce t t' → Reduces t' t'' → Reduces t t''

theorem preservation_multi {t t' : Term} {T : Typ} :
    GtT [] t T → Reduces t t' → GtT [] t' T := by
  sorry

/-! ## Safety -/

/-- Type safety: a closed well-typed term never reaches a stuck state - every
    term it reduces to is either a value or can reduce again. -/
theorem safety {t t' : Term} {T : Typ} :
    GtT [] t T → Reduces t t' → IsValue t' ∨ ∃ t'', reduce t' t'' := by
  sorry

/-- The same, spelled as "no closed well-typed term gets stuck". -/
def Stuck (t : Term) : Prop := ¬ IsValue t ∧ ¬ ∃ t', reduce t t'

theorem never_stuck {t t' : Term} {T : Typ} :
    GtT [] t T → Reduces t t' → ¬ Stuck t' := by
  sorry

/-! ## Two remarks on the generated definitions

    **Preservation does not hold in a non-empty context.**  `tsubst_t` captures,
    so with `Γ = [(y, T)]` the term `(λx. λy. x) y` is well typed and reduces to
    `λy. y`, which has a different type.  Stating `preservation` for an
    arbitrary `Γ` would therefore be false, not merely unproven.  Fixing that is
    a question about the Ott source - a capture-avoiding substitution, or a
    locally nameless representation - and not about these statements.  The two
    examples below check that claim rather than asserting it; they are the only
    things in this file that are proved.

    **The context is a list with first-match lookup.**  `bound` is defined in
    the `{{ lean }}` embed of tests/test10st.ott by walking the list and
    stopping at the first matching variable, so `GtT_lambda`, which conses onto
    the front, shadows rather than requiring freshness.  That is the usual
    convention and the statements above are stated for it; a weakening lemma,
    if one is wanted, has to respect the shadowing:

      GtT Γ t T → GtT ((x, T') :: Γ) t T   requires x ∉ fv_t t -/

/-! The two facts the remarks above rest on, checked.  They depend on `termvar`
    being `String`, which is what the `{{ lean String }}` hom on the metavar
    gives. -/

/-- The empty context binds nothing: this is what rules out `t_Var` in
    `progress`. -/
example (x : termvar) (T : Typ) : ¬ bound x T [] := by simp [bound]

/-- Substitution captures: the free `y` of the substituted term is caught by the
    binder it is substituted under. -/
example :
    tsubst_t (t_Var "y") "x" (t_Lam "y" (t_Var "x")) = t_Lam "y" (t_Var "y") := by
  rfl
