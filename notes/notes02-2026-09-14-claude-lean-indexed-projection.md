# Deferred: the Lean encoding of an indexed projection changes what a rule means

Claude: this note is written by Claude (Opus 5), 2026-09-14, recording one item
deliberately left undone during the Lean-output work on branch lean-experiment.

A rule that projects the i'th element of a list -- `t1 .. tn` with a premise
`1 <= i <= n` -- is generated for Lean as

```lean
| SA_Rcd : ∀ (k_S_list : list_label_Typ) (i : index) (m : index),
    (∀ i, (1 <= i ∧ i <= m) → SAf G ((fun (k_,S_) => k_) ((unmake_list_label_Typ k_S_list)[i - 1]!)) …) →
    …
```

The indexing is `l[i - 1]!`, from `pp_nt_or_mv_with_de_with_sie_internal` in
`src/grammar_pp.ml`.  Two things are wrong with it as a faithful encoding:

- `i : Nat`, so `i - 1` truncates rather than going negative.  For `i = 0` it
  selects element 0, and the only thing standing between that and an unintended
  reading of the rule is the `1 <= i` premise sitting beside it.
- `[...]!` is the panic-on-out-of-range form: out of range it yields the
  `Inhabited` default rather than failing to elaborate, so a rule instance with
  `i > m` states something about the default element.  The `deriving Inhabited`
  clauses on the generated inductives exist to make this form typecheck at all.

The Coq backend does not have this problem: it hoists the projection into an
extra premise,

```coq
nth_list_label_T i l = Some t1 -> …
```

so the rule simply has no instance when the index is out of range, and no
default value is ever named.  See the `Coq co` arm of
`pp_nt_or_mv_with_de_with_sie_internal`, which builds `nth_pred` and appends it
to `coq_non_local_hyp_defn`; the machinery that hoists such a premise is
Coq-specific (`coq_non_local_hyp_defn`, `coq_non_local_hyp_defn_vars` in
`pp_coq_opts`) and has no Lean counterpart.

Options, when this is picked up again:

1. Give Lean the same premise-hoisting: add the two fields to `pp_lean_opts`
   and emit `nth_list_... i l = some x →` before the premise that uses `x`.
   Faithful, and it would let the `deriving Inhabited` clauses go, since
   nothing would need a default any more.
2. Keep the indexing but use `l[i - 1]?` and match on the `Option`, which is
   honest but awkward to read inside an inductive's constructor type.
3. Leave it, and document that a generated rule involving an indexed
   projection is only meaningful together with its bounds premise.

Option 1 is the one that matches the Coq output and removes the reliance on
`Inhabited`; it is the most work.
