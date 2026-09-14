# Plan: the style, and one bug, of the generated Coq

Claude: this note is written by Claude (Opus 5), 2026-09-14, from reading the
Coq generated for `tests/test10st.ott` and `tests/tmp_test7.ott` in both list
representations at commit 98be425 on branch lean-experiment.  All four files
compile.  Nothing here has been done to the sources.

## What is already good

The output is recognisably hand-written Coq in shape: sectioned with `(**
subrules *)`-style headers, mutual groups as `Inductive ... with ...` in
dependency order, decidable-equality lemmas each followed by `#[export] Hint
Resolve`, `Arguments` declarations for the implicit parameters of the library
functions, and the inductive relations laid out one premise per line.

## Findings

### A. Correctness

**A1. An indexed projection under a dotted premise is hoisted out of the
quantifier that binds the index.**  This is a real bug, not a style point.
From `tmp_test7` with `-coq_expand_list_types true`:

```coq
| SA_Rcd : forall (l_T_list k_S_list:list_label_T) (G5:G) (i m:index) (t101 t102:(label*T)),
    nth_list_label_T (i - 1) k_S_list = Some t101 ->
    nth_list_label_T (i - 1) k_S_list = Some t102 ->
    (forall i, (1 <= i /\ i <= m) ->
       SAf G5 (match t102 with (k_,S_) => k_ end) (match t101 with (k_,S_) => S_ end) l_T_list) ->
    SA G5 (Ty_Rec k_S_list) (Ty_Rec l_T_list)
```

The two `nth` premises mention the `i` bound by the constructor.  The body then
binds its own `i`, which shadows it, and uses that one only in the bound check.
So the projected element is fixed once, by an arbitrary index, and does not
vary with the index the property is asserted for -- whereas the source rule,
`forall i isin 1 -- m . G |- ki Si <:f { l1 : T1 , .. , ln : Tn }`, says the
premise holds of the i'th element for each i.  `M_Rcd` has the same shape with
three hoisted premises.

Two further things are visible in the same place:

- the hoisted premise is emitted once per *projection* rather than once per
  *element*: `t101` and `t102` are bound by two identical premises, and
  `t107`, `t108`, `t109` by three.  One premise binding one variable, with the
  projections as `match`es on it, would say the same thing;
- the premises are indented inconsistently with the rest (`          nth_...`
  against `     nth_...`).

The machinery is the pair of fields `coq_non_local_hyp_defn` and
`coq_non_local_hyp_defn_vars` in `pp_coq_opts` (`src/types.ml:809`), filled by
the `Coq co` arm of `pp_nt_or_mv_with_de_with_sie_internal` in
`src/grammar_pp.ml` and drained at `src/defns.ml:521`, which always places what
it has collected at the top of the constructor.  The fix is to give it a notion
of the scope the premise belongs to, rather than always the outermost one.

The Lean backend has a different encoding of the same construct, `l[i - 1]!`,
whose own problems are recorded in `notes02-2026-09-14`; these two should be
settled together, since it is one design question about what an indexed
projection means.

**A2. `GT_Rcd` is correct only by variable capture.**  With lists expanded:

```coq
(forall G5 T_, In (G5,T_)
   (map (fun (pat_: (label*T)) => match pat_ with (l_,T_) => (G5,T_) end)
        (unmake_list_label_T l_T_list)) -> (GT G5 T_)) ->
```

The `G5` inside the mapped function is the environment bound by the
constructor, captured; the `forall G5` then shadows it; and the `In`
constraint forces the quantified `G5` back to the captured one, since every
pair in the mapped list has it as its first component.  It does mean the right
thing.  It is also unreadable, and it is one renaming away from meaning
something else.  The Lean backend now emits the direct form for the same rule,
`∀ x ∈ l, (fun (l_,T_) => GT G T_) x`, which is what this should look like.

### B. Deprecations

Rocq 9.2 warns on the generated files.  Attribution matters here:

- **Ott's**: the equality hints are emitted as `#[export] Hint Resolve eq_X :
  ott_coq_equality.` (`src/grammar_pp.ml:1287`) without the database ever being
  created, so every file warns *"Implicitly declaring hint databases is
  deprecated.  Please explicitly create ott_coq_equality"*.  A single `Create
  HintDb ott_coq_equality.` in the preamble, or in `coq/ott_list_eq_dec.v`,
  settles it.
- **the tests'**, not Ott's: `Notation G_nil := (@nil (termvar*T)).` and `Hint
  Constructors reduce GtT : rules.` both come from embeds in
  `tests/test10st.ott` (lines 70 and 139).  The first warns *"Use of Notation
  keyword for abbreviations is deprecated, use Abbreviation"*, the second
  implicitly creates the `rules` database and has no `#[export]`, unlike the
  hints Ott itself emits.  Fixing these is a test-file edit.

### C. Consistency and cosmetics

1. Constructor forms are mixed within one `Inductive`: `| Ty_Var (X:typevar)`
   beside `| Ty_Top : T`, the latter annotated only because it has no
   arguments.
2. Anonymous binders, `| Ty_Rec (_:list_label_T)`, where a name would read
   better and would be needed to talk about the field in a proof script.
3. In the expanded representation the generated list type is printed first in
   its mutual block: `Inductive list_label_p ... with p : Set := ...`, so the
   type the user wrote comes second.
4. Whitespace noise from the symterm printer, where terminals have been
   dropped: `(bound  x   T5   G5 )`, `GtT  (cons ( x1 , T1 )  G5 )  t5 T_5`,
   `( tsubst_t  v2   x   t12  )`.  The same noise was in the Lean output until
   commit 98be425, which added a squash for expressions and a test that avoids
   double parentheses; both are Lean-only at the moment and are the obvious
   thing to generalise.
5. Comment convention is inconsistent: section headers are coqdoc `(** ... *)`,
   but the per-declaration comments from `com` homs are trailing `(* ... *)`,
   which coqdoc does not attach to anything.  The Lean backend now puts these
   in doc comments before the declaration.
6. `(* definitions *)` is emitted once per defnclass, so it repeats before
   every block.
7. `end.` closing a `match` is at column 0.
8. The subrule predicate is `bool` in one list representation and `Prop` in the
   other -- `Is_true (is_v_of_t v2)` against `is_v_of_t v_5` -- so a proof
   written against one does not port to the other.  This is by design, but it
   is worth a deliberate decision rather than an accident of the flag.

## Plan

**Stage 0 -- re-baseline.**  Every stage below changes Coq output, which ends
the "no non-Lean generated file differs" check that the Lean work has been
verified against (`regression/report-2026-09-13b-dir`).  Take a fresh snapshot
first, and change the check to: every diff must be explainable by the change in
hand, and the Coq and CoqNL columns must not drop from their current 76 and 76.

**Stage 1 -- printer only, no change of meaning.**  B (Ott's half), C4, C6, C7:
create the hint database, generalise the whitespace squash and the
parenthesisation test from `defns.ml` to the Coq arms, emit the section header
once, indent `end.`.  Mechanical, but it touches nearly every generated file,
which is why it should go first and by itself.

**Stage 2 -- declaration layout.**  C1, C2, C3, C5: one constructor form, named
binders, the user's type first in its mutual group, `(** ... *)` before
declarations rather than `(* ... *)` after.  Still no change of meaning, but
the diffs want reading rather than counting.

**Stage 3 -- A1, the fix.**  Emit the projection premise inside the quantifier
that binds the index, once per element rather than once per projection, binding
one variable and destructuring it.  Start with a minimal `.ott` that reproduces
it -- one rule with `forall i . P (t_i)` -- because the present output is easy
to misread.  A2 then becomes a simplification rather than a fix: the bounded
`In` form can be written directly, as Lean's now is.  This changes what
generated rules state, so each affected test wants looking at, and the Lean
side of `notes02` should be settled in the same pass.

**Stage 4 -- decide C8**, which is a question about what users' proofs should
look like rather than a cleanup.

Suggested order: Stage 1, then Stage 3, leaving 2 and 4 to be decided
separately.  Stage 3 is the only one that matters mathematically; Stage 1 is
cheap and clears warnings that a later Rocq will turn into errors.

## Test-file follow-ups noticed on the way

- `tests/test10st.ott` line 70 `Notation` and line 139 `Hint Constructors`, as
  above.
- `tests/test10st.ott` line 29 gives the Lean hom `{{ lean List (termvar×Typ)
  }}`, with no spaces around the product, and its `{{ lean }}` embed writes
  `def bound (x:termvar) ...` in the same unspaced style.  Cosmetic, Lean-side.
