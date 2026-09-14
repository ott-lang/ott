# Remaining style points in the generated Lean

Claude: this note is written by Claude (Opus 5), 2026-09-14, from reading
`tests/test10st.ott`'s Lean output after the layout pass in commit 98be425.
Nothing here has been done to the sources; this is the list of what that pass
left behind.

The declarations themselves are in reasonable shape now: doc comments before
types, constructors, metavar abbreviations and defns; binder form for
constructor arguments; `∀` and `→`; one premise per line; no `mutual` around a
singleton; no `_root_.` qualification.  What follows is what a reader still
notices.

## 1. Function headers were not brought in line with constructors

The pass changed `pp_element`, through which constructor arguments are printed,
so a constructor reads `| T_var (X : typvar) : Typ`.  The headers of the
generated *functions* are built elsewhere -- in `src/substs_pp.ml`,
`src/subrules_pp.ml` and `src/defns.ml` -- and were not changed, so the same
file mixes two conventions:

```lean
  | T_arrow (T5 : Typ) (T' : Typ) : Typ      -- constructor
def is_v_of_t (t_6:Term) : Bool :=           -- function
def tsubst_t (t_6:Term) (x5:termvar) (t__7:Term) : Term :=
def fv_t (t_6:Term) :  List termvar :=       -- and a double space after the colon
```

This is the most visible of the leftovers and the easiest to fix: the binder
spelling wants to come from one place rather than from each printer.

## 2. The whitespace squash reaches only the inductive relations

`lean_squash` and `lean_paren` in `src/defns.ml` are applied to the premises and
conclusion of a defn rule.  The clauses of generated functions go through a
different path and still carry the pretty-printer's spacing and its
parentheses:

```lean
  | (t_Lam x t5) => (if  List.elem x5 ([x]) then t5 else (tsubst_t t_6 x5 t5))
  | (t_App t5 t') => (fv_t t5) ++ (fv_t t')
  | (t_Lam x t) => (true)
```

Three things are wrong with these lines: a doubled space after `if`, redundant
parentheses around whole right-hand sides and around `[x]`, and `(true)` for
`true`.  The match patterns are parenthesised too -- `| (t_Var x) =>` -- where
Lean would write `| t_Var x =>`.

## 3. Section comments

`Auxl.big_line_comment` is built for targets whose comments are `(* ... *)`, so
in Lean it produces

```lean
/- - subrules - -/
/- - library functions - -/
```

with the stray inner dashes.  `/- subrules -/` is what is wanted.  `/-
definitions -/` is also emitted once per defnclass, so it repeats before every
block; the Coq output has the same duplication, recorded as C6 in
`notes03-2026-09-14`.

## 4. Blank lines

Four blank lines follow the header comment, and there are doubled blank lines
between sections and after some declarations.  One blank line between top-level
declarations would read better.

## 5. A Bool where a Prop is wanted

A subrule premise appears in a rule as

```lean
  | ax_app : ∀ (x : termvar) (t12 : Term) (v2 : Term),
      (is_v_of_t v2) →
```

`is_v_of_t` has type `Bool`, and a premise position wants a `Prop`; this
elaborates only because Lean silently coerces `b` to `b = true`.  Coq says what
it means, `Is_true (is_v_of_t v2) ->`.  Either write `is_v_of_t v2 = true`
here, or make the subrule predicates `Prop`-valued for Lean as the Coq backend
does under `-coq_expand_list_types true`.  This is the same question as C8 in
`notes03-2026-09-14` and should be settled once for both backends.

## 6. Inhabited is derived whether or not anything needs it

`deriving Inhabited` goes on every type whose group admits it.  The only reason
anything needs it is the panic-indexing `l[i - 1]!` used for an indexed
projection, which `tests/test10st.ott` does not use at all.  If that encoding
changes -- see `notes02-2026-09-14` -- the deriving clauses can go, and with
them the transitive inhabitedness analysis in `pp_rule_list` that decides where
they are safe.

## 7. Test-side, not the printer

- `tests/test10st.ott:29` gives `{{ lean List (termvar×Typ) }}`, with no spaces
  around the product, and `{{ lean }}` embeds in the same file write
  `def bound (x:termvar) (t0:Typ) (g:G) :=` in the same unspaced style.
- That `bound` has no result type and mixes `false` (a `Bool`) in one branch
  with `t0 = t'` (a `Prop`) in another, so it typechecks only through the
  coercion of point 5 and ends up `Prop`-valued.  `False` is what is meant.

## Suggested order, if these are picked up

1 and 3 are small and independent.  2 is slightly more work, because it means
applying the squash where function clauses are assembled rather than where
defn rules are, and the parenthesis-stripping wants care around operators.  4
is trivial once 3 is being touched.  5 and 6 are design decisions rather than
cleanups, and both are already recorded as questions in the earlier notes.
