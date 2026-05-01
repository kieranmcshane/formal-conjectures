# R33-C / T1.1 — `kernel_decay` audit (kernel_geometric_decay verdict)

## Context

R33-C brief (post-Grok): the brief identified `kernel_decay` as having a
wrong-shape pointwise form (residual issue from R33-A → R33-B), and
flagged a Cowork-detected potential issue that **the OTHER decay
hypothesis `kernel_geometric_decay` may ALSO be unsatisfiable for
`kernel_even_plus`**.  The brief's worry: if R31 reported
`kernel_even_plus_geometric_decay` closed without sorry, either (i) the
closure is wrong, (ii) the lemma form differs from the axiom signature,
or (iii) some math trick was used.

**T1.1 is the verification step before T2.3 fires.**

## Current axiom signature (verbatim from `Helpers/StochasticProcessAxiom.lean:83-97`)

```lean
axiom kmt_aided_gaussian_process
    (kernel : ℝ → ℕ → ℕ → ℝ)
    (_kernel_bound : ∀ u, 0 ≤ u → ∀ k n, |kernel u k n| ≤ 1)
    (_kernel_decay : ∀ ε > 0, ∃ U > 0, ∀ n : ℕ, 1 ≤ n →
      ∀ u ≥ U, ∀ k : ℕ, 1 ≤ k → k ≤ n → |kernel u k n| ≤ ε)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha : Erdos524.IsRademacherSequence a) :
    ∃ (Y : ℝ → Ω → ℝ), …
```

The axiom takes **two** kernel hypotheses:

1. `_kernel_bound` — pointwise `|kernel u k n| ≤ 1` for `u ≥ 0`.
2. `_kernel_decay` — pointwise eventual smallness (R33-B-tightened to
   `1 ≤ k ≤ n`).

## Verdict per kernel hypothesis

### `_kernel_bound`: **Sound**

- **Form satisfiable for `kernel_even_plus`?** Yes. Closed cleanly in
  `kernel_even_plus_bound` at `TwoDimKMTFromOneDim.lean:171-193`.
- **Form satisfiable for `kernel_odd_minus`?** Yes. Closed cleanly in
  `kernel_odd_minus_bound` at `TwoDimKMTFromOneDim.lean:199-229`.
- No R33-C action needed.

### `_kernel_decay`: **Wrong-shape (pre-R33-C)**

- The pointwise form `∀ k, 1 ≤ k → k ≤ n → |kernel u k n| ≤ ε` is
  unsatisfiable for `kernel_even_plus` at `(k = 1, n` large`)`, where
  `|kernel_even_plus u 1 n| = √(1/2) · exp(-u/n) → √(1/2)` as
  `n → ∞`. See R33-B file-level docstring at
  `TwoDimKMTFromOneDim.lean:231-273` and the TAG'd sorries at
  `TwoDimKMTFromOneDim.lean:284-292` (T2.1.a) and `:304-311` (T2.1.b).
- **R33-C T2.1 mandatory action**: replace with Path A
  (normalized L²-energy form), Grok-validated.

### `kernel_geometric_decay`: **Does not exist in codebase**

This is the key T1.1 finding.

- `git grep kernel_geometric_decay` across the entire repo: zero
  matches in any `.lean` file.  Verified via:

  ```
  grep -rn "kernel_geometric_decay\|geometric_decay\|kernel_even_plus_geometric_decay" \
       FormalConjectures/ 2>&1
  ```

  returns **no hits** in `.lean` sources.

- The current `kmt_aided_gaussian_process` axiom signature has exactly
  the two hypotheses listed above. There is no third
  `_kernel_geometric_decay` hypothesis.

- The R31 / R32 round summaries do not appear to reference a
  `kernel_geometric_decay` lemma either. The `KMTOptionCPlan.md` and
  `R31BuildStatus.md` documents track `kernel_*_bound` and (later)
  `kernel_*_decay` lemmas, but no geometric-decay variant.

- **Conclusion**: the brief's "OTHER decay hypothesis
  `kernel_geometric_decay`" is a phantom — likely conflated with an
  earlier-round design exploration or the R30 brief sketch that was
  never instantiated.  No closure exists to be wrong-shape, no axiom
  hypothesis exists to be replaced.

### T2.3 trigger

T2.3 is **conditional on T1.1 verdict being wrong-shape or
hidden-sorry for `kernel_geometric_decay`**.  Since
`kernel_geometric_decay` does not exist, **T2.3 does not fire**.
Mark T2.3 as not-applicable.  R33-C continues with T2.1 / T2.2 / T2.4
/ T2.5 as the four mandatory Lean-code outcomes.

## Honest residual concern

The R31 round summary is not pulled into this audit (the round
artefacts are git-archived, and the active `R31BuildStatus.md` tracks
`kernel_*_bound` only).  If a future round re-introduces a geometric
decay variant under a different name (e.g.
`kernel_*_exponential_decay`, `kernel_*_geometric`), this audit's
"phantom" verdict would need re-checking against that name.

For R33-C specifically, the codebase as of commit `6ae1b2d`
(`r33-b-linear-combo`) has only the two listed hypotheses and the
phantom verdict stands.

## R33-C action item summary

| Item | Verdict | Action |
|------|---------|--------|
| `_kernel_bound` | Sound | none |
| `_kernel_decay` | Wrong-shape | T2.1: replace with Path A; T2.2: close with witness `U = 1/(4ε)` |
| `kernel_geometric_decay` | Does not exist | T2.3 not triggered |
