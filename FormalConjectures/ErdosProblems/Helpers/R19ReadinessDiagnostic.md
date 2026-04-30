# R19 Readiness Diagnostic

Closing-of-R18 diagnostic listing the prioritized open work that will
turn into the R19 manifest. R18's headline result is the witness
refactor for `glwGaussianLimit_Y_GLW_existence` (conjuncts 8 Full,
conjuncts 3-7 re-derived from R17 via ae-transfer); the residual
blocker is conjunct 9 (tail decay).

## Blocker A (priority A) — Conjunct 9: tail decay

**State:** the existential `∀ ε > 0, ∀ᵐ ω, ∃ T₀, ∀ u ≥ T₀, |Y u ω| ≤ ε`
is the **sole remaining sorry** in `glwGaussianLimit_Y_GLW_existence`
after R18. Tag: `R18-blocker`.

**Why it's hard:** the witness `Y u ω = Y' u.toNNReal ω` ranges over
continuum `u : ℝ`, not just integer points. To turn integer-Borel-
Cantelli (which is feasible) into a continuum statement, we need
either (i) a *uniform* sup-bound on Hölder constants of the
modification, or (ii) a process-level sup-tail bound (Borell-TIS).

**Mathlib gaps blocking R19 closure:**

1. **No Gaussian-tail bound in Mathlib at HEAD.** The marginal
   Gaussian tail `P(|X| > t) ≤ 2 exp(-t²/(2σ²))` for `X ~ N(0, σ²)`
   is not a named lemma. Only the MGF / charFun / variance
   infrastructure exists in `Mathlib.Probability.Distributions.Gaussian.Real`.
   Would require ~50 LOC PR to Mathlib (or in-project bypass via
   Markov on 4th moment, costing ~2 LOC per step but losing the
   exponential summability).
2. **No measurable Hölder-constant for the modification.**
   `exists_modification_holder'''` returns the per-ω Hölder constant
   `C(ω)` only as an existential — there is no API exposing
   `(ω ↦ C(ω))` as a measurable function. Without this, the
   Borell-TIS-style sup-bound `P(sup_{[T,T+1]} |Y| ≥ ε) ≤ ...`
   cannot be assembled even with the marginal tail.
3. **No Borell-TIS in Mathlib or brownian-motion.** This is the
   canonical route; both libraries currently leave it out.

**Resolution options for R19:**

* **Option A1 — Mathlib-PR Gaussian tail + L⁴ Borel-Cantelli on
  rationals.** Prove a Mathlib-targeted Gaussian tail lemma; combine
  with a careful enumeration of rational `u ∈ [1, ∞)` (variance
  bounded by `1/(2 floor(u))`); 4th-moment Markov on each rational
  point gives summable tails. The continuum-decay step then uses
  continuity of paths to identify `sup |Y(u)|` with `sup_{u ∈ ℚ} |Y(u)|`
  on each compact, but the union-bound diverges across all rationals
  in `[T, T+1]`. **Verdict: still requires sup-control. Does not close.**
* **Option A2 — In-project measurable Hölder constant.** Write a new
  variant of `exists_modification_holder'''` that exposes the Hölder
  constant as a measurable random variable, using
  `IsLimitOfIndicator.measurable_edist`-style arguments to lift the
  countable-supremum representation to measurability. ~200 LOC, deep
  brownian-motion-library work. **Verdict: feasible; ~3 waves.**
* **Option A3 — Wait for upstream Borell-TIS.** Track the
  `brownian-motion` library; when Borell-TIS lands, plug in directly.
  Outside our control timing-wise.

**Recommended R19 path:** A2. The measurable-Hölder-constant lift is
a substantial but bounded piece of work, and unblocks not just
conjunct 9 but also any future quantitative path-regularity claims
about GLW.

## Blocker B (priority B) — Phase A: Slepian comparison

**State:** unchanged from R18; `Slepian_GLW_vs_OU` and the
`gaussianDensity` sign lemma are signature placeholders in
`PhaseAUpperBound.lean`.

**Resolution path (unchanged from R18):**

1. Density-monotonicity sub-lemma for jointly Gaussian pairs
   (Pitt 1977, Joag-Dev 1983 elementary form).
2. Path-of-covariances integration.

**Mathlib gap:** Slepian's inequality is not in Mathlib. Density-
monotone form has elementary proofs that don't require multivariate
Gaussian apparatus.

**Estimated effort:** ~300 LOC / 3 waves. Independent of Blocker A.

## Blocker C (priority B) — Phase A: Sudakov-Fernique

Depends on Blocker B (Slepian). ~150 LOC. Standard SF reduction via
incremental Slepian along Gaussian interpolation
`Z_t(λ) = √(1-λ) X_t + √λ X'_t`.

## Blocker D (priority C) — Two-dim KMT retirement

Unchanged from R18 (`R18ReadinessDiagnostic.md` Blocker 5). 1-D KMT
not in Mathlib at HEAD; 2-D coupling adds substantial coordinate-by-
coordinate construction. ~1000+ LOC / 6+ waves.

## Summary table

| # | Blocker | Priority | Effort | Unblocks |
|---|---------|----------|--------|----------|
| A | Conj 9 tail decay (measurable Hölder route) | A | 200 LOC / 3 waves | `Y_GLW_exists` axiom retirement (project headline) |
| B | Slepian comparison | B | 300 LOC / 3 waves | Phase A upper bound |
| C | Sudakov-Fernique | B (after B) | 150 LOC | Phase A upper bound |
| D | Two-dim KMT | C | 1000+ LOC / 6+ waves | A2-axiom retirement |

R19's natural focus is Blocker A. Closing it is the single highest-
leverage move in the project: it retires the conjunct-9 sorry, which
in turn retires the `sorryAx` from `Y_GLW_exists`, which delivers the
**first axiom retirement of the Erdős 524 project** and the +500
project bonus that has been gated since R13.

## R18 → R19 axiom delta

```
R18 (current): sorryAx + propext + Classical.choice + Quot.sound
R19 (target after A1): propext + Classical.choice + Quot.sound  ← clean
```

The two non-`sorry` axioms (`propext`, `Quot.sound`) are Lean's
unconditional kernel-level axioms; their presence after R19 is
expected and not a soundness issue. `Classical.choice` enters via
`exists_modification_holder'''`'s `Classical.choose` and is also
unavoidable for any non-constructive existence theorem.

## Calibration notes

R18 calibration check: the round budgeted T1.1+T1.2+T1.3 at ~370 pts
ceiling; all three landed Full, on a substantially smaller manifest
than R17 (14 outcomes vs 35). Phase 2 (T2.x) was honestly stubbed at
zero — the Mathlib gap is real and the 200-LOC "elementary route"
estimate in `R18ReadinessDiagnostic.md` underestimated the
measurable-Hölder-constant requirement. This is now the headline
blocker for R19.
