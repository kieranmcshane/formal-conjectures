# Round 11 Predictions — Cowork Claude

**Committed before round start.**
Round target: **retire the `Y_GLW_exists` axiom** in
`Helpers/GLWProcess.lean:82` by explicit construction
`Y(u) = ∫₀¹ e^{-us} dB(s)` as a Wiener integral.

Recalibration applied: prior over-pessimism factor escalated from 2x
to **2.5x**. Round 10 still over-shot expectations despite 2x correction
(Pred 1 at 75% was near-certain, Pred 7 at 65% was ~85-90%).
Confidences below are intentionally pushed up to compensate.

## Predictions

| # | Prediction | Confidence | Stake |
|---|------------|-----------|-------|
| 1 | The `Y_GLW_exists` axiom is replaced by an explicit theorem (i.e., the literal word `axiom` on line `Y_GLW_exists` is gone, replaced by `theorem` or `def` + theorem). | 80% | 80 |
| 2 | At least 250 lines of substantive math added across helper files (likely a new `Helpers/GLWProcessConstruction.lean` or similar). | 90% | 90 |
| 3 | Full build of `FormalConjectures.ErdosProblems.«524»` remains green. | 95% | 95 |
| 4 | Net axiom count drops from 2 to 1 (i.e., only `two_dim_KMT_coupling` remains). | 80% | 80 |
| 5 | Local Claude hits the time floor (90-min wall clock, no early stop). | 80% | 80 |
| 6 | The covariance computation `∫₀¹ exp(-us)·exp(-vs) ds = (1-exp(-(u+v)))/(u+v)` is proven as a named sub-lemma. | 85% | 85 |
| 7 | At least 2 distinct named lemmas about Wiener integrals or Gaussian-process construction are cited from Mathlib (i.e., 2 lemmas not previously used in the campaign). | 80% | 80 |
| 8 | The constructed `Y` is shown to be `IsGaussianProcess` (or whatever the Mathlib name is for "all finite-dim distributions are jointly Gaussian"). | 70% | 70 |

**Total at risk:** 660 units. (Out of current balance 1240.)

## Resolution mechanics (Brier-style)

Same as Rounds 9, 10:
- YES → gain `(100 − c)` units
- NO → lose `c` units
- PARTIAL → judged by Kieran in validation step.

## Stretch goals (mandatory cascade if Target A closes early)

The "no early-exit even when criteria met" rule remains. Stretch
cascade:

1. **Stretch A**: prove continuity of `Y(u)` in `u` (uniform on
   compacts, via Kolmogorov's continuity criterion or direct L²
   argument).

2. **Stretch B**: identify the L²([0,1]) inner-product structure
   underlying the Wiener integral and expose
   `Y_inner_product : ⟨exp(-u·), exp(-v·)⟩_L² = K_GLW(u,v)`.

3. **Stretch C**: refactor `IsGLWProcess` predicate (if needed) to
   expose `Y` as a Gaussian process with the correct covariance
   in a way usable by downstream consumers.

4. **Stretch D**: prove that any two GLW processes are equidistributed
   (uniqueness in law). This would let downstream code drop the
   "exists Y" weakness and work with the canonical witness.

5. **Stretch E**: discharge any consumer of `Y_GLW_exists` in
   `524.lean` or `Helpers/` that currently uses the axiom — make them
   use the new theorem directly.

## Notes for Kieran (validator)

- All 8 predictions are independent.
- Pred 1 + Pred 4 are joint-correlated (both require axiom retirement).
  Treating them as independent is intentional: Pred 1 has a stricter
  resolution criterion (literal `axiom` keyword gone) while Pred 4
  has a weaker one (axiom *count* down by 1, which could be satisfied
  even if the axiom is renamed/relocated).
- Pred 8 is the hardest (Gaussian-process membership) and the lowest
  confidence. If Mathlib's `IsGaussianProcess` API is incomplete, this
  may resolve PARTIAL.
- Pred 5 is set to 80% (up from 70% in R10) because R10 hit the floor
  perfectly. Trend is favorable.
