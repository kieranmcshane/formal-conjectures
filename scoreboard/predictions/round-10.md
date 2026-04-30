# Round 10 Predictions — Cowork Claude

**Committed before round start.**
Round target: prove `(hierCauchyG m).PosDef` (classical Cauchy-matrix
positive definiteness).

Recalibration applied: prior over-pessimism factor escalated from 1.5x
to **2x**. Round 9 still over-shot expectations despite 1.5x correction.
Confidences below are intentionally pushed up.

## Predictions

| # | Prediction | Confidence | Stake |
|---|------------|-----------|-------|
| 1 | `hierCauchyG_PosDef` (or equivalent named theorem) proved without sorry, in some helper file. | 75% | 75 |
| 2 | At least 200 lines of substantive math added across helpers (likely a new `Helpers/HierCauchyPosDef.lean` or extension of `HierCauchyFacts.lean`). | 85% | 85 |
| 3 | Full build of `FormalConjectures.ErdosProblems.«524»` remains green. | 95% | 95 |
| 4 | No new axiom introduced (axiom count stays at 2). | 90% | 90 |
| 5 | Local Claude hits the time floor (90-min wall clock, no early stop, this time fully). | 70% | 70 |
| 6 | The classical Cauchy integral identity `1/(g_i + g_j) = ∫₀^∞ exp(-(g_i+g_j)·t) dt` is proven as a sub-lemma. | 80% | 80 |
| 7 | `glwBoxProb_anderson_upper_via_round9_mm` (Round 9, conditional on `hierCauchyG.PosDef`) becomes unconditional via the new theorem — i.e. an unconditional version is also proven in this round. | 65% | 65 |

**Total at risk:** 560 units. (Out of current balance 1100.)

## Resolution mechanics (Brier-style)

Same as Round 9:
- YES → gain `(100 − c)` units
- NO → lose `c` units
- PARTIAL → judged by Kieran in validation step.

## Stretch goals (mandatory cascade if Target A closes early)

The "no early-exit even when criteria met" rule remains. Stretch
cascade:

1. **Stretch A** (target of Pred 7): make
   `glwBoxProb_anderson_upper_via_round9_mm` unconditional. This is
   a clean composition: feed `hierCauchyG_PosDef` into the existing
   conditional theorem.

2. **Stretch B**: discharge the V1 instance's `anderson_upper` field
   in `Helpers/GLWBoxProbInstance.lean` using the new unconditional
   bound. This is the **first** V1 field that the Round 9 + 10 work
   together unblock.

3. **Stretch C**: attempt to close the central
   `gao_li_wellner_small_ball_upper` sorry by exploiting the now-discharged
   V1 anderson_upper field, via the optimization
   `m(ε) ~ |log ε|²` route. The Karhunen-Loève piece is still a
   Mathlib gap, but a partial reduction (truncated chaining) may be
   doable.

4. **Stretch D**: prove `(hierCauchyG m).PosSemidef` as a weaker form
   if `PosDef` blocks, and document precisely what's missing for the
   strict positivity.

5. **Stretch E**: write 2–3 corollaries of `hierCauchyG.PosDef` that
   downstream consumers will likely need (e.g. invertibility,
   `det > 0`, `realMatrixSqrt_hierCauchyG.PosDef`).

## Notes for Kieran (validator)

- All 7 predictions are independent.
- The big stake is on Pred 1, Pred 2, Pred 6 (math content) and Pred 5
  (discipline). Pred 3, 4 are safety predictions (high confidence,
  low risk) for stability.
- Pred 7 is the "cascade" stretch — included as 65% because it's a
  pure composition once Pred 1 lands, but might fail if there's a
  signature-mismatch issue between the conditional and the new
  unconditional version.
