# R23 build status — Y_GLW_exists axiom retirement

## Headline

R23 mono-task: discharge `tsum_Cp_T_explicit_lt_top_R22` (R22's single
named sorry) at the bottom of `Helpers/GLWGaussianProjectiveLimit.lean`.

**Outcome: Partial.** R23 lands the **summability of the asymptotic
bound** (Full) and the **uniform logarithmic asymptotic**
`(log x)² ≤ 16√x` for `x ≥ 1` (Full); the **per-T pointwise bound**
`Cp_T_explicit T ≤ ENNReal.ofReal (K / (T+1)^(3/2))` requires the
`constL` unfolding + Cauchy-Schwarz inner-dyadic split (~150-300 LOC
of ENNReal arithmetic) and is left as the residual sorry.

**Axiom status:** since T2.1 retains a sorry, `#print axioms
Y_GLW_exists` shows `[propext, sorryAx, Classical.choice, Quot.sound]`.
T3.1 (axiom retirement headline) = Stub. The +500 project bonus does
not trigger. R24 picks up the bound discharge.

## Build state per file (post-R23)

| File | Builds | Sorry count | Status |
|------|--------|-------------|--------|
| `Helpers/GLWKernel.lean` | ✓ | 0 | Full |
| `Helpers/YGLWConstruction.lean` | ✓ | 0 | Full |
| `Helpers/YGLWFromBrownianMotion.lean` | ✓ | 0 | Full |
| `Helpers/SubGaussianGaussianReal.lean` | ✓ | 0 | Full |
| `Helpers/GLWGaussianProjectiveLimit.lean` | ✓ | 1 | Partial (R23 progress) |
| `Helpers/GLWProcess.lean` | ✓ | 0 (transitive 1) | Theorem (transitive sorry from R23 residual) |
| `Helpers/GLWProcessPredicate.lean` | ✓ | 0 | Full |

## R23 lemma map

### Full (new in R23)

* `log_sq_le_sqrt {x : ℝ} (hx : 1 ≤ x) : (Real.log x)^2 ≤ 16 * x^(1/2)` —
  uniform logarithmic asymptotic via `Real.log_le_rpow_div` at
  α = 1/4 (squaring gives the uniform `(log x)² ≤ 16 √x` bound for
  `x ≥ 1`, no N₀ threshold needed). Mirrors the Grok-validated
  α = 1/2 / p = 3/2 route.
* `summable_K_div_succ_rpow_three_halves (K : ℝ) :` —
  `Summable (fun T : ℕ => K / (T+1)^(3/2))` via
  `Real.summable_one_div_nat_rpow` at p = 3/2 > 1, with `summable_nat_add_iff`
  shift to `(T+1)`.
* `K_div_succ_rpow_nonneg (K : ℝ) (hK : 0 ≤ K) :`
  `∀ T, 0 ≤ K / (T+1)^(3/2)` — nonnegativity for the `ofReal_tsum`
  step.
* T = 0 case of the pointwise bound: `Cp_T_explicit 0 = 0` (since
  `M_0 = ofReal(1/(2·0³)) = ofReal(0) = 0`), trivially ≤ any
  nonneg target.

### Partial (R23 retains residual sorry)

* `tsum_Cp_T_explicit_lt_top_R22` —
  the structural proof composes through `ENNReal.tsum_le_tsum`,
  `ENNReal.ofReal_tsum_of_nonneg`, and `ENNReal.ofReal_lt_top`. The
  pointwise bound at T ≥ 1 has a single residual sorry tagged
  `[R23-bound-pointwise]`, gated on `constL` unfolding.

## Imports added

* `import Mathlib.Analysis.PSeries` — for `Real.summable_one_div_nat_rpow`.

## Remaining work for R24

The single residual sorry in `tsum_Cp_T_explicit_lt_top_R22` requires:

1. Unfold `Cp_T_explicit T = (M_T : ℝ≥0∞) * constL ↥S c_T 1 2 2 (1/4) Set.univ`.
2. Unfold `constL` (definition on `BrownianMotion/Continuity/KolmogorovChentsovInequality.lean:142`).
3. Bound `(EMetric.diam (Set.univ : Set ↥S) + 1)^(2-1) ≤ 2`.
4. Bound the inner dyadic tsum via Cauchy-Schwarz on
   `(L + (k+2))² ≤ 2L² + 2(k+2)²`, separating T-dependence from k-dependence.
5. Bound `(log_2 c_T.toReal)² = (log_2(6(T+1)))² ≤ K_log * √(T+1)`
   using the R23 helper `log_sq_le_sqrt` (Full).
6. Bound `M_T * c_T = (1/(2T³)) * 6(T+1) ≤ 6/T²` (in ENNReal) for T ≥ 1.
7. Combine: `Cp_T_explicit T ≤ ofReal(K_main / (T+1)^(3/2)) + ofReal(K_minor / (T+1)^2)`.
8. Use `ofReal a + ofReal b ≤ ofReal(a + b) ≤ ofReal(2K_total / (T+1)^(3/2))`
   for the unified bound form.

Each step is mechanical but the ENNReal arithmetic is verbose. Estimate
~150-300 LOC for the discharge.

## Project-wide status

Previous rounds R13-R22 brought
`Helpers/GLWGaussianProjectiveLimit.lean` from many sorries down to 1.
R23 makes structural progress (summability + asymptotic helpers Full)
without closing the final residual.

**Cumulative project bonus** (axiom retirement): NOT TRIGGERED.
Awaiting R24 closure of `[R23-bound-pointwise]`.

## Test commands

```bash
# Full build
lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit

# Axiom check (will show sorryAx until R24)
echo 'import FormalConjectures.ErdosProblems.Helpers.GLWProcess
open Erdos524.Helpers
#print axioms Y_GLW_exists' | lake env lean --stdin
```
