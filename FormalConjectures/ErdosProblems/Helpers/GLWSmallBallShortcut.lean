/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.ErdosProblems.Helpers.GaussianParametricAnalysis

/-!
# R48-T3.2 — GLW small-ball shortcut prep (compression-bundle item iv)

**R48 stretch deliverable** per the strategic post-R47 Grok pre-flight
Q5 BONUS verdict: GLW determinant shortcut for A4/A5 honest closure
~110-150 LOC (vs ~150-300 LOC for the KL+Talagrand chain). Path
B'-style structural shortcut.

This file sets up the R50-R51 GLW shortcut closure target signatures
without inflating mainline debt — following the R46-T3.1 pattern in
`GaussianParametricAnalysis.lean`, the target signatures live in this
docstring as a markdown code block, NOT as TAG'd Stubs. R50-R51 will
land them as Full theorems (or honest TAG'd Stubs at that time).

## Compression bundle context

Per R48-T2.3 status doc, the compression bundle items in play are:

* (i) Path γ' Phase 2 body close — **R48 attempted, T2.1 ABORTED**
  per Q3 framing audit (see `R48_T1_PathGammaPrimeAudit.md`).
* (iii) Track D round 3 cleanup — BTIS-via-Chernoff sub-lemma 3 Full
  closure. ~70% plausibility per R47 process discipline.
* **(iv) GLW shortcut for A4/A5 — this file's R50-R51 scope.**
  ~75% plausibility per Grok Q5 verdict. Net retirement: -2 sorries
  if A4 + A5 both land Full.

R48 stretch lands the imports + scaffolding; R50-R51 ships the bodies.

## Target signatures (R50-R51 scope, NOT yet landed as Stubs)

The following are the consumer-facing target signatures for the GLW
determinant shortcut. They are listed here as named-target theorems so
that R50-R51 rounds can find them by grep without ambiguity.

### Lemma 4.1 (GLW det-route bridge)

```
-- R50 candidate (NOT YET LANDED):
theorem glw_det_route_lower_bound
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) (h_kernel : GLWKernel hierarchy B) :
    ∃ c : ℝ, 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      Real.exp (-c * ε^(-2 / (n : ℝ))) ≤
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε)
```

Recipe (Grok Q5 BONUS): bound the Gaussian small-ball probability
below by a determinant-driven exponential, using the GLW projective
limit + `det_CFC_sqrt_pos_of_posDef` (R46-T2.1) + uniform spectral
lower bound from `posDef_min_eigenvalue_pos` (R46-T2.2). Estimated
~50-70 LOC.

### Lemma 4.2 (GLW det-route upper bridge)

```
-- R50 candidate (NOT YET LANDED):
theorem glw_det_route_upper_bound
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) (h_kernel : GLWKernel hierarchy B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε →
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε) ≤
        C * Real.exp (-c_upper hierarchy * ε^(-2 / (n : ℝ)))
```

Recipe: dual of Lemma 4.1, uses the same R46 helpers + the existing
`GLWUpperProof.gao_li_wellner_small_ball_upper_kernel_bridge`.
Estimated ~50-70 LOC.

### A4 closure (`524.lean` consumer target)

```
-- R51 candidate (NOT YET LANDED):
theorem gao_li_wellner_small_ball_lower_via_det_route
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) :
    ∃ c : ℝ, 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      Real.exp (-c * ε^(-2 / (n : ℝ))) ≤
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε)
```

Closes the A4 axiom via Lemma 4.1 + the GLW kernel construction.
Estimated ~10-15 LOC of composition. **-1 sorry mainline retirement.**

### A5 closure (`524.lean` consumer target)

```
-- R51 candidate (NOT YET LANDED):
theorem gao_li_wellner_small_ball_upper_via_det_route
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) :
    ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε →
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε) ≤
        C * Real.exp (-c_upper hierarchy * ε^(-2 / (n : ℝ)))
```

Dual of A4 closure via Lemma 4.2. Estimated ~10-15 LOC. **-1 sorry
mainline retirement.**

## Mathlib API status (R48-T1.1 audit grounding)

All Mathlib citations below verified at `mathlib4 @ 25ce63313608` +
`brownian-motion @ 91267abd71bd`:

* `Matrix.PosDef.eigenvalues_pos` — `Mathlib/Analysis/Matrix/PosDef.lean:85`
* `Matrix.PosSemidef.det_nonneg` — `Mathlib/Analysis/Matrix/PosDef.lean:51`
* `det_CFC_sqrt_eq_sqrt_det` — `Helpers/MultivariateGaussianPdf.lean:171`
  (R46-T2.1 Full)
* `det_CFC_sqrt_pos_of_posDef` — `Helpers/MultivariateGaussianPdf.lean:195`
  (R46-T2.1 corollary Full)
* `posDef_min_eigenvalue_pos` — `Helpers/PhaseAUpperBound.lean:245`
  (R46-T2.2 Full)
* `Metric.ball_pi` — `Mathlib/Topology/MetricSpace/Pi.lean` (verified
  at pin)
* `gao_li_wellner_small_ball_upper_kernel_bridge` —
  `Helpers/GLWUpperProof.lean` (existing R29-R34 work)

## R48 stretch outcome

This file shipped at T+~1:30 as part of T3.2 stretch. **No new TAG'd
Stubs added** — debt-neutral. R50-R51 will land the bodies above as
Full theorems (or honest TAG'd Stubs at that time, per the R46-T3.1
Cowork pattern in `GaussianParametricAnalysis.lean`).

R48 mainline net retirement remains 0; this stretch deliverable is
**preparatory infrastructure** for R50-R51 compression bundle item
(iv) execution. Cumulative R48-R52 mainline retirement target: ~2
(R40 Stub + Phase 2 body) + Track D round 3 contribution (-2 to -3) +
this file's R50-R51 contribution (-2 if both A4/A5 land) = ~6-7
retirements jointly.

See `Helpers/PhaseV2R48Status.md` and
`Helpers/R48_T1_PathGammaPrimeAudit.md` for the round status doc +
framing audit. -/

namespace Erdos524.Helpers.GLWSmallBallShortcut

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Real MatrixOrder

/-! ## Imports + scaffolding only — no new TAG'd Stubs in R48 stretch

This namespace is reserved for R50-R51 GLW shortcut closure targets.
The signatures listed in this file's docstring above will land as
Full theorems (or honest TAG'd Stubs at that time) in those rounds.

R48 stretch leaves this namespace empty by design to avoid debt
inflation (R46-T3.1 pattern).

R48 stretch import set is intentionally minimal
(`GaussianParametricAnalysis` only, which transitively brings the
needed `multivariateGaussian` + R46 helpers); R50-R51 will expand
imports to include `MultivariateSmallBallUpper`,
`GLWGaussianProjectiveLimit`, `GLWUpperProof`, and `GLWLowerProof`
as the theorem bodies are written. -/

end Erdos524.Helpers.GLWSmallBallShortcut
