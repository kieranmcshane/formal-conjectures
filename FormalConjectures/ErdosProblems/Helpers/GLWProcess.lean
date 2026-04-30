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

import FormalConjectures.ErdosProblems.Helpers.GLWKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Phase 2 / Node 1B — GLW process existence axiom (stepping-stone)

Single axiom `Y_GLW_exists` asserting the existence of a probability space
carrying a centered Gaussian process `Y_GLW : ℝ → Ω → ℝ` with covariance
`K_GLW(u, v) = (1 - exp(-(u+v)))/(u+v)` (the kernel of `∫₀¹ e^{-us} dB(s)`),
joint Gaussianity, continuous sample paths, and a.s. tail decay
`sup_{u ≥ T} |Y u| → 0`.

**Materially smaller than the GLW axioms it stages toward**
(`gao_li_wellner_small_ball_upper` and `_lower` in `524.lean`): asserts only
existence + covariance + Gaussianity + sample-path regularity, **no** small-ball
estimate. The cubic-exponential bound — the actual hard probabilistic content
of Gao–Li–Wellner (2010) — is derived downstream via the Node 3 helper
(`GaussianGridSmallBall`), Node 2's hierarchical-Cauchy comparison, and
Node 4's discretization.

**Existential over `(Ω, μ)`.** Quantifying universally over the probability
space is mathematically inconsistent on the trivial 1-point space (no
non-trivial Gaussian process can live there) — the same false-for-trivial-`Ω`
flaw as `gao_li_wellner_small_ball_upper`. Producing `Ω` from the construction
matches Daniell–Kolmogorov, which builds `Ω = ℝ^[0,∞)` with the cylinder
measure.

**Tail-decay rationale.** `σ²(T) → 0` alone gives `L²`-convergence, not
pointwise a.s. eventual smallness. The actual justification of the conjunct:
Borell on `sup_{u ∈ [T, T+1]} |Y u|` (Ledoux *Concentration of Measure*, §1.3
eq. (1.7)), using continuous-paths separability + σ²-decay; then Borel–Cantelli
over the integer-indexed sequence `T = 1, 2, 3, ...`. The conjunct itself is
the standard packaging.

**Integrability conjuncts.** Mathlib's `∫ ω, f ω ∂μ` returns `0` for
non-integrable `f`, so without explicit `Integrable (Y u) μ` /
`Integrable (Y u · Y v) μ` the centeredness and covariance conjuncts would be
vacuously true for non-integrable `Y`. The `IsGaussian` conjunct on pushforward
measures does **not** imply integrability of `Y u` itself (different measure).

**Materially-smaller justification.**

| Claim | GLW axiom | This axiom |
|---|---|---|
| Existence of `Y` | implicit | explicit |
| Quantifier over `(Ω, μ)` | universal (false on trivial Ω) | existential (consistent) |
| Integrability of `Y u`, `Y u · Y v` | unstated | conjuncted |
| Covariance kernel | unconstrained | `K_GLW` |
| Joint Gaussianity | unstated | conjuncted |
| Continuous sample paths | unstated | conjuncted |
| Sample-path tail decay | unstated | conjuncted |
| Small-ball cubic bound | **claimed** | **not claimed** |

**Retirement roadmap.** The deterministic-analytic content of the
`Y_GLW(u) = ∫₀¹ exp(-us) dB(s)` Wiener-integral construction lives in
`Helpers/YGLWConstruction.lean`. That file proves:

* the **covariance integral identity** `K_GLW(u, v) = ∫₀¹ exp(-(u+v)·s) ds`,
* the **Mercer / L²-inner-product representation** `K_GLW(u, v) =
  ⟨exp(-u·), exp(-v·)⟩_{L²([0,1])}`,
* **positive semi-definiteness** of `K_GLW` via the integral-of-squares
  representation,
* **variance decay** `K_GLW(u, u) → 0` as `u → ∞` (deterministic ground
  floor for the tail-decay conjunct),
* **L² Hölder-1 bound** `‖exp(-u·) - exp(-v·)‖²_{L²([0,1])} ≤ |u - v|²`
  (deterministic ground floor for Kolmogorov–Chentsov continuous paths).

The companion bridge file `Helpers/YGLWFromBrownianMotion.lean`
packages the matrix-side preconditions for an eventual retirement via
the [Degenne–Pfaffelhuber `brownian-motion`]
(https://github.com/RemyDegenne/brownian-motion) project (which already
implements the kernel-generic projective-limit construction). It
proves:

* `glwCovMatrix`: the K_GLW finite-grid Gram matrix.
* `glwCovMatrix_PosSemidef`: positive semi-definiteness, the
  precondition for `multivariateGaussian`.
* `gramMatrixL2_PosSemidef`: a **Mathlib-PR-shaped abstraction**
  showing that the Gram matrix of any continuous family of L²([0,1])
  functions is PSD; `glwCovMatrix_PosSemidef` is the K_GLW special
  case.

Until the `brownian-motion` project's API is available in our
toolchain (toolchain alignment pending), the axiom cannot be
discharged to a theorem. When that lands, the discharge reduces to a
5-step proof in `YGLWFromBrownianMotion.lean`, each step a one-line
application of a project-API call to the kernel-side content already
proved.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory

/-- **Stepping-stone axiom (Phase 2 Node 1B, v3).** Existence of a probability
space `(Ω, μ)` carrying a centered Gaussian process
`Y_GLW : ℝ → Ω → ℝ` with covariance `K_GLW(u, v) = (1 - exp(-(u+v)))/(u+v)`,
joint Gaussianity, continuous sample paths, and a.s. tail decay.

Consumers extract via
  `obtain ⟨Ω, _mS, μ, Y, hY_prob, hY_meas, hY_int, hY_int_prod, hY_centered,`
  `       hY_cov, hY_gauss, hY_paths, hY_tail⟩ := Y_GLW_exists`
and then `haveI : IsProbabilityMeasure μ := hY_prob` to bring the
probability-measure instance into scope. -/
axiom Y_GLW_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (Y : ℝ → Ω → ℝ),
      IsProbabilityMeasure μ ∧
      -- measurability
      (∀ u, Measurable (Y u)) ∧
      -- integrability of marginals and pairwise products (load-bearing
      -- because `∫` returns `0` for non-integrable functions)
      (∀ u, Integrable (Y u) μ) ∧
      (∀ u v : ℝ, Integrable (fun ω => Y u ω * Y v ω) μ) ∧
      -- centeredness
      (∀ u, ∫ ω, Y u ω ∂μ = 0) ∧
      -- covariance kernel
      (∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
        ∫ ω, Y u ω * Y v ω ∂μ = K_GLW u v) ∧
      -- joint Gaussianity: every finite linear combination of `Y u_i` is
      -- Gaussian on ℝ. Load-bearing for downstream Anderson-inequality use
      -- inside Node 6 via `GaussianBoxProb.anderson_lower`.
      (∀ (n : ℕ) (us : Fin n → ℝ) (cs : Fin n → ℝ),
        IsGaussian (Measure.map (fun ω => ∑ i, cs i * Y (us i) ω) μ)) ∧
      -- continuous sample paths (Kolmogorov–Chentsov)
      (∀ᵐ ω ∂μ, Continuous (fun u => Y u ω)) ∧
      -- sample-path tail decay (Borell on `sup_{[T,T+1]}` + Borel–Cantelli)
      (∀ ε > 0, ∀ᵐ ω ∂μ, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε)

end Erdos524.Helpers
