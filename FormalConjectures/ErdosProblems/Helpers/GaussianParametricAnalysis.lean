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

import FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf
import FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound

/-!
# R46-T3.1 — Gaussian Parametric Analysis library

**Cross-track synergy library extracted at R46 per Grok R46 pre-flight Q5.**

This file consolidates the foundational analytic helpers around the
multivariate Gaussian density `multivariateGaussianPdf` and PosDef
covariance matrices needed by:

* **Track A (mainline)** — Phase 2 body Full close (R47+ scope):
  uniform Gaussian tail majorant on compact PosDef sets enables the
  dominated-convergence step in differentiation under the integral sign
  for `multivariateGaussianOrthantCDF`.
* **Track C (1D KMT formalisation)** — round 2 quantile measurability:
  reuses `posDef_min_eigenvalue_pos` to establish uniform pdf bounds on
  the Gaussian quantile inverse.
* **Track D (BTIS honest formalisation)** — round 2 Herbst density chain
  rules: reuses `det_CFC_sqrt_eq_sqrt_det` + `posDef_min_eigenvalue_pos`
  for the closed-form Lebesgue density factor in the Herbst / OU bridge.

## R46 deliverables (Full, no Stubs)

1. **Re-exports of R46-T2.1 sub-lemma (a) `det_CFC_sqrt_eq_sqrt_det`** —
   `(CFC.sqrt S).det = √(det S)` for PosSemidef S. Composition of
   `CFC.sqrt_mul_sqrt_self` + `Matrix.det_mul` +
   `Real.sqrt_eq_iff_mul_self_eq`. See
   `Helpers/MultivariateGaussianPdf.lean`.

2. **Re-exports of R46-T2.2 PosDef minimum-eigenvalue helpers**
   (`posDef_min_eigenvalue_pos`, `posDef_min_eigenvalue_witness`) — for
   PosDef M with `[Nonempty n]`, `∃ c > 0, ∀ i, c ≤ eigenvalues i`.
   This is the framing-corrected Hermitian-subspace version of the
   (mathematically false) Grok claim "`Matrix.PosDef.isOpen`" in
   `Matrix n n ℝ`. See `Helpers/PhaseAUpperBound.lean` for the body.

## R47+ scope (documented but not yet implemented)

The following theorems are scoped here as the consumer-facing API but
lie outside R46's mandatory floor. Each is a separate sub-round
deliverable:

3. **Uniform Gaussian tail bound on compact PosDef sets** — for compact
   `K ⊂ Mat(n, ℝ)` with `K ⊆ {Σ | Σ.PosDef}`, exists `C, c > 0` such
   that `∀ Σ ∈ K, ∀ x, multivariateGaussianPdf S x ≤ C exp(-c‖x‖²)`.
   Proof composes `posDef_min_eigenvalue_pos` (uniform λ_min lower
   bound on K via continuity of eigenvalues) + `det_CFC_sqrt_pos_of_posDef`
   (uniform `(det Σ)^(-1/2)` upper bound on K). Estimated ~60-100 LOC.

4. **Parametric differentiation under the integral sign for Gaussian
   families** — for parametric integrand `(σ, x) ↦ f(σ, x) g(σ, x)` with
   `g = multivariateGaussianPdf σ` and `f` differentiable with locally
   integrable Lipschitz-on-compact bounds, the integral
   `σ ↦ ∫ f(σ, ·) g(σ, ·) dx` is differentiable. Apply
   `MeasureTheory.hasFDerivAt_integral_of_dominated_loc_of_lip`
   (Mathlib `Analysis/Calculus/ParametricIntegral.lean:164`). Estimated
   ~40-80 LOC.

5. **Local stability of PosDef under Hermitian perturbations** — for
   `M.PosDef`, exists `ε > 0` s.t. for all symmetric N with `‖N - M‖ < ε`,
   N is also PosDef. Decomposes via spectral theorem applied to
   `posDef_min_eigenvalue_pos` (Rayleigh lower bound) + bilinear form
   norm estimate. Estimated ~50-80 LOC.

## Mathlib API status (per R46-T1.1 grep audit)

All Mathlib citations below verified at `mathlib4 @ 25ce63313608` +
`brownian-motion @ 91267abd71bd`:

* `Matrix.PosDef.eigenvalues_pos` — `Mathlib/Analysis/Matrix/PosDef.lean:85`
* `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` — `:74`
* `Matrix.PosSemidef.det_nonneg` — `Mathlib/Analysis/Matrix/PosDef.lean:51`
* `CFC.sqrt_mul_sqrt_self` — `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:259`
* `Matrix.det_mul` — `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:138`
* `Real.sqrt_eq_iff_mul_self_eq` — `Mathlib/Data/Real/Sqrt.lean:150`
* `Finset.exists_min_image` — `Mathlib/Data/Finset/Max.lean:543`
* `map_linearMap_addHaar_eq_smul_addHaar` — `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:234`
* `MeasureTheory.hasFDerivAt_integral_of_dominated_loc_of_lip` —
  `Mathlib/Analysis/Calculus/ParametricIntegral.lean:164`
* `gaussianReal_of_var_ne_zero` — `Mathlib/Probability/Distributions/Gaussian/Real.lean:202`
* `stdGaussian_eq_pi_map_orthonormalBasis` —
  `BrownianMotion/Gaussian/MultivariateGaussian.lean:145`
-/

namespace Erdos524.Helpers.GaussianParametricAnalysis

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Real MatrixOrder

/-! ## Re-exports of R46 Full theorems

These are the immediately-consumable Full theorems landed in R46. They
are re-exposed here under the `GaussianParametricAnalysis` namespace so
that Track C / Track D / Phase 2 consumers have a single import target. -/

/-- **R46-T2.1 sub-lemma (a) Full** (re-exported). For positive
semidefinite `S : Matrix ι ι ℝ`, `(CFC.sqrt S).det = Real.sqrt S.det`.

Forwards directly to
`Erdos524.Helpers.MultivariateGaussianPdf.det_CFC_sqrt_eq_sqrt_det`. -/
theorem det_CFC_sqrt_eq_sqrt_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (CFC.sqrt S).det = Real.sqrt S.det :=
  _root_.Erdos524.Helpers.MultivariateGaussianPdf.det_CFC_sqrt_eq_sqrt_det hS

/-- **R46-T2.1 sub-lemma (a) corollary Full** (re-exported). For
positive-definite `S`, `0 < (CFC.sqrt S).det`. -/
theorem det_CFC_sqrt_pos_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    0 < (CFC.sqrt S).det :=
  _root_.Erdos524.Helpers.MultivariateGaussianPdf.det_CFC_sqrt_pos_of_posDef hS

/-- **R46-T2.2 PosDef minimum-eigenvalue Full** (re-exported). For PosDef
`M` with `[Nonempty n]`, `∃ c > 0, ∀ i, c ≤ eigenvalues i`.

This is the framing-corrected Hermitian-subspace version of Grok's
(false-as-stated) "`Matrix.PosDef.isOpen`" in the full matrix space. -/
theorem posDef_min_eigenvalue_pos
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ i : n, c ≤ hM.isHermitian.eigenvalues i :=
  _root_.Erdos524.PhaseAUpperBound.posDef_min_eigenvalue_pos hM

/-- **R46-T2.2 PosDef minimum-eigenvalue witness Full** (re-exported).
Same content as `posDef_min_eigenvalue_pos` with the constant `c` pinned
explicitly via `Finset.min'`. -/
theorem posDef_min_eigenvalue_witness
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    let c := ((Finset.univ : Finset n).image hM.isHermitian.eigenvalues).min' (by
      rw [Finset.image_nonempty]
      exact Finset.univ_nonempty)
    0 < c ∧ ∀ i : n, c ≤ hM.isHermitian.eigenvalues i :=
  _root_.Erdos524.PhaseAUpperBound.posDef_min_eigenvalue_witness hM

/-! ## R47+ scaffolding (documentation only — no Stubs added)

The following theorems are *scoped* here as the consumer-facing API but
lie outside R46's mandatory floor. They are listed in this docstring
section as named-target theorems so that R47+ rounds and Track C/Track D
parallel work can find them by grep without ambiguity.

**Not added as TAG'd Stubs in R46** to avoid debt inflation. R47+ rounds
will land them as Full theorems (or honest TAG'd Stubs at that time).

```
-- R47+ scope (NOT YET LANDED):
theorem multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Set (Matrix ι ι ℝ)) (hK : IsCompact K)
    (hK_posDef : ∀ S ∈ K, S.PosDef) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ S ∈ K, ∀ x : ι → ℝ,
      multivariateGaussianPdf S x ≤ C * Real.exp (-c * (x ⬝ᵥ x))

-- R47+ scope (NOT YET LANDED):
theorem hasFDerivAt_integral_multivariateGaussianPdf
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Set (Matrix ι ι ℝ)) (hE_open : IsOpen E)
    (hE_posDef : ∀ S ∈ E, S.PosDef)
    (S₀ : Matrix ι ι ℝ) (hS₀ : S₀ ∈ E)
    (f : Matrix ι ι ℝ → (ι → ℝ) → ℝ) (hf_diff : ...) :
    DifferentiableAt ℝ
      (fun S => ∫ x, f S x * multivariateGaussianPdf S x) S₀

-- R47+ scope (NOT YET LANDED):
theorem posDef_local_stability_under_isHermitian_perturbation
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧
    ∀ N : Matrix n n ℝ, N.IsHermitian → ‖N - M‖ < ε → N.PosDef
```

The proof recipes for each are documented in
`Helpers/R46_T1_GrepAuditAndFramingVerification.md` §5 (uniform tail) and
§4 (local stability). Track C round 2 and Track D round 2 may import
these scaffolds directly as named-Stubs if needed before R47 closure;
the choice between Stub-now-vs-Wait-for-R47 is per-track. -/

end Erdos524.Helpers.GaussianParametricAnalysis
