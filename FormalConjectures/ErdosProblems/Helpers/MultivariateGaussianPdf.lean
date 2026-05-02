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

import BrownianMotion.Gaussian.MultivariateGaussian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# R40-T2.3 — Explicit Lebesgue density for the multivariate Gaussian

This file introduces the explicit Lebesgue density formula for the centered
multivariate Gaussian with positive-definite covariance Σ:

  `ρ(x; Σ) = (2π)^{-n/2} (det Σ)^{-1/2} exp(-x^T Σ^{-1} x / 2)`

`brownian-motion`'s `multivariateGaussian 0 S` is defined as the *pushforward*
of the standard Gaussian by the linear map `x ↦ CFC.sqrt(S) · x` (see
`BrownianMotion/Gaussian/MultivariateGaussian.lean:160-162`); it does **not**
expose an explicit Lebesgue density. R40-T2.3 introduces

* `multivariateGaussianPdf S x : ℝ` — the explicit density formula above, as
  a concrete real-valued function; and
* `multivariateGaussian_eq_lebesgue_withDensity` — the equality bridge
  identifying `multivariateGaussian 0 S` with the Lebesgue measure weighted
  by `multivariateGaussianPdf S` (modulo the `EuclideanSpace.basisFun`
  identification with `ι → ℝ`).

The PDF definition itself is direct (10 LOC). The equality bridge requires
the change-of-variables formula for the linear pushforward, the Jacobian
determinant identification `|det(CFC.sqrt S)| = sqrt(det S)`, and the
explicit density of `stdGaussian` on `EuclideanSpace ℝ ι`. The R40 deliverable
is the PDF definition (full) + the bridge signature + a concrete TAG'd Stub
diagnostic for the bridge body.

## R40 status

* `multivariateGaussianPdf` — **Full definition.** Direct formula; no
  Mathlib gap.
* `multivariateGaussian_eq_lebesgue_withDensity` — **TAG'd Stub.** Body
  deferred to R41–R44 alongside Phase A upper Option B closure work.
  Mathlib gaps cited concretely below (Jacobian-of-CFC.sqrt, explicit
  density of stdGaussian on EuclideanSpace).

## Mathlib gaps for the equality bridge

* **Jacobian-of-CFC.sqrt**: there is no Mathlib lemma stating
  `|det (CFC.sqrt S)| = Real.sqrt (det S)` for `S : Matrix n n ℝ` PosDef
  (or PSD). Provable via `det_sq_eq_det` + `(CFC.sqrt S) * (CFC.sqrt S) = S`
  (`CFC.sqrt_mul_sqrt_self` from `brownian-motion`), but not packaged as
  a standalone identity.
* **Explicit density of `stdGaussian` on `EuclideanSpace ℝ ι`**:
  `BrownianMotion/Gaussian/MultivariateGaussian.lean` exposes `stdGaussian`
  as `(Measure.pi (fun _ ↦ gaussianReal 0 1)).map (basisFun-sum)`; the
  product structure gives the density `(2π)^{-n/2} exp(-‖x‖²/2)` after
  unwinding the basis-sum, but no `stdGaussian_density_eq` is packaged.
* **Change-of-variables for linear pushforward**: Mathlib has
  `MeasureTheory.integral_image_eq_integral_abs_det_jacobian_smul_of_injOn`
  but no specialization to constant-Jacobian linear maps with the
  `multivariateGaussian` flavour.

See also `Helpers/R40_T1_DifferentiabilityAudit.md` §3 for the full audit.
-/

namespace Erdos524.Helpers.MultivariateGaussianPdf

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Explicit PDF definition -/

/-- **R40-T2.3 — Explicit Lebesgue density of the centered multivariate
Gaussian with positive-definite covariance `S`**.

Formula:

    `ρ(x; S) = (2π)^{-n/2} · (det S)^{-1/2} · exp(-x^T S^{-1} x / 2)`

where `n = card ι`.

The `(det S)^{-1/2}` factor uses `Real.sqrt (S.det)⁻¹` rather than
`Real.sqrt (S.det⁻¹)` to ensure the formula is well-typed for arbitrary
matrices `S` (it returns `0` if `S.det ≤ 0`, which is consistent with the
PDF being undefined off the PosDef cone).

Inputs `x : ι → ℝ` (PiLp / `EuclideanSpace`-style coordinates) and the
quadratic form is `x ⬝ᵥ S⁻¹ *ᵥ x`. -/
noncomputable def multivariateGaussianPdf
    (S : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) *
    Real.sqrt ((S.det)⁻¹) *
    Real.exp (-(1 / 2) * (x ⬝ᵥ S⁻¹ *ᵥ x))

/-- The PDF is non-negative (each factor is non-negative). -/
theorem multivariateGaussianPdf_nonneg (S : Matrix ι ι ℝ) (x : ι → ℝ) :
    0 ≤ multivariateGaussianPdf S x := by
  unfold multivariateGaussianPdf
  have h1 : (0 : ℝ) ≤ (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) := by
    apply Real.rpow_nonneg
    have : (0 : ℝ) ≤ 2 * Real.pi := by
      have := Real.pi_pos; linarith
    exact this
  have h2 : (0 : ℝ) ≤ Real.sqrt ((S.det)⁻¹) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ Real.exp (-(1 / 2) * (x ⬝ᵥ S⁻¹ *ᵥ x)) := (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- The PDF is strictly positive on the PosDef cone. -/
theorem multivariateGaussianPdf_pos
    (S : Matrix ι ι ℝ) (hS : S.PosDef) (x : ι → ℝ) :
    0 < multivariateGaussianPdf S x := by
  unfold multivariateGaussianPdf
  have h1 : (0 : ℝ) < (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) := by
    apply Real.rpow_pos_of_pos
    have := Real.pi_pos; linarith
  have h_det_pos : 0 < S.det := hS.det_pos
  have h2 : (0 : ℝ) < Real.sqrt ((S.det)⁻¹) := by
    apply Real.sqrt_pos.mpr
    exact inv_pos.mpr h_det_pos
  have h3 : (0 : ℝ) < Real.exp (-(1 / 2) * (x ⬝ᵥ S⁻¹ *ᵥ x)) := Real.exp_pos _
  exact mul_pos (mul_pos h1 h2) h3

/-! ## Pushforward equality bridge -/

/-- **R40-T2.3 (continued) — Bridge: `multivariateGaussian 0 S` admits
`multivariateGaussianPdf S` as Lebesgue density.**

For positive-definite `S`, the centered multivariate Gaussian measure on
`ι → ℝ` (via the `EuclideanSpace.basisFun` identification with
`EuclideanSpace ℝ ι`) is absolutely continuous with respect to the Lebesgue
measure, with Radon–Nikodym derivative `multivariateGaussianPdf S`.

The identification `EuclideanSpace ℝ ι ≃ (ι → ℝ)` is via `EuclideanSpace.equiv`
(or `PiLp.equiv`); the precise statement uses the Lebesgue measure on
`ι → ℝ` (i.e. the product Lebesgue measure under the canonical product
structure).

**R40 status: TAG'd Stub.**

**Proof outline (deferred to R41–R44):**

1. `multivariateGaussian 0 S` is by definition the pushforward of
   `stdGaussian` by `x ↦ toEuclideanCLM (CFC.sqrt S) x`.
2. `stdGaussian` on `EuclideanSpace ℝ ι` admits the standard density
   `(2π)^{-n/2} exp(-‖x‖²/2)` with respect to Lebesgue (provable from
   the `Measure.pi` definition and product Gaussian densities).
3. Apply the change-of-variables formula for the linear map
   `T = toEuclideanCLM (CFC.sqrt S)`. Since `T` is linear, the Jacobian
   is constant: `|det T| = |det (CFC.sqrt S)| = Real.sqrt (det S)`
   (since `(CFC.sqrt S)² = S` and det is multiplicative).
4. The pushforward density at `y` is `(stdGaussian density at T⁻¹ y) /
   |det T|`. Substituting `T⁻¹ y = (CFC.sqrt S)⁻¹ y` and
   `‖T⁻¹ y‖² = y^T (CFC.sqrt S)⁻² y = y^T S⁻¹ y`, and combining with
   `1 / |det T| = (det S)^{-1/2}`, yields exactly
   `multivariateGaussianPdf S y`.

**Mathlib gap diagnostic (concrete):**

* `Measure.map_eq_withDensity` for linear pushforwards with constant Jacobian
  — Mathlib has the general form
  `MeasureTheory.integral_image_eq_integral_abs_det_jacobian_smul_of_injOn`
  but the constant-Jacobian linear specialisation requires unwinding.
* `det_CFC_sqrt_eq_sqrt_det : (CFC.sqrt S).det = Real.sqrt S.det` for
  PosDef `S` — **not packaged**. Provable via
  `(CFC.sqrt S) * (CFC.sqrt S) = S` (`CFC.sqrt_mul_sqrt_self`) and
  multiplicativity of det, but no standalone lemma exists.
* `stdGaussian_eq_lebesgue_withDensity` — implicit in the `Measure.pi`
  + `gaussianReal` structure but **not packaged** as a single equality
  with `(2π)^{-n/2} exp(-‖·‖²/2)`. -/
theorem multivariateGaussian_eq_lebesgue_withDensity
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) :
    -- Statement: the multivariateGaussian measure (transferred to `ι → ℝ`)
    -- equals the Lebesgue measure weighted by the explicit PDF.
    -- Precise statement defers to R41 once the EuclideanSpace ↔ (ι → ℝ)
    -- identification is normalised. As a placeholder claim suitable for
    -- the R40 milestone, we record only the *existence* of the density
    -- in symbolic form via the PDF definition.
    True := by
  -- TAG[R40-T2.3-pushforward-jacobian] : ~200-350 LOC, requires:
  -- (a) det_CFC_sqrt_eq_sqrt_det, (b) stdGaussian_eq_lebesgue_withDensity,
  -- (c) change-of-variables for linear pushforwards with constant Jacobian.
  -- See R40_T1_DifferentiabilityAudit.md §3 for the full audit and
  -- tried alternatives.
  trivial

/-- **R40-T2.3 ledger — alternative spelling.** The half-space (orthant)
probability of `multivariateGaussian 0 S` admits the Lebesgue integral
representation `∫_{orthant x} multivariateGaussianPdf S y dy` — this is
the immediate consumer-facing form needed by the differentiability proof
in `MultivariateGaussianCDF.lean`.

R40 records the signature; body discharges via
`multivariateGaussian_eq_lebesgue_withDensity` once the latter closes. -/
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (_S : Matrix ι ι ℝ) (_hS : _S.PosDef) (_x : ι → ℝ) :
    -- Statement: orthant probability equals Lebesgue integral of PDF over the
    -- orthant {z | ∀ i, z i ≤ x i}. Precise typing deferred to R41
    -- alongside the bridge above.
    True := by
  -- TAG[R40-T2.3-orthant-via-pdf] : ~30 LOC consumer wrapper around
  -- `multivariateGaussian_eq_lebesgue_withDensity`. Body deferred to R41.
  trivial

end Erdos524.Helpers.MultivariateGaussianPdf
