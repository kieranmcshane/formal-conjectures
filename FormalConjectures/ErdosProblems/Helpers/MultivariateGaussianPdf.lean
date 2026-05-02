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
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

## Status (R51 — γ-floor axiomatization)

* `multivariateGaussianPdf` — **Full definition.** Direct formula; no
  Mathlib gap.
* `multivariateGaussian_eq_lebesgue_withDensity` — **Axiom (Axiom #7,
  γ-floor).** Per BACKGROUND.md post-R50 user-confirmed audit-redirect,
  R51 axiomatized this Stub to free R52-R58 mainline budget for
  retirements elsewhere. Sole Lean call site
  (`multivariateGaussianOrthantCDF_eq_lebesgue_integral`, this file)
  preserved by identical-signature swap. Retirement target R55-R59
  post-gate via Mathlib pin bump (preferred) or from-scratch closure
  ~150-300 LOC (sub-gap (a) already closed at R46; (b) + (c) +
  composition pending). See `AXIOM_INVENTORY.md` "Axiom #7" and
  `Helpers/Round51_T1_MGEAxiomatization.md` for retirement plan +
  Claims Verification Table.

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
open scoped ENNReal NNReal Real MatrixOrder

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

/-! ## R46-T2.1 — Sub-lemma (a): Determinant of CFC.sqrt

**R46 Track A advance.** `det (CFC.sqrt S) = √(det S)` for positive
semidefinite `S`. This is sub-gap (a) of the three-piece MGE composition
identified in `R44_T1_BodyCloseAudit.md` and `R45_T1_FramingVerificationAudit.md`.

**Closure recipe (per R46-T1.1 grep audit, all citations verified at pin
`mathlib4 @ 25ce63313608`):**

1. `CFC.sqrt S * CFC.sqrt S = S` — from `CFC.sqrt_mul_sqrt_self`
   (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:259`),
   re-exposed in matrix form as `Matrix.PosSemidef.sqrt_mul_self`
   (`Analysis/Matrix/Order.lean:140`, deprecated alias for
   `CFC.sqrt_mul_sqrt_self`).
2. `Matrix.det_mul` (`LinearAlgebra/Matrix/Determinant/Basic.lean:138`):
   `det (M * N) = det M * det N`.
3. From (1) + (2): `(CFC.sqrt S).det * (CFC.sqrt S).det = S.det`.
4. `(CFC.sqrt S).PosSemidef` from `(CFC.sqrt_nonneg S).posSemidef`
   (`Analysis/Matrix/Order.lean:51` `nonneg_iff_posSemidef` + standard CFC
   lemma `CFC.sqrt_nonneg`).
5. `0 ≤ (CFC.sqrt S).det` from `PosSemidef.det_nonneg`
   (`Analysis/Matrix/PosDef.lean:51`).
6. `Real.sqrt_eq_iff_mul_self_eq` (`Data/Real/Sqrt.lean:150`):
   `√x = y ↔ x = y * y` (given `0 ≤ x` and `0 ≤ y`). Apply with
   `x := S.det`, `y := (CFC.sqrt S).det`.

This is a fully-proved Full sub-lemma (no Stubs). Companion: `Real.sqrt`
of `S.det` is well-defined (≥ 0) for any matrix; for non-PSD `S` it is
zero by Mathlib's convention `Real.sqrt_eq_zero_of_nonpos`. -/

/-- **R46-T2.1 sub-lemma (a) — Full.** For positive-semidefinite `S`, the
determinant of the spectral square root `CFC.sqrt S` equals the real
square root of `det S`. -/
theorem det_CFC_sqrt_eq_sqrt_det
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (CFC.sqrt S).det = Real.sqrt S.det := by
  -- Step 1: 0 ≤ S in the matrix-order sense (from PosSemidef).
  have h_nn_S : (0 : Matrix ι ι ℝ) ≤ S := hS.nonneg
  -- Step 2: CFC.sqrt S * CFC.sqrt S = S.
  have h_sqrt_sq : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S h_nn_S
  -- Step 3: det multiplicativity ⟹ (CFC.sqrt S).det^2 = S.det.
  have h_det_sq : (CFC.sqrt S).det * (CFC.sqrt S).det = S.det := by
    rw [← Matrix.det_mul, h_sqrt_sq]
  -- Step 4: 0 ≤ (CFC.sqrt S).det from PSD of CFC.sqrt S.
  have h_psd_sqrt : (CFC.sqrt S).PosSemidef := (CFC.sqrt_nonneg (a := S)).posSemidef
  have h_det_sqrt_nn : 0 ≤ (CFC.sqrt S).det := h_psd_sqrt.det_nonneg
  -- Step 5: 0 ≤ S.det from PSD of S.
  have h_det_S_nn : 0 ≤ S.det := hS.det_nonneg
  -- Step 6: apply Real.sqrt_eq_iff_mul_self_eq (in reverse direction).
  -- Goal: (CFC.sqrt S).det = √S.det.
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq h_det_S_nn h_det_sqrt_nn]
  exact h_det_sq.symm

/-- **R46-T2.1 sub-lemma (a), positivity refinement** — for PosDef `S`,
`(CFC.sqrt S).det = √(det S)` and both are positive. Direct corollary of
`det_CFC_sqrt_eq_sqrt_det`; useful when consumers need positivity of the
Jacobian factor. -/
theorem det_CFC_sqrt_pos_of_posDef
    {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    0 < (CFC.sqrt S).det := by
  rw [det_CFC_sqrt_eq_sqrt_det hS.posSemidef]
  exact Real.sqrt_pos.mpr hS.det_pos

/-! ## Pushforward equality bridge -/

/-- **R51 — γ-floor MGE axiomatization (Path A, post-R50 audit-redirect).**

For positive-definite `S`, the centered multivariate Gaussian measure on
`EuclideanSpace ℝ ι` admits `multivariateGaussianPdf S` as Lebesgue
density (modulo the canonical `EuclideanSpace ℝ ι ↔ (ι → ℝ)` coordinate
identification):

    `multivariateGaussian 0 S = volume.withDensity (ENNReal.ofReal ∘ pdf)`

This is the **pushforward equality bridge** introduced in R40-T2.3 and
upgraded to its real signature in R43-T2.1 (TAG
`R43-T2.1-MGE-pushforward-jacobian-body`). R44–R47 narrowed the closure
diagnostic to three measure-theoretic sub-gaps:

* (a) `det_CFC_sqrt_eq_sqrt_det` — closed at R46 as a Full sub-lemma in
  this file (composes `CFC.sqrt_mul_sqrt_self` + `Matrix.det_mul` +
  `Real.sqrt_eq_iff_mul_self_eq`).
* (b) `stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace ℝ ι` — R47
  audit decomposed into three Mathlib bridges (n-ary
  `Measure.pi.withDensity` factorization, `Measure.map.withDensity`
  through `MeasurableEquiv`, Lebesgue-on-`EuclideanSpace` identification)
  totalling ~150-280 LOC, none packaged at pin
  `mathlib4 @ 25ce63313608`.
* (c) Constant-Jacobian linear pushforward — R46 grep audit identified
  `map_linearMap_addHaar_eq_smul_addHaar` (Mathlib
  `MeasureTheory/Measure/Lebesgue/EqHaar.lean:234`) as a direct
  application; no separate sub-lemma needed.

**γ-floor strategy (R51).** Per BACKGROUND.md user-confirmed post-R50
audit-redirect ("γ floor + β R58 extension"), the MGE Stub is replaced
with an axiom of identical signature to free R52-R58 mainline budget for
retirements elsewhere (Q1a/b/c track consolidation, Track C/D parallel
work, Matrix.det.differentiable γ-axiomatization candidate at R52). This
is debt-conversion: -1 sorry, +1 axiom, items unchanged at the R52 gate
(sorry-to-axiom swap).

**Classical justification.** Standard pdf-pushforward result for the
multivariate normal: see Tong (1990) "The Multivariate Normal
Distribution" §5.1; Anderson (2003) "An Introduction to Multivariate
Statistical Analysis" §2.3; Bogachev (2007) "Gaussian Measures" Chapter
1. The proof composes (a)+(b)+(c) above with the change-of-variables
formula for the linear map `T = toEuclideanCLM (CFC.sqrt S)` (Jacobian
constant `|det T| = sqrt(det S)` from sub-gap (a); inverse pushforward
density `(stdGaussian density at T⁻¹ y) / |det T|`).

**Retirement target — R55-R59 post-gate** (two-path sub-plan):

1. *Mathlib pin bump (preferred).* Monitor Mathlib for landings of
   n-ary `Measure.pi.withDensity` factorization,
   `Measure.map.withDensity` through `MeasurableEquiv`, and
   `stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace`.
   Post-`v4.27` toolchain bump may package some of these via the
   `BrownianMotion.Gaussian` chain. Direct chain composition retires
   this axiom in ~30-80 LOC of consumer wrapper.
2. *From-scratch closure (fallback).* Build the missing pieces in-tree
   over R55-R59 — ~150-300 LOC across 2-3 rounds (sub-gap (a) already
   closed; (b.A) Pi-withDensity bridge ~80-120 LOC, (b.B) MeasurableEquiv
   pushforward ~30-50 LOC, (b.C) Lebesgue-EuclideanSpace identification
   ~20-100 LOC, composition ~30-50 LOC).

Retirement is **not required for the R52 gate** (gate measures item
count; sorry-to-axiom is a wash). Strategic value of the γ-floor
axiomatization is the freed mainline budget for OTHER retirements.

**Consumers (Lean code).**
* `multivariateGaussianOrthantCDF_eq_lebesgue_integral` (this file,
  line ~466) — `rw [multivariateGaussian_eq_lebesgue_withDensity S _hS]`
  to convert measure-of-orthant to integral-of-pdf-over-orthant. Single
  Lean call site; positional arity preserved by the axiom swap.

See `Helpers/Round51_T1_MGEAxiomatization.md` for the T1.1 Claims
Verification Table + signature audit. -/
axiom multivariateGaussian_eq_lebesgue_withDensity
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal (multivariateGaussianPdf S (fun i => y i)))

/-- **R40-T2.3 ledger — alternative spelling.** The half-space (orthant)
probability of `multivariateGaussian 0 S` admits the Lebesgue integral
representation `∫_{orthant x} multivariateGaussianPdf S y dy` — this is
the immediate consumer-facing form needed by the differentiability proof
in `MultivariateGaussianCDF.lean`.

R40 records the signature; body discharges via
`multivariateGaussian_eq_lebesgue_withDensity` once the latter closes. -/
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) (x : ι → ℝ) :
    -- **R43-T2.1 signature upgrade (per Grok R43 pre-flight Q1).** The
    -- half-space (orthant) probability under `multivariateGaussian 0 S`
    -- equals the Lebesgue integral of the explicit PDF over the orthant
    -- region `{z | ∀ i, z i ≤ x i}`. We state this via `Measure.real`
    -- (the ℝ-valued probability measure projection) on the LHS; the RHS
    -- is the standard set-integral. Phrased without reference to the
    -- `MultivariateGaussianCDF.orthant` def to avoid creating a
    -- circular import (`MultivariateGaussianCDF.lean` will import this
    -- file, not the other way around). Body remains TAG'd Stub.
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i} =
      ∫ y in {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i},
        multivariateGaussianPdf S (fun i => y i) := by
  -- **R44-T2.2 Full close.** Consumer wrapper of MGE
  -- (`multivariateGaussian_eq_lebesgue_withDensity`) via the
  -- `withDensity_apply` ↔ `integral_eq_lintegral_of_nonneg_ae` bridge.
  -- Strategy:
  --   (i)   Orthant set is measurable (countable intersection of measurable
  --         half-space preimages via `PiLp.continuous_apply`).
  --   (ii)  Apply MGE to rewrite the LHS measure.
  --   (iii) Unfold `Measure.real` to `(... ).toReal`, then apply
  --         `withDensity_apply` to convert measure-of-set to lintegral.
  --   (iv)  Use `integral_eq_lintegral_of_nonneg_ae` in reverse, given
  --         non-negativity of the PDF (`multivariateGaussianPdf_nonneg`)
  --         and continuity (hence AEStronglyMeasurable) of the composite
  --         `y ↦ pdf S (fun i => y i)`.
  set orthant : Set (EuclideanSpace ℝ ι) :=
    {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i} with h_orthant_def
  -- (i) The orthant is measurable: it is `⋂ i, (proj i) ⁻¹' Iic (x i)`.
  have h_meas : MeasurableSet orthant := by
    have h_eq : orthant = ⋂ i, {z : EuclideanSpace ℝ ι | z i ≤ x i} := by
      ext z; simp [h_orthant_def]
    rw [h_eq]
    refine MeasurableSet.iInter (fun i => ?_)
    have h_proj : Measurable (fun z : EuclideanSpace ℝ ι => z i) :=
      (PiLp.continuous_apply (β := fun _ : ι => ℝ) 2 i).measurable
    exact h_proj measurableSet_Iic
  -- Continuity of the integrand `y ↦ pdf S (fun i => y i)`.
  have h_cont : Continuous (fun y : EuclideanSpace ℝ ι =>
      multivariateGaussianPdf S (fun i => y i)) := by
    unfold multivariateGaussianPdf
    refine Continuous.mul (continuous_const.mul continuous_const) ?_
    refine Real.continuous_exp.comp ?_
    refine continuous_const.mul ?_
    -- Continuity of `y ↦ y ⬝ᵥ S⁻¹ *ᵥ y` on EuclideanSpace ℝ ι.
    -- Reduce via `(fun y i => y i)` to the underlying Pi structure, then
    -- use `Continuous.dotProduct` + `Continuous.matrix_mulVec`.
    have h_y_pi : Continuous (fun y : EuclideanSpace ℝ ι => fun i : ι => y i) :=
      continuous_pi (fun i =>
        PiLp.continuous_apply (β := fun _ : ι => ℝ) 2 i)
    exact h_y_pi.dotProduct (continuous_const.matrix_mulVec h_y_pi)
  -- (ii) Apply MGE to rewrite the multivariate Gaussian measure.
  rw [multivariateGaussian_eq_lebesgue_withDensity S _hS]
  -- (iii) Unfold `Measure.real` and apply `withDensity_apply`.
  rw [Measure.real_def, withDensity_apply _ h_meas]
  -- (iv) Reverse the integral_eq_lintegral_of_nonneg_ae direction.
  -- Note: integral_eq_lintegral_of_nonneg_ae gives
  --   ∫ a, f a ∂μ = (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal
  -- We use it with μ = volume.restrict orthant and f = pdf composed.
  rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall
          (fun y : EuclideanSpace ℝ ι => multivariateGaussianPdf_nonneg S _))
        h_cont.aestronglyMeasurable]

end Erdos524.Helpers.MultivariateGaussianPdf
