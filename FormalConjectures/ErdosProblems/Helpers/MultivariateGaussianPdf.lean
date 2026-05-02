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
    -- **R43-T2.1 signature upgrade (per Grok R43 pre-flight Q1).**
    -- The multivariate Gaussian measure on `EuclideanSpace ℝ ι` equals the
    -- canonical (Lebesgue) volume measure weighted by the explicit PDF.
    -- The PDF is evaluated at `fun i => y i`, applying the standard
    -- `EuclideanSpace ℝ ι ↔ (ι → ℝ)` coordinate identification at the
    -- consumer site. Body remains TAG'd Stub (R44 Phase 2 scope).
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal (multivariateGaussianPdf S (fun i => y i))) := by
  -- TAG[R43-T2.1-MGE-pushforward-jacobian-body] : Real-signature upgrade of
  -- the R40 `True := by trivial` placeholder. Body remains a TAG'd Stub
  -- after R44 work (single `sorry`, debt-neutral).
  --
  -- **R46-T2.1 advance (last round):** Sub-gap (a) `det_CFC_sqrt_eq_sqrt_det`
  -- now lands as a Full sub-lemma (line ~158 above) via the recipe
  -- audited in `R46_T1_GrepAuditAndFramingVerification.md` §1. Sub-gap (c)
  -- (constant-Jacobian linear pushforward) is verified to be a DIRECT
  -- application of Mathlib's `map_linearMap_addHaar_eq_smul_addHaar`
  -- (`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:234`) — no
  -- separate sub-lemma needed; the application happens inline in the
  -- composition step.
  --
  -- **R47-T1.1 audit revision (this round):** the single 80-120 LOC
  -- estimate for sub-gap (b) `stdGaussian_eq_lebesgue_withDensity` is
  -- INCORRECT. T1.1 grep audit
  -- (`R47_T1_GrepAuditAndFramingVerification.md` §2) verified at pin
  -- `mathlib4 @ 25ce63313608` that sub-gap (b) decomposes into THREE
  -- intermediate Mathlib bridges, each unpackaged:
  --
  --   (b.A) **n-ary `Measure.pi.withDensity` factorization**:
  --         `Measure.pi (μ.withDensity f) =
  --            (Measure.pi μ).withDensity (∏ i, f i (x i))`.
  --         Mathlib has the BINARY version (`prod_withDensity` at
  --         `Mathlib/MeasureTheory/Measure/WithDensity.lean:683`); n-ary
  --         generalisation via `Measure.pi_eq` characterisation +
  --         `restrict_pi_pi` (`Pi.lean:434`) + n-ary Pi-Tonelli for
  --         products of factors (`lmarginal_insert` induction at
  --         `Marginal.lean:164`) is NOT packaged. R47 attempted this as
  --         T2.1 but discovered non-trivial typeclass-inference issues
  --         for the `SigmaFinite` constraint on `withDensity` factors,
  --         plus `lintegral_mul_const` finiteness side-conditions in
  --         the inductive step that require an
  --         AEMeasurable-vs-Measurable hypothesis split.
  --         Estimated bridge LOC: **~80-120**.
  --
  --   (b.B) **`Measure.map.withDensity` through measurable equiv**:
  --         `(μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm)`
  --         for `e : α ≃ᵐ β`. Closest packaged form is
  --         `MeasurableEmbedding.withDensity_map` (one-sided embedding
  --         only). The `MeasurableEquiv` specialisation is derivable
  --         but not packaged. Estimated bridge LOC: **~30-50**.
  --
  --   (b.C) **Lebesgue-on-EuclideanSpace identification**:
  --         `(volume : Measure (EuclideanSpace ℝ ι)) =
  --           ((Measure.pi (fun _ ↦ (volume : Measure ℝ))).map (toLp 2))`.
  --         The `EuclideanSpace.volume_preserving` family exists in
  --         `Mathlib/MeasureTheory/Measure/Lebesgue/EuclideanSpace.lean`
  --         but the exact pushforward identity through `toLp 2` requires
  --         verification + possibly custom unwinding.
  --         Estimated bridge LOC: **~20-100**.
  --
  -- **Revised total LOC for sub-gap (b) Full close: ~150-280** (NOT
  -- 80-120 as previously estimated). This exceeds R47's T2.1 budget by
  -- 1.5-2.5× and is not a single-round close target.
  --
  -- **Future-round closure path (R48+):**
  --
  --   * R48 candidate: close Bridge (b.A) as a standalone Full helper
  --     (most reusable across the project — Track C 1D KMT product
  --     constructions, independent-coordinate Pi-Gaussian arguments).
  --     LOC ~80-120.
  --   * R49 candidate: close (b.B) + (b.C) and compose, retiring this
  --     MGE main Stub. LOC ~50-150. Net retirement: 1 sorry.
  --
  -- The single MGE `sorry` here is narrowed in DIAGNOSTIC PRECISION
  -- (three precise bridges identified) but not retired. R47 net
  -- retirement: 0 sorries.
  --
  -- **R44 verification (this round, post-investigation):** the brief's
  -- Grok Q1/Q2 pre-flight described MGE as a "Jacobi formula" close
  -- (`HasFDerivAt det`); see `R44_T1_BodyCloseAudit.md` for the brief-vs-
  -- reality reconciliation. The actual closure prerequisites for THIS
  -- theorem (pushforward measure equality) are the three measure-theoretic
  -- gaps (a)–(c) below, all confirmed missing at `mathlib4 @ 25ce63313608`
  -- + `brownian-motion` HEAD via search of:
  --   * `det_CFC_sqrt`, `det_sqrt`, `Matrix.det.*sqrt` — 0 hits.
  --     **R46 update**: Now PROVED here as `det_CFC_sqrt_eq_sqrt_det`
  --     Full sub-lemma (composes `CFC.sqrt_mul_sqrt_self` +
  --     `Matrix.det_mul` + `Real.sqrt_eq_iff_mul_self_eq`).
  --   * `stdGaussian.*=.*withDensity`, `stdGaussian.*lebesgue` — 0 hits in
  --     `BrownianMotion/Gaussian/`. Only special-case lemma is
  --     `multivariateGaussian_zero_one` (`MultivariateGaussian.lean:325`).
  --   * `map_linearMap_addHaar_eq_smul_addHaar` — **R46 grep audit FOUND**
  --     at `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:234`. This
  --     is the exact constant-Jacobian linear pushforward identity
  --     (sub-gap (c)); no separate sub-lemma needed.
  -- The remaining novel gap is therefore (b) only, ~80-120 LOC instead
  -- of the original ~150-200 LOC estimate.
  --
  -- The R44 brief's Grok-derived 80-120 LOC estimate (and P~0.75 Full
  -- close) was based on the misframed Jacobi-formula scope and does not
  -- apply to this theorem.
  --
  -- **Closure prerequisites (R45+ scope, decomposed):**
  --
  --   (a) `det_CFC_sqrt_eq_sqrt_det : (CFC.sqrt S).det = Real.sqrt S.det`
  --       for PosDef `S`. **Recipe**: `(CFC.sqrt S) * (CFC.sqrt S) = S`
  --       (`CFC.sqrt_mul_sqrt_self` from brownian-motion's spectral
  --       calculus chain) ⟹ `(CFC.sqrt S).det^2 = S.det` via
  --       `Matrix.det_mul`; combined with `0 ≤ (CFC.sqrt S).det` (from
  --       PSD of `CFC.sqrt S`, which inherits via continuous functional
  --       calculus) gives `(CFC.sqrt S).det = Real.sqrt S.det` by
  --       `Real.sqrt_eq_iff_sq_eq`. Estimated ~30-50 LOC.
  --
  --   (b) `stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace ℝ ι`.
  --       **Recipe**: `stdGaussian (EuclideanSpace ℝ ι)` is defined as
  --       `(Measure.pi (fun _ ↦ gaussianReal 0 1)).map (basis-sum)`. For
  --       `EuclideanSpace ℝ ι = PiLp 2 (fun _ : ι => ℝ)`, the basis-sum
  --       `fun x => ∑ i, x i • basisFun i` reduces (after `simp`) to the
  --       `WithLp.equiv`-conjugated identity since `EuclideanSpace.basisFun`
  --       is the canonical basis. Then by `Measure.pi`-on-product +
  --       `gaussianReal_of_var_ne_zero` (Mathlib
  --       `Probability/Distributions/Gaussian/Real.lean:204`) +
  --       `Measure.pi_withDensity` chain, the result is
  --       `volume.withDensity ((2π)^(-n/2) · exp(-‖·‖²/2))`. Estimated
  --       ~80-120 LOC. Subsidiary gap: `Measure.pi_withDensity` may need
  --       custom unwinding for `gaussianPDF` factor.
  --
  --   (c) Change-of-variables for constant-Jacobian linear pushforward
  --       on `EuclideanSpace ℝ ι`. **Recipe**: for an invertible linear
  --       map `T : E ≃L[ℝ] E` with `|det T| = c > 0`, the pushforward of
  --       `volume.withDensity ρ` by `T` is `volume.withDensity (ρ ∘ T⁻¹ * c⁻¹)`
  --       — derivable from `MeasureTheory.MeasurePreserving.set_lintegral_comp`
  --       + the `addHaar_smul` family on `E`'s Haar measure. Estimated
  --       ~40-80 LOC. The `T = toEuclideanCLM (CFC.sqrt S)` specialisation
  --       takes `|det T| = sqrt S.det` from gap (a).
  --
  -- **Composition** (~30-50 LOC):
  --   * Apply gap (b) to rewrite `stdGaussian = volume.withDensity ρ_std`.
  --   * Apply gap (c) with `T = toEuclideanCLM (CFC.sqrt S)` to compute
  --     the pushforward `T_*(volume.withDensity ρ_std) = volume.withDensity ρ'`.
  --   * Use gap (a) to identify `|det T|⁻¹ = (Real.sqrt S.det)⁻¹` and
  --     simplify `ρ_std (T⁻¹ y) · |det T|⁻¹ = multivariateGaussianPdf S y`.
  --   * Conclude.
  --
  -- **Total estimate**: ~180-300 LOC across (a)+(b)+(c)+composition.
  -- Per Q5 BTIS-merge compression option in R59 ceiling check, this can
  -- absorb into a multi-round closure (R45 + R46) if needed.
  --
  -- See `Helpers/R44_T1_BodyCloseAudit.md` §2 (R44 reconciliation) +
  -- `R43_T1_SignatureUpgradeAudit.md` §2.1 (R43 baseline).
  sorry

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
