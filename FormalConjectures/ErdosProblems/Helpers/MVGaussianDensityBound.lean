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

import FormalConjectures.ErdosProblems.Helpers.GaussianBoxBounds
import FormalConjectures.ErdosProblems.Helpers.MVGaussianRotation

/-!
# Phase 2 Round 6 — Multivariate Gaussian density-at-mode small-ball bound

For an `n × n` symmetric positive-definite real matrix `M`, the multivariate
Gaussian on `n → ℝ` with covariance `M`,
`mvGaussianFromPosDef M = Measure.map (mulVec L) standardMVGaussian`,
where `L = realMatrixSqrt M`, satisfies the Anderson-style density-at-mode
upper bound on a symmetric anisotropic box `∏ᵢ [-εᵢ, εᵢ]`:

  `ℙ[X ∈ B] ≤ (∏ᵢ 2 εᵢ) · (2π)^(-n/2) · (det M)^(-1/2)`.

The proof outline (textbook Anderson):

1.  Density of the MV Gaussian at `x = 0` (the mode) is
    `(2π)^(-n/2) · (det M)^(-1/2)`, since the exponential factor
    `exp(-xᵀ M⁻¹ x / 2)` evaluated at zero is `1`.
2.  For all `x ∈ B`, `xᵀ M⁻¹ x ≥ 0` (since `M⁻¹` is PosDef), so the
    exponential factor is `≤ 1`, hence `p_X(x) ≤ p_X(0)`.
3.  Integrate the pointwise bound over `B`:
    `ℙ[X ∈ B] = ∫_B p_X(x) dx ≤ p_X(0) · vol(B) = p_X(0) · ∏ᵢ 2εᵢ`.

This file:

* Proves the **standard MV Gaussian** anisotropic-box bound (cov = `1`)
  fully, no `sorry`. This is the supporting lemma of Target A.

* States the **general PosDef** version with a single documented `sorry`
  on the precise change-of-variables / density-formula step that Mathlib
  does not expose for general PosDef covariance.

* Specialises the PosDef version to `M = 1` (provable from the standard
  MV bound — no `sorry`).

The standard MV bound is itself the key input the V1 instance needs for
its `anderson_upper` field on the diagonal-covariance reduction.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {n : Type*} [Fintype n]

/-! ## Anisotropic box event = product of intervals -/

set_option linter.unusedSectionVars false in
/-- The anisotropic symmetric box `{x | ∀ i, |x i| ≤ ε i}` is exactly the
product of intervals `Set.pi univ (fun i => Set.Icc (-ε i) (ε i))`. -/
theorem anisotropic_box_event_eq_pi (ε : n → ℝ) :
    {x : n → ℝ | ∀ i, |x i| ≤ ε i} =
      Set.pi Set.univ (fun i => Set.Icc (-ε i) (ε i)) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies, abs_le]

/-! ## Anisotropic box probability factorises as a product of 1-D probabilities -/

theorem standardMVGaussian_anisotropic_box_eq_prod (ε : n → ℝ) :
    standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε i} =
      ∏ i, gaussianReal 0 1 (Set.Icc (-ε i) (ε i)) := by
  rw [anisotropic_box_event_eq_pi]
  unfold standardMVGaussian
  exact Measure.pi_pi (fun _ => gaussianReal 0 1) _

/-! ## Each 1-D box probability is finite -/

theorem gaussianReal_Icc_finite (a b : ℝ) :
    gaussianReal 0 1 (Set.Icc a b) ≠ ⊤ := by
  have h_le : gaussianReal 0 1 (Set.Icc a b) ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
  exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)

/-! ## Each 1-D box probability is nonneg as `toReal` -/

theorem gaussianReal_Icc_toReal_nonneg (a b : ℝ) :
    (0 : ℝ) ≤ (gaussianReal 0 1 (Set.Icc a b)).toReal :=
  ENNReal.toReal_nonneg

/-! ## Per-coordinate 1-D bound: `(gaussianReal 0 1 (Icc (-εᵢ) εᵢ)).toReal ≤ 2εᵢ · (√(2π))⁻¹` -/

theorem gaussianReal_Icc_neg_le_aniso (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal ≤ 2 * ε * (Real.sqrt (2 * Real.pi))⁻¹ :=
  one_d_box_bound_uniform ε hε

/-! ## Anisotropic Anderson-upper for `standardMVGaussian` (no `sorry`)

Headline theorem of this file in the cov = `1` case: for any anisotropic
symmetric box, the box probability is at most `(∏ᵢ 2εᵢ) · (√(2π))⁻¹^n`. -/

theorem standardMVGaussian_anisotropic_box_density_at_mode_bound
    (ε : n → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε i}).toReal ≤
      (∏ i, 2 * ε i) * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  -- Factor the box probability as a product of 1-D box probabilities.
  rw [standardMVGaussian_anisotropic_box_eq_prod]
  -- toReal of finite product = product of toReal.
  rw [ENNReal.toReal_prod]
  -- Bound each 1-D factor by `2εᵢ · (√(2π))⁻¹`.
  have h_per_factor :
      ∀ i, (gaussianReal 0 1 (Set.Icc (-ε i) (ε i))).toReal ≤
           2 * ε i * (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro i; exact gaussianReal_Icc_neg_le_aniso (ε i) (hε i)
  have h_prod_le :
      ∏ i, (gaussianReal 0 1 (Set.Icc (-ε i) (ε i))).toReal ≤
        ∏ i, (2 * ε i * (Real.sqrt (2 * Real.pi))⁻¹) := by
    apply Finset.prod_le_prod (fun i _ => gaussianReal_Icc_toReal_nonneg _ _)
      (fun i _ => h_per_factor i)
  refine h_prod_le.trans ?_
  -- Split `∏ (2εᵢ · c) = (∏ 2εᵢ) · c^n`.
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-! ## Reciprocal-square-root form: `(√(2π))⁻¹^n` is positive -/

theorem inv_sqrt_two_pi_pow_pos (n : ℕ) :
    0 < (Real.sqrt (2 * Real.pi))⁻¹ ^ n := by
  apply pow_pos
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem inv_sqrt_two_pi_pow_nonneg (n : ℕ) :
    0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ ^ n :=
  le_of_lt (inv_sqrt_two_pi_pow_pos n)

/-! ## Determinant of a PosDef matrix is positive — convenience wrappers -/

theorem sqrt_det_pos_of_posDef [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) : 0 < Real.sqrt M.det :=
  Real.sqrt_pos.mpr hM.det_pos

theorem sqrt_det_nonneg_of_posDef [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) : 0 ≤ Real.sqrt M.det :=
  le_of_lt (sqrt_det_pos_of_posDef hM)

/-! ## Round 9 — Determinant of the symmetric square root

For a PosDef matrix `M`, the symmetric square root `realMatrixSqrt M` (= `CFC.sqrt M`)
has determinant `Real.sqrt (det M)`. This follows from
`Matrix.PosSemidef.det_sqrt` (Mathlib `Analysis/Matrix/Order.lean`), specialised
to the field `ℝ`: `RCLike.sqrt` of a real argument is `Real.sqrt`.
-/

theorem realMatrixSqrt_det [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    (realMatrixSqrt M).det = Real.sqrt M.det := by
  unfold realMatrixSqrt
  rw [hM.det_sqrt]
  exact RCLike.sqrt_real

theorem realMatrixSqrt_det_pos [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    0 < (realMatrixSqrt M).det := by
  rw [realMatrixSqrt_det hM.posSemidef]
  exact Real.sqrt_pos.mpr hM.det_pos

theorem realMatrixSqrt_det_ne_zero [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    (realMatrixSqrt M).det ≠ 0 :=
  ne_of_gt (realMatrixSqrt_det_pos hM)

/-- The symmetric square root of a PosDef matrix is invertible (over ℝ a field). -/
theorem realMatrixSqrt_isUnit [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    IsUnit (realMatrixSqrt M) :=
  Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_iff_ne_zero.mpr (realMatrixSqrt_det_ne_zero hM))

/-! ## Round 9 — Change-of-variables identity for `mvGaussianFromPosDef`

For any measurable set `S`, the box probability under `mvGaussianFromPosDef M`
is the standard MV measure of the preimage parallelepiped under
`(realMatrixSqrt M).mulVec`. This is the pushforward identity in operational
form. -/

theorem mvGaussianFromPosDef_apply_eq [DecidableEq n]
    (M : Matrix n n ℝ) {S : Set (n → ℝ)} (hS : MeasurableSet S) :
    mvGaussianFromPosDef M S =
      standardMVGaussian n ((realMatrixSqrt M).mulVec ⁻¹' S) := by
  unfold mvGaussianFromPosDef mvGaussianFromMatrix
  rw [Measure.map_apply (mulVec_measurable _) hS]

/-- The anisotropic symmetric box `{x | ∀ i, |x i| ≤ ε i}` is measurable
(it equals a product of closed intervals). -/
theorem anisotropic_box_measurable (ε : n → ℝ) :
    MeasurableSet {x : n → ℝ | ∀ i, |x i| ≤ ε i} := by
  rw [anisotropic_box_event_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- Specialised change-of-variables for the anisotropic box. -/
theorem mvGaussianFromPosDef_box_apply_eq [DecidableEq n]
    (M : Matrix n n ℝ) (ε : n → ℝ) :
    mvGaussianFromPosDef M {x : n → ℝ | ∀ i, |x i| ≤ ε i} =
      standardMVGaussian n
        ((realMatrixSqrt M).mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε i}) :=
  mvGaussianFromPosDef_apply_eq M (anisotropic_box_measurable ε)

/-! ## General PosDef case: documented `sorry` on the Anderson bound

The PosDef Anderson bound is the multivariate density-at-mode small-ball
upper bound. The proof outline:

1. The pushforward `mvGaussianFromPosDef M` is the Gaussian on `n → ℝ`
   with mean 0, covariance `M`. Its density (Lebesgue-a.e.) is
     `p_M(x) = (2π)^(-n/2) · (det M)^(-1/2) · exp(-xᵀ M⁻¹ x / 2)`.
2. At the mode `x = 0`: `p_M(0) = (2π)^(-n/2) · (det M)^(-1/2)`.
3. For `x ∈ B`, `xᵀ M⁻¹ x ≥ 0` (since `M⁻¹` is PosDef), so
   `exp(-xᵀ M⁻¹ x / 2) ≤ 1`, hence `p_M(x) ≤ p_M(0)`.
4. `ℙ[X ∈ B] = ∫_B p_M(x) dx ≤ p_M(0) · vol(B) = p_M(0) · ∏ᵢ 2εᵢ`.

The mathematical content of this chain rests on having the explicit MV
Gaussian density formula for `mvGaussianFromPosDef M` packaged as a
named Mathlib lemma. This is not yet exported in the form needed.
-/

-- BLOCKER: explicit MV Gaussian density `(2π)^(-n/2) · (det M)^(-1/2) ·
--   exp(-xᵀ M⁻¹ x / 2)` for `mvGaussianFromPosDef M` w.r.t. Lebesgue.
-- TRIED: (1) `Mathlib.Probability.Distributions.Gaussian.Basic` has
--   `IsGaussian` and the 1-D density `gaussianPDFReal`, but no general
--   PosDef MV density lemma; (2) the Round 6 cascade
--   `mvGaussian_pushforward_cov_eq` + `covarianceBilin_apply_pi` gives the
--   covariance correctly, but the box density bound is a SEPARATE
--   property — one needs the Lebesgue density, not just the covariance;
--   (3) `Measure.pi (gaussianReal 0 1) = volume.withDensity (∏ gaussianPDFReal 0 1)`
--   would give the standard MV Gaussian density, but Mathlib does not
--   expose a `pi_withDensity` lemma; (4) for the general PosDef case the
--   pushforward `Measure.map (mulVec L) standardMVGaussian` requires the
--   Jacobian formula `|det L| = √(det M)` lifted to measure pushforward,
--   which Mathlib has only for measure-preserving maps (not for scaled
--   ones).
-- NEEDS: (a) a Mathlib lemma `mvGaussianFromPosDef M` is
--   `HaveLebesgueDensity` with density `(2π)^(-n/2) · (det M)^(-1/2) ·
--   exp(-⟪x, M⁻¹ x⟫ / 2)`, OR (b) the chain `pi_pi_withDensity` +
--   `Measure.map_linear_invertible_eq_density_smul` to compose a
--   per-coordinate density into the multivariate density.
/-- General PosDef multivariate Gaussian Anderson-upper / density-at-mode
small-ball bound for an anisotropic symmetric box. -/
theorem mvGaussian_box_density_at_mode_bound [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) (ε : n → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    ((mvGaussianFromPosDef M) {x : n → ℝ | ∀ i, |x i| ≤ ε i}).toReal ≤
      (∏ i, 2 * ε i) * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n /
        Real.sqrt M.det := by
  sorry

/-! ## Identity-covariance specialisation (provable from the standard MV bound) -/

/-- Specialisation of the PosDef bound to `M = 1`, where `det 1 = 1`. -/
theorem mvGaussian_box_density_at_mode_bound_one [DecidableEq n]
    (ε : n → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    ((mvGaussianFromPosDef (1 : Matrix n n ℝ))
        {x : n → ℝ | ∀ i, |x i| ≤ ε i}).toReal ≤
      (∏ i, 2 * ε i) * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  -- `mvGaussianFromPosDef 1 = standardMVGaussian` (Round 4).
  rw [mvGaussianFromPosDef_one_eq]
  exact standardMVGaussian_anisotropic_box_density_at_mode_bound ε hε

end Erdos524.Helpers
