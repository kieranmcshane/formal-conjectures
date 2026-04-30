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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsClosing
import FormalConjectures.ErdosProblems.Helpers.GaussianHierCauchyBox

/-!
# Phase 2 Round 4 — V1 instance corollaries

A few miscellaneous corollaries of the Round 4 chain.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

/-! ## More wrappers -/

theorem glwBoxProb_le_one_alt (m : ℕ) (ε : ℝ) : glwBoxProb m ε ≤ 1 :=
  glwBoxProb_le_one_via_pullback m ε

theorem glwBoxProb_eq_box_event_toReal (m : ℕ) (ε : ℝ) :
    glwBoxProb m ε = (gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε}).toReal := rfl

theorem gaussianHierCauchy_box_le_one_alt (m : ℕ) (ε : ℝ) :
    gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε} ≤ 1 :=
  le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)

/-! ## Variance-boundedness through pullback -/

theorem standardMVGaussian_pullback_box_finite_real (m : ℕ) (ε : ℝ) :
    (standardMVGaussian (Fin m × Fin m)
      ((realMatrixSqrt (hierCauchyG m)).mulVec ⁻¹'
        {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε})).toReal ≤ 1 :=
  standard_pullback_box_le_one m ε

/-! ## Trivial m≥1 case -/

theorem hierCauchyG_det_pos_at_one : 0 < (hierCauchyG 1).det := hierCauchyG_det_pos 1 (by norm_num)

theorem hierCauchyG_inv_sqrt_det_pos_at_one : 0 < (Real.sqrt ((hierCauchyG 1).det))⁻¹ :=
  hierCauchyG_inv_sqrt_det_pos 1 (by norm_num)

/-! ## Round 10 — Stretch B: V1-field-shaped Anderson upper

The V1 contract requires `anderson_upper : ∀ ε > 0, boxProb ε ≤ (2ε)^(m·m) ·
(2π)^(-(m·m)/2) · sqrt(cov.det)⁻¹`. With Round 10's hierCauchyG_PosDef
discharging the Round 9 conditional, this field is now provable
unconditionally for `m ≥ 1`. -/

/-- V1-field-shaped `anderson_upper`: with `cov := glwBoxProb_cov m = hierCauchyG m`,
the Anderson upper bound holds unconditionally for `m ≥ 1`. -/
theorem glwBoxProb_anderson_upper_field {m : ℕ} (hm : 1 ≤ m) :
    ∀ ε : ℝ, 0 < ε →
      glwBoxProb m ε ≤
        (2 * ε) ^ (m * m) *
          (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
          (Real.sqrt (glwBoxProb_cov m).det)⁻¹ := by
  intro ε hε
  -- glwBoxProb_cov = hierCauchyG by definition, so the dets match.
  have h_cov_eq : (glwBoxProb_cov m).det = (hierCauchyG m).det := by
    rw [glwBoxProb_cov_eq_hierCauchy]
  rw [h_cov_eq]
  exact glwBoxProb_anderson_upper_v1 hm hε

/-! ## Round 10 — Stretch D: realMatrixSqrt corollaries

Round 9 set up the `realMatrixSqrt` API for general PosDef matrices.
With Round 10's `hierCauchyG_PosDef` we can specialise to the
hierarchical Cauchy matrix. -/

/-- `(realMatrixSqrt (hierCauchyG m)).det = Real.sqrt (hierCauchyG m).det`. -/
theorem hierCauchyG_realMatrixSqrt_det (m : ℕ) (hm : 1 ≤ m) :
    (realMatrixSqrt (hierCauchyG m)).det = Real.sqrt (hierCauchyG m).det := by
  classical
  exact realMatrixSqrt_det (hierCauchyG_PosSemidef m)

/-- The symmetric square root of `hierCauchyG m` has strictly positive determinant. -/
theorem hierCauchyG_realMatrixSqrt_det_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < (realMatrixSqrt (hierCauchyG m)).det := by
  classical
  exact realMatrixSqrt_det_pos (hierCauchyG_PosDef m hm)

/-- The symmetric square root of `hierCauchyG m` is invertible. -/
theorem hierCauchyG_realMatrixSqrt_isUnit (m : ℕ) (hm : 1 ≤ m) :
    IsUnit (realMatrixSqrt (hierCauchyG m)) := by
  classical
  exact realMatrixSqrt_isUnit (hierCauchyG_PosDef m hm)

/-! ## Round 10 — Direct gaussianHierCauchy Anderson bound

A more direct entry point: bypass `glwBoxProb` entirely and state
the Anderson upper bound for the box event under the
`gaussianHierCauchy` measure. -/

/-- Anderson upper bound for the box event under `gaussianHierCauchy m`,
unconditional for `m ≥ 1`. Direct form. -/
theorem gaussianHierCauchy_box_anderson_upper {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    (gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε}).toReal ≤
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG m).det)⁻¹ := by
  -- glwBoxProb m ε = (gaussianHierCauchy m _).toReal by definition.
  show glwBoxProb m ε ≤ _
  exact glwBoxProb_anderson_upper_v1 hm hε

/-- Sanity-check examples for the m = 1 case. -/
example {ε : ℝ} (hε : 0 < ε) :
    glwBoxProb 1 ε ≤
      (2 * ε) ^ (1 * 1) *
        (2 * Real.pi) ^ (-((1 * 1 : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG 1).det)⁻¹ :=
  glwBoxProb_anderson_upper_v1 (by norm_num) hε

example {ε : ℝ} (hε : 0 < ε) :
    (gaussianHierCauchy 1 {x : Fin 1 × Fin 1 → ℝ | ∀ ij, |x ij| ≤ ε}).toReal ≤
      (2 * ε) ^ (1 * 1) *
        (2 * Real.pi) ^ (-((1 * 1 : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG 1).det)⁻¹ :=
  gaussianHierCauchy_box_anderson_upper (by norm_num) hε

/-! ## Round 10 — Reformulation via realMatrixSqrt det

Equivalent form of the Anderson upper bound using the realMatrixSqrt
determinant identity `(realMatrixSqrt M).det = sqrt(det M)`. -/

/-- Anderson upper bound rewritten using `(realMatrixSqrt _).det` instead of
`Real.sqrt _.det`. -/
theorem glwBoxProb_anderson_upper_via_sqrt {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    glwBoxProb m ε ≤
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        ((realMatrixSqrt (hierCauchyG m)).det)⁻¹ := by
  classical
  rw [hierCauchyG_realMatrixSqrt_det m hm]
  exact glwBoxProb_anderson_upper_v1 hm hε

end Erdos524.Helpers
