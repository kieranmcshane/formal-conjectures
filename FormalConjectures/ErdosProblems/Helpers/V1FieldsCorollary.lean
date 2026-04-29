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

end Erdos524.Helpers
