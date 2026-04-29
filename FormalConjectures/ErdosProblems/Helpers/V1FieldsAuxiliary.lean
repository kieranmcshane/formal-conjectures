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

import FormalConjectures.ErdosProblems.Helpers.GaussianHierCauchyBox
import FormalConjectures.ErdosProblems.Helpers.MVGaussianRpowChain
import FormalConjectures.ErdosProblems.Helpers.HierCauchyFacts

/-!
# Phase 2 Round 4 — V1-instance auxiliary lemmas

A collection of small lemmas geared specifically at filling V1 instance
candidate fields. Each is a focused statement that the eventual V1 instance
constructor will compose.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

/-! ## Cardinality of `Fin m × Fin m` -/

theorem fintype_card_prod_fin (m : ℕ) :
    Fintype.card (Fin m × Fin m) = m * m := by
  rw [Fintype.card_prod, Fintype.card_fin]

/-! ## Determinant positivity for hierCauchyG (sqrt) -/

theorem hierCauchyG_sqrt_det_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < Real.sqrt ((hierCauchyG m).det) := by
  apply Real.sqrt_pos.mpr
  exact hierCauchyG_det_pos m hm

theorem hierCauchyG_sqrt_det_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((hierCauchyG m).det) ≠ 0 :=
  ne_of_gt (hierCauchyG_sqrt_det_pos m hm)

theorem hierCauchyG_inv_sqrt_det_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < (Real.sqrt ((hierCauchyG m).det))⁻¹ :=
  inv_pos.mpr (hierCauchyG_sqrt_det_pos m hm)

theorem hierCauchyG_inv_sqrt_det_nonneg (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ (Real.sqrt ((hierCauchyG m).det))⁻¹ :=
  le_of_lt (hierCauchyG_inv_sqrt_det_pos m hm)

/-! ## V1-shape RHS positivity for hierCauchyG covariance -/

theorem v1_anderson_rhs_pos (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    (0 : ℝ) <
      (2 * ε) ^ (Fintype.card (Fin m × Fin m)) *
        (2 * Real.pi) ^ (-(Fintype.card (Fin m × Fin m) : ℝ) / 2) *
        (Real.sqrt ((hierCauchyG m).det))⁻¹ := by
  apply mul_pos
  · exact anderson_upper_rhs_rpow_pos ε hε _
  · exact hierCauchyG_inv_sqrt_det_pos m hm

theorem v1_anderson_rhs_nonneg (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 ≤ ε) :
    (0 : ℝ) ≤
      (2 * ε) ^ (Fintype.card (Fin m × Fin m)) *
        (2 * Real.pi) ^ (-(Fintype.card (Fin m × Fin m) : ℝ) / 2) *
        (Real.sqrt ((hierCauchyG m).det))⁻¹ := by
  apply mul_nonneg
  · exact anderson_upper_rhs_rpow_nonneg ε hε _
  · exact hierCauchyG_inv_sqrt_det_nonneg m hm

/-! ## Direct computation form of V1 RHS -/

theorem v1_anderson_rhs_eq (m : ℕ) (ε : ℝ) :
    (2 * ε) ^ (Fintype.card (Fin m × Fin m)) *
        (2 * Real.pi) ^ (-(Fintype.card (Fin m × Fin m) : ℝ) / 2) *
        (Real.sqrt ((hierCauchyG m).det))⁻¹ =
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-(m * m : ℕ) / 2 : ℝ) *
        (Real.sqrt ((hierCauchyG m).det))⁻¹ := by
  rw [fintype_card_prod_fin]

end Erdos524.Helpers
