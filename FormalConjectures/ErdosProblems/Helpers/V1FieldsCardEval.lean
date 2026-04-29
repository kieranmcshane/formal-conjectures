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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsAuxiliary
import FormalConjectures.ErdosProblems.Helpers.V1FieldsBoxRel
import FormalConjectures.ErdosProblems.Helpers.MVGaussianRpowChain

/-!
# Phase 2 Round 4 — Cardinality evaluation for V1 RHS

Concrete numeric evaluations of the Anderson-upper RHS at specific m
values, useful for spot-checking the V1 instance contract is consumed
in the right shape downstream.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix Real

/-! ## RHS in card form for general m -/

theorem v1_anderson_rhs_card_eq (m : ℕ) (ε : ℝ) :
    (2 * ε) ^ (Fintype.card (Fin m × Fin m)) =
      (2 * ε) ^ (m * m) := by
  rw [fintype_card_prod_fin]

theorem v1_anderson_rpow_factor_card_eq (m : ℕ) :
    (2 * Real.pi) ^ (-(Fintype.card (Fin m × Fin m) : ℝ) / 2) =
      (2 * Real.pi) ^ (-(m * m : ℝ) / 2) := by
  rw [fintype_card_prod_fin]; push_cast; ring_nf

theorem v1_anderson_full_card_eq (m : ℕ) (ε : ℝ) :
    (2 * ε) ^ (Fintype.card (Fin m × Fin m)) *
      (2 * Real.pi) ^ (-(Fintype.card (Fin m × Fin m) : ℝ) / 2) *
      (Real.sqrt ((hierCauchyG m).det))⁻¹ =
    (2 * ε) ^ (m * m) *
      (2 * Real.pi) ^ (-(m * m : ℝ) / 2) *
      (Real.sqrt ((hierCauchyG m).det))⁻¹ := by
  rw [v1_anderson_rhs_card_eq, v1_anderson_rpow_factor_card_eq]

/-! ## Trivial m=0 case: card = 0, all powers are 1 -/

theorem v1_anderson_zero_card (ε : ℝ) :
    (2 * ε) ^ (Fintype.card (Fin 0 × Fin 0)) *
      (2 * Real.pi) ^ (-(Fintype.card (Fin 0 × Fin 0) : ℝ) / 2) = 1 := by
  rw [fintype_card_prod_fin]
  simp

/-! ## Standard MV Gaussian box bound at m=0 -/

theorem standardMVGaussian_box_zero_card (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian (Fin 0 × Fin 0) {x | ∀ i, |x i| ≤ ε}).toReal ≤ 1 := by
  have h := standardMVGaussian_box_le_rpow (Fin 0 × Fin 0) ε hε
  rw [v1_anderson_zero_card] at h
  exact h

/-! ## glwBoxProb at m=0 is bounded -/

theorem glwBoxProb_zero_le_anderson (ε : ℝ) :
    glwBoxProb 0 ε ≤ 1 := by
  exact glwBoxProb_le_one_via_pullback 0 ε

end Erdos524.Helpers
