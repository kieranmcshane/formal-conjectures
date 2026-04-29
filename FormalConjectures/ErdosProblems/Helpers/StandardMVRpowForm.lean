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

import FormalConjectures.ErdosProblems.Helpers.StandardMVGaussianBox
import FormalConjectures.ErdosProblems.Helpers.SqrtTwoPiBounds
import FormalConjectures.ErdosProblems.Helpers.GaussianBoxBounds

/-!
# Phase 2 Round 4 — Anderson upper in `rpow (-card/2)` form

The V1 instance's `anderson_upper` field expects the bound
`(2 * ε) ^ (m * m) * (2π) ^ (-(m * m : ℕ) : ℝ) / 2 * (√cov.det)⁻¹`,
i.e. uses `(2π)^(-card/2)` rather than `((√(2π))⁻¹)^card`. Both forms are
equal, but the V1 contract is in the rpow form. This file converts.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ## Standard MV Gaussian box bound in rpow form -/

theorem standardMVGaussian_box_le_rpow
    (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card n * (2 * Real.pi) ^ (-(Fintype.card n : ℝ) / 2) := by
  have h := standardMVGaussian_box_le n ε hε
  rw [inv_sqrt_two_pi_pow_eq_rpow_neg_half] at h
  exact h

/-! ## Variations -/

theorem inv_sqrt_two_pi_rpow_pos (n : ℕ) :
    (0 : ℝ) < (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
  rw [← inv_sqrt_two_pi_pow_eq_rpow_neg_half]
  exact inv_sqrt_two_pi_pow_pos n

theorem inv_sqrt_two_pi_rpow_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (2 * Real.pi) ^ (-(n : ℝ) / 2) :=
  le_of_lt (inv_sqrt_two_pi_rpow_pos n)

/-! ## RHS positivity in rpow form -/

theorem anderson_upper_rhs_rpow_pos (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (0 : ℝ) < (2 * ε) ^ n * (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
  rw [← inv_sqrt_two_pi_pow_eq_rpow_neg_half]
  exact anderson_upper_rhs_pos ε hε n

theorem anderson_upper_rhs_rpow_nonneg (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (0 : ℝ) ≤ (2 * ε) ^ n * (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
  rw [← inv_sqrt_two_pi_pow_eq_rpow_neg_half]
  exact anderson_upper_rhs_nonneg ε hε n

/-! ## Combined bound chain in rpow form -/

theorem standardMVGaussian_box_le_rpow_explicit
    (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card n * (2 * Real.pi) ^ (-(Fintype.card n : ℝ) / 2) :=
  standardMVGaussian_box_le_rpow n ε hε

end Erdos524.Helpers
