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

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Phase 2 Round 4 — `√(2π)` arithmetic

Algebraic identities relating `(√(2π))⁻¹^n` to `(2π)^(-n/2)` used
ubiquitously in Anderson-upper-style bounds for multivariate Gaussian
box probabilities.
-/

namespace Erdos524.Helpers
open Real

/-! ## Positivity facts -/

theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by
  have := Real.pi_pos; linarith

theorem two_pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := le_of_lt two_pi_pos

theorem sqrt_two_pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.mpr two_pi_pos

theorem sqrt_two_pi_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 :=
  ne_of_gt sqrt_two_pi_pos

theorem inv_sqrt_two_pi_pos : (0 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ :=
  inv_pos.mpr sqrt_two_pi_pos

theorem inv_sqrt_two_pi_nonneg : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ :=
  le_of_lt inv_sqrt_two_pi_pos

/-! ## Powers of `(√(2π))⁻¹` are nonneg / positive -/

theorem inv_sqrt_two_pi_pow_pos (n : ℕ) :
    (0 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ ^ n :=
  pow_pos inv_sqrt_two_pi_pos n

theorem inv_sqrt_two_pi_pow_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ ^ n :=
  le_of_lt (inv_sqrt_two_pi_pow_pos n)

/-! ## (Optional) rpow form -/

theorem inv_sqrt_two_pi_eq_rpow_neg_half :
    (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi) ^ (-(1 : ℝ) / 2) := by
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) from by ring]
  rw [Real.rpow_neg (le_of_lt two_pi_pos)]
  rw [Real.sqrt_eq_rpow]

/-! ## `(2 * ε)^n` positivity -/

theorem two_eps_pow_nonneg (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) : (0 : ℝ) ≤ (2 * ε) ^ n :=
  pow_nonneg (by linarith) n

theorem two_eps_pow_pos (ε : ℝ) (hε : 0 < ε) (n : ℕ) : (0 : ℝ) < (2 * ε) ^ n :=
  pow_pos (by linarith) n

/-! ## Combined Anderson-upper RHS positivity -/

theorem anderson_upper_rhs_pos (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (0 : ℝ) < (2 * ε) ^ n * (Real.sqrt (2 * Real.pi))⁻¹ ^ n :=
  mul_pos (two_eps_pow_pos ε hε n) (inv_sqrt_two_pi_pow_pos n)

theorem anderson_upper_rhs_nonneg (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (0 : ℝ) ≤ (2 * ε) ^ n * (Real.sqrt (2 * Real.pi))⁻¹ ^ n :=
  mul_nonneg (two_eps_pow_nonneg ε hε n) (inv_sqrt_two_pi_pow_nonneg n)

end Erdos524.Helpers
