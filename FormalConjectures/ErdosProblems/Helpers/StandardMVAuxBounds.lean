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
import FormalConjectures.ErdosProblems.Helpers.GaussianBoxBounds
import FormalConjectures.ErdosProblems.Helpers.StandardMVDensityBound

/-!
# Phase 2 Round 4 — Auxiliary Anderson-upper-style box bounds

Algebraic forms of the box-probability bound, useful for the V1 instance
Anderson_upper field. Each lemma here is a re-arrangement / specialisation
of `standardMVGaussian_box_le` proved earlier in this round.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ## Variations on the Anderson-upper for standard MV Gaussian -/

/-- Anderson-upper with cardinality cast to real explicitly. -/
theorem standardMVGaussian_box_le_real_card
    (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ (Fintype.card n : ℕ) *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ (Fintype.card n : ℕ) :=
  standardMVGaussian_box_le n ε hε

/-- Anderson-upper bound is nonnegative on the RHS. -/
theorem standardMVGaussian_box_bound_nonneg
    (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (0 : ℝ) ≤ (2 * ε) ^ Fintype.card n *
              (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  apply mul_nonneg
  · exact pow_nonneg (by linarith) _
  · exact pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _

/-- Strict positivity for ε > 0. -/
theorem standardMVGaussian_box_bound_pos
    (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 < ε) :
    (0 : ℝ) < (2 * ε) ^ Fintype.card n *
              (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  have h_2eps : 0 < 2 * ε := by linarith
  have h_inv_sqrt : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    have := Real.pi_pos; linarith
  exact mul_pos (pow_pos h_2eps _) (pow_pos h_inv_sqrt _)

/-! ## Comparison with constant `1` form

Probability ≤ Anderson-upper ≤ ? -/

/-- Probability is ≤ 1, regardless of cleverness. -/
theorem standardMVGaussian_box_le_one (n : Type*) [Fintype n] (ε : ℝ) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤ 1 :=
  standardMVGaussian_le_one n _

/-! ## Distributing the power across multiplication -/

theorem prod_two_eps_inv_sqrt_eq_pow (n : Type*) [Fintype n] (ε : ℝ) :
    ∏ _ : n, (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) =
      (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card n := by
  rw [Finset.prod_const, Finset.card_univ]

theorem prod_two_eps_inv_sqrt_eq_pow_split (n : Type*) [Fintype n] (ε : ℝ) :
    ∏ _ : n, (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) =
      (2 * ε) ^ Fintype.card n *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  rw [prod_two_eps_inv_sqrt_eq_pow, mul_pow]

/-! ## Combined direct-form Anderson-upper -/

theorem standardMVGaussian_box_anderson_direct
    (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      ∏ _ : n, (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) := by
  rw [prod_two_eps_inv_sqrt_eq_pow_split]
  exact standardMVGaussian_box_le n ε hε

/-! ## Bound on the product of nonneg-bounded factors -/

theorem prod_le_pow_of_uniform {α : Type*} [Fintype α]
    (f : α → ℝ) (M : ℝ) (hM : 0 ≤ M) (h : ∀ i, 0 ≤ f i) (hb : ∀ i, f i ≤ M) :
    ∏ i : α, f i ≤ M ^ Fintype.card α := by
  rw [show M ^ Fintype.card α = ∏ _ : α, M from by
    rw [Finset.prod_const, Finset.card_univ]]
  apply Finset.prod_le_prod
  · exact fun i _ => h i
  · exact fun i _ => hb i

/-! ## Multiplicative factoring -/

theorem prod_split_two_factor (n : Type*) [Fintype n] (a b : ℝ) :
    (∏ _ : n, (a * b)) = a ^ Fintype.card n * b ^ Fintype.card n := by
  rw [Finset.prod_const, Finset.card_univ, mul_pow]

end Erdos524.Helpers
