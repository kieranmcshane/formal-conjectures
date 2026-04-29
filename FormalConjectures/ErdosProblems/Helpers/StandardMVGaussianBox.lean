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

import FormalConjectures.ErdosProblems.Helpers.StandardMVGaussian
import FormalConjectures.ErdosProblems.Helpers.GaussianPDFBounds

/-!
# Phase 2 Round 4 — Anderson-upper for the standard multivariate Gaussian

For the standard multivariate Gaussian on `n → ℝ` (product of `n` independent
`gaussianReal 0 1` factors), we prove the Anderson-upper-style bound on the
symmetric box probability:
  `(standardMVGaussian n {x | ∀ i, |x i| ≤ ε}).toReal ≤
     (2ε)^n · (√(2π))⁻¹^n`,
which equals `(2ε)^n · (2π)^(-n/2)`.

The proof factors the product measure into a product of 1-D box probabilities
via `Measure.pi_pi`, then bounds each factor by the 1-D density-at-mode lemma
`gaussianReal_Icc_le` from `GaussianPDFBounds.lean`.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ## Box event = product of intervals -/

/-- The symmetric box event `{x | ∀ i, |x i| ≤ ε}` is exactly the product
of intervals `Set.pi univ (fun _ => Set.Icc (-ε) ε)`. -/
theorem box_event_eq_pi (n : Type*) [Fintype n] (ε : ℝ) :
    {x : n → ℝ | ∀ i, |x i| ≤ ε} = Set.pi Set.univ (fun _ => Set.Icc (-ε) ε) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies, abs_le]

/-! ## Factorisation of the box probability -/

/-- The standard MV Gaussian box probability factors as a product of 1-D
`gaussianReal 0 1`-box probabilities, via `Measure.pi_pi`. -/
theorem standardMVGaussian_box_eq_prod (n : Type*) [Fintype n] (ε : ℝ) :
    standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε} =
      ∏ _ : n, gaussianReal 0 1 (Set.Icc (-ε) ε) := by
  rw [box_event_eq_pi]
  unfold standardMVGaussian
  exact Measure.pi_pi (fun _ => gaussianReal 0 1) _

/-! ## Anderson-upper for the standard multivariate Gaussian (`v = 1`)

For `n` factors, the symmetric box probability of `standardMVGaussian n` is
at most `(2ε)^n · (√(2π))⁻¹^n`. -/

theorem standardMVGaussian_box_le (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card n * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  -- Rewrite the box probability as a product of 1-D box probabilities.
  rw [standardMVGaussian_box_eq_prod]
  -- Get the per-factor 1-D bound (variance v = 1).
  have h_one_v : ((1 : ℝ≥0) : ℝ) = 1 := by simp
  have h_one_ne_zero : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have h_per_factor :
      ∀ _ : n, (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal ≤
                2 * ε * (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ := by
    intro _
    exact gaussianReal_Icc_le 1 h_one_ne_zero ε hε
  -- Each factor is in `[0, 1]` (since `gaussianReal` is a probability measure).
  have h_per_factor_le_one :
      ∀ _ : n, (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal ≤ 1 := by
    intro _
    have h_le : gaussianReal 0 1 (Set.Icc (-ε) ε) ≤ 1 := by
      calc gaussianReal 0 1 (Set.Icc (-ε) ε) ≤ gaussianReal 0 1 Set.univ := by
            exact measure_mono (Set.subset_univ _)
        _ = 1 := by exact measure_univ
    rw [show (1 : ℝ) = ENNReal.toReal 1 from rfl]
    exact ENNReal.toReal_mono ENNReal.one_ne_top h_le
  have h_per_factor_nn :
      ∀ _ : n, (0 : ℝ) ≤ (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal := by
    intro _; exact ENNReal.toReal_nonneg
  -- The product is finite (each factor ≤ 1), so .toReal of product = product of .toReal.
  have h_prod_finite : ∀ _ : n, gaussianReal 0 1 (Set.Icc (-ε) ε) ≠ ⊤ := by
    intro _
    have h_le : gaussianReal 0 1 (Set.Icc (-ε) ε) ≤ 1 :=
      (le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ))
    exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
  rw [ENNReal.toReal_prod]
  -- Now bound the product: each factor ≤ 2ε · (√(2π))⁻¹.
  have h_factor_bound : 2 * ε * (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ =
                       2 * ε * (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [mul_one]
  -- Apply the product-monotonicity lemma.
  have h_prod_le :
      ∏ _ : n, (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal ≤
        ∏ _ : n, (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) := by
    apply Finset.prod_le_prod
    · exact fun i _ => h_per_factor_nn i
    · intro i _
      have h := h_per_factor i
      rw [h_factor_bound] at h
      exact h
  refine h_prod_le.trans ?_
  -- Right-hand side: ∏ over n of (2ε · (√(2π))⁻¹) = (2ε · (√(2π))⁻¹)^|n|.
  rw [Finset.prod_const, Finset.card_univ]
  -- Goal: (2ε · (√(2π))⁻¹)^card ≤ (2ε)^card · ((√(2π))⁻¹)^card
  rw [mul_pow]

end Erdos524.Helpers
