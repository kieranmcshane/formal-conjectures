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

/-!
# Phase 2 Round 4 — Density-at-mode bounds for Gaussian box-style sets

The standard 1-D Gaussian density at the mean (= mode `μ`) is
`(√(2π v))⁻¹`. The product structure of `standardMVGaussian n` carries
this through coordinate-wise: a "diagonal-mode" bound on the
multivariate density.

Auxiliary lemmas for the eventual Anderson-upper inequality.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ## Density-at-mode for standard 1D Gaussian -/

theorem gaussianPDFReal_zero_one_le_inv_sqrt (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  have h := gaussianPDFReal_le_inv_sqrt 0 1 x
  have h_simp : Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) = Real.sqrt (2 * Real.pi) := by
    have h_one : ((1 : ℝ≥0) : ℝ) = 1 := by simp
    rw [h_one, mul_one]
  rwa [h_simp] at h

/-! ## Strong nonneg / positivity for standard PDF -/

theorem gaussianPDFReal_zero_one_pos (x : ℝ) : 0 < gaussianPDFReal 0 1 x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

theorem gaussianPDFReal_zero_one_nonneg (x : ℝ) : 0 ≤ gaussianPDFReal 0 1 x :=
  gaussianPDFReal_nonneg 0 1 x

/-! ## 1D set integral bound: simplified for v=1 -/

theorem setIntegral_gaussianPDFReal_zero_one_le (a b : ℝ) (hab : a ≤ b) :
    ∫ x in Set.Icc a b, gaussianPDFReal 0 1 x ≤ (b - a) * (Real.sqrt (2 * Real.pi))⁻¹ := by
  have h := setIntegral_gaussianPDFReal_le 0 1 a b hab
  have h_simp : Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) = Real.sqrt (2 * Real.pi) := by
    have h_one : ((1 : ℝ≥0) : ℝ) = 1 := by simp
    rw [h_one, mul_one]
  rwa [h_simp] at h

/-! ## Bound on the symmetric Icc set integral -/

theorem setIntegral_gaussianPDFReal_zero_one_Icc_neg_le (ε : ℝ) (hε : 0 ≤ ε) :
    ∫ x in Set.Icc (-ε) ε, gaussianPDFReal 0 1 x ≤ 2 * ε * (Real.sqrt (2 * Real.pi))⁻¹ := by
  have h := setIntegral_gaussianPDFReal_zero_one_le (-ε) ε (by linarith)
  have h_eq : ε - (-ε) = 2 * ε := by ring
  rw [h_eq] at h
  exact h

/-! ## ENNReal-toReal preservation for symmetric Icc -/

theorem gaussianReal_zero_one_Icc_eq_integral (ε : ℝ) :
    (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal =
      ∫ x in Set.Icc (-ε) ε, gaussianPDFReal 0 1 x := by
  rw [gaussianReal_apply_eq_integral _ one_ne_zero]
  rw [ENNReal.toReal_ofReal]
  apply integral_nonneg
  intro x
  exact gaussianPDFReal_nonneg _ _ _

/-! ## Strong upper-bound chain: gaussianReal Icc → integral → 2ε * const -/

theorem gaussianReal_zero_one_Icc_chain_bound (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal ≤ 2 * ε * (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [gaussianReal_zero_one_Icc_eq_integral ε]
  exact setIntegral_gaussianPDFReal_zero_one_Icc_neg_le ε hε

/-! ## Symmetric box on a Cartesian product

For `n` an arbitrary finite type, the symmetric box probability of
`standardMVGaussian n` factorises as a product of `n` copies of the 1D
gaussian box probability. -/

theorem standardMVGaussian_box_eq_prod_gaussianReal
    (n : Type*) [Fintype n] (ε : ℝ) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal =
      ∏ _ : n, (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal := by
  rw [standardMVGaussian_box_eq_prod]
  rw [ENNReal.toReal_prod]

end Erdos524.Helpers
