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

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Phase 2 Round 4 — Density-at-mode bounds on `gaussianPDFReal`

The 1-D Gaussian density `gaussianPDFReal μ v` attains its maximum at the
mean `μ`, where the value is `(√(2π v))⁻¹`. This file proves the
density-at-mode inequality and an immediate corollary: the box probability
`gaussianReal μ v (Set.Icc (μ - ε) (μ + ε))` is at most
`2ε · (√(2π v))⁻¹`. These are the 1-D inputs to the multivariate Anderson-
upper bound for `gaussianHierCauchy`.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ## Density-at-mode bound

For a Gaussian with mean `μ` and variance `v`, the density never exceeds the
mode value `(√(2π v))⁻¹`. The proof: the exponential factor
`exp(-(x-μ)² / (2v))` is at most `exp 0 = 1` because the exponent is nonpositive
(squared term ≥ 0, denominator ≥ 0). -/

theorem gaussianPDFReal_le_inv_sqrt (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  rw [gaussianPDFReal]
  set c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hc_def
  have h_c_nn : 0 ≤ c := by
    rw [hc_def]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h_exp_le_one : Real.exp (-(x - μ) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    rcases (eq_or_ne v 0) with hv0 | hv_ne
    · simp [hv0]
    · have hv_pos : (0 : ℝ) < v := by
        have h_v_pos : (0 : ℝ≥0) < v := lt_of_le_of_ne (zero_le _) (Ne.symm hv_ne)
        exact_mod_cast h_v_pos
      have h2v_pos : (0 : ℝ) < 2 * v := by linarith
      have h_num : -(x - μ) ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg _)
      exact div_nonpos_of_nonpos_of_nonneg h_num (le_of_lt h2v_pos)
  calc c * Real.exp (-(x - μ) ^ 2 / (2 * v))
      ≤ c * 1 := mul_le_mul_of_nonneg_left h_exp_le_one h_c_nn
    _ = c := mul_one c

/-! ## Set-integral bound for the Gaussian PDF over a real interval

If `s ⊆ [μ - r, μ + r]` (a symmetric interval of half-length `r ≥ 0`), then
`∫_s gaussianPDFReal μ v ≤ 2r · (√(2π v))⁻¹`. -/

theorem setIntegral_gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (a b : ℝ) (hab : a ≤ b) :
    ∫ x in Set.Icc a b, gaussianPDFReal μ v x ≤ (b - a) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  -- Bound the PDF pointwise by `(√(2π v))⁻¹` and integrate the constant.
  set c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hc_def
  have h_c_nn : 0 ≤ c := by
    rw [hc_def]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h_pointwise : ∀ x ∈ Set.Icc a b, gaussianPDFReal μ v x ≤ c :=
    fun x _ => gaussianPDFReal_le_inv_sqrt μ v x
  have h_const_integral : ∫ _ in Set.Icc a b, c = (b - a) * c := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul]
  have h_vol_finite : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have h_integral_le :
      ∫ x in Set.Icc a b, gaussianPDFReal μ v x ≤ ∫ _ in Set.Icc a b, c := by
    apply MeasureTheory.setIntegral_mono_on
    · exact (integrable_gaussianPDFReal μ v).integrableOn
    · exact MeasureTheory.integrableOn_const h_vol_finite
    · exact measurableSet_Icc
    · exact h_pointwise
  linarith [h_const_integral, h_integral_le]

/-! ## Box-probability bound for `gaussianReal`

For symmetric box `Set.Icc (-ε) ε` and the standard `gaussianReal 0 1`:
`gaussianReal 0 1 (Icc (-ε) ε) ≤ 2ε · (√(2π))⁻¹`.

Stated for general `μ = 0` and any positive `v ≠ 0`. -/

theorem gaussianReal_Icc_le (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 v (Set.Icc (-ε) ε)).toReal ≤ 2 * ε * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  rw [gaussianReal_apply_eq_integral _ hv]
  rw [ENNReal.toReal_ofReal]
  · -- Goal: ∫ x in Icc (-ε) ε, gaussianPDFReal 0 v x ≤ 2 * ε * (√(2 π v))⁻¹
    have h_le := setIntegral_gaussianPDFReal_le 0 v (-ε) ε (by linarith)
    have h_eq : (ε - (-ε)) = 2 * ε := by ring
    rw [h_eq] at h_le
    exact h_le
  · -- 0 ≤ ∫ x in Icc (-ε) ε, gaussianPDFReal 0 v x
    apply integral_nonneg
    intro x
    exact gaussianPDFReal_nonneg _ _ _

end Erdos524.Helpers
