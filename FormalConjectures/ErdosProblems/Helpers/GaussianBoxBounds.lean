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

import FormalConjectures.ErdosProblems.Helpers.GaussianPDFBounds
import FormalConjectures.ErdosProblems.Helpers.StandardMVGaussianBox

/-!
# Phase 2 Round 4 — Auxiliary box-probability bounds for Gaussian measures

Combinatorial / monotonicity wrappers around `gaussianReal_Icc_le` and
`standardMVGaussian_box_le` that the V1-instance Anderson-upper field will
need at multiple specialised arities.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ## Box probability factorises as `(2ε · const)^card` -/

theorem standardMVGaussian_box_le_compact (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card n := by
  have h := standardMVGaussian_box_le n ε hε
  have h_eq : (2 * ε) ^ Fintype.card n * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n
        = (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card n := by
    rw [← mul_pow]
  rw [h_eq] at h
  exact h

/-! ## Simple monotonicity for the box event under set-valued ε -/

theorem box_event_mono (n : Type*) [Fintype n] {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    {x : n → ℝ | ∀ i, |x i| ≤ ε₁} ⊆ {x : n → ℝ | ∀ i, |x i| ≤ ε₂} := by
  intro x hx i
  exact (hx i).trans hε

theorem standardMVGaussian_box_mono (n : Type*) [Fintype n] {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε₁} ≤
      standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε₂} :=
  measure_mono (box_event_mono n hε)

/-! ## Probability is at most 1 -/

theorem standardMVGaussian_le_one (n : Type*) [Fintype n] (S : Set (n → ℝ)) :
    (standardMVGaussian n S).toReal ≤ 1 := by
  have h_le : standardMVGaussian n S ≤ 1 := by
    calc standardMVGaussian n S ≤ standardMVGaussian n Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  rw [show (1 : ℝ) = ENNReal.toReal 1 from rfl]
  exact ENNReal.toReal_mono ENNReal.one_ne_top h_le

/-! ## Combined: 1D box probability bound is uniform across coordinates -/

theorem one_d_box_bound_uniform (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal ≤ 2 * ε * (Real.sqrt (2 * Real.pi))⁻¹ := by
  have h := gaussianReal_Icc_le 1 one_ne_zero ε hε
  -- The variance v = 1 case: simplify (2π · 1) = 2π in the radical.
  have h_simp : Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) = Real.sqrt (2 * Real.pi) := by
    have h_one : ((1 : ℝ≥0) : ℝ) = 1 := by simp
    rw [h_one, mul_one]
  rw [h_simp] at h
  exact h

/-! ## Refined product form -/

theorem standardMVGaussian_box_le_via_prod (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      ∏ _ : n, (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) := by
  rw [Finset.prod_const, Finset.card_univ]
  exact standardMVGaussian_box_le_compact n ε hε

/-! ## Simple corollary: probability of empty box (ε ≤ 0) -/

theorem standardMVGaussian_box_zero_le (n : Type*) [Fintype n] :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ 0}).toReal ≤
      (2 * 0 * (Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card n :=
  standardMVGaussian_box_le_compact n 0 (le_refl _)

/-! ## Box-event measure is finite (probability bound implies finite ENNReal) -/

theorem standardMVGaussian_box_finite (n : Type*) [Fintype n] (ε : ℝ) :
    standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε} ≠ ⊤ := by
  have h_le : standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε} ≤ 1 := by
    calc standardMVGaussian n _ ≤ standardMVGaussian n Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)

/-! ## Pulled-back box has finite measure under standard MV Gaussian -/

theorem mulVec_preimage_box_finite {n : Type*} [Fintype n] [DecidableEq n]
    (L : Matrix n n ℝ) (ε : ℝ) :
    standardMVGaussian n (L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε}) ≠ ⊤ := by
  have h_le :
      standardMVGaussian n (L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε}) ≤ 1 := by
    calc standardMVGaussian n _ ≤ standardMVGaussian n Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)

end Erdos524.Helpers
