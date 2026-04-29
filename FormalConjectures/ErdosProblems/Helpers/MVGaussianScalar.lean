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

import FormalConjectures.ErdosProblems.Helpers.MVGaussianRotation
import FormalConjectures.ErdosProblems.Helpers.MVGaussianPullback

/-!
# Phase 2 Round 4 — Scalar-multiple pushforward

For a positive scalar `c`, the matrix `c · 1 : Matrix n n ℝ` has
`(c · 1).mulVec x = c • x`. The pushforward
`mvGaussianFromMatrix (c · 1) = Measure.map (· ∘ smul c) (standardMVGaussian n)`
is the standard MV Gaussian's image under coordinate-wise scaling.

We prove the box-probability identity
  `(mvGaussianFromMatrix (c · 1) {x | ∀ i, |x i| ≤ ε}) =`
  `  (standardMVGaussian {x | ∀ i, |x i| ≤ ε / c})`
and the resulting Anderson-upper bound for the scalar-covariance case.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Scalar matrix `c • 1` and its mulVec -/

/-- `(c • 1).mulVec x = c • x`, expressed pointwise. -/
theorem smul_one_mulVec (c : ℝ) (x : n → ℝ) :
    ((c • (1 : Matrix n n ℝ)).mulVec) x = c • x := by
  ext i
  simp [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]

/-- The full function-level identity. -/
theorem smul_one_mulVec_eq (c : ℝ) :
    ((c • (1 : Matrix n n ℝ)).mulVec) = (c • ·) := by
  funext x
  exact smul_one_mulVec c x

/-! ## Pulled-back box for the scalar matrix

`(c • 1).mulVec ⁻¹' {x | ∀ i, |x i| ≤ ε}` equals the box of half-width
`ε / |c|` when `c ≠ 0`. -/

theorem smul_one_mulVec_preimage_box (c : ℝ) (hc : c ≠ 0) (ε : ℝ) :
    ((c • (1 : Matrix n n ℝ)).mulVec) ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε} =
      {x : n → ℝ | ∀ i, |x i| ≤ ε / |c|} := by
  have hc_pos : 0 < |c| := abs_pos.mpr hc
  ext x
  rw [Set.mem_preimage]
  simp only [Set.mem_setOf_eq, smul_one_mulVec, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h i
    have hi := h i
    have h_abs : |c * x i| = |c| * |x i| := abs_mul c (x i)
    rw [h_abs] at hi
    -- From `|c| * |x i| ≤ ε`, conclude `|x i| ≤ ε / |c|`.
    rw [le_div_iff₀ hc_pos]
    linarith
  · intro h i
    have hi := h i
    have h_abs : |c * x i| = |c| * |x i| := abs_mul c (x i)
    rw [h_abs]
    -- From `|x i| ≤ ε / |c|`, conclude `|c| * |x i| ≤ ε`.
    rw [le_div_iff₀ hc_pos] at hi
    linarith

/-! ## Pushforward of box under scalar matrix -/

theorem mvGaussianFromMatrix_smul_one_box (c : ℝ) (hc : c ≠ 0) (ε : ℝ) :
    mvGaussianFromMatrix (c • (1 : Matrix n n ℝ))
        {x : n → ℝ | ∀ i, |x i| ≤ ε} =
      standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε / |c|} := by
  rw [mvGaussianFromMatrix_apply_eq_standard_pullback _ _ (box_event_measurable _ ε)]
  rw [smul_one_mulVec_preimage_box c hc ε]

/-! ## Anderson-upper for the scalar-covariance case

For c > 0 and ε ≥ 0:
  `(mvGaussianFromMatrix (c • 1) box ε).toReal ≤ (2ε/c)^n · (√(2π))⁻¹^n
                                                = (2ε)^n · (√(2π))⁻¹^n / c^n`. -/

theorem mvGaussianFromMatrix_smul_one_box_le
    (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (c • (1 : Matrix n n ℝ))
        {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * (ε / c)) ^ Fintype.card n *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  rw [mvGaussianFromMatrix_smul_one_box c (ne_of_gt hc) ε]
  have h_abs : |c| = c := abs_of_pos hc
  rw [h_abs]
  apply standardMVGaussian_box_le n (ε / c)
  exact div_nonneg hε (le_of_lt hc)

/-! ## Box probability for `c • 1` covariance is bounded by `(2ε)^n / c^n · (2π)^(-n/2)` -/

theorem mvGaussianFromMatrix_smul_one_box_le_div
    (m : Type*) [Fintype m] [DecidableEq m]
    (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (c • (1 : Matrix m m ℝ))
        {x : m → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card m / c ^ Fintype.card m *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card m := by
  have h := mvGaussianFromMatrix_smul_one_box_le (n := m) c hc ε hε
  -- (2 * (ε / c))^card = (2*ε)^card / c^card
  have h_eq : (2 * (ε / c)) ^ Fintype.card m =
              (2 * ε) ^ Fintype.card m / c ^ Fintype.card m := by
    rw [show (2 * (ε / c)) = (2 * ε) / c from by ring, div_pow]
  rw [h_eq] at h
  exact h

end Erdos524.Helpers
