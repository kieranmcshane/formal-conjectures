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

import FormalConjectures.ErdosProblems.Helpers.MVGaussianScalar
import FormalConjectures.ErdosProblems.Helpers.MVGaussianRotation
import FormalConjectures.ErdosProblems.Helpers.StandardMVRpowForm

/-!
# Phase 2 Round 4 — rpow-form Anderson-upper for special covariance cases

For each special covariance case (`I`, `c² · I`), the Anderson-upper bound
is also expressible in `(2π)^(-card/2)` rpow form. This file ships those
specialised lemmas.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Identity covariance (cov = 1) — rpow form -/

theorem mvGaussianFromMatrix_one_box_le_rpow (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (1 : Matrix n n ℝ)
        {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card n *
        (2 * Real.pi) ^ (-(Fintype.card n : ℝ) / 2) := by
  rw [mvGaussianFromMatrix_one_eq]
  exact standardMVGaussian_box_le_rpow n ε hε

/-! ## Scalar covariance (`c²·I` after Cholesky) — rpow form -/

theorem mvGaussianFromMatrix_smul_one_box_le_rpow
    (m : Type*) [Fintype m] [DecidableEq m]
    (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (c • (1 : Matrix m m ℝ))
        {x : m → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * (ε / c)) ^ Fintype.card m *
        (2 * Real.pi) ^ (-(Fintype.card m : ℝ) / 2) := by
  have h := mvGaussianFromMatrix_smul_one_box_le (n := m) c hc ε hε
  rw [inv_sqrt_two_pi_pow_eq_rpow_neg_half] at h
  exact h

/-! ## Same as above but with the (2ε)^n / c^n factor split out -/

theorem mvGaussianFromMatrix_smul_one_box_le_rpow_div
    (m : Type*) [Fintype m] [DecidableEq m]
    (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (c • (1 : Matrix m m ℝ))
        {x : m → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card m / c ^ Fintype.card m *
        (2 * Real.pi) ^ (-(Fintype.card m : ℝ) / 2) := by
  have h := mvGaussianFromMatrix_smul_one_box_le_div (m := m) c hc ε hε
  rw [inv_sqrt_two_pi_pow_eq_rpow_neg_half] at h
  exact h

/-! ## Comparison: V1 instance Anderson_upper field shape -/

/-- The V1 instance's `anderson_upper` field has the form
`boxProb ε ≤ (2 * ε) ^ (m * m) * (2π) ^ (-(m * m : ℕ) : ℝ) / 2 *
                        (Real.sqrt cov.det)⁻¹`. For our identity-covariance case,
`cov.det = 1` so `(Real.sqrt 1)⁻¹ = 1`. -/
theorem anderson_upper_v1_form_for_identity
    (m : Type*) [Fintype m] [DecidableEq m] (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (1 : Matrix m m ℝ)
        {x : m → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card m *
        (2 * Real.pi) ^ (-(Fintype.card m : ℝ) / 2) *
        (Real.sqrt ((1 : Matrix m m ℝ).det))⁻¹ := by
  have h := mvGaussianFromMatrix_one_box_le_rpow (n := m) ε hε
  have h_det : (1 : Matrix m m ℝ).det = 1 := Matrix.det_one
  rw [h_det, Real.sqrt_one, inv_one, mul_one]
  exact h

end Erdos524.Helpers
