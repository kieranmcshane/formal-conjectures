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

import FormalConjectures.ErdosProblems.Helpers.GaussianHierCauchyBox
import FormalConjectures.ErdosProblems.Helpers.MVGaussianRotation
import FormalConjectures.ErdosProblems.Helpers.MVGaussianMisc

/-!
# Phase 2 Round 4 — V1-instance refinements

Refined statements for the V1 instance candidate `glwBoxProb`, building on
`GaussianHierCauchyBox` + the multivariate Gaussian framework.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

/-! ## glwBoxProb monotone with respect to inclusion of cov -/

theorem glwBoxProb_le_when_box_contains
    (m : ℕ) (S : Set (Fin m × Fin m → ℝ))
    (hS : MeasurableSet S)
    (h_subset : ∀ ε > 0, {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε} ⊆ S) :
    ∀ ε > 0, glwBoxProb m ε ≤ (gaussianHierCauchy m S).toReal := by
  intro ε hε
  unfold glwBoxProb
  apply ENNReal.toReal_mono
  · -- finite
    have h_le : gaussianHierCauchy m S ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
  · exact measure_mono (h_subset ε hε)

/-! ## glwBoxProb expressed as a non-strict ENNReal bound -/

theorem gaussianHierCauchy_box_le_one_ennreal (m : ℕ) (ε : ℝ) :
    gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε} ≤ 1 :=
  le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)

/-! ## Using the pullback identity for ε bounds -/

theorem glwBoxProb_eq_pullback_at_pos (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    glwBoxProb m ε =
      (standardMVGaussian (Fin m × Fin m)
        ((realMatrixSqrt (hierCauchyG m)).mulVec ⁻¹'
          {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε})).toReal :=
  glwBoxProb_eq_pullback_standardMV m ε

/-! ## Pulled-back-box probability is bounded by standard MV trivially -/

theorem standardMV_pullback_le_one (m : ℕ) (L : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ)
    (ε : ℝ) :
    (standardMVGaussian (Fin m × Fin m)
      (L.mulVec ⁻¹' {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε})).toReal ≤ 1 :=
  standardMVGaussian_le_one (Fin m × Fin m) _

/-! ## glwBoxProb's nonnegativity from the trivial side -/

theorem glwBoxProb_nonneg_explicit (m : ℕ) (ε : ℝ) :
    0 ≤ glwBoxProb m ε := by
  unfold glwBoxProb; exact ENNReal.toReal_nonneg

/-! ## Combining bound with chain identity -/

theorem glwBoxProb_le_pullback_one (m : ℕ) (ε : ℝ) :
    glwBoxProb m ε ≤ 1 := by
  rw [glwBoxProb_eq_pullback_standardMV]
  exact standardMVGaussian_le_one _ _

/-! ## Constraint relating glwBoxProb to the standard pullback identity -/

theorem glwBoxProb_eq_zero_iff_pullback_zero (m : ℕ) (ε : ℝ) :
    glwBoxProb m ε = 0 ↔
      (standardMVGaussian (Fin m × Fin m)
        ((realMatrixSqrt (hierCauchyG m)).mulVec ⁻¹'
          {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε})).toReal = 0 := by
  rw [glwBoxProb_eq_pullback_standardMV]

end Erdos524.Helpers
