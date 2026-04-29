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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsAuxiliary
import FormalConjectures.ErdosProblems.Helpers.GaussianHierCauchyBox

/-!
# Phase 2 Round 4 — Box-event relations for V1 instance

Relations between box-event sets used in the V1 instance contract.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

/-! ## Box vs sub-box -/

theorem box_event_subset_when_eps_le (n : Type*) [Fintype n] {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    {x : n → ℝ | ∀ i, |x i| ≤ ε₁} ⊆ {x : n → ℝ | ∀ i, |x i| ≤ ε₂} :=
  fun _ hx i => (hx i).trans h

theorem gaussianHierCauchy_box_le_box (m : ℕ) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε₁} ≤
      gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε₂} :=
  measure_mono (box_event_subset_when_eps_le _ h)

/-! ## glwBoxProb monotone (alternate form) -/

theorem glwBoxProb_le_of_le_alt (m : ℕ) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    glwBoxProb m ε₁ ≤ glwBoxProb m ε₂ := by
  unfold glwBoxProb
  apply ENNReal.toReal_mono
  · -- finiteness
    have h_le :
        gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε₂} ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
  · exact gaussianHierCauchy_box_le_box m h

/-! ## Trivial boxProb ≤ 1 form -/

theorem glwBoxProb_le_one_explicit_alt (m : ℕ) (ε : ℝ) :
    glwBoxProb m ε ≤ 1 := glwBoxProb_le_one_via_pullback m ε

/-! ## Pulled-back box subsets -/

theorem mulVec_preimage_box_subset_when_eps_le {n : Type*} [Fintype n] [DecidableEq n]
    (L : Matrix n n ℝ) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₁} ⊆
      L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₂} :=
  Set.preimage_mono (box_event_subset_when_eps_le _ h)

/-! ## standardMVGaussian on pulled-back box, monotone -/

theorem standardMVGaussian_pulled_back_box_le_box {n : Type*} [Fintype n] [DecidableEq n]
    (L : Matrix n n ℝ) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    standardMVGaussian n (L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₁}) ≤
      standardMVGaussian n (L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₂}) :=
  measure_mono (mulVec_preimage_box_subset_when_eps_le L h)

end Erdos524.Helpers
