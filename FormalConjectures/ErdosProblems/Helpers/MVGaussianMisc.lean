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
import FormalConjectures.ErdosProblems.Helpers.MVGaussianScalar

/-!
# Phase 2 Round 4 — Miscellaneous multivariate Gaussian utilities

A grab-bag of small utility lemmas about the multivariate Gaussian pieces
shipped this round, useful for the V1 instance bookkeeping.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Pushforward by zero matrix

`Matrix.mulVec 0 x = 0` for all x. So `mvGaussianFromMatrix 0` is the
Dirac measure at 0. Useful as a degenerate edge case. -/

theorem zero_mulVec_eq (x : n → ℝ) : (0 : Matrix n n ℝ).mulVec x = 0 := by
  simp [Matrix.zero_mulVec]

theorem zero_mulVec_eq_const : ((0 : Matrix n n ℝ).mulVec) = (0 : (n → ℝ) → (n → ℝ)) := by
  funext x
  exact zero_mulVec_eq x

/-! ## Box-event nonemptiness for ε ≥ 0

The symmetric box `{x | ∀ i, |x i| ≤ ε}` is nonempty when ε ≥ 0
(it contains the zero vector). -/

theorem box_event_nonempty_of_nonneg (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    Set.Nonempty {x : n → ℝ | ∀ i, |x i| ≤ ε} := by
  refine ⟨0, ?_⟩
  intro i
  simp [hε]

theorem zero_mem_box_event (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (0 : n → ℝ) ∈ {x : n → ℝ | ∀ i, |x i| ≤ ε} := by
  intro i; simp [hε]

/-! ## Pulled-back box always contains zero -/

theorem zero_mem_mulVec_preimage_box
    (L : Matrix n n ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    (0 : n → ℝ) ∈ L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε} := by
  rw [Set.mem_preimage, Matrix.mulVec_zero]
  intro i
  rw [Pi.zero_apply, abs_zero]
  exact hε

/-! ## Pulled-back-box monotonicity in ε -/

theorem mulVec_preimage_box_mono
    (L : Matrix n n ℝ) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₁} ⊆
      L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₂} :=
  Set.preimage_mono (box_event_mono n hε)

/-! ## Convenience lemma: standardMVGaussian and pulled-back monotonicity -/

theorem standardMVGaussian_pulled_back_box_mono
    (L : Matrix n n ℝ) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    standardMVGaussian n (L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₁}) ≤
      standardMVGaussian n (L.mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε₂}) :=
  measure_mono (mulVec_preimage_box_mono L hε)

/-! ## Scaling factor for `c • 1` matrix's pulled-back box probability -/

theorem standardMVGaussian_scaled_box_le_div
    (n : Type*) [Fintype n] (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε / c}).toReal ≤
      (2 * ε) ^ Fintype.card n / c ^ Fintype.card n *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  have h := standardMVGaussian_box_le n (ε / c) (div_nonneg hε (le_of_lt hc))
  have h_eq : (2 * (ε / c)) ^ Fintype.card n =
              (2 * ε) ^ Fintype.card n / c ^ Fintype.card n := by
    rw [show (2 * (ε / c)) = (2 * ε) / c from by ring, div_pow]
  rw [h_eq] at h
  exact h

end Erdos524.Helpers
