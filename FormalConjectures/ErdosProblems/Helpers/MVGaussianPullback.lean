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

import FormalConjectures.ErdosProblems.Helpers.MVGaussianPushforward
import FormalConjectures.ErdosProblems.Helpers.StandardMVGaussianBox

/-!
# Phase 2 Round 4 — Pullback of `mvGaussianFromMatrix` events

For a matrix `L : Matrix n n ℝ`, the pushforward measure
`mvGaussianFromMatrix L = Measure.map (L.mulVec) (standardMVGaussian n)`
satisfies, for every measurable `S ⊆ (n → ℝ)`,
  `(mvGaussianFromMatrix L) S = (standardMVGaussian n) (L.mulVec ⁻¹' S)`.

This is a direct application of `Measure.map_apply` once we know that
`L.mulVec` is measurable (proved in Stage 3).

We use this pullback identity to express the box probability under
`mvGaussianFromMatrix L` as a probability under the standard MV Gaussian
of the inverse-image set, which is a key step toward Anderson-upper for
the general PosDef-covariance case.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Pullback identity for measurable sets -/

theorem mvGaussianFromMatrix_apply_eq_standard_pullback
    (L : Matrix n n ℝ) (S : Set (n → ℝ)) (hS : MeasurableSet S) :
    mvGaussianFromMatrix L S = standardMVGaussian n (L.mulVec ⁻¹' S) := by
  unfold mvGaussianFromMatrix
  rw [Measure.map_apply (mulVec_measurable L) hS]

/-- The box event `{y | ∀ i, |y i| ≤ ε}` is measurable. -/
theorem box_event_measurable (n : Type*) [Fintype n] (ε : ℝ) :
    MeasurableSet ({y : n → ℝ | ∀ i, |y i| ≤ ε}) := by
  rw [box_event_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-! ## Box event under the pushforward -/

/-- Box probability under `mvGaussianFromMatrix L` equals box probability under
the standard MV Gaussian of the pulled-back set. -/
theorem mvGaussianFromMatrix_box_eq_pullback (L : Matrix n n ℝ) (ε : ℝ) :
    mvGaussianFromMatrix L {y : n → ℝ | ∀ i, |y i| ≤ ε} =
      standardMVGaussian n (L.mulVec ⁻¹' {y : n → ℝ | ∀ i, |y i| ≤ ε}) :=
  mvGaussianFromMatrix_apply_eq_standard_pullback L _ (box_event_measurable n ε)

/-! ## Concrete corollary: measurable .toReal box probability inequality

The box probability under any pushforward `mvGaussianFromMatrix L` is upper-
bounded by the standard MV Gaussian's measure of the pulled-back set; this
trivially holds (equality), but we expose the `.toReal` form. -/

theorem mvGaussianFromMatrix_box_toReal_eq_pullback (L : Matrix n n ℝ) (ε : ℝ) :
    (mvGaussianFromMatrix L {y : n → ℝ | ∀ i, |y i| ≤ ε}).toReal =
      (standardMVGaussian n (L.mulVec ⁻¹' {y : n → ℝ | ∀ i, |y i| ≤ ε})).toReal := by
  rw [mvGaussianFromMatrix_box_eq_pullback]

/-! ## Symmetry of box: |y_i| ≤ ε iff y_i ∈ Icc (-ε) ε -/

theorem box_event_set_iff (ε : ℝ) (y : n → ℝ) :
    y ∈ ({y : n → ℝ | ∀ i, |y i| ≤ ε}) ↔ ∀ i, y i ∈ Set.Icc (-ε) ε := by
  simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]

/-- Pulled-back box is preimage of a Cartesian product. -/
theorem mulVec_preimage_box_subset_univ (L : Matrix n n ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    L.mulVec ⁻¹' {y : n → ℝ | ∀ i, |y i| ≤ ε} ⊆ Set.univ := Set.subset_univ _

theorem mulVec_preimage_box_measurable (L : Matrix n n ℝ) (ε : ℝ) :
    MeasurableSet (L.mulVec ⁻¹' {y : n → ℝ | ∀ i, |y i| ≤ ε}) := by
  exact (mulVec_measurable L) (box_event_measurable n ε)

end Erdos524.Helpers
