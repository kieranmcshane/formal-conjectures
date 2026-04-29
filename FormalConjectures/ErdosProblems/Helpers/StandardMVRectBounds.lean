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

import FormalConjectures.ErdosProblems.Helpers.StandardMVGaussianBox
import FormalConjectures.ErdosProblems.Helpers.GaussianBoxBounds

/-!
# Phase 2 Round 4 — Standard MV Gaussian rectangle bounds

Generalised box-probability bounds: the standard MV Gaussian over an
asymmetric rectangle `∏ Icc a_i b_i` satisfies
`P(rect) = ∏ gaussianReal 0 1 (Icc a_i b_i)`,
each factor ≤ `(b_i - a_i) · (√(2π))⁻¹` (provided `a_i ≤ b_i`).

Useful for the Node 6 V1 instance's `boxProb_sub` field, which restricts to
sub-grid coordinates and an asymmetric box.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ## Asymmetric rectangle event -/

/-- Asymmetric rectangle in `n → ℝ` with per-coordinate `Icc (a i) (b i)`. -/
def rectEvent (n : Type*) [Fintype n] (a b : n → ℝ) : Set (n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (a i) (b i))

theorem rectEvent_measurable (n : Type*) [Fintype n] (a b : n → ℝ) :
    MeasurableSet (rectEvent n a b) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-! ## Box event is a special case of rect -/

theorem box_event_eq_rect (n : Type*) [Fintype n] (ε : ℝ) :
    {x : n → ℝ | ∀ i, |x i| ≤ ε} = rectEvent n (fun _ => -ε) (fun _ => ε) := by
  rw [box_event_eq_pi]; rfl

/-! ## Standard MV Gaussian on a rectangle factorises -/

theorem standardMVGaussian_rect_eq_prod (n : Type*) [Fintype n] (a b : n → ℝ) :
    standardMVGaussian n (rectEvent n a b) =
      ∏ i : n, gaussianReal 0 1 (Set.Icc (a i) (b i)) := by
  unfold standardMVGaussian rectEvent
  exact Measure.pi_pi (fun _ => gaussianReal 0 1) _

/-! ## Per-coordinate rectangle bound -/

theorem gaussianReal_Icc_le_general (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1 (Set.Icc a b)).toReal ≤ (b - a) * (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [gaussianReal_apply_eq_integral _ one_ne_zero]
  rw [ENNReal.toReal_ofReal]
  · have h_le := setIntegral_gaussianPDFReal_le 0 1 a b hab
    have h_simp : Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) = Real.sqrt (2 * Real.pi) := by
      have h_one : ((1 : ℝ≥0) : ℝ) = 1 := by simp
      rw [h_one, mul_one]
    rw [h_simp] at h_le
    exact h_le
  · apply integral_nonneg
    intro x
    exact gaussianPDFReal_nonneg _ _ _

/-! ## Standard MV Gaussian rectangle bound -/

theorem standardMVGaussian_rect_le (n : Type*) [Fintype n] (a b : n → ℝ)
    (hab : ∀ i, a i ≤ b i) :
    (standardMVGaussian n (rectEvent n a b)).toReal ≤
      ∏ i : n, ((b i - a i) * (Real.sqrt (2 * Real.pi))⁻¹) := by
  -- Factor into product of 1-D measures.
  rw [standardMVGaussian_rect_eq_prod]
  -- Per-coordinate finiteness for ENNReal product → real product conversion.
  have h_finite : ∀ i : n, gaussianReal 0 1 (Set.Icc (a i) (b i)) ≠ ⊤ := by
    intro i
    have h_le : gaussianReal 0 1 (Set.Icc (a i) (b i)) ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
  rw [ENNReal.toReal_prod]
  -- Per-coordinate bound.
  apply Finset.prod_le_prod
  · exact fun i _ => ENNReal.toReal_nonneg
  · intro i _
    exact gaussianReal_Icc_le_general (a i) (b i) (hab i)

/-! ## Symmetric box recovered from rect bound -/

theorem standardMVGaussian_box_le_via_rect (n : Type*) [Fintype n] (ε : ℝ) (hε : 0 ≤ ε) :
    (standardMVGaussian n (rectEvent n (fun _ => -ε) (fun _ => ε))).toReal ≤
      ∏ _ : n, (2 * ε * (Real.sqrt (2 * Real.pi))⁻¹) := by
  have h := standardMVGaussian_rect_le n (fun _ => -ε) (fun _ => ε)
    (fun _ => by linarith)
  refine h.trans ?_
  apply le_of_eq
  apply Finset.prod_congr rfl
  intro i _
  show (ε - -ε) * (Real.sqrt (2 * Real.pi))⁻¹ = 2 * ε * (Real.sqrt (2 * Real.pi))⁻¹
  ring

/-! ## Subset of box from rect monotonicity -/

theorem rect_subset_of_componentwise (n : Type*) [Fintype n] {a₁ b₁ a₂ b₂ : n → ℝ}
    (ha : ∀ i, a₂ i ≤ a₁ i) (hb : ∀ i, b₁ i ≤ b₂ i) :
    rectEvent n a₁ b₁ ⊆ rectEvent n a₂ b₂ := by
  intro x hx i hi
  exact ⟨(ha i).trans (hx i hi).1, (hx i hi).2.trans (hb i)⟩

end Erdos524.Helpers
