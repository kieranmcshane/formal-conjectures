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

import FormalConjectures.ErdosProblems.Helpers.GaussianHierCauchy
import FormalConjectures.ErdosProblems.Helpers.MVGaussianPullback
import FormalConjectures.ErdosProblems.Helpers.GaussianBoxBounds
import FormalConjectures.ErdosProblems.Helpers.GLWBoxProbInstance
import FormalConjectures.ErdosProblems.Helpers.MVGaussianDensityBound
import FormalConjectures.ErdosProblems.Helpers.HierCauchyPosDef

/-!
# Phase 2 Round 4 — Box-probability bounds for `gaussianHierCauchy`

Combines the Stage 1-5 multivariate-Gaussian framework + Round 4
PDF / pullback / standard-MV-box bounds into:

* `glwBoxProb_eq_pullback_standardMV` — explicit pullback formula for
  the V1 candidate `boxProb`;
* `glwBoxProb_le_one_via_pullback` — alternate proof of the trivial
  probability bound via the pullback identity (sanity check that the
  Stage 4-6 chain composes correctly);
* measurability and probability-bound corollaries used by the Node 6 V1
  instance's `boxProb_sub` and Anderson_upper-style fields.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix Real

/-! ## Pullback formula -/

/-- The candidate V1 `boxProb` for `gaussianHierCauchy m` equals the standard
multivariate Gaussian's measure of the pulled-back box (`mulVec L⁻¹' box`). -/
theorem glwBoxProb_eq_pullback_standardMV (m : ℕ) (ε : ℝ) :
    glwBoxProb m ε =
      (standardMVGaussian (Fin m × Fin m)
        ((realMatrixSqrt (hierCauchyG m)).mulVec ⁻¹'
          {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε})).toReal := by
  unfold glwBoxProb gaussianHierCauchy mvGaussianFromPosDef mvGaussianFromMatrix
  rw [Measure.map_apply (mulVec_measurable _) (box_event_measurable _ ε)]

/-! ## Probability bound through the pullback -/

/-- Sanity check: the V1 candidate boxProb is at most 1 via the pullback chain. -/
theorem glwBoxProb_le_one_via_pullback (m : ℕ) (ε : ℝ) : glwBoxProb m ε ≤ 1 := by
  rw [glwBoxProb_eq_pullback_standardMV]
  exact standardMVGaussian_le_one (Fin m × Fin m) _

/-! ## Nonnegativity through the pullback -/

theorem glwBoxProb_nonneg_via_pullback (m : ℕ) (ε : ℝ) : 0 ≤ glwBoxProb m ε := by
  rw [glwBoxProb_eq_pullback_standardMV]
  exact ENNReal.toReal_nonneg

/-! ## Box-event measurability under the pullback -/

theorem mulVec_realMatrixSqrt_preimage_box_measurable (m : ℕ) (ε : ℝ) :
    MeasurableSet
      ((realMatrixSqrt (hierCauchyG m)).mulVec ⁻¹'
        {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε}) :=
  (mulVec_measurable _) (box_event_measurable _ ε)

/-! ## Monotonicity in ε for the V1 boxProb -/

theorem glwBoxProb_mono (m : ℕ) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    glwBoxProb m ε₁ ≤ glwBoxProb m ε₂ := by
  rw [glwBoxProb, glwBoxProb]
  apply ENNReal.toReal_mono
  · -- gaussianHierCauchy m {x | ∀ ij, |x ij| ≤ ε₂} ≠ ⊤
    have h_le :
        gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε₂} ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
  · exact measure_mono (box_event_mono (Fin m × Fin m) hε)

/-! ## Subset bound: glwBoxProb ε ≤ glwBoxProb (ε + δ) for δ ≥ 0 -/

theorem glwBoxProb_le_of_le {m : ℕ} {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    glwBoxProb m ε₁ ≤ glwBoxProb m ε₂ := glwBoxProb_mono m hε

/-! ## Empty box: glwBoxProb m 0 ≤ 1 trivially -/

theorem glwBoxProb_zero_le_one (m : ℕ) : glwBoxProb m 0 ≤ 1 :=
  glwBoxProb_le_one_via_pullback m 0

/-! ## Finite ENNReal: gaussianHierCauchy box ≠ ⊤ -/

theorem gaussianHierCauchy_box_finite (m : ℕ) (ε : ℝ) :
    gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε} ≠ ⊤ := by
  have h_le :
      gaussianHierCauchy m {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε} ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
  exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)

/-! ## Pulled-back-box probability bound: trivial 1 -/

theorem standard_pullback_box_le_one (m : ℕ) (ε : ℝ) :
    (standardMVGaussian (Fin m × Fin m)
      ((realMatrixSqrt (hierCauchyG m)).mulVec ⁻¹'
        {x : Fin m × Fin m → ℝ | ∀ ij, |x ij| ≤ ε})).toReal ≤ 1 :=
  standardMVGaussian_le_one (Fin m × Fin m) _

/-! ## Round 9 — Anderson upper bound for `glwBoxProb`, conditional on
`hierCauchyG.PosDef`

If `(hierCauchyG m).PosDef` holds (a separate spectral / Cauchy-matrix
PosDef result, currently a Mathlib gap), then Round 9's
`mvGaussian_isotropic_box_density_at_mode_bound_rpow` yields the V1
instance's `anderson_upper`-shaped bound for `glwBoxProb`. Records the
exact dependency. -/

theorem glwBoxProb_anderson_upper_via_round9 {m : ℕ}
    (hPosDef : (hierCauchyG m).PosDef) {ε : ℝ} (hε : 0 ≤ ε) :
    glwBoxProb m ε ≤
      (2 * ε) ^ (Fintype.card (Fin m × Fin m)) *
        (2 * Real.pi) ^ (-((Fintype.card (Fin m × Fin m) : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG m).det)⁻¹ := by
  unfold glwBoxProb gaussianHierCauchy
  exact mvGaussian_isotropic_box_density_at_mode_bound_rpow hPosDef hε

/-- V1-instance-shaped form: `Fintype.card (Fin m × Fin m) = m * m`. -/
theorem glwBoxProb_anderson_upper_via_round9_mm {m : ℕ}
    (hPosDef : (hierCauchyG m).PosDef) {ε : ℝ} (hε : 0 ≤ ε) :
    glwBoxProb m ε ≤
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG m).det)⁻¹ := by
  have h := glwBoxProb_anderson_upper_via_round9 hPosDef hε
  rwa [show Fintype.card (Fin m × Fin m) = m * m from by
        rw [Fintype.card_prod, Fintype.card_fin]] at h

/-! ## Round 10 — Unconditional Anderson upper bound (Stretch A)

After Round 10 closed `(hierCauchyG m).PosDef` for `m ≥ 1`, the
`glwBoxProb_anderson_upper_via_round9_mm` conditional becomes
unconditional: feed in `hierCauchyG_PosDef`. -/

/-- Unconditional Anderson upper bound for `glwBoxProb`, valid for `m ≥ 1`.
This is the V1-instance-shaped `anderson_upper` field. -/
theorem glwBoxProb_anderson_upper_unconditional {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 ≤ ε) :
    glwBoxProb m ε ≤
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG m).det)⁻¹ :=
  glwBoxProb_anderson_upper_via_round9_mm (hierCauchyG_PosDef m hm) hε

/-- Unconditional Anderson upper bound for `glwBoxProb`, V1 contract form
(uses `0 < ε` rather than `0 ≤ ε`). -/
theorem glwBoxProb_anderson_upper_v1 {m : ℕ} (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    glwBoxProb m ε ≤
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG m).det)⁻¹ :=
  glwBoxProb_anderson_upper_unconditional hm hε.le

end Erdos524.Helpers
