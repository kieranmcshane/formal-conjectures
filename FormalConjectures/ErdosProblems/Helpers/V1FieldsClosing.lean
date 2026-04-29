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
import FormalConjectures.ErdosProblems.Helpers.V1FieldsBoxRel
import FormalConjectures.ErdosProblems.Helpers.V1FieldsCardEval
import FormalConjectures.ErdosProblems.Helpers.MVGaussianRpowChain

/-!
# Phase 2 Round 4 — V1-instance closing lemmas

Closing lemmas combining the V1FieldsAux + V1FieldsBoxRel + V1FieldsCardEval
chains. These are the "almost-complete" Anderson-upper-style statements
expressed in the precise V1 instance contract shape.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix Real

/-! ## Combined Anderson-upper for the identity covariance V1 instance

For the trivial identity covariance, the Anderson-upper bound holds in
the exact V1 contract shape. Useful as a sanity-check that the framework
landed correctly. -/

theorem mvGaussianFromMatrix_one_box_le_v1_form
    {m : Type*} [Fintype m] [DecidableEq m] (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (1 : Matrix m m ℝ)
        {x : m → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card m *
        (2 * Real.pi) ^ (-(Fintype.card m : ℝ) / 2) *
        (Real.sqrt ((1 : Matrix m m ℝ).det))⁻¹ :=
  anderson_upper_v1_form_for_identity m ε hε

/-! ## Combined Anderson-upper for the scalar covariance V1 instance -/

theorem mvGaussianFromMatrix_smul_one_box_le_v1_form
    {m : Type*} [Fintype m] [DecidableEq m] (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (c • (1 : Matrix m m ℝ))
        {x : m → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * (ε / c)) ^ Fintype.card m *
        (2 * Real.pi) ^ (-(Fintype.card m : ℝ) / 2) :=
  mvGaussianFromMatrix_smul_one_box_le_rpow m c hc ε hε

/-! ## Combined Anderson-lower-style placeholders (to be tightened) -/

/-- Trivially `boxProb ≥ 0` (V1 anderson_lower's lower bound is at least 0). -/
theorem v1_anderson_lower_trivial (m : ℕ) (ε : ℝ) :
    (0 : ℝ) ≤ glwBoxProb m ε := glwBoxProb_nonneg_via_pullback m ε

/-! ## Closing identity: V1 candidate cov_det_pos is consistent -/

theorem glwBoxProb_cov_det_pos_alt (m : ℕ) (hm : 1 ≤ m) :
    0 < (glwBoxProb_cov m).det := glwBoxProb_cov_det_pos m hm

/-! ## Closing identity: glwBoxProb_cov is symmetric -/

theorem glwBoxProb_cov_symm (m : ℕ) (i j : Fin m × Fin m) :
    glwBoxProb_cov m i j = glwBoxProb_cov m j i := hierCauchyG_symm m i j

end Erdos524.Helpers
