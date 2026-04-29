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
import FormalConjectures.ErdosProblems.Helpers.MVGaussianFromPosDef
import FormalConjectures.ErdosProblems.Helpers.StandardMVDensityBound

/-!
# Phase 2 Round 4 — Identity-pushforward sanity lemmas

Lemmas verifying `mvGaussianFromMatrix 1 = standardMVGaussian` (where
`1 : Matrix n n ℝ` is the identity matrix). This is the trivial-Cholesky
specialisation of Stage 3, useful as a sanity-check that the
Cholesky→pushforward→standard-MV chain composes correctly when
`M = 1` (the identity covariance case).
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Identity matrix pushforward -/

theorem one_mulVec_apply (x : n → ℝ) : (1 : Matrix n n ℝ).mulVec x = x :=
  Matrix.one_mulVec x

/-- The identity matrix's `mulVec` is the identity function. -/
theorem one_mulVec_eq_id : (1 : Matrix n n ℝ).mulVec = id := by
  funext x
  exact one_mulVec_apply x

/-- Pushforward by identity is the source measure. -/
theorem mvGaussianFromMatrix_one_eq :
    mvGaussianFromMatrix (1 : Matrix n n ℝ) = standardMVGaussian n := by
  unfold mvGaussianFromMatrix
  rw [one_mulVec_eq_id, Measure.map_id]

/-! ## Box-probability for identity-pushforward -/

theorem mvGaussianFromMatrix_one_box_eq (ε : ℝ) :
    mvGaussianFromMatrix (1 : Matrix n n ℝ)
        {x : n → ℝ | ∀ i, |x i| ≤ ε} =
      standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε} := by
  rw [mvGaussianFromMatrix_one_eq]

theorem mvGaussianFromMatrix_one_box_le (ε : ℝ) (hε : 0 ≤ ε) :
    (mvGaussianFromMatrix (1 : Matrix n n ℝ)
        {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card n * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  rw [mvGaussianFromMatrix_one_box_eq]
  exact standardMVGaussian_box_le n ε hε

/-! ## Pullback identity for the identity matrix -/

theorem mvGaussianFromMatrix_one_apply (S : Set (n → ℝ)) (hS : MeasurableSet S) :
    mvGaussianFromMatrix (1 : Matrix n n ℝ) S = standardMVGaussian n S := by
  rw [mvGaussianFromMatrix_one_eq]

/-! ## Pullback structure: `1.mulVec ⁻¹' S = S` -/

theorem one_mulVec_preimage (S : Set (n → ℝ)) :
    (1 : Matrix n n ℝ).mulVec ⁻¹' S = S := by
  ext x
  simp [Set.mem_preimage, one_mulVec_apply]

/-! ## Connecting glwBoxProb at "covariance = 1"

If we instantiated `glwBoxProb` at the matrix `1` (which is PosDef but isn't
`hierCauchyG m`), the Anderson-upper would follow trivially from
`mvGaussianFromMatrix_one_box_le`. The actual `hierCauchyG m` case needs the
Cholesky pushforward of a non-trivial matrix, which has a different shape.
-/

theorem mvGaussianFromPosDef_one_eq :
    (mvGaussianFromPosDef (1 : Matrix n n ℝ)) = standardMVGaussian n := by
  unfold mvGaussianFromPosDef
  rw [show realMatrixSqrt (1 : Matrix n n ℝ) = (1 : Matrix n n ℝ) from ?_]
  · exact mvGaussianFromMatrix_one_eq
  · -- realMatrixSqrt 1 = 1 (square root of identity is identity).
    unfold realMatrixSqrt
    -- CFC.sqrt 1 = 1 since 1² = 1.
    exact CFC.sqrt_one

end Erdos524.Helpers
