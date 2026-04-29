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

import FormalConjectures.ErdosProblems.Helpers.CholeskyExistence
import FormalConjectures.ErdosProblems.Helpers.MVGaussianPushforward

/-!
# Phase 2 Stage 4 — Multivariate Gaussian with arbitrary PosDef covariance

Composes Stage 1 (`realMatrixSqrt M` for PosDef `M`) and Stage 3
(`mvGaussianFromMatrix L`) to produce a probability measure on `n → ℝ`
parameterised by an arbitrary PosDef matrix `M`. Its covariance equals `M`
(once a follow-up covariance lemma in `MVGaussianPushforward` lands); for
this stage we deliver the construction + probability-measure-ness.
-/

namespace Erdos524.Helpers
open MeasureTheory Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Multivariate Gaussian on `n → ℝ` with covariance matrix `M` (when `M`
is PosDef): pushforward of the standard MV Gaussian by the symmetric
square root of `M`. -/
noncomputable def mvGaussianFromPosDef (M : Matrix n n ℝ) : Measure (n → ℝ) :=
  mvGaussianFromMatrix (realMatrixSqrt M)

instance instIsProbabilityMeasureMVGaussianFromPosDef (M : Matrix n n ℝ) :
    IsProbabilityMeasure (mvGaussianFromPosDef M) := by
  unfold mvGaussianFromPosDef
  infer_instance

/-- The construction is well-defined for any input — for non-PosDef inputs
the resulting measure is still a valid probability measure (the covariance
relation may not hold, but pushforward of a probability measure is always
a probability measure). -/
theorem mvGaussianFromPosDef_apply (M : Matrix n n ℝ) :
    mvGaussianFromPosDef M = Measure.map ((realMatrixSqrt M).mulVec) (standardMVGaussian n) := rfl

end Erdos524.Helpers
