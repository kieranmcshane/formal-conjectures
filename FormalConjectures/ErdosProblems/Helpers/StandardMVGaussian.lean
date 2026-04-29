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

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Phase 2 Stage 2 — Standard multivariate Gaussian on `n → ℝ`

The product measure of `n` independent `N(0, 1)` factors. Used by Stage 4
as the source measure pushed forward by `Matrix.mulVec L` (where `L` is
the Cholesky factor of the target covariance).
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory

variable (n : Type*) [Fintype n]

/-- Standard multivariate Gaussian on `n → ℝ`: the product of `n` independent
`gaussianReal 0 1` distributions. -/
noncomputable def standardMVGaussian : Measure (n → ℝ) :=
  Measure.pi (fun _ : n => gaussianReal 0 1)

/-- The standard multivariate Gaussian is a probability measure. -/
instance instIsProbabilityMeasureStandardMVGaussian :
    IsProbabilityMeasure (standardMVGaussian n) := by
  unfold standardMVGaussian
  infer_instance

end Erdos524.Helpers
