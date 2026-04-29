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

import FormalConjectures.ErdosProblems.Helpers.StandardMVGaussian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Phase 2 Stage 3 — Linear pushforward of the standard multivariate Gaussian

For an `n × n` real matrix `L`, we construct
`mvGaussianFromMatrix L := Measure.map (L.mulVec) (standardMVGaussian n)`
and prove it is a probability measure.

The full covariance computation `cov(mvGaussianFromMatrix L) = L · Lᵀ` is
left to a follow-up — the immediate need from Stage 5 is the construction
itself + probability-measure-ness, which suffices to define the V1
instance's `boxProb` field.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

variable {n : Type*} [Fintype n]

/-- Pushforward of the standard MV Gaussian by a matrix-vector product. -/
noncomputable def mvGaussianFromMatrix (L : Matrix n n ℝ) : Measure (n → ℝ) :=
  Measure.map (L.mulVec) (standardMVGaussian n)

theorem mulVec_measurable (L : Matrix n n ℝ) : Measurable (L.mulVec) := by
  -- `mulVec` is a continuous linear map on a finite-dim Euclidean space.
  exact (Matrix.mulVecLin L).continuous_of_finiteDimensional.measurable

instance instIsProbabilityMeasureMVGaussianFromMatrix (L : Matrix n n ℝ) :
    IsProbabilityMeasure (mvGaussianFromMatrix L) := by
  unfold mvGaussianFromMatrix
  exact Measure.isProbabilityMeasure_map (mulVec_measurable L).aemeasurable

end Erdos524.Helpers
