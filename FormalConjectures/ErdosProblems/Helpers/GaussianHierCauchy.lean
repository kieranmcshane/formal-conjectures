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

import FormalConjectures.ErdosProblems.Helpers.MVGaussianFromPosDef
import FormalConjectures.ErdosProblems.Helpers.GaussianGridSmallBall
import FormalConjectures.ErdosProblems.Helpers.HierCauchyFacts

/-!
# Phase 2 Stage 5 — Multivariate Gaussian with `hierCauchyG m` covariance

Specializes Stage 4's `mvGaussianFromPosDef` to the hierarchical Cauchy
matrix `hierCauchyG m`. This is the measure that the Node 6 V1 instance's
`boxProb` field will reference.

Construction is well-defined for any `m`. The PosDef status of
`hierCauchyG m` (which would make the covariance equal `hierCauchyG m`
once the Stage 3 covariance lemma lands) is a separate result derivable
from `cauchy_hierarchical_det_lower_bound` + spectral analysis; deferred.
-/

namespace Erdos524.Helpers
open MeasureTheory Matrix

/-- Multivariate Gaussian on `(Fin m × Fin m) → ℝ` with covariance
`hierCauchyG m`. -/
noncomputable def gaussianHierCauchy (m : ℕ) : Measure ((Fin m × Fin m) → ℝ) :=
  mvGaussianFromPosDef (hierCauchyG m)

instance instIsProbabilityMeasureGaussianHierCauchy (m : ℕ) :
    IsProbabilityMeasure (gaussianHierCauchy m) := by
  unfold gaussianHierCauchy
  infer_instance

theorem gaussianHierCauchy_apply (m : ℕ) :
    gaussianHierCauchy m =
      Measure.map ((realMatrixSqrt (hierCauchyG m)).mulVec)
        (standardMVGaussian (Fin m × Fin m)) := rfl

end Erdos524.Helpers
