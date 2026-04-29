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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsCorollary

/-!
# Phase 2 Round 4 — Final V1-instance lemmas

A few very small concluding lemmas tying off the round.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

/-! ## glwBoxProb_cov reduction -/

theorem glwBoxProb_cov_apply (m : ℕ) (i j : Fin m × Fin m) :
    glwBoxProb_cov m i j = 1 / (hierGrid m i + hierGrid m j) := by
  unfold glwBoxProb_cov
  exact hierCauchyG_apply m i j

theorem glwBoxProb_cov_pos (m : ℕ) (i j : Fin m × Fin m) :
    0 < glwBoxProb_cov m i j := hierCauchyG_pos m i j

theorem glwBoxProb_cov_apply_zero_sum (m : ℕ) (i j : Fin m × Fin m) :
    0 < glwBoxProb_cov m i j + glwBoxProb_cov m j i := by
  rw [glwBoxProb_cov_symm m i j]
  exact add_pos (glwBoxProb_cov_pos m j i) (glwBoxProb_cov_pos m j i)

end Erdos524.Helpers
