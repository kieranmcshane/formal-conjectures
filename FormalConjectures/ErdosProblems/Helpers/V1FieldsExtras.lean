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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsFinal

/-!
# Phase 2 Round 4 — Extra V1-instance helpers

Additional V1-instance helper lemmas.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

/-! ## hierCauchyG via glwBoxProb_cov -/

theorem hierCauchyG_eq_glwBoxProb_cov (m : ℕ) :
    hierCauchyG m = glwBoxProb_cov m := rfl

theorem glwBoxProb_cov_eq_hierCauchyG (m : ℕ) :
    glwBoxProb_cov m = hierCauchyG m := rfl

/-! ## Sums of cov entries -/

theorem glwBoxProb_cov_le_one (m : ℕ) (i j : Fin m × Fin m)
    (h_sum_ge_one : 1 ≤ hierGrid m i + hierGrid m j) :
    glwBoxProb_cov m i j ≤ 1 :=
  hierCauchyG_le_one_of_hierGrid_sum_ge_one m i j h_sum_ge_one

theorem glwBoxProb_cov_pos_alt (m : ℕ) (i j : Fin m × Fin m) :
    0 < glwBoxProb_cov m i j := glwBoxProb_cov_pos m i j

/-! ## Bound interplay -/

theorem hierCauchyG_box_prob_le_one (m : ℕ) (S : Set ((Fin m × Fin m) → ℝ)) :
    gaussianHierCauchy m S ≤ 1 :=
  le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)

end Erdos524.Helpers
