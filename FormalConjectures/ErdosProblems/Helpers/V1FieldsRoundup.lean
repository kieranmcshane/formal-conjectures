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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsHierGrid

/-!
# Phase 2 Round 4 — Final V1 round-up

Last few wrap-up lemmas of Round 4.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix

theorem glwBoxProb_cov_apply_alt (m : ℕ) (i j : Fin m × Fin m) :
    glwBoxProb_cov m i j = (hierGrid m i + hierGrid m j)⁻¹ := by
  rw [glwBoxProb_cov_apply, one_div]

theorem hierCauchyG_eq_glwBoxProb_cov_alt (m : ℕ) :
    hierCauchyG m = glwBoxProb_cov m := rfl

end Erdos524.Helpers
