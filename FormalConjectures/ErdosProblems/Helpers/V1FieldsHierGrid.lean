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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsExtras
import FormalConjectures.ErdosProblems.Helpers.HierCauchyFacts

/-!
# Phase 2 Round 4 — hierGrid-based corollaries
-/

namespace Erdos524.Helpers
open Real

/-! ## hierGrid sums and inverse bounds -/

theorem hierGrid_sum_pos_alt (m : ℕ) (i j : Fin m × Fin m) :
    0 < hierGrid m i + hierGrid m j := hierGrid_sum_pos m i j

theorem hierGrid_sum_inv_pos (m : ℕ) (i j : Fin m × Fin m) :
    0 < (hierGrid m i + hierGrid m j)⁻¹ :=
  inv_pos.mpr (hierGrid_sum_pos m i j)

theorem hierGrid_sum_inv_eq_hierCauchyG (m : ℕ) (i j : Fin m × Fin m) :
    (hierGrid m i + hierGrid m j)⁻¹ = hierCauchyG m i j := by
  rw [hierCauchyG_apply]
  rw [one_div]

theorem hierCauchyG_eq_inv (m : ℕ) (i j : Fin m × Fin m) :
    hierCauchyG m i j = (hierGrid m i + hierGrid m j)⁻¹ := by
  rw [← hierGrid_sum_inv_eq_hierCauchyG]

end Erdos524.Helpers
