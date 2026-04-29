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

import FormalConjectures.ErdosProblems.Helpers.GLWHierApprox
import FormalConjectures.ErdosProblems.Helpers.HierCauchyFacts
import FormalConjectures.ErdosProblems.Helpers.MatrixDetPerturbation

/-!
# Phase 2 Node 6 prereq — `K_GLW_matrix.det` close to `hierCauchyG.det`

Application of the entrywise determinant-perturbation lemma
(`abs_det_sub_det_le` from `MatrixDetPerturbation.lean`) to the specific
pair `(K_GLW_matrix m, hierCauchyG m)`, given the entrywise closeness
bound proved in Node 2 (`K_GLW_matrix_close_hierCauchy`).

The form here is parameterized over a uniform entrywise bound `δ`, an
entrywise norm bound `M`, and the corresponding hypotheses. Node 6 will
instantiate this at concrete `m`-dependent values of `δ` and `M` once
it picks the regime.

The two halves needed downstream (a determinant lower bound on
`K_GLW_matrix`, and the box-probability transfer) cascade from this
single bridge lemma + Node 1A's `K_GLW_le_one` and Node 2's
`K_GLW_matrix_close_hierCauchy`.
-/

namespace Erdos524.Helpers
open Real Matrix

/-- Entrywise determinant closeness: instantiation of `abs_det_sub_det_le` at
the specific matrices `K_GLW_matrix m` and `hierCauchyG m`. -/
theorem K_GLW_hierCauchy_det_close (m : ℕ) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (h_K_bd : ∀ i j, |K_GLW_matrix m i j| ≤ M)
    (h_hier_bd : ∀ i j, |hierCauchyG m i j| ≤ M)
    (h_close : ∀ i j, |K_GLW_matrix m i j - hierCauchyG m i j| ≤ δ) :
    |(K_GLW_matrix m).det - (hierCauchyG m).det| ≤
      (Fintype.card (Fin m × Fin m)) *
        (Fintype.card (Fin m × Fin m)).factorial *
        δ *
        M ^ ((Fintype.card (Fin m × Fin m)) - 1) :=
  abs_det_sub_det_le (K_GLW_matrix m) (hierCauchyG m) M δ
    hM hδ h_K_bd h_hier_bd h_close

/-- Pre-specialised entrywise norm bound for `K_GLW_matrix m`: every entry is
in `[0, 1]`, so `|K_GLW_matrix m i j| ≤ 1`. -/
theorem K_GLW_matrix_abs_le_one (m : ℕ) (i j : Fin m × Fin m) :
    |K_GLW_matrix m i j| ≤ 1 := by
  have h_pos : 0 < K_GLW_matrix m i j := K_GLW_matrix_pos m i j
  have h_le : K_GLW_matrix m i j ≤ 1 := K_GLW_matrix_le_one m i j
  rw [abs_of_pos h_pos]
  exact h_le

/-- Pre-specialised entrywise norm bound for `hierCauchyG m` under the
diagonal-sum-≥-1 hypothesis: every entry is in `(0, 1]`, so absolute value ≤ 1. -/
theorem hierCauchyG_abs_le_one_of_hierGrid_sum_ge_one (m : ℕ)
    (h_sum_ge_one : ∀ i j, 1 ≤ hierGrid m i + hierGrid m j) (i j : Fin m × Fin m) :
    |hierCauchyG m i j| ≤ 1 := by
  have h_pos : 0 < hierCauchyG m i j := hierCauchyG_pos m i j
  have h_le : hierCauchyG m i j ≤ 1 :=
    hierCauchyG_le_one_of_hierGrid_sum_ge_one m i j (h_sum_ge_one i j)
  rw [abs_of_pos h_pos]
  exact h_le

/-- Convenience corollary using `M = 1`: when both matrices have entries in
`[0, 1]` (which holds for `K_GLW_matrix m` always and for `hierCauchyG m` on
the diagonal-sum-≥-1 region), the determinant difference is bounded by
`(m²)·(m²)! · δ`. -/
theorem K_GLW_hierCauchy_det_close_unit_M (m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h_sum_ge_one : ∀ i j, 1 ≤ hierGrid m i + hierGrid m j)
    (h_close : ∀ i j, |K_GLW_matrix m i j - hierCauchyG m i j| ≤ δ) :
    |(K_GLW_matrix m).det - (hierCauchyG m).det| ≤
      (Fintype.card (Fin m × Fin m)) *
        (Fintype.card (Fin m × Fin m)).factorial *
        δ *
        (1 : ℝ) ^ ((Fintype.card (Fin m × Fin m)) - 1) :=
  K_GLW_hierCauchy_det_close m 1 δ (by norm_num) hδ
    (K_GLW_matrix_abs_le_one m)
    (hierCauchyG_abs_le_one_of_hierGrid_sum_ge_one m h_sum_ge_one) h_close

end Erdos524.Helpers
