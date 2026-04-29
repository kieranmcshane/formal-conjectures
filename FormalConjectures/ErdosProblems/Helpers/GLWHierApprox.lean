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

import FormalConjectures.ErdosProblems.Helpers.GLWKernel
import FormalConjectures.ErdosProblems.Helpers.GaussianGridSmallBall

/-!
# Phase 2 / Node 2 — Hierarchical-Cauchy approximation of the GLW covariance

We sample the (hypothetical) GLW process `Y_GLW` at the hierarchical times
`hierGrid m`, producing the discrete `m × m` covariance matrix

  `K_GLW_matrix m i j := K_GLW (hierGrid m i) (hierGrid m j)`,

and compare it entrywise to `hierCauchyG m i j = 1 / (hierGrid m i + hierGrid m j)`.
The comparison is the core lemma `K_GLW_matrix_close_hierCauchy`, which says
the entrywise discrepancy is bounded by `exp(-(g_i+g_j))/(g_i+g_j)`.

## Why this matters for Node 6

The Node 3 helper (`GaussianGridSmallBall.lean`) consumes a `GaussianBoxProb m`
whose `cov` is **literally** `hierCauchyG m` (via `cov_eq_hierCauchy`). The true
covariance of `Y_GLW` sampled at `hierGrid m` is `K_GLW_matrix m`, not
`hierCauchyG m` — so Node 6 needs the discrepancy bound to transfer the
helper's `boxProb` claims back to the GLW context.

Pure linear-algebra / analysis content; no probability hypotheses are used.
The `Y_GLW` process itself is referenced only in the docstring — Node 1B's
stepping-stone axiom is **not** imported by this file.
-/

namespace Erdos524.Helpers
open Real

/-! ## Sample times and discrete covariance matrix -/

/-- Hierarchical sample times for the GLW process. Identifies with the
hierarchical Cauchy grid points so that
`hierCauchyG m i j = 1 / (hierTimes m i + hierTimes m j)` holds definitionally. -/
noncomputable def hierTimes (m : ℕ) : Fin m × Fin m → ℝ := hierGrid m

theorem hierTimes_pos (m : ℕ) (ij : Fin m × Fin m) : 0 < hierTimes m ij := by
  unfold hierTimes
  exact hierGrid_pos m ij

theorem hierTimes_sum_pos (m : ℕ) (i j : Fin m × Fin m) :
    0 < hierTimes m i + hierTimes m j := by
  unfold hierTimes
  exact hierGrid_sum_pos m i j

/-- The discrete GLW covariance matrix at the hierarchical sample times.
Entry `(i, j)` equals `K_GLW (hierTimes m i) (hierTimes m j)`. -/
noncomputable def K_GLW_matrix (m : ℕ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  Matrix.of fun i j => K_GLW (hierTimes m i) (hierTimes m j)

theorem K_GLW_matrix_apply (m : ℕ) (i j : Fin m × Fin m) :
    K_GLW_matrix m i j = K_GLW (hierTimes m i) (hierTimes m j) := rfl

theorem K_GLW_matrix_symm (m : ℕ) (i j : Fin m × Fin m) :
    K_GLW_matrix m i j = K_GLW_matrix m j i := by
  rw [K_GLW_matrix_apply, K_GLW_matrix_apply, K_GLW_symm]

/-! ## Entrywise positivity and unit upper bound -/

theorem K_GLW_matrix_pos (m : ℕ) (i j : Fin m × Fin m) :
    0 < K_GLW_matrix m i j := by
  rw [K_GLW_matrix_apply]
  exact K_GLW_pos _ _ (le_of_lt (hierTimes_pos m i)) (le_of_lt (hierTimes_pos m j))

theorem K_GLW_matrix_le_one (m : ℕ) (i j : Fin m × Fin m) :
    K_GLW_matrix m i j ≤ 1 := by
  rw [K_GLW_matrix_apply]
  exact K_GLW_le_one _ _ (le_of_lt (hierTimes_pos m i)) (le_of_lt (hierTimes_pos m j))

/-! ## Entrywise comparison to the hierarchical Cauchy matrix

This is the headline lemma of Node 2 — it powers the Node 6 transfer of
`gaussian_grid_smallball_*_final` bounds back into the GLW box-probability
statement. -/

theorem K_GLW_matrix_close_hierCauchy (m : ℕ) (_hm : 1 ≤ m) (i j : Fin m × Fin m) :
    |K_GLW_matrix m i j - hierCauchyG m i j| ≤
      Real.exp (-(hierGrid m i + hierGrid m j)) / (hierGrid m i + hierGrid m j) := by
  rw [K_GLW_matrix_apply]
  -- `hierCauchyG m i j` reduces to `1 / (hierGrid m i + hierGrid m j)` via its
  -- definition; `hierTimes m = hierGrid m` by definition. So the LHS is
  -- `|K_GLW (hierGrid m i) (hierGrid m j) - 1 / (hierGrid m i + hierGrid m j)|`
  -- and the result is exactly `K_GLW_cauchy_asymptotic`.
  show |K_GLW (hierGrid m i) (hierGrid m j) - hierCauchyG m i j| ≤
       Real.exp (-(hierGrid m i + hierGrid m j)) / (hierGrid m i + hierGrid m j)
  have h_hier : hierCauchyG m i j = 1 / (hierGrid m i + hierGrid m j) := by
    unfold hierCauchyG
    simp [Matrix.of_apply]
  rw [h_hier]
  exact K_GLW_cauchy_asymptotic (hierGrid m i) (hierGrid m j) (hierGrid_sum_pos m i j)

/-- Restated with the convenient absolute-value-symmetry form. -/
theorem hierCauchy_close_K_GLW_matrix (m : ℕ) (hm : 1 ≤ m) (i j : Fin m × Fin m) :
    |hierCauchyG m i j - K_GLW_matrix m i j| ≤
      Real.exp (-(hierGrid m i + hierGrid m j)) / (hierGrid m i + hierGrid m j) := by
  rw [abs_sub_comm]
  exact K_GLW_matrix_close_hierCauchy m hm i j

end Erdos524.Helpers
