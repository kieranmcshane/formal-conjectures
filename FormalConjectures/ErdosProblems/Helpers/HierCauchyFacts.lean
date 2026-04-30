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

import FormalConjectures.ErdosProblems.Helpers.CauchyDetLowerBound
import FormalConjectures.ErdosProblems.Helpers.GaussianGridSmallBall

/-!
# Phase 2 prerequisites — facts about the hierarchical Cauchy matrix

Self-contained facts about `hierCauchyG m` (defined in
`GaussianGridSmallBall.lean`) that the future Node 6 V1 instance constructor
will need. None of these touch the GLW process or `Y_GLW_exists`; they are
pure linear-algebra / analytic statements about the hierarchical Cauchy
matrix as a real matrix.

Exposed:

* `hierCauchyG_apply` — entrywise definitional unfolding.
* `hierCauchyG_pos` — strict entrywise positivity.
* `hierCauchyG_le_one_when_hierGrid_sum_ge_one` — entrywise upper bound by 1
  on the diagonal-block region where `hierGrid m i + hierGrid m j ≥ 1`.
* `hierCauchyG_symm` — symmetry (matches `K_GLW`'s symmetry, used by Node 2).
* `hierCauchyG_det_pos` — strict positivity of the determinant, derived from
  the existing `cauchy_hierarchical_det_lower_bound`. (Already provable from
  the `cov_det_pos` field of any V1 instance, but exposed here so the V1
  instance constructor doesn't have to re-derive.)
-/

namespace Erdos524.Helpers
open Real Matrix

theorem hierCauchyG_apply (m : ℕ) (i j : Fin m × Fin m) :
    hierCauchyG m i j = 1 / (hierGrid m i + hierGrid m j) := by
  unfold hierCauchyG
  simp [Matrix.of_apply]

theorem hierCauchyG_pos (m : ℕ) (i j : Fin m × Fin m) :
    0 < hierCauchyG m i j := by
  rw [hierCauchyG_apply]
  exact div_pos one_pos (hierGrid_sum_pos m i j)

theorem hierCauchyG_symm (m : ℕ) (i j : Fin m × Fin m) :
    hierCauchyG m i j = hierCauchyG m j i := by
  rw [hierCauchyG_apply, hierCauchyG_apply, add_comm]

/-- When `hierGrid_i + hierGrid_j ≥ 1`, the entry is bounded above by `1`. -/
theorem hierCauchyG_le_one_of_hierGrid_sum_ge_one (m : ℕ) (i j : Fin m × Fin m)
    (h_sum_ge_one : 1 ≤ hierGrid m i + hierGrid m j) :
    hierCauchyG m i j ≤ 1 := by
  rw [hierCauchyG_apply]
  rw [div_le_one (hierGrid_sum_pos m i j)]
  exact h_sum_ge_one

/-- Strict positivity of the hierarchical-Cauchy determinant.
Derived from `cauchy_hierarchical_det_lower_bound` (which gives a positive
exponential lower bound on the determinant). -/
theorem hierCauchyG_det_pos (m : ℕ) (hm : 1 ≤ m) : 0 < (hierCauchyG m).det := by
  obtain ⟨c₀, hc₀_pos, hc₀⟩ := cauchy_grid_det_lower_bound
  exact lt_of_lt_of_le (Real.exp_pos _) (hc₀ m hm)

/-! ## Round 9 — Pending Mathlib gap: `(hierCauchyG m).PosDef` for `m ≥ 1`

This is the spectral / Cauchy-matrix PosDef result that, combined with
the Round 9 Anderson bound, would close the V1 instance's
`anderson_upper` field. Standard textbook proof: the Cauchy matrix
`C_{ij} = 1/(h_i + h_j)` is PosDef when the `h_i` are distinct positive
reals, via the integral identity
`1/(h_i + h_j) = ∫_0^∞ exp(-(h_i + h_j) t) dt`, which gives
`x^T C x = ∫_0^∞ (∑_i x_i exp(-h_i t))^2 dt > 0` for `x ≠ 0`.

Both `hierGrid m` is positive and injective (the latter requires a small
combinatorial argument on the formula `4^(p+m) · (m + q + 1)`), so the
Cauchy structure applies. This is deferred — multi-day Lean project.

BLOCKER: `(hierCauchyG m).PosDef` for `m ≥ 1`.

TRIED: relating to `Matrix.PosDef.diagonal` (no, hierCauchyG is not
diagonal); `Matrix.posDef_iff_eq_transpose_mul_self` (no clear
factorisation); reducing to a Schur-complement decomposition (the
per-block local Schurs are PosDef but the full hierCauchyG isn't a
direct block sum).

NEEDS: (a) Cauchy-matrix integral identity Lean'd up; OR (b) Mathlib-PR
adding `PosDef` for Cauchy matrices over `ℝ` with distinct positive
parameters; OR (c) explicit eigenvalue / quadratic-form analysis. -/

end Erdos524.Helpers
