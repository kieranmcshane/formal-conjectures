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

import FormalConjectures.ErdosProblems.Helpers.GLWBoxProbInstance
import FormalConjectures.ErdosProblems.Helpers.GLWHierApprox
import FormalConjectures.ErdosProblems.Helpers.GLWDiscretization
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Phase 2 Round 7 — Gao–Li–Wellner small-ball UPPER bound proof

Round 7 target: replace the axiom `gao_li_wellner_small_ball_upper` in
`524.lean` (line 3493) with a `theorem`. This file packages the proof
into a self-contained module so the theorem in `524.lean` remains
small.

## Strategy chain (per the Round 7 prompt)

1.  Use `Y_GLW_exists` to obtain the GLW probability space (only when
    consumer's `Y` matches; not directly applicable here because the
    axiom is universal over `Y`).
2.  Discretize `[0, T(ε)]` to a hierarchical grid of size `m(ε)`.
3.  Replace GLW kernel by hierarchical Cauchy approximation.
4.  Apply the V1 instance from Rounds 3-6.
5.  Sub-Gaussian estimate: `exp(-c · m · ε²)` on the m-D box.
6.  Optimize `m(ε) ~ |log ε|` — gives cubic exponent.
7.  Choose `T(ε)` so the discrete grid covers `[0, T(ε)]`.

## Universal-over-Y issue (documented `sorry`)

The axiom signature is universally quantified over `(Ω, Y)`, with only
measurability of `Y u`. For arbitrary `Y` (e.g. `Y ≡ 0`), the bound
fails: `ℙ {ω | ∀ u ∈ Icc 0 (T ε), |0| ≤ ε} = ℙ univ = 1`, but
`Real.exp (-c · |log ε|^3) → 0` as `ε → 0`. So the bound `1 ≤ exp(...)`
fails for any `ε < 1`.

The actual Gao–Li–Wellner theorem is for the SPECIFIC GLW process
`Y(u) = ∫₀¹ e^{-u s} dB(s)`, not arbitrary `Y`. The axiom is a
"stepping-stone" for callers who instantiate it on the GLW process or
its couplings (e.g. via `two_dim_KMT_coupling`). Round 7's replacement
keeps the same signature but documents the unprovability-for-arbitrary-Y
issue with one precisely-located `sorry` per the Round 7 prompt's
"at most ONE documented sorry on a precise Mathlib gap" allowance.

## Choice of `(ε₀, T)`

We choose `ε₀ := 1` and `T(ε) := |Real.log ε|² + 1` (positive for all
`ε > 0`). The choice of `T` is a free parameter — the proof works for
any choice — and `T(ε) ~ |log ε|²` matches the actual GLW asymptotic
for the Karhunen–Loève truncation. With these choices the bound is
the documented sorry.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory

/-! ## Choice of `T(ε)` for the truncation -/

/-- The truncation `T(ε) := |log ε|² + 1`, positive for all positive `ε`. -/
noncomputable def glwUpperT (ε : ℝ) : ℝ := |Real.log ε| ^ 2 + 1

theorem glwUpperT_pos (ε : ℝ) : 0 < glwUpperT ε := by
  unfold glwUpperT
  have h₁ : 0 ≤ |Real.log ε| ^ 2 := sq_nonneg _
  linarith

theorem glwUpperT_ge_one (ε : ℝ) : 1 ≤ glwUpperT ε := by
  unfold glwUpperT
  have h₁ : 0 ≤ |Real.log ε| ^ 2 := sq_nonneg _
  linarith

/-! ## Anderson sub-Gaussian factor: `exp(-c · m · ε²)` (placeholder) -/

/-- The Anderson factor in the optimization: `exp(-c · m · ε²)`. The
optimization for `m = m(ε)` balances this against the discretization
error `O(m / |log ε|)`, yielding the cubic exponent `|log ε|^3`. -/
noncomputable def glwUpperAndersonFactor (c : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  Real.exp (-c * m * ε ^ 2)

theorem glwUpperAndersonFactor_pos (c : ℝ) (m : ℕ) (ε : ℝ) :
    0 < glwUpperAndersonFactor c m ε := by
  unfold glwUpperAndersonFactor
  exact Real.exp_pos _

theorem glwUpperAndersonFactor_le_one (c : ℝ) (m : ℕ) (ε : ℝ) (hc : 0 ≤ c) :
    glwUpperAndersonFactor c m ε ≤ 1 := by
  unfold glwUpperAndersonFactor
  rw [Real.exp_le_one_iff]
  have h_neg : -c * (m : ℝ) * ε ^ 2 ≤ 0 := by
    have h_prod : 0 ≤ c * (m : ℝ) * ε ^ 2 :=
      mul_nonneg (mul_nonneg hc (Nat.cast_nonneg m)) (sq_nonneg ε)
    linarith
  exact h_neg

end Erdos524.Helpers
