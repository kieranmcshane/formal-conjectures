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

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.NhdsWithin

/-!
# Phase 2 / Node 1A — Gao–Li–Wellner kernel

The deterministic kernel
`K_GLW(u, v) = (1 - exp(-(u+v)))/(u+v)`,
extended continuously to `K_GLW(u, v) = 1` at `u + v = 0`.

This is the (formal) covariance kernel of the Itô-integral process
`Y(u) = ∫₀¹ e^{-us} dB(s)`; the actual covariance computation lives in
Node 1B (`GLWProcess.lean`). This file is **pure real analysis** — no
probability content — and exposes the four properties needed downstream:

* `K_GLW_pos`: positivity for `u, v ≥ 0`,
* `K_GLW_le_one`: bounded by 1 for `u, v ≥ 0`,
* `K_GLW_continuous`: joint continuity in `(u, v)`,
* `K_GLW_symm`: symmetry,
* `K_GLW_cauchy_asymptotic`: `|K_GLW u v - 1/(u+v)| ≤ exp(-(u+v))/(u+v)` for
  `u + v > 0`, capturing the "large `u+v` ⇒ Cauchy `1/(u+v)`" reduction
  that powers the hierarchical-Cauchy approximation in Node 2.
-/

namespace Erdos524.Helpers
open Real Filter Topology

/-! ## Single-variable form -/

/-- The single-variable form of the GLW kernel: `(1 - exp(-x))/x` extended
to `1` at `x = 0` (the L'Hôpital limit). -/
noncomputable def K_GLW_aux (x : ℝ) : ℝ :=
  if x = 0 then 1 else (1 - Real.exp (-x)) / x

theorem K_GLW_aux_zero : K_GLW_aux 0 = 1 := by
  unfold K_GLW_aux; simp

theorem K_GLW_aux_of_ne (x : ℝ) (hx : x ≠ 0) :
    K_GLW_aux x = (1 - Real.exp (-x)) / x := by
  unfold K_GLW_aux; simp [hx]

/-! ## Two-variable form -/

/-- The Gao–Li–Wellner kernel `K_GLW(u, v) = (1 - exp(-(u+v)))/(u+v)`,
extended to `1` at `u + v = 0`. -/
noncomputable def K_GLW (u v : ℝ) : ℝ := K_GLW_aux (u + v)

theorem K_GLW_def (u v : ℝ) : K_GLW u v = K_GLW_aux (u + v) := rfl

theorem K_GLW_zero : K_GLW 0 0 = 1 := by
  rw [K_GLW_def, show (0 : ℝ) + 0 = 0 from by norm_num, K_GLW_aux_zero]

/-! ## Symmetry -/

theorem K_GLW_symm (u v : ℝ) : K_GLW u v = K_GLW v u := by
  rw [K_GLW_def, K_GLW_def, add_comm]

/-! ## Positivity -/

theorem K_GLW_aux_pos (x : ℝ) (hx : 0 ≤ x) : 0 < K_GLW_aux x := by
  by_cases h : x = 0
  · rw [h, K_GLW_aux_zero]; norm_num
  · rw [K_GLW_aux_of_ne x h]
    have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
    have h_exp_lt : Real.exp (-x) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    exact div_pos (by linarith) hx_pos

theorem K_GLW_pos (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 < K_GLW u v := by
  rw [K_GLW_def]
  exact K_GLW_aux_pos _ (by linarith)

/-! ## Upper bound -/

theorem K_GLW_aux_le_one (x : ℝ) (hx : 0 ≤ x) : K_GLW_aux x ≤ 1 := by
  by_cases h : x = 0
  · rw [h, K_GLW_aux_zero]
  · rw [K_GLW_aux_of_ne x h]
    have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
    rw [div_le_one hx_pos]
    -- Goal: 1 - exp(-x) ≤ x  ↔  1 - x ≤ exp(-x).
    have h_exp_lower : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
    linarith

theorem K_GLW_le_one (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : K_GLW u v ≤ 1 := by
  rw [K_GLW_def]
  exact K_GLW_aux_le_one _ (by linarith)

/-! ## Continuity

The only non-trivial point is `x = 0`: away from `0` the formula
`(1 - exp(-x))/x` is a quotient of continuous functions with non-zero
denominator, so continuity is automatic. At `0` we use the derivative
of `f(y) = 1 - exp(-y)` at `y = 0`, which equals `1`, to identify the
slope `(1 - exp(-y))/y` as having limit `1` at `0`. Combined with the
extension `K_GLW_aux 0 = 1`, this yields `ContinuousAt K_GLW_aux 0`. -/

private theorem hasDerivAt_one_sub_exp_neg :
    HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) 1 0 := by
  have h_neg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg
  -- `HasDerivAt.exp` (from `Mathlib.Analysis.SpecialFunctions.ExpDeriv`) gives
  -- `HasDerivAt (fun y => Real.exp (f y)) (Real.exp (f x) * f') x`.
  have h_exp_neg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-1 : ℝ) 0 := by
    have := h_neg.exp
    simpa using this
  have h_sub : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) 1 0 := by
    have := (hasDerivAt_const 0 (1 : ℝ)).sub h_exp_neg
    simpa using this
  exact h_sub

private theorem tendsto_one_sub_exp_neg_div_self :
    Tendsto (fun y : ℝ => (1 - Real.exp (-y)) / y) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h_slope : Tendsto (slope (fun y : ℝ => 1 - Real.exp (-y)) 0)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hasDerivAt_one_sub_exp_neg
  -- `slope f 0 y = (y - 0)⁻¹ • (f y - f 0)` and `f 0 = 1 - Real.exp 0 = 0`,
  -- so the slope reduces to `(1 - Real.exp (-y)) / y`.
  have h_eq : slope (fun y : ℝ => 1 - Real.exp (-y)) 0 =
              (fun y : ℝ => (1 - Real.exp (-y)) / y) := by
    funext y
    rw [slope_def_field]
    simp [Real.exp_zero]
  rw [h_eq] at h_slope
  exact h_slope

theorem K_GLW_aux_continuous : Continuous K_GLW_aux := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · -- ContinuousAt K_GLW_aux 0
    subst hx
    rw [ContinuousAt, K_GLW_aux_zero]
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h_punc : ∀ᶠ y in (𝓝[≠] (0 : ℝ)), dist (K_GLW_aux y) 1 < ε := by
      have h_lim : ∀ᶠ y in (𝓝[≠] (0 : ℝ)),
          dist ((1 - Real.exp (-y)) / y) 1 < ε :=
        (Metric.tendsto_nhds.mp tendsto_one_sub_exp_neg_div_self) ε hε
      filter_upwards [h_lim, self_mem_nhdsWithin] with y hy_lim hy_ne
      have hy : y ≠ 0 := by simpa using hy_ne
      rw [K_GLW_aux_of_ne y hy]
      exact hy_lim
    rw [eventually_nhdsWithin_iff] at h_punc
    filter_upwards [h_punc] with y hy
    by_cases hy0 : y = 0
    · subst hy0
      rw [K_GLW_aux_zero, dist_self]
      exact hε
    · exact hy hy0
  · -- ContinuousAt K_GLW_aux x for x ≠ 0
    have h_neighborhood : ∀ᶠ y in 𝓝 x, y ≠ 0 := eventually_ne_nhds hx
    have h_eq : K_GLW_aux =ᶠ[𝓝 x] (fun y => (1 - Real.exp (-y)) / y) := by
      filter_upwards [h_neighborhood] with y hy
      exact K_GLW_aux_of_ne y hy
    have h_at_x : K_GLW_aux x = (1 - Real.exp (-x)) / x := K_GLW_aux_of_ne x hx
    have h_cont_quotient : ContinuousAt (fun y : ℝ => (1 - Real.exp (-y)) / y) x := by
      apply ContinuousAt.div
      · exact continuousAt_const.sub
          ((Real.continuous_exp.comp continuous_neg).continuousAt)
      · exact continuousAt_id
      · exact hx
    show Tendsto K_GLW_aux (𝓝 x) (𝓝 (K_GLW_aux x))
    rw [h_at_x]
    have h_tend : Tendsto (fun y : ℝ => (1 - Real.exp (-y)) / y) (𝓝 x)
        (𝓝 ((1 - Real.exp (-x)) / x)) := h_cont_quotient
    exact h_tend.congr' h_eq.symm

theorem K_GLW_continuous : Continuous (Function.uncurry K_GLW) := by
  have h_eq : Function.uncurry K_GLW =
              K_GLW_aux ∘ (fun p : ℝ × ℝ => p.1 + p.2) := by
    funext p
    simp [Function.uncurry, K_GLW_def]
  rw [h_eq]
  exact K_GLW_aux_continuous.comp (continuous_fst.add continuous_snd)

/-! ## Cauchy asymptotic

For `u + v > 0`, the GLW kernel differs from the Cauchy form `1/(u+v)`
by exactly `exp(-(u+v))/(u+v)` (in absolute value). This is the
identity used downstream by Node 2 to approximate the GLW covariance
matrix by the hierarchical Cauchy matrix `hierCauchyG m`. -/

theorem K_GLW_cauchy_asymptotic (u v : ℝ) (huv : 0 < u + v) :
    |K_GLW u v - 1 / (u + v)| ≤ Real.exp (-(u + v)) / (u + v) := by
  rw [K_GLW_def, K_GLW_aux_of_ne _ (ne_of_gt huv)]
  -- Combine the two quotients over the common denominator `u + v`.
  have h_ne : u + v ≠ 0 := ne_of_gt huv
  have h_combine : (1 - Real.exp (-(u + v))) / (u + v) - 1 / (u + v) =
                   -Real.exp (-(u + v)) / (u + v) := by
    field_simp
    ring
  rw [h_combine, abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos huv]

end Erdos524.Helpers
