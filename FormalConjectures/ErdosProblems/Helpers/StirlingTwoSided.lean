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

import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Two-sided effective Stirling bound (helper for Erdős problem 524)

Mathlib provides an effective lower bound
`Stirling.le_factorial_stirling : √(2π · n) · (n / e)^n ≤ n!`
(valid for all `n`, including `n = 0`).

This file provides a matching *effective upper* bound with an absolute constant. Since
Mathlib's `Stirling.stirlingSeq n := n! / (√(2 n) · (n / e)^n)` is antitone in `n`
(restricted to `n ≥ 1`) with limit `√π`, we have for every `n ≥ 1`
`stirlingSeq n ≤ stirlingSeq 1 = exp 1 / √2`, which unfolds to
`n ! ≤ (exp 1 / √(2π)) · √(2π · n) · (n / e)^n`.

The constant `exp 1 / √(2π) ≈ 1.0844` is not the sharp Robbins constant
`exp (1 / (12 n)) → 1`, but it matches the Mathlib lower bound in form and is sufficient
for applications requiring a two-sided effective bound.
-/

namespace Erdos524
namespace Helpers

open Real Stirling

/-- `stirlingSeq 1 = exp 1 / √2`, restated explicitly for use in the upper bound. -/
theorem stirlingSeq_one_eq : stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 :=
  Stirling.stirlingSeq_one

/-- The Mathlib `Stirling.stirlingSeq` is bounded above by its value at `1`, i.e.
by `exp 1 / √2`, for all `n ≥ 1`. This is the antitone property of
`stirlingSeq ∘ succ` evaluated at the base point. -/
theorem stirlingSeq_le_exp_div_sqrt_two {n : ℕ} (hn : 1 ≤ n) :
    stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 := by
  have hanti : stirlingSeq (n - 1 + 1) ≤ stirlingSeq (0 + 1) :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le _)
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hsucc, zero_add, Stirling.stirlingSeq_one] at hanti
  exact hanti

/-- An effective upper bound on the factorial in the same form as
`Stirling.le_factorial_stirling` (the Mathlib lower bound), valid for all `n ≥ 1`.

The absolute constant is `exp 1 / √(2π) ≈ 1.0844`. It is not the sharp Robbins constant
`exp (1 / (12 n))`, but suffices for applications requiring a two-sided effective bound. -/
theorem factorial_le_stirling {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ (Real.exp 1 / Real.sqrt (2 * Real.pi)) *
      (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have hden_pos : (0 : ℝ) < Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by
    have hs : 0 < Real.sqrt (2 * n) := Real.sqrt_pos.mpr h2n
    exact mul_pos hs (by positivity)
  have hbd : stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 :=
    stirlingSeq_le_exp_div_sqrt_two hn
  have hmul :
      (n.factorial : ℝ) ≤ (Real.exp 1 / Real.sqrt 2) *
        (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
    have hbd' : (n.factorial : ℝ) / (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) ≤
        Real.exp 1 / Real.sqrt 2 := by
      simpa [Stirling.stirlingSeq] using hbd
    exact (div_le_iff₀ hden_pos).mp hbd'
  have hrewrite :
      (Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * n) =
        (Real.exp 1 / Real.sqrt (2 * Real.pi)) * Real.sqrt (2 * Real.pi * n) := by
    have sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have sqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi
    have lhs : (Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * n) = Real.exp 1 * Real.sqrt n := by
      have h2nn : Real.sqrt (2 * n) = Real.sqrt 2 * Real.sqrt n :=
        Real.sqrt_mul (by norm_num) _
      rw [h2nn]
      field_simp
    have rhs : (Real.exp 1 / Real.sqrt (2 * Real.pi)) * Real.sqrt (2 * Real.pi * n) =
        Real.exp 1 * Real.sqrt n := by
      have h2pinn : Real.sqrt (2 * Real.pi * n) = Real.sqrt (2 * Real.pi) * Real.sqrt n :=
        Real.sqrt_mul h2pi.le _
      rw [h2pinn]
      field_simp
    rw [lhs, rhs]
  calc (n.factorial : ℝ)
      ≤ (Real.exp 1 / Real.sqrt 2) *
          (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := hmul
    _ = ((Real.exp 1 / Real.sqrt 2) * Real.sqrt (2 * n)) * (n / Real.exp 1) ^ n := by ring
    _ = ((Real.exp 1 / Real.sqrt (2 * Real.pi)) * Real.sqrt (2 * Real.pi * n)) *
          (n / Real.exp 1) ^ n := by rw [hrewrite]
    _ = (Real.exp 1 / Real.sqrt (2 * Real.pi)) *
          (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) := by ring

/-- Restatement of Mathlib's `Stirling.le_factorial_stirling` under a local name. -/
theorem sqrt_two_pi_mul_pow_le_factorial (n : ℕ) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n ≤ (n.factorial : ℝ) :=
  Stirling.le_factorial_stirling n

/-- **Two-sided effective Stirling bound.** For every `n ≥ 1`, the factorial is sandwiched
between `√(2π n) · (n/e)^n` and `(exp 1 / √(2π)) · √(2π n) · (n/e)^n`. -/
theorem two_sided_stirling {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n ≤ (n.factorial : ℝ)
      ∧ (n.factorial : ℝ) ≤ (Real.exp 1 / Real.sqrt (2 * Real.pi)) *
          (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) :=
  ⟨sqrt_two_pi_mul_pow_le_factorial n, factorial_le_stirling hn⟩

/-- The ratio `n ! / (√(2π n) · (n/e)^n)` lies in `[1, exp 1 / √(2π)]` for `n ≥ 1`. -/
theorem ratio_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n)
      ∧ (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n)
          ≤ Real.exp 1 / Real.sqrt (2 * Real.pi) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pin : (0 : ℝ) < 2 * Real.pi * n := by positivity
  have hden : 0 < Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n := by
    have hs : 0 < Real.sqrt (2 * Real.pi * n) := Real.sqrt_pos.mpr h2pin
    exact mul_pos hs (by positivity)
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hden, one_mul]
    exact sqrt_two_pi_mul_pow_le_factorial n
  · rw [div_le_iff₀ hden]
    exact factorial_le_stirling hn

/-- Log-form of the two-sided bound: `|log(n! / (√(2π n) · (n/e)^n))| ≤ 1 - (1/2) log(2π)`.
The explicit constant `1 - (1/2) log(2π) = log(exp 1 / √(2π)) ≈ 0.081`. -/
theorem abs_log_factorial_sub_stirling_le {n : ℕ} (hn : 1 ≤ n) :
    |Real.log ((n.factorial : ℝ) /
        (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n))|
      ≤ 1 - (1 / 2) * Real.log (2 * Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2pin : (0 : ℝ) < 2 * Real.pi * n := by positivity
  have hden : 0 < Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n := by
    have hs : 0 < Real.sqrt (2 * Real.pi * n) := Real.sqrt_pos.mpr h2pin
    exact mul_pos hs (by positivity)
  obtain ⟨hlo, hhi⟩ := ratio_bounds hn
  set r : ℝ := (n.factorial : ℝ) /
    (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) with hr_def
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hlo
  have hlog_lo : 0 ≤ Real.log r := Real.log_nonneg hlo
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hlog_hi : Real.log r ≤ Real.log (Real.exp 1 / Real.sqrt (2 * Real.pi)) :=
    Real.log_le_log hrpos hhi
  have hRHS :
      Real.log (Real.exp 1 / Real.sqrt (2 * Real.pi)) =
        1 - (1 / 2) * Real.log (2 * Real.pi) := by
    rw [Real.log_div (Real.exp_pos 1).ne' hsqrt_pos.ne',
        Real.log_exp, Real.log_sqrt (by positivity)]
    ring
  rw [hRHS] at hlog_hi
  rw [abs_of_nonneg hlog_lo]
  exact hlog_hi

/-- **Refined log-Stirling-diff bound (Robbins-grade).**

Strengthens Mathlib's `Stirling.log_stirlingSeq_diff_le_geo_sum` by extracting the
`1 / 3` factor from `1/(2(k+1)+1) ≤ 1/3` for k ≥ 0. The resulting bound
`1 / (12 (n+1) (n+2))` is the precise form needed for Robbins' antitonicity. -/
private lemma log_stirlingSeq_diff_le_robbins (n : ℕ) :
    Real.log (stirlingSeq (n + 1)) - Real.log (stirlingSeq (n + 2)) ≤
      1 / (12 * (↑(n + 1) : ℝ) * (↑(n + 2) : ℝ)) := by
  have h_nonneg : (0 : ℝ) ≤ ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 := sq_nonneg _
  have hq_sq_lt_one : ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 < 1 := by
    rw [one_div, inv_pow]
    exact inv_lt_one_of_one_lt₀
      (one_lt_pow₀ (lt_add_of_pos_left _ <| by positivity) two_ne_zero)
  -- Geometric series: ∑ k≥0, q²^(k+1) = q²/(1-q²)
  have g : HasSum (fun k : ℕ => (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) ^ (k + 1))
      (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 /
        (1 - ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2)) := by
    have h_geo := (hasSum_geometric_of_lt_one h_nonneg hq_sq_lt_one).mul_left
      (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2)
    -- h_geo : HasSum (fun k => q² * (q²)^k) (q² * (1-q²)⁻¹)
    have hfun :
        (fun k : ℕ => ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 *
          (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) ^ k) =
        (fun k : ℕ => (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) ^ (k + 1)) := by
      funext k
      exact (pow_succ' _ _).symm
    have hval : ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 *
        (1 - ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2)⁻¹ =
      ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 /
        (1 - ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) :=
      (div_eq_mul_inv _ _).symm
    rw [← hval, ← hfun]
    exact h_geo
  -- Term-by-term: 1/(2(k+1)+1) ≤ 1/3
  have hab (k : ℕ) :
      (1 : ℝ) / (2 * ↑(k + 1) + 1) *
          ((1 / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1) ≤
        (1 / 3 : ℝ) * (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) ^ (k + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg h_nonneg _)
    have h2k1_pos : (0 : ℝ) < 2 * (↑(k + 1) : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ h2k1_pos (by norm_num : (0 : ℝ) < 3)]
    push_cast
    linarith [(Nat.zero_le k : 0 ≤ k)]
  -- Use Mathlib's series for stirling diff (form ↑(k+1)), which is = (k+1)
  have h_dom : HasSum
      (fun k : ℕ => (1 / 3 : ℝ) *
        (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2) ^ (k + 1))
      ((1 / 3) * (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 /
          (1 - ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2))) := g.mul_left _
  have h_sum_bd : Real.log (stirlingSeq (n + 1)) - Real.log (stirlingSeq (n + 2)) ≤
      (1 / 3) * (((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2 /
        (1 - ((1 : ℝ) / (2 * ↑(n + 1) + 1)) ^ 2)) :=
    hasSum_le hab (Stirling.log_stirlingSeq_diff_hasSum n) h_dom
  -- Algebraic identity: (1/3) · q² / (1 - q²) = 1/(12(n+1)(n+2))
  refine h_sum_bd.trans (le_of_eq ?_)
  have h2n1 : (0 : ℝ) < 2 * (↑(n + 1) : ℝ) + 1 := by positivity
  have h2n1_ne : (2 * (↑(n + 1) : ℝ) + 1) ≠ 0 := h2n1.ne'
  have h2n1_sq_pos : (0 : ℝ) < (2 * (↑(n + 1) : ℝ) + 1) ^ 2 := pow_pos h2n1 _
  have h2n1_sq_ne : (2 * (↑(n + 1) : ℝ) + 1) ^ 2 ≠ 0 := h2n1_sq_pos.ne'
  have h_alg : (2 * (↑(n + 1) : ℝ) + 1) ^ 2 - 1 = 4 * (↑(n + 1) : ℝ) * (↑(n + 2) : ℝ) := by
    push_cast; ring
  have h_alg_pos : (0 : ℝ) < (2 * (↑(n + 1) : ℝ) + 1) ^ 2 - 1 := by rw [h_alg]; positivity
  have h_alg_ne : (2 * (↑(n + 1) : ℝ) + 1) ^ 2 - 1 ≠ 0 := h_alg_pos.ne'
  rw [div_pow, one_pow]
  -- Step 1: rewrite 1 - 1/(2(n+1)+1)^2 = ((2(n+1)+1)^2 - 1)/(2(n+1)+1)^2
  have h_one_sub : (1 : ℝ) - 1 / (2 * (↑(n + 1) : ℝ) + 1) ^ 2 =
      ((2 * (↑(n + 1) : ℝ) + 1) ^ 2 - 1) / (2 * (↑(n + 1) : ℝ) + 1) ^ 2 := by
    rw [sub_div, div_self h2n1_sq_ne]
  rw [h_one_sub]
  -- Step 2: cancel via div_div_div_cancel_right₀
  rw [div_div_div_cancel_right₀ h2n1_sq_ne]
  -- Goal: 1/3 * (1 / ((2(n+1)+1)^2 - 1)) = 1/(12(n+1)(n+2))
  rw [mul_one_div, div_div, h_alg]
  -- Goal: 1/(3 * (4 * (n+1) * (n+2))) = 1/(12 * (n+1) * (n+2))
  congr 1
  ring

/-- **Robbins-corrected log Stirling sequence.**

`robbinsCorr n := log(stirlingSeq (n+1)) - 1/(12·(n+1))`. This sequence is
*monotone increasing* in n with limit `log √π`, by the refined log-diff bound. -/
private noncomputable def robbinsCorr (n : ℕ) : ℝ :=
  Real.log (stirlingSeq (n + 1)) - 1 / (12 * (↑(n + 1) : ℝ))

/-- **Robbins-corrected sequence is monotone increasing.**

For n ≤ m, `robbinsCorr n ≤ robbinsCorr m`. Proven via `monotone_nat_of_le_succ`
and the refined log-diff bound. -/
private lemma robbinsCorr_monotone : Monotone robbinsCorr := by
  apply monotone_nat_of_le_succ
  intro n
  have h_diff := log_stirlingSeq_diff_le_robbins n
  -- h_diff : log(stirlingSeq (n+1)) - log(stirlingSeq (n+2)) ≤ 1/(12(n+1)(n+2))
  -- Goal: robbinsCorr n ≤ robbinsCorr (n+1)
  -- i.e., log(stirlingSeq (n+1)) - 1/(12(n+1)) ≤ log(stirlingSeq (n+2)) - 1/(12(n+2))
  -- i.e., log(stirlingSeq (n+1)) - log(stirlingSeq (n+2)) ≤ 1/(12(n+1)) - 1/(12(n+2))
  -- RHS = 1/(12(n+1)(n+2)) ✓
  unfold robbinsCorr
  have h_pos_n1 : (0 : ℝ) < ↑(n + 1) := by positivity
  have h_pos_n2 : (0 : ℝ) < ↑(n + 2) := by positivity
  have h_eq : (1 : ℝ) / (12 * (↑(n + 1) : ℝ)) - 1 / (12 * (↑(n + 2) : ℝ)) =
      1 / (12 * (↑(n + 1) : ℝ) * (↑(n + 2) : ℝ)) := by
    field_simp
    push_cast
    ring
  -- Goal: log(stirlingSeq (n+1)) - 1/(12(n+1)) ≤ log(stirlingSeq ((n+1)+1)) - 1/(12((n+1)+1))
  show Real.log (stirlingSeq (n + 1)) - 1 / (12 * (↑(n + 1) : ℝ)) ≤
       Real.log (stirlingSeq (n + 1 + 1)) - 1 / (12 * (↑(n + 1 + 1) : ℝ))
  have h_succ : n + 1 + 1 = n + 2 := rfl
  rw [h_succ]
  linarith [h_diff, h_eq]

/-- **Limit of robbinsCorr is `log √π`.** -/
private lemma robbinsCorr_tendsto :
    Filter.Tendsto robbinsCorr Filter.atTop (nhds (Real.log (Real.sqrt Real.pi))) := by
  unfold robbinsCorr
  -- log(stirlingSeq (n+1)) → log √π
  have h1 : Filter.Tendsto (fun n : ℕ => Real.log (stirlingSeq (n + 1)))
      Filter.atTop (nhds (Real.log (Real.sqrt Real.pi))) := by
    have hsp : Real.sqrt Real.pi > 0 := Real.sqrt_pos.mpr Real.pi_pos
    have hss : Filter.Tendsto (fun n : ℕ => stirlingSeq (n + 1))
        Filter.atTop (nhds (Real.sqrt Real.pi)) := by
      have := Stirling.tendsto_stirlingSeq_sqrt_pi
      exact this.comp (Filter.tendsto_add_atTop_nat 1)
    exact (Real.continuousAt_log hsp.ne').tendsto.comp hss
  -- 1/(12·(n+1)) → 0
  have h2 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (12 * (↑(n + 1) : ℝ)))
      Filter.atTop (nhds 0) := by
    -- Build via composition: (n+1 → ∞) ⟹ (12·(n+1) → ∞) ⟹ (1/(12·(n+1)) → 0)
    have h_step : Filter.Tendsto (fun n : ℕ => 12 * ((n + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_n_atTop : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
          Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
      exact h_n_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
    have h_inv : Filter.Tendsto (fun n : ℕ => (12 * ((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp h_step
    refine h_inv.congr fun n => ?_
    rw [one_div]
  have := h1.sub h2
  simpa using this

/-- **`robbinsCorr n ≤ log √π` for all n.** -/
private lemma robbinsCorr_le_log_sqrt_pi (n : ℕ) :
    robbinsCorr n ≤ Real.log (Real.sqrt Real.pi) :=
  robbinsCorr_monotone.ge_of_tendsto robbinsCorr_tendsto n

/-- **Stirling-Robbins upper bound on the Stirling sequence.**

For all n, `stirlingSeq (n+1) ≤ √π · exp(1/(12·(n+1)))`. -/
private lemma stirlingSeq_le_sqrt_pi_robbins (n : ℕ) :
    stirlingSeq (n + 1) ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * (↑(n + 1) : ℝ))) := by
  have h_sp_pos : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h_ss_pos : (0 : ℝ) < stirlingSeq (n + 1) := Stirling.stirlingSeq'_pos n
  have h_corr := robbinsCorr_le_log_sqrt_pi n
  -- h_corr : log(stirlingSeq (n+1)) - 1/(12(n+1)) ≤ log √π
  -- ⟹ log(stirlingSeq (n+1)) ≤ log √π + 1/(12(n+1)) = log(√π · exp(1/(12(n+1))))
  unfold robbinsCorr at h_corr
  have h_log_le : Real.log (stirlingSeq (n + 1)) ≤
      Real.log (Real.sqrt Real.pi) + 1 / (12 * (↑(n + 1) : ℝ)) := by linarith
  have h_rhs_pos : (0 : ℝ) <
      Real.sqrt Real.pi * Real.exp (1 / (12 * (↑(n + 1) : ℝ))) := by positivity
  have h_log_rhs : Real.log (Real.sqrt Real.pi * Real.exp (1 / (12 * (↑(n + 1) : ℝ)))) =
      Real.log (Real.sqrt Real.pi) + 1 / (12 * (↑(n + 1) : ℝ)) := by
    rw [Real.log_mul h_sp_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [← h_log_rhs] at h_log_le
  exact (Real.log_le_log_iff h_ss_pos h_rhs_pos).mp h_log_le

/-- **Robbins 1955 sharp upper bound.**

For all `n ≥ 1`, `n! ≤ √(2π n) · (n/e)^n · exp(1/(12n))`.

This is the *sharp* form of Stirling's upper bound: the constant `exp(1/(12n))` decays to `1`,
matching the Mathlib lower bound `√(2π n) · (n/e)^n ≤ n!` asymptotically.

**TC8 close** via refined log-diff bound + `Monotone.ge_of_tendsto` machinery —
bypasses the explicit trapezoidal-rule path documented in TC7's deferred plan. -/
theorem factorial_le_stirling_robbins {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n *
        Real.exp (1 / (12 * (n : ℝ))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  -- Goal: ((m+1)! : ℝ) ≤ √(2π(m+1)) · ((m+1)/e)^(m+1) · exp(1/(12(m+1)))
  have h_seq_le := stirlingSeq_le_sqrt_pi_robbins m
  -- h_seq_le : stirlingSeq (m+1) ≤ √π · exp(1/(12(m+1)))
  -- stirlingSeq (m+1) = (m+1)! / (√(2(m+1)) · ((m+1)/e)^(m+1))
  have h_pos_2m1 : (0 : ℝ) < 2 * (↑(m + 1) : ℝ) := by positivity
  have h_pos_sqrt : (0 : ℝ) < Real.sqrt (2 * (↑(m + 1) : ℝ)) := Real.sqrt_pos.mpr h_pos_2m1
  have h_pos_pow : (0 : ℝ) < ((↑(m + 1) : ℝ) / Real.exp 1) ^ (m + 1) := by positivity
  have h_pos_den : (0 : ℝ) <
      Real.sqrt (2 * (↑(m + 1) : ℝ)) * ((↑(m + 1) : ℝ) / Real.exp 1) ^ (m + 1) :=
    mul_pos h_pos_sqrt h_pos_pow
  -- Multiply h_seq_le by denominator
  have h_unfold : stirlingSeq (m + 1) =
      ((m + 1).factorial : ℝ) /
        (Real.sqrt (2 * (↑(m + 1) : ℝ)) * ((↑(m + 1) : ℝ) / Real.exp 1) ^ (m + 1)) := by
    show ((m + 1).factorial : ℝ) /
      (Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) = _
    rfl
  rw [h_unfold] at h_seq_le
  rw [div_le_iff₀ h_pos_den] at h_seq_le
  -- h_seq_le : (m+1)! ≤ (√π · exp(1/(12(m+1)))) · (√(2(m+1)) · ((m+1)/e)^(m+1))
  -- Goal: (m+1)! ≤ √(2π(m+1)) · ((m+1)/e)^(m+1) · exp(1/(12(m+1)))
  have h_sqrt_combine :
      Real.sqrt Real.pi * Real.sqrt (2 * (↑(m + 1) : ℝ)) =
        Real.sqrt (2 * Real.pi * (↑(m + 1) : ℝ)) := by
    rw [← Real.sqrt_mul Real.pi_pos.le]
    congr 1
    ring
  refine h_seq_le.trans (le_of_eq ?_)
  -- Reorder LHS to extract √π · √(2(m+1)) factor
  have h_lhs_reorder :
      Real.sqrt Real.pi * Real.exp (1 / (12 * (↑(m + 1) : ℝ))) *
        (Real.sqrt (2 * (↑(m + 1) : ℝ)) * ((↑(m + 1) : ℝ) / Real.exp 1) ^ (m + 1)) =
        (Real.sqrt Real.pi * Real.sqrt (2 * (↑(m + 1) : ℝ))) *
          ((↑(m + 1) : ℝ) / Real.exp 1) ^ (m + 1) *
          Real.exp (1 / (12 * (↑(m + 1) : ℝ))) := by ring
  rw [h_lhs_reorder, h_sqrt_combine]

end Helpers
end Erdos524
