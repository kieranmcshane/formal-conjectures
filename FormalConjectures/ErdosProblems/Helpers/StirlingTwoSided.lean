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

/-- **Robbins 1955 sharp upper bound.**

For all `n ≥ 1`, `n! ≤ √(2π n) · (n/e)^n · exp(1/(12n))`.

This is the *sharp* form of Stirling's upper bound: the constant `exp(1/(12n))` decays to `1`,
matching the Mathlib lower bound `√(2π n) · (n/e)^n ≤ n!` asymptotically. The looser
`factorial_le_stirling` above uses an absolute constant `exp 1 / √(2π) ≈ 1.0844` instead.

Mathlib pin status (`mathlib4 @ 25ce633136`, verified TC6 T1.1 + TC7 T1.1): NOT formalised.
Mathlib explicitly comments at `Mathlib/Analysis/SpecialFunctions/Stirling.lean:264, 280` that
*"Sharper bounds due to Robbins are available, but are not yet formalised."*

**TC7 T2.2B refined diagnostic — Mathlib gap binding.**

This Stub will NOT close in TC7. The closure path is genuine Robbins-trapezoidal
machinery (~120-200 LOC) which requires deriving the log-correction antitonicity
of `log(stirlingSeq n) - 1/(12n)` from scratch, since Mathlib provides only the
weaker `Stirling.stirlingSeq'_antitone` (without the `1/(12n)` quantitative rate).

**Closure plan for TC8+ (deferred):**

1. *Log-correction antitonicity (Robbins 1955).* Define
   `robbinsCorr n : ℝ := Real.log (Stirling.stirlingSeq n) - 1 / (12 * n)`
   for `n ≥ 1`. Show `Antitone robbinsCorr` via the trapezoidal-rule remainder:
   `log(n+1) - log(n) ≥ 1/(2n) + 1/(2(n+1)) - 1/(12n²) + 1/(12(n+1)²)` for `n ≥ 1`.
   This is the integral-comparison estimate `∫_n^{n+1} log t dt ≥ trapezoid - error`.
   ~60-80 LOC.

2. *Limit at infinity.* From `Stirling.tendsto_stirlingSeq_sqrt_pi : stirlingSeq → √π`
   (`Stirling.lean:228`) and `1/(12n) → 0` we get `robbinsCorr n → log √π`.
   Combined with antitonicity (step 1): `robbinsCorr n ≥ log √π` for all `n ≥ 1`.
   ~10-20 LOC.

3. *Unfold to factorial form.* From `robbinsCorr n ≥ log √π`:
   `log(stirlingSeq n) ≥ log √π + 1/(12n)`,
   `stirlingSeq n ≥ √π · exp(1/(12n))`. Wait — this gives a LOWER bound, not upper.
   The correct direction for the *upper* Robbins bound uses an antitonicity of
   `log(stirlingSeq n) + 1/(12n)` (the *positive* correction term), giving an upper
   limit. Need to flip the trapezoid argument: `log(n+1) - log(n) ≤ trapezoid + error`
   for the OTHER side of the integral comparison.
   ~30-50 LOC.

4. *Final algebra.* From `stirlingSeq n ≤ √π · exp(1/(12n))` and the unfold
   `stirlingSeq n = n! / (√(2n) · (n/e)^n)`, derive the desired bound by
   multiplying through and using `√(2n) · √π = √(2π n)`.
   ~20-30 LOC.

Total: ~120-180 LOC. **Only step 4 is mechanical**; steps 1-3 require explicit
trapezoidal-remainder analysis. TC7 budget cannot accommodate this within the
4h round; deferred to TC8 as a dedicated Stirling-Robbins close round.

**Carter-Pollard composition impact**: this Stub is ONE of the three TC7 prelude
gaps (Mills _antitone, Stirling Robbins, Real-Beta) needed for full Carter-Pollard
polynomial bound assembly. With Real-Beta closed (TC7 T2.2A) and Mills _pos closed
(TC7 T2.1A), the *tail case* of Carter-Pollard becomes provable using the looser
`factorial_le_stirling` (TC6, with constant `exp 1/√(2π) ≈ 1.0844`). The *bulk
case* (where binomial-Gaussian comparison is sharp) requires Robbins. -/
theorem factorial_le_stirling_robbins {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n *
        Real.exp (1 / (12 * (n : ℝ))) := by
  -- TAG[TrackC-Layer3-Stirling-robbins]: TC8+ close target.
  -- See Mathlib comment at Stirling.lean:264, 280: "Sharper bounds due to Robbins
  -- are available, but are not yet formalised." TC7 T1.1 confirmed gap binding.
  sorry

end Helpers
end Erdos524
