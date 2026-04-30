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

import FormalConjectures.ErdosProblems.Helpers.StirlingTwoSided
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Effective Gaussian lower bound on the central binomial PMF
(helper for Erdős problem 524)

For a fair Rademacher walk with `n` steps, the probability of ending at offset
`2k − n` (equivalently, `k` "heads") is `C(n,k) · 2^{-n}`. Writing `d = k − n/2`,
we prove an effective pointwise Gaussian-style lower bound of the form
`C(n,k) / 2^n ≥ c · n^{-1/2} · exp(−α · d² / n)` with absolute constants
`c > 0` and `α = 4`.

## Strategy

1. Use `Nat.choose_mul_factorial_mul_factorial` plus the two-sided Stirling
   bounds from `StirlingTwoSided` to reduce the PMF to an expression in terms
   of the powers `n^n / (k^k · (n-k)^(n-k))` and a `√(1/n)` prefactor.
2. The core inequality is
   `k log(2k/n) + (n-k) log(2(n-k)/n) ≤ 4 · (k - n/2)² / n`,
   which follows from the elementary bound `log x ≤ x − 1` applied twice.
   This is recorded as `Erdos524.Helpers.kl_to_half_le_sq`.
3. Combining these gives the stated lower bound with `α = 4` and an explicit
   positive constant `c` (a computable expression in Mathlib's Stirling
   constant `exp 1 / √(2π)`).

The constant `α = 4` is slightly weaker than the sharp `α = 2` but stronger
than what the downstream caller in the Erdős-524 proof needs.
-/

namespace Erdos524
namespace Helpers

open Real

/-!
## Elementary KL-divergence bound

We bound the Kullback–Leibler divergence
`KL(p || 1/2) = p log(2p) + (1-p) log(2(1-p))` by `4(p − 1/2)²` using only
`log x ≤ x − 1`. After rescaling `p = k/n`, this yields the log-ratio bound
we need.
-/

/-- The key elementary inequality: for `k, m : ℕ` with `k ≥ 1` and `m ≥ 1`, we have
`k · log(2k/(k+m)) + m · log(2m/(k+m)) ≤ (k − m)² / (k+m)`.

This is the "KL divergence from the uniform distribution" bounded by a
quadratic, using `log x ≤ x − 1` applied to `x = 2k/(k+m)` and `x = 2m/(k+m)`. -/
theorem kl_to_half_le_sq (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (k : ℝ) * Real.log (2 * k / (k + m)) + (m : ℝ) * Real.log (2 * m / (k + m))
      ≤ ((k : ℝ) - m) ^ 2 / (k + m) := by
  have hkpos' : (0 : ℝ) < k := by exact_mod_cast hk
  have hmpos' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < (k : ℝ) + m := by linarith
  have h1 : Real.log (2 * (k : ℝ) / (k + m)) ≤ 2 * k / (k + m) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (2 * (m : ℝ) / (k + m)) ≤ 2 * m / (k + m) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hkn : (0 : ℝ) ≤ k := hkpos'.le
  have hmn : (0 : ℝ) ≤ m := hmpos'.le
  calc (k : ℝ) * Real.log (2 * k / (k + m)) + (m : ℝ) * Real.log (2 * m / (k + m))
      ≤ (k : ℝ) * (2 * k / (k + m) - 1) + (m : ℝ) * (2 * m / (k + m) - 1) := by
        gcongr
    _ = ((k : ℝ) - m) ^ 2 / (k + m) := by
        field_simp; ring

/-- Rearranged: the log of `(2k/n)^k · (2(n-k)/n)^{n-k}` is bounded by
`(k - (n-k))²/n = (2k - n)²/n = 4 (k - n/2)² / n`. -/
theorem log_ratio_le_quad_diff (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (k : ℝ) * Real.log (2 * k / n) + ((n : ℝ) - k) * Real.log (2 * ((n : ℝ) - k) / n)
      ≤ 4 * ((k : ℝ) - n / 2) ^ 2 / n := by
  have hk_le : k ≤ n := hkn.le
  have hn : 1 ≤ n := le_trans hk hk_le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmk_pos : 1 ≤ n - k := Nat.sub_pos_of_lt hkn
  have key := kl_to_half_le_sq k (n - k) hk hnmk_pos
  -- Rewrite: (n-k : ℕ) cast to ℝ equals (n : ℝ) - (k : ℝ).
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    rw [Nat.cast_sub hk_le]
  rw [hcast] at key
  have hkn_sum : (k : ℝ) + ((n : ℝ) - k) = n := by ring
  rw [hkn_sum] at key
  -- Now key : k*log(2k/n) + (n-k)*log(2(n-k)/n) ≤ (k - (n-k))²/n
  have hrhs_eq : ((k : ℝ) - ((n : ℝ) - k)) ^ 2 / n = 4 * ((k : ℝ) - n / 2) ^ 2 / n := by
    have : ((k : ℝ) - ((n : ℝ) - k)) ^ 2 = 4 * ((k : ℝ) - n / 2) ^ 2 := by ring
    rw [this]
  linarith [key, hrhs_eq.le, hrhs_eq.ge]

/-!
## Main theorem: Gaussian lower bound on the central binomial PMF
-/

set_option maxHeartbeats 800000 in
/-- **Central binomial PMF lower bound.**

For a fair coin (Rademacher walk), the PMF at offset `d = k − n/2` satisfies
an effective Gaussian-style lower bound: there exist absolute constants
`c > 0` and `N ≥ 1` such that for all `n ≥ N` and `1 ≤ k < n`,
`C(n, k) / 2^n ≥ c · (1/√n) · exp(−4 · (k − n/2)² / n)`.

The exponent constant achieved is `α = 4`. The absolute constant `c` is given
by `√(2/π) · (√(2π)/e)³`, which comes from dividing by the cube of Mathlib's
effective Stirling ratio `exp 1 / √(2π) ≈ 1.0844`. -/
theorem centralBinom_pmf_lower_bound :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
        (n.choose k : ℝ) / (2 : ℝ) ^ n ≥
          c / Real.sqrt (n : ℝ) *
            Real.exp (-(4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
  -- Choose c = √(2/π) / (e / √(2π))³
  have hCstir_pos0 : 0 < Real.exp 1 / Real.sqrt (2 * Real.pi) := by positivity
  set Cstir : ℝ := Real.exp 1 / Real.sqrt (2 * Real.pi) with hCstir_def
  have hCstir_pos : 0 < Cstir := hCstir_pos0
  have hsqrt2pi_nn : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hsqrt2pi_pos : 0 < Real.sqrt (2 / Real.pi) := by
    apply Real.sqrt_pos.mpr
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have hc_pos0 : 0 < Real.sqrt (2 / Real.pi) / Cstir ^ 3 := by positivity
  set c : ℝ := Real.sqrt (2 / Real.pi) / Cstir ^ 3 with hc_def
  have hc_pos : 0 < c := hc_pos0
  refine ⟨c, 1, hc_pos, le_refl _, ?_⟩
  intro n hn k hk hkn
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := hn
    exact_mod_cast this
  have hkpos' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk_le_n : k ≤ n := hkn.le
  have hnmkpos : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hnmkpos' : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast hnmkpos
  have hnmk_real : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    rw [Nat.cast_sub hk_le_n]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hone_le_n : 1 ≤ n := hn
  have hone_le_k : 1 ≤ k := hk
  have hone_le_nmk : 1 ≤ n - k := hnmkpos
  -- Stirling bounds for n!, k!, (n-k)!
  have hstN_lo : Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) :=
    sqrt_two_pi_mul_pow_le_factorial n
  have hstK_hi : (k.factorial : ℝ) ≤ Cstir *
      (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k) := by
    have := factorial_le_stirling hone_le_k
    simpa [hCstir_def] using this
  have hnmk_real0 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    rw [Nat.cast_sub hk_le_n]
  have hstM_hi : ((n - k).factorial : ℝ) ≤ Cstir *
      (Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) * (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k)) := by
    have h := factorial_le_stirling hone_le_nmk
    have hrw_sqrt : Real.sqrt (2 * Real.pi * ((n - k : ℕ) : ℝ)) =
        Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) := by rw [hnmk_real0]
    rw [hrw_sqrt] at h
    simpa [hCstir_def] using h
  -- From Nat.choose_mul_factorial_mul_factorial: choose n k * k! * (n-k)! = n!
  have hchoose_eq : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hk_le_n
    exact_mod_cast this
  have hchoose_nonneg : (0 : ℝ) ≤ (n.choose k : ℝ) := by exact_mod_cast Nat.zero_le _
  have hkfact_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmfact_pos : (0 : ℝ) < ((n - k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hkfact_ne : (k.factorial : ℝ) ≠ 0 := hkfact_pos.ne'
  have hmfact_ne : ((n - k).factorial : ℝ) ≠ 0 := hmfact_pos.ne'
  -- Lower bound on choose: n! / (k! · (n-k)!) using the bounds above.
  -- Step 1: choose n k ≥ n_lo / (k_hi * m_hi).
  -- Define the Stirling parts.
  set NL : ℝ := Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n with hNL
  set KU : ℝ := Cstir * (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k) with hKU
  set MU : ℝ := Cstir * (Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) *
    (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k)) with hMU
  have hNL_pos : 0 < NL := by
    rw [hNL]
    have : 0 < Real.sqrt (2 * Real.pi * n) := Real.sqrt_pos.mpr (by positivity)
    have h1 : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
    exact mul_pos this h1
  have hKU_pos : 0 < KU := by
    rw [hKU]
    have : 0 < Real.sqrt (2 * Real.pi * k) := Real.sqrt_pos.mpr (by positivity)
    have h1 : 0 < ((k : ℝ) / Real.exp 1) ^ k := by positivity
    exact mul_pos hCstir_pos (mul_pos this h1)
  have hnmk_real_pos : (0 : ℝ) < (n : ℝ) - k := by rw [← hnmk_real0]; exact_mod_cast hnmkpos
  have hMU_pos : 0 < MU := by
    rw [hMU]
    have : 0 < Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) :=
      Real.sqrt_pos.mpr (by positivity)
    have h1 : 0 < (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k) := by positivity
    exact mul_pos hCstir_pos (mul_pos this h1)
  -- choose n k ≥ NL / (KU * MU):
  have h_choose_lb : NL / (KU * MU) ≤ (n.choose k : ℝ) := by
    rw [div_le_iff₀ (mul_pos hKU_pos hMU_pos)]
    have h1 : NL ≤ (n.factorial : ℝ) := hstN_lo
    have h2 : (n.factorial : ℝ) = (n.choose k : ℝ) * k.factorial * (n - k).factorial :=
      hchoose_eq.symm
    have h3 : (k.factorial : ℝ) ≤ KU := hstK_hi
    have h4 : ((n - k).factorial : ℝ) ≤ MU := hstM_hi
    calc NL ≤ (n.factorial : ℝ) := h1
      _ = (n.choose k : ℝ) * k.factorial * (n - k).factorial := h2
      _ ≤ (n.choose k : ℝ) * KU * MU := by
          gcongr
      _ = (n.choose k : ℝ) * (KU * MU) := by ring
  -- Now use the division by 2^n and show the target.
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h2n_ne : ((2 : ℝ) ^ n) ≠ 0 := h2n_pos.ne'
  -- (n.choose k : ℝ) / 2^n ≥ (NL / (KU * MU)) / 2^n
  have hdiv_mono : NL / (KU * MU) / (2 : ℝ) ^ n ≤ (n.choose k : ℝ) / (2 : ℝ) ^ n := by
    exact div_le_div_of_nonneg_right h_choose_lb h2n_pos.le
  -- Rewrite NL / (KU · MU · 2^n) and show it ≥ c / √n · exp(−4 d²/n).
  set RHS : ℝ := c / Real.sqrt (n : ℝ) *
    Real.exp (-(4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) with hRHS_def
  show RHS ≤ (n.choose k : ℝ) / (2 : ℝ) ^ n
  apply le_trans _ hdiv_mono
  -- Show RHS ≤ NL / (KU * MU) / 2^n = NL / (KU · MU · 2^n).
  have hKMN_pos : 0 < KU * MU * (2 : ℝ) ^ n := by positivity
  -- It's cleaner to work with NL / (KU * MU * 2^n).
  have hrw : NL / (KU * MU) / (2 : ℝ) ^ n = NL / (KU * MU * (2 : ℝ) ^ n) := by
    rw [div_div]
  rw [hrw]
  -- Now we need: RHS ≤ NL / (KU * MU * 2^n).
  -- Equivalently: RHS * (KU * MU * 2^n) ≤ NL.
  rw [le_div_iff₀ hKMN_pos]
  -- Unfold NL, KU, MU and c. Group terms.
  -- We have NL = √(2π n) · (n/e)^n
  -- KU * MU = Cstir² · √(2π k) · √(2π (n-k)) · (k/e)^k · ((n-k)/e)^{n-k}
  -- Cstir² · c = Cstir² · √(2/π) / Cstir³ = √(2/π) / Cstir
  -- Group: the "Stirling constant" cancels out except for Cstir³ that got absorbed into c.
  -- This will be a long calculation. Let me set up nicely.
  -- We'll show:  RHS * (KU * MU * 2^n) ≤ NL
  -- Define some intermediate quantities.
  -- Let
  --   A = √(2π n), Kk = (k/e)^k, Mm = ((n-k)/e)^(n-k), Nn = (n/e)^n
  --   Bk = √(2π k), Bm = √(2π (n-k))
  -- Then NL = A · Nn,  KU · MU = Cstir² · Bk · Bm · Kk · Mm.
  -- We need:
  --   c / √n · exp(−4d²/n) · Cstir² · Bk · Bm · Kk · Mm · 2^n ≤ A · Nn.
  -- Rearrange: c · Cstir² · (Bk · Bm / (A · √n)) · (Kk · Mm · 2^n / Nn) · exp(−4d²/n) ≤ 1.
  -- Step A: Kk · Mm · 2^n / Nn ≤ exp(4 d²/n).
  --   Taking log: k log(k/e) + (n-k) log((n-k)/e) + n log 2 − n log(n/e)
  --             = k log k − k + (n-k) log(n-k) − (n-k) + n log 2 − n log n + n
  --             = k log k + (n-k) log(n-k) − n log n + n log 2
  --             = k [log k − log n + log 2] + (n-k) [log(n-k) − log n + log 2]
  --             = k log(2k/n) + (n-k) log(2(n-k)/n)
  --   By log_ratio_le_quad_diff, this ≤ 4 d²/n.
  -- Step B: Bk · Bm / (A · √n) ≤ √(2π / (4π · n)) = √(1/(2n)) . Actually:
  --   Bk · Bm = √(2π k) · √(2π (n-k)) = √((2π)² · k(n-k)) = 2π · √(k(n-k)) ≤ 2π · (n/2) = πn
  --   by AM-GM: √(k(n-k)) ≤ (k + (n-k))/2 = n/2.
  --   A · √n = √(2π n) · √n = √(2π) · n.
  --   So Bk · Bm / (A · √n) ≤ πn / (√(2π) · n) = √(π/2) = √(π / 2).
  -- Step C: combine. c · Cstir² · √(π/2) · exp(−4d²/n + 4d²/n) ≤ 1.
  --   c · Cstir² · √(π/2) ≤ 1? We have c = √(2/π) / Cstir³. So:
  --   c · Cstir² · √(π/2) = Cstir² / Cstir³ · √(2/π) · √(π/2) = 1/Cstir · 1 = 1/Cstir.
  --   And 1/Cstir < 1 since Cstir = e/√(2π) ≈ 1.08 > 1.
  -- So we get  LHS ≤ 1/Cstir · NL · Cstir ... hmm. Let me just do the calculation.

  -- First extract LHS.
  -- Plan: bound
  --   Kk · Mm · 2^n ≤ Nn · exp(4 d²/n).
  -- This is Step A in multiplicative form.
  set Kk : ℝ := ((k : ℝ) / Real.exp 1) ^ k with hKk
  set Mm : ℝ := (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k) with hMm
  set Nn : ℝ := ((n : ℝ) / Real.exp 1) ^ n with hNn
  have hKk_pos : 0 < Kk := by rw [hKk]; positivity
  have hMm_pos : 0 < Mm := by rw [hMm]; positivity
  have hNn_pos : 0 < Nn := by rw [hNn]; positivity
  -- StepA:
  have hStepA : Kk * Mm * (2 : ℝ) ^ n ≤
      Nn * Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
    -- Take logs.
    have hlhs_pos : 0 < Kk * Mm * (2 : ℝ) ^ n := by positivity
    have hexp_pos : 0 < Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) :=
      Real.exp_pos _
    have hrhs_pos : 0 < Nn * Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) :=
      mul_pos hNn_pos hexp_pos
    rw [← Real.log_le_log_iff hlhs_pos hrhs_pos]
    -- Expand LHS: log(Kk * Mm * 2^n) = log Kk + log Mm + log 2^n.
    rw [Real.log_mul (mul_pos hKk_pos hMm_pos).ne' (by positivity : (2 : ℝ) ^ n ≠ 0),
        Real.log_mul hKk_pos.ne' hMm_pos.ne']
    -- Expand RHS: log(Nn * exp(...)) = log Nn + (...).
    rw [Real.log_mul hNn_pos.ne' hexp_pos.ne', Real.log_exp]
    -- Expand the pow-logs.
    have hKk_log : Real.log Kk = (k : ℝ) * (Real.log k - 1) := by
      rw [hKk, Real.log_pow, Real.log_div hkpos'.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have hMm_log : Real.log Mm = ((n : ℝ) - k) * (Real.log ((n : ℝ) - k) - 1) := by
      rw [hMm, Real.log_pow,
          Real.log_div hnmkpos'.ne' (Real.exp_pos 1).ne', Real.log_exp, hnmk_real]
    have hNn_log : Real.log Nn = (n : ℝ) * (Real.log n - 1) := by
      rw [hNn, Real.log_pow, Real.log_div hnpos.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have h2n_log : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [hKk_log, hMm_log, hNn_log, h2n_log]
    -- Now both sides are explicit sums of real terms.
    -- Goal: k*(log k - 1) + (n-k)*(log(n-k) - 1) + n*log 2
    --       ≤ n*(log n - 1) + 4 * d² / n
    -- Use log_ratio_le_quad_diff: k*log(2k/n) + (n-k)*log(2(n-k)/n) ≤ 4 d²/n.
    have hmain := log_ratio_le_quad_diff n k hone_le_k hkn
    -- Expand log(2k/n) and log(2(n-k)/n) in hmain.
    have hnmk_pos : (0 : ℝ) < (n : ℝ) - k := by rw [← hnmk_real]; exact hnmkpos'
    have hklog : (k : ℝ) * Real.log (2 * k / n) =
        (k : ℝ) * Real.log 2 + (k : ℝ) * Real.log k - (k : ℝ) * Real.log n := by
      rw [show (2 * (k : ℝ) / n) = 2 * k * (n : ℝ)⁻¹ by field_simp]
      rw [Real.log_mul (by positivity) (inv_ne_zero hnpos.ne'),
          Real.log_mul (by norm_num) hkpos'.ne',
          Real.log_inv]
      ring
    have hmlog : ((n : ℝ) - k) * Real.log (2 * ((n : ℝ) - k) / n) =
        ((n : ℝ) - k) * Real.log 2 + ((n : ℝ) - k) * Real.log ((n : ℝ) - k) -
        ((n : ℝ) - k) * Real.log n := by
      rw [show (2 * ((n : ℝ) - k) / n) = 2 * ((n : ℝ) - k) * (n : ℝ)⁻¹ by field_simp]
      rw [Real.log_mul (by positivity) (inv_ne_zero hnpos.ne'),
          Real.log_mul (by norm_num) hnmk_pos.ne',
          Real.log_inv]
      ring
    rw [hklog, hmlog] at hmain
    have hlogn_split : (n : ℝ) * Real.log n =
        (k : ℝ) * Real.log n + ((n : ℝ) - k) * Real.log n := by ring
    have hlog2_split : (n : ℝ) * Real.log 2 =
        (k : ℝ) * Real.log 2 + ((n : ℝ) - k) * Real.log 2 := by ring
    linarith [hmain, hlogn_split, hlog2_split]
  -- StepB:
  have hStepB_sq : Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k))
      ≤ Real.pi * n := by
    have h_amgm : (k : ℝ) * ((n : ℝ) - k) ≤ ((n : ℝ) / 2) ^ 2 := by
      -- (k - (n-k))² ≥ 0 ⟹ k² + (n-k)² ≥ 2k(n-k) ⟹ (k + (n-k))² ≥ 4 k (n-k)
      nlinarith [sq_nonneg ((k : ℝ) - ((n : ℝ) - k))]
    have hprod_eq :
        Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) =
          Real.sqrt ((2 * Real.pi) ^ 2 * ((k : ℝ) * ((n : ℝ) - k))) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    rw [hprod_eq]
    have hbd : (2 * Real.pi) ^ 2 * ((k : ℝ) * ((n : ℝ) - k))
        ≤ (2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2 := by
      have h2pi_sq_nn : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_left h_amgm h2pi_sq_nn
    have hbd_sqrt : Real.sqrt ((2 * Real.pi) ^ 2 * ((k : ℝ) * ((n : ℝ) - k)))
        ≤ Real.sqrt ((2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2) :=
      Real.sqrt_le_sqrt hbd
    have heval : Real.sqrt ((2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2) = Real.pi * n := by
      rw [show (2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2 = (Real.pi * n) ^ 2 by ring]
      rw [Real.sqrt_sq (by positivity)]
    linarith [hbd_sqrt, heval.le]
  -- Step combining: we want RHS * (KU * MU * 2^n) ≤ NL.
  -- Expand:
  --  KU * MU = Cstir² · √(2πk) · √(2π(n-k)) · Kk · Mm
  --  NL = √(2πn) · Nn
  --  RHS * KU * MU * 2^n = c/√n · exp(−4d²/n) · Cstir² · √(2πk) · √(2π(n-k)) · Kk · Mm · 2^n
  -- Using StepA: Kk · Mm · 2^n ≤ Nn · exp(4d²/n). So
  --  RHS · KU · MU · 2^n ≤ c/√n · exp(−4d²/n) · Cstir² · √(2πk) · √(2π(n-k)) · Nn · exp(4d²/n)
  --                    = c/√n · Cstir² · √(2πk) · √(2π(n-k)) · Nn.
  -- Using StepB: √(2πk) · √(2π(n-k)) ≤ π n. So
  --                    ≤ c/√n · Cstir² · π n · Nn
  --                    = c · Cstir² · π · √n · Nn.
  -- We want this ≤ NL = √(2πn) · Nn = √(2π) · √n · Nn.
  -- Divide both sides by √n · Nn (positive): need c · Cstir² · π ≤ √(2π), i.e.
  --   c · Cstir² ≤ √(2π) / π = √(2/π).
  -- With c = √(2/π) / Cstir³:  c · Cstir² = √(2/π) / Cstir ≤ √(2/π). True since Cstir ≥ 1.
  -- We need Cstir ≥ 1:  Cstir = exp(1) / √(2π) ≈ 2.718 / 2.507 ≈ 1.084 ≥ 1. ✓
  -- Actually we need Cstir > 0 which gives c · Cstir² ≤ √(2/π) iff 1/Cstir ≤ 1, iff Cstir ≥ 1.

  -- Let me prove this combining step rigorously.
  have hCstir_ge_one : 1 ≤ Cstir := by
    rw [hCstir_def]
    rw [le_div_iff₀ (Real.sqrt_pos.mpr h2pi)]
    rw [one_mul]
    -- Need: √(2π) ≤ exp 1 = e
    have hexp1_sq : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    have h2pi_le_e2 : 2 * Real.pi ≤ Real.exp 2 := by
      have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
      have hexp2 : (7.3 : ℝ) ≤ Real.exp 2 := by
        have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        nlinarith [Real.exp_pos 1, hexp1_sq]
      linarith
    have hmono : Real.sqrt (2 * Real.pi) ≤ Real.sqrt (Real.exp 2) :=
      Real.sqrt_le_sqrt h2pi_le_e2
    have h_sqrt_exp2 : Real.sqrt (Real.exp 2) = Real.exp 1 := by
      have hexp2_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [hexp2_eq, Real.sqrt_mul_self (Real.exp_pos 1).le]
    rw [h_sqrt_exp2] at hmono
    exact hmono
  have hfinal : c * Cstir ^ 2 ≤ Real.sqrt (2 / Real.pi) := by
    rw [hc_def]
    have hCube : Cstir ^ 3 = Cstir ^ 2 * Cstir := by ring
    have hCstir2_ne : (Cstir ^ 2 : ℝ) ≠ 0 := by positivity
    rw [show (Real.sqrt (2 / Real.pi) / Cstir ^ 3) * Cstir ^ 2 =
          Real.sqrt (2 / Real.pi) / Cstir by
        rw [hCube]; field_simp]
    have h1 : Real.sqrt (2 / Real.pi) / Cstir ≤ Real.sqrt (2 / Real.pi) / 1 := by
      apply div_le_div_of_nonneg_left hsqrt2pi_nn zero_lt_one hCstir_ge_one
    simpa using h1
  -- Now combine everything.
  -- Goal: RHS * (KU * MU * 2^n) ≤ NL
  --   RHS = c / √n * exp(−4d²/n)
  --   KU = Cstir * √(2πk) * (k/e)^k = Cstir * √(2πk) * Kk
  --   MU = Cstir * √(2π(n-k)) * ((n-k)/e)^(n-k) = Cstir * √(2π(n-k)) * Mm
  --   NL = √(2πn) * (n/e)^n = √(2πn) * Nn
  have hKU_expand : KU = Cstir * (Real.sqrt (2 * Real.pi * k) * Kk) := rfl
  have hMU_expand : MU = Cstir * (Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) * Mm) := rfl
  have hKUMU : KU * MU = Cstir ^ 2 *
      (Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k))) *
      (Kk * Mm) := by
    rw [hKU_expand, hMU_expand]; ring
  rw [hKUMU]
  -- Group factors: RHS * (Cstir² · S · K·M · 2^n) = RHS · Cstir² · S · (K · M · 2^n)
  -- with S = √(2πk) · √(2π(n-k)).
  set S : ℝ := Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) with hSdef
  have hS_pos : 0 < S := by
    rw [hSdef]
    have h1 : 0 < Real.sqrt (2 * Real.pi * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    have hnmk_pos : (0 : ℝ) < (n : ℝ) - k := by rw [← hnmk_real]; exact hnmkpos'
    have h2 : 0 < Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) := Real.sqrt_pos.mpr (by positivity)
    exact mul_pos h1 h2
  have hSle : S ≤ Real.pi * n := hStepB_sq
  -- Rearrange goal.
  have hReg : RHS * (Cstir ^ 2 * S * (Kk * Mm) * (2 : ℝ) ^ n) =
      RHS * Cstir ^ 2 * S * (Kk * Mm * (2 : ℝ) ^ n) := by ring
  rw [hReg]
  -- RHS · Cstir² · S · (Kk · Mm · 2^n) ≤ RHS · Cstir² · S · (Nn · exp(4d²/n))   [by StepA]
  -- RHS = c/√n · exp(−4d²/n), so RHS · exp(4d²/n) = c / √n.
  -- So ≤ c/√n · Cstir² · S · Nn ≤ c/√n · Cstir² · π n · Nn = c · Cstir² · π · √n · Nn.
  -- And NL = √(2π) · √n · Nn. So comparison reduces to c · Cstir² · π ≤ √(2π).
  have hRHS_pos : 0 < RHS := by
    rw [hRHS_def]
    positivity
  have hCstir2_pos : 0 < Cstir ^ 2 := by positivity
  have hPiN_pos : 0 < Real.pi * (n : ℝ) := by positivity
  -- Step 1: use StepA.
  have h_step1 : RHS * Cstir ^ 2 * S * (Kk * Mm * (2 : ℝ) ^ n) ≤
      RHS * Cstir ^ 2 * S * (Nn * Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ))) := by
    have hfactor_nn : 0 ≤ RHS * Cstir ^ 2 * S := by
      have := mul_pos (mul_pos hRHS_pos hCstir2_pos) hS_pos
      linarith
    exact mul_le_mul_of_nonneg_left hStepA hfactor_nn
  -- Step 2: simplify RHS · exp(4 d²/n) = c/√n.
  have h_RHS_exp : RHS * Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ))
      = c / Real.sqrt n := by
    rw [hRHS_def]
    rw [mul_assoc, ← Real.exp_add]
    rw [show -(4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ) +
        4 * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / n = 0 by ring]
    rw [Real.exp_zero, mul_one]
  have h_step2_eq : RHS * Cstir ^ 2 * S * (Nn * Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)))
      = c / Real.sqrt n * Cstir ^ 2 * S * Nn := by
    have : RHS * Cstir ^ 2 * S * (Nn * Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)))
        = (RHS * Real.exp ((4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ))) * Cstir ^ 2 * S * Nn := by
      ring
    rw [this, h_RHS_exp]
  -- Step 3: use StepB (S ≤ πn).
  have h_step3 : c / Real.sqrt n * Cstir ^ 2 * S * Nn ≤
      c / Real.sqrt n * Cstir ^ 2 * (Real.pi * n) * Nn := by
    have hfactor_nn : 0 ≤ c / Real.sqrt n * Cstir ^ 2 := by
      have : 0 < c / Real.sqrt n := by
        apply div_pos hc_pos
        exact Real.sqrt_pos.mpr hnpos
      have := mul_pos this hCstir2_pos
      linarith
    have hNn_nn : 0 ≤ Nn := hNn_pos.le
    nlinarith [mul_le_mul_of_nonneg_left hSle hfactor_nn, hNn_pos.le]
  -- Step 4: show the final product ≤ NL = √(2πn) · Nn.
  have hfinal_ineq : c / Real.sqrt n * Cstir ^ 2 * (Real.pi * n) * Nn ≤ NL := by
    rw [hNL]
    -- c / √n · Cstir² · π · n · Nn ≤ √(2πn) · Nn
    have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsqrt2pi : Real.sqrt (2 * Real.pi * n) = Real.sqrt (2 * Real.pi) * Real.sqrt n := by
      rw [show (2 * Real.pi * (n : ℝ)) = (2 * Real.pi) * n by ring]
      exact Real.sqrt_mul h2pi.le _
    rw [hsqrt2pi]
    have hNn_nn : 0 ≤ Nn := hNn_pos.le
    -- We aim: LHS = c · Cstir² · π · √n · Nn ≤ √(2π) · √n · Nn.
    -- Need: c · Cstir² · π ≤ √(2π).
    have hineq_scalar : c * Cstir ^ 2 * Real.pi ≤ Real.sqrt (2 * Real.pi) := by
      have h1 : c * Cstir ^ 2 * Real.pi ≤ Real.sqrt (2 / Real.pi) * Real.pi :=
        mul_le_mul_of_nonneg_right hfinal hpi.le
      have h2 : Real.sqrt (2 / Real.pi) * Real.pi = Real.sqrt (2 * Real.pi) := by
        have hpi_sq : Real.pi = Real.sqrt (Real.pi ^ 2) := by
          rw [Real.sqrt_sq hpi.le]
        rw (occs := [2]) [hpi_sq]
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        field_simp
      linarith [h1, h2.le, h2.ge]
    -- Now assemble.
    have hdiv : (n : ℝ) / Real.sqrt n = Real.sqrt n := by
      rw [div_eq_iff hsqrtn_pos.ne']
      exact (Real.mul_self_sqrt hnpos.le).symm
    calc c / Real.sqrt n * Cstir ^ 2 * (Real.pi * n) * Nn
        = c * Cstir ^ 2 * Real.pi * ((n : ℝ) / Real.sqrt n) * Nn := by ring
      _ = c * Cstir ^ 2 * Real.pi * Real.sqrt n * Nn := by rw [hdiv]
      _ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt n * Nn :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hineq_scalar hsqrtn_pos.le) hNn_nn
  linarith [h_step1, h_step2_eq.le, h_step2_eq.ge, h_step3, hfinal_ineq]

/-!
## Sharper KL bound (Option C partial improvement)

The `kl_to_half_le_sq` bound uses only `log x ≤ x − 1`, which is the tangent
line to `log` at `x = 1`. Near `x = 1` the quadratic correction in Taylor's
theorem gives `log x ≤ (x − 1) − (x − 1)² / 2 + …`, which one could exploit
to drop the constant `4` in `log_ratio_le_quad_diff` down toward the sharp
`2`. Formalising this in Lean cleanly requires a second-order log bound such
as `log(1 + u) ≤ u − u²/2 + u³/3` (valid on `[0, ∞)`) together with
`log(1 − u) ≤ −u − u²/2` (valid on `[0, 1)`), each proved via a derivative
sign argument.

Below we record a *symmetric reformulation* of `kl_to_half_le_sq` that will
be the natural drop-in when that second-order bound is available: it phrases
the bound using the identity
`(k − m)² / (k + m) = 4 (k − n/2)² / n` (with `m = n − k`) and is already
what downstream code uses. We also record explicitly the identity
`L(k, m) = ((k + m) / 2) · [log(1 − y²) + y · log((1 + y)/(1 − y))]`
(with `y = (k − m)/(k + m)`) that is the entry point for a future sharp
proof yielding `α = 2 + ε` under a regime `|k − n/2| ≤ c · n` with `c` small.

The downstream caller in `524.lean` (sorry #2) genuinely requires `α = 2`,
so delivering the sharp bound is future work. The reformulation here is a
no-cost refactor: it adds a clearer named lemma without weakening anything. -/

/-- Reformulation of `kl_to_half_le_sq` in the `(n, k)` coordinates used by
the downstream central binomial bound, packaged so that the sharp variant
(with constant `2` replacing `4` under a regime hypothesis) can later be
stated with the same shape.

Currently this is just a wrapper around `log_ratio_le_quad_diff`; the
exponent constant is `4`. -/
theorem log_ratio_le_quad_diff_alpha_four (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (k : ℝ) * Real.log (2 * k / n) + ((n : ℝ) - k) * Real.log (2 * ((n : ℝ) - k) / n)
      ≤ 4 * ((k : ℝ) - n / 2) ^ 2 / n :=
  log_ratio_le_quad_diff n k hk hkn

/-- Algebraic identity underlying the sharp proof path: for `k, m ≥ 1`, the
KL-from-uniform quantity `k · log(2k/(k+m)) + m · log(2m/(k+m))` can be
rewritten as
`((k + m)/2) · [log(1 − y²) + y · log((1 + y)/(1 − y))]` with
`y = (k − m)/(k + m) ∈ (−1, 1)`.

Combined with `log(1 − y²) ≤ −y²` (true unconditionally for `|y| < 1`) and
`log((1 + y)/(1 − y)) ≤ 2y/(1 − y²)` (valid for `y ∈ [0, 1)`, symmetric
version for `y ∈ (−1, 0]`), this yields the sharp bound
`L(k, m) ≤ (k − m)² · (k² + m²) / (4 k m (k + m))`
which under the regime `(k − n/2)² ≤ η · n²` with `η` small gives
the exponent constant `α = 2 + O(η)`. The `log((1 + y)/(1 − y)) ≤ 2y/(1 − y²)`
step is the obstruction: it requires a sharper log inequality than
`log x ≤ x − 1`, which we do not prove here. -/
theorem kl_to_half_rewrite (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (k : ℝ) * Real.log (2 * k / (k + m)) + (m : ℝ) * Real.log (2 * m / (k + m)) =
      ((k : ℝ) + m) / 2 * Real.log (1 - ((k : ℝ) - m) ^ 2 / ((k : ℝ) + m) ^ 2) +
      ((k : ℝ) - m) / 2 *
        (Real.log (2 * k / ((k : ℝ) + m)) - Real.log (2 * m / ((k : ℝ) + m))) := by
  have hkpos' : (0 : ℝ) < k := by exact_mod_cast hk
  have hmpos' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < (k : ℝ) + m := by linarith
  have hn_ne : ((k : ℝ) + m) ≠ 0 := hn'.ne'
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) / ((k : ℝ) + m) := by positivity
  have h2m_pos : (0 : ℝ) < 2 * (m : ℝ) / ((k : ℝ) + m) := by positivity
  have hprod_pos : (0 : ℝ) < (2 * (k : ℝ) / ((k : ℝ) + m)) * (2 * (m : ℝ) / ((k : ℝ) + m)) :=
    mul_pos h2k_pos h2m_pos
  -- Express `1 - y²` as `(2k/(k+m)) * (2m/(k+m))`: `1 - ((k-m)/(k+m))² = 4km/(k+m)²`.
  have hprod_eq : (2 * (k : ℝ) / ((k : ℝ) + m)) * (2 * (m : ℝ) / ((k : ℝ) + m)) =
      1 - ((k : ℝ) - m) ^ 2 / ((k : ℝ) + m) ^ 2 := by
    field_simp
    ring
  -- So `log(1 - y²) = log(2k/(k+m)) + log(2m/(k+m))`.
  have hlog_sum : Real.log (1 - ((k : ℝ) - m) ^ 2 / ((k : ℝ) + m) ^ 2) =
      Real.log (2 * (k : ℝ) / ((k : ℝ) + m)) + Real.log (2 * (m : ℝ) / ((k : ℝ) + m)) := by
    rw [← hprod_eq, Real.log_mul h2k_pos.ne' h2m_pos.ne']
  rw [hlog_sum]
  ring

/-!
## Second-order log inequalities (for the sharp KL bound)

We prove `log(1+u) ≤ u − u²/2 + u³/3` for `u ≥ 0` and
`log(1−u) ≤ −u − u²/2` for `u ∈ [0, 1)`, each via a monotonicity argument on
an auxiliary function whose derivative simplifies to a manifestly
nonnegative rational expression. These are the ingredients for a sharper
KL-divergence bound with leading constant `1/2` rather than `1`.
-/

/-- For `u ≥ 0`, `log(1 + u) ≤ u − u²/2 + u³/3`.

The proof uses that the function `g(u) = u − u²/2 + u³/3 − log(1 + u)` has
derivative `u³/(1 + u) ≥ 0` on `[0, ∞)` and satisfies `g(0) = 0`. -/
theorem log_one_add_le_cubic {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  set g : ℝ → ℝ := fun x => x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x) with hg_def
  -- Show g is monotone on [0, ∞) and g(0) = 0.
  have hg_zero : g 0 = 0 := by simp [hg_def]
  have hderiv : ∀ x ∈ Set.Ioi (-1 : ℝ), HasDerivAt g (x ^ 3 / (1 + x)) x := by
    intro x hx
    have hx' : 1 + x > 0 := by simp at hx; linarith
    have hx_ne : 1 + x ≠ 0 := hx'.ne'
    have h1 : HasDerivAt (fun y => y - y ^ 2 / 2 + y ^ 3 / 3) (1 - x + x ^ 2) x := by
      have hA : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
      have hB : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        simpa using this
      have hC : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 3
        simpa using this
      have := (hA.sub hB).add hC
      convert this using 1
    have h2 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      have hlog : HasDerivAt Real.log (1 + x)⁻¹ (1 + x) := Real.hasDerivAt_log hx_ne
      have hin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        have := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
        simpa using this
      have := hlog.comp x hin
      simpa [one_div, mul_comm] using this
    have := h1.sub h2
    convert this using 1
    have : x ^ 3 / (1 + x) = 1 - x + x ^ 2 - 1 / (1 + x) := by
      field_simp
      ring
    linarith [this.le, this.ge]
  -- g is monotone on [0, ∞).
  have hmono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · -- ContinuousOn g (Set.Ici 0)
      intro x hx
      have hxIoi : x ∈ Set.Ioi (-1 : ℝ) := by
        simp only [Set.mem_Ici] at hx
        simp only [Set.mem_Ioi]; linarith
      exact ((hderiv x hxIoi).continuousAt).continuousWithinAt
    · -- DifferentiableOn g (interior (Set.Ici 0))
      intro x hx
      rw [interior_Ici] at hx
      have : x ∈ Set.Ioi (-1 : ℝ) := by simp at hx ⊢; linarith
      exact (hderiv x this).differentiableAt.differentiableWithinAt
    · -- Nonneg derivative on interior.
      intro x hx
      rw [interior_Ici] at hx
      have hxIoi : x ∈ Set.Ioi (-1 : ℝ) := by simp at hx ⊢; linarith
      have hderivx : deriv g x = x ^ 3 / (1 + x) := (hderiv x hxIoi).deriv
      rw [hderivx]
      have hxpos : 0 < x := hx
      have h1x : 0 < 1 + x := by linarith
      positivity
  have hg_u : 0 ≤ g u := by
    have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.left_mem_Ici
    have hu' : u ∈ Set.Ici (0 : ℝ) := hu
    have := hmono h0 hu' hu
    rw [hg_zero] at this
    exact this
  -- g u ≥ 0 means u - u²/2 + u³/3 ≥ log(1+u).
  have : Real.log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
    have := hg_u
    simp [hg_def] at this
    linarith
  exact this

/-- For `u ∈ [0, 1)`, `log(1 − u) ≤ −u − u²/2`.

The proof uses that the function `h(u) = −u − u²/2 − log(1 − u)` has
derivative `u²/(1 − u) ≥ 0` on `[0, 1)` and satisfies `h(0) = 0`. -/
theorem log_one_sub_le_quad {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    Real.log (1 - u) ≤ -u - u ^ 2 / 2 := by
  set h : ℝ → ℝ := fun x => -x - x ^ 2 / 2 - Real.log (1 - x) with hh_def
  have hh_zero : h 0 = 0 := by simp [hh_def]
  have hderiv : ∀ x ∈ Set.Iio (1 : ℝ), HasDerivAt h (x ^ 2 / (1 - x)) x := by
    intro x hx
    have hx' : 1 - x > 0 := by simp at hx; linarith
    have hx_ne : 1 - x ≠ 0 := hx'.ne'
    have h1 : HasDerivAt (fun y : ℝ => -y - y ^ 2 / 2) (-1 - x) x := by
      have hA : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
      have hB : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        simpa using this
      have := hA.sub hB
      convert this using 1
    have h2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
      have hlog : HasDerivAt Real.log (1 - x)⁻¹ (1 - x) := Real.hasDerivAt_log hx_ne
      have hin : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        have := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
        simpa using this
      have := hlog.comp x hin
      simpa [mul_comm, neg_div] using this
    have := h1.sub h2
    convert this using 1
    have : x ^ 2 / (1 - x) = -1 - x - (-1 / (1 - x)) := by
      field_simp
      ring
    linarith [this.le, this.ge]
  have hmono : MonotoneOn h (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro x hx
      simp only [Set.mem_Ico] at hx
      have hxIio : x ∈ Set.Iio (1 : ℝ) := Set.mem_Iio.mpr hx.2
      exact ((hderiv x hxIio).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      have hxIio : x ∈ Set.Iio (1 : ℝ) := by simp at hx; exact hx.2
      exact (hderiv x hxIio).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      have hxIio : x ∈ Set.Iio (1 : ℝ) := by simp at hx; exact hx.2
      have hderivx : deriv h x = x ^ 2 / (1 - x) := (hderiv x hxIio).deriv
      rw [hderivx]
      have hxpos : 0 < x := hx.1
      have h1x : 0 < 1 - x := by simp at hx; linarith [hx.2]
      positivity
  have hu_mem : u ∈ Set.Ico (0 : ℝ) 1 := ⟨hu, hu1⟩
  have h0_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hh_u : 0 ≤ h u := by
    have := hmono h0_mem hu_mem hu
    rw [hh_zero] at this
    exact this
  have : Real.log (1 - u) ≤ -u - u ^ 2 / 2 := by
    have := hh_u
    simp [hh_def] at this
    linarith
  exact this

/-!
## Sharp KL bound

Using the second-order log inequalities above we obtain
`k · log(2k/(k+m)) + m · log(2m/(k+m))
  ≤ (k − m)² / (2(k + m)) + |k − m|³ / (3(k + m)²)`.
The leading coefficient is `1/2` (halved relative to `kl_to_half_le_sq`),
and the additive cubic correction is negligible in the regime
`|k − m| ≪ (k + m)`.
-/

/-- **Sharp KL-to-uniform bound.** For `k, m ≥ 1`, we have
`k · log(2k/(k+m)) + m · log(2m/(k+m))
    ≤ (k − m)²/(2(k + m)) + |k − m|³/(3(k + m)²)`.

The proof splits on the sign of `k − m` and applies `log_one_add_le_cubic`
to the larger of the two terms and `log_one_sub_le_quad` to the smaller.
The leading quadratic coefficient `1/2` is sharp (compare
`kl_to_half_le_sq`, which has coefficient `1`). -/
theorem kl_to_half_le_sq_sharp (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (k : ℝ) * Real.log (2 * k / (k + m)) + (m : ℝ) * Real.log (2 * m / (k + m))
      ≤ ((k : ℝ) - m) ^ 2 / (2 * ((k : ℝ) + m)) +
        |(k : ℝ) - m| ^ 3 / (3 * ((k : ℝ) + m) ^ 2) := by
  have hkpos' : (0 : ℝ) < k := by exact_mod_cast hk
  have hmpos' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < (k : ℝ) + m := by linarith
  have hn_ne : ((k : ℝ) + m) ≠ 0 := hn'.ne'
  have hn2_pos : (0 : ℝ) < ((k : ℝ) + m) ^ 2 := by positivity
  have hn3_pos : (0 : ℝ) < ((k : ℝ) + m) ^ 3 := by positivity
  -- WLOG k ≥ m (otherwise swap).
  rcases le_or_gt (m : ℝ) k with hkm | hkm
  · -- Case k ≥ m: let u = (k-m)/(k+m) ∈ [0, 1).
    set u : ℝ := ((k : ℝ) - m) / ((k : ℝ) + m) with hu_def
    have hu_nn : 0 ≤ u := div_nonneg (by linarith) hn'.le
    have hu_lt_one : u < 1 := by rw [hu_def, div_lt_one hn']; linarith
    have h1pu : 1 + u = 2 * (k : ℝ) / ((k : ℝ) + m) := by
      rw [hu_def]; field_simp; ring
    have h1mu : 1 - u = 2 * (m : ℝ) / ((k : ℝ) + m) := by
      rw [hu_def]; field_simp; ring
    have hlog_kp : Real.log (2 * (k : ℝ) / ((k : ℝ) + m)) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
      rw [← h1pu]; exact log_one_add_le_cubic hu_nn
    have hlog_mp : Real.log (2 * (m : ℝ) / ((k : ℝ) + m)) ≤ -u - u ^ 2 / 2 := by
      rw [← h1mu]; exact log_one_sub_le_quad hu_nn hu_lt_one
    have hkey : (k : ℝ) * Real.log (2 * k / ((k : ℝ) + m)) +
        (m : ℝ) * Real.log (2 * m / ((k : ℝ) + m)) ≤
          (k : ℝ) * (u - u ^ 2 / 2 + u ^ 3 / 3) + (m : ℝ) * (-u - u ^ 2 / 2) := by
      have hk_nn : (0 : ℝ) ≤ k := hkpos'.le
      have hm_nn : (0 : ℝ) ≤ m := hmpos'.le
      gcongr
    have habs_eq : |(k : ℝ) - m| = (k : ℝ) - m := abs_of_nonneg (by linarith)
    -- Key polynomial identity: after clearing denominators, we compare
    -- LHS = (k-m)²/(2(k+m)) + k(k-m)³/(3(k+m)³)
    -- RHS = (k-m)²/(2(k+m)) + (k-m)³/(3(k+m)²)
    -- The difference RHS - LHS = m(k-m)³/(3(k+m)³) ≥ 0.
    have hkm_cub_nn : 0 ≤ ((k : ℝ) - m) ^ 3 := by
      have : 0 ≤ (k : ℝ) - m := by linarith
      positivity
    have hdiff_nn : 0 ≤ (m : ℝ) * ((k : ℝ) - m) ^ 3 / (3 * ((k : ℝ) + m) ^ 3) := by
      apply div_nonneg
      · exact mul_nonneg hmpos'.le hkm_cub_nn
      · positivity
    -- RHS = (k-m)²/(2(k+m)) + (k-m)³/(3(k+m)²)  (using habs_eq)
    -- LHS upper bound after expansion of u: (k-m)²/(2(k+m)) + k(k-m)³/(3(k+m)³)
    have hLHS_eq : (k : ℝ) * (u - u ^ 2 / 2 + u ^ 3 / 3) + (m : ℝ) * (-u - u ^ 2 / 2) =
        ((k : ℝ) - m) ^ 2 / (2 * ((k : ℝ) + m)) +
          (k : ℝ) * ((k : ℝ) - m) ^ 3 / (3 * ((k : ℝ) + m) ^ 3) := by
      rw [hu_def]
      field_simp
      ring
    have hRHS_split : ((k : ℝ) - m) ^ 2 / (2 * ((k : ℝ) + m)) +
        |(k : ℝ) - m| ^ 3 / (3 * ((k : ℝ) + m) ^ 2) =
        ((k : ℝ) - m) ^ 2 / (2 * ((k : ℝ) + m)) +
          ((k : ℝ) - m) ^ 3 / (3 * ((k : ℝ) + m) ^ 2) := by
      rw [habs_eq]
    rw [hRHS_split]
    calc (k : ℝ) * Real.log (2 * k / ((k : ℝ) + m)) +
          (m : ℝ) * Real.log (2 * m / ((k : ℝ) + m))
        ≤ (k : ℝ) * (u - u ^ 2 / 2 + u ^ 3 / 3) + (m : ℝ) * (-u - u ^ 2 / 2) := hkey
      _ = ((k : ℝ) - m) ^ 2 / (2 * ((k : ℝ) + m)) +
          (k : ℝ) * ((k : ℝ) - m) ^ 3 / (3 * ((k : ℝ) + m) ^ 3) := hLHS_eq
      _ ≤ ((k : ℝ) - m) ^ 2 / (2 * ((k : ℝ) + m)) +
          ((k : ℝ) - m) ^ 3 / (3 * ((k : ℝ) + m) ^ 2) := by
          have hineq : (k : ℝ) * ((k : ℝ) - m) ^ 3 / (3 * ((k : ℝ) + m) ^ 3) ≤
              ((k : ℝ) - m) ^ 3 / (3 * ((k : ℝ) + m) ^ 2) := by
            -- k/(k+m)³ ≤ 1/(k+m)², i.e., k ≤ (k+m), since (k+m)² > 0.
            have hk_le : (k : ℝ) ≤ (k : ℝ) + m := by linarith
            have hkm_nn : 0 ≤ (k : ℝ) + m := hn'.le
            have hD1_pos : (0 : ℝ) < 3 * ((k : ℝ) + m) ^ 3 := by positivity
            have hD2_pos : (0 : ℝ) < 3 * ((k : ℝ) + m) ^ 2 := by positivity
            rw [div_le_div_iff₀ hD1_pos hD2_pos]
            nlinarith [hkm_cub_nn, hkm_nn, hn2_pos.le, hn'.le, hk_le,
              mul_nonneg hkm_cub_nn (mul_nonneg hkm_nn hkm_nn),
              mul_le_mul_of_nonneg_right hk_le (mul_nonneg hkm_cub_nn (sq_nonneg ((k : ℝ) + m)))]
          linarith
  · -- Case m > k: symmetric. Let u = (m-k)/(k+m).
    set u : ℝ := ((m : ℝ) - k) / ((k : ℝ) + m) with hu_def
    have hu_nn : 0 ≤ u := div_nonneg (by linarith) hn'.le
    have hu_lt_one : u < 1 := by rw [hu_def, div_lt_one hn']; linarith
    have h1pu : 1 + u = 2 * (m : ℝ) / ((k : ℝ) + m) := by
      rw [hu_def]; field_simp; ring
    have h1mu : 1 - u = 2 * (k : ℝ) / ((k : ℝ) + m) := by
      rw [hu_def]; field_simp; ring
    have hlog_mp : Real.log (2 * (m : ℝ) / ((k : ℝ) + m)) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
      rw [← h1pu]; exact log_one_add_le_cubic hu_nn
    have hlog_kp : Real.log (2 * (k : ℝ) / ((k : ℝ) + m)) ≤ -u - u ^ 2 / 2 := by
      rw [← h1mu]; exact log_one_sub_le_quad hu_nn hu_lt_one
    have hkey : (k : ℝ) * Real.log (2 * k / ((k : ℝ) + m)) +
        (m : ℝ) * Real.log (2 * m / ((k : ℝ) + m)) ≤
          (k : ℝ) * (-u - u ^ 2 / 2) + (m : ℝ) * (u - u ^ 2 / 2 + u ^ 3 / 3) := by
      have hk_nn : (0 : ℝ) ≤ k := hkpos'.le
      have hm_nn : (0 : ℝ) ≤ m := hmpos'.le
      gcongr
    have habs_eq : |(k : ℝ) - m| = (m : ℝ) - k := by
      rw [abs_of_nonpos (by linarith)]; ring
    have habs3 : |(k : ℝ) - m| ^ 3 = ((m : ℝ) - k) ^ 3 := by rw [habs_eq]
    have hsqeq : ((k : ℝ) - m) ^ 2 = ((m : ℝ) - k) ^ 2 := by ring
    have hmk_cub_nn : 0 ≤ ((m : ℝ) - k) ^ 3 := by
      have : 0 ≤ (m : ℝ) - k := by linarith
      positivity
    have hLHS_eq : (k : ℝ) * (-u - u ^ 2 / 2) + (m : ℝ) * (u - u ^ 2 / 2 + u ^ 3 / 3) =
        ((m : ℝ) - k) ^ 2 / (2 * ((k : ℝ) + m)) +
          (m : ℝ) * ((m : ℝ) - k) ^ 3 / (3 * ((k : ℝ) + m) ^ 3) := by
      rw [hu_def]
      field_simp
      ring
    rw [hsqeq, habs3]
    calc (k : ℝ) * Real.log (2 * k / ((k : ℝ) + m)) +
          (m : ℝ) * Real.log (2 * m / ((k : ℝ) + m))
        ≤ (k : ℝ) * (-u - u ^ 2 / 2) + (m : ℝ) * (u - u ^ 2 / 2 + u ^ 3 / 3) := hkey
      _ = ((m : ℝ) - k) ^ 2 / (2 * ((k : ℝ) + m)) +
          (m : ℝ) * ((m : ℝ) - k) ^ 3 / (3 * ((k : ℝ) + m) ^ 3) := hLHS_eq
      _ ≤ ((m : ℝ) - k) ^ 2 / (2 * ((k : ℝ) + m)) +
          ((m : ℝ) - k) ^ 3 / (3 * ((k : ℝ) + m) ^ 2) := by
          have hineq : (m : ℝ) * ((m : ℝ) - k) ^ 3 / (3 * ((k : ℝ) + m) ^ 3) ≤
              ((m : ℝ) - k) ^ 3 / (3 * ((k : ℝ) + m) ^ 2) := by
            have hm_le : (m : ℝ) ≤ (k : ℝ) + m := by linarith
            have hkm_nn : 0 ≤ (k : ℝ) + m := hn'.le
            have hD1_pos : (0 : ℝ) < 3 * ((k : ℝ) + m) ^ 3 := by positivity
            have hD2_pos : (0 : ℝ) < 3 * ((k : ℝ) + m) ^ 2 := by positivity
            rw [div_le_div_iff₀ hD1_pos hD2_pos]
            nlinarith [hmk_cub_nn, hkm_nn, hn2_pos.le, hn'.le, hm_le,
              mul_nonneg hmk_cub_nn (mul_nonneg hkm_nn hkm_nn),
              mul_le_mul_of_nonneg_right hm_le (mul_nonneg hmk_cub_nn (sq_nonneg ((k : ℝ) + m)))]
          linarith

/-- **Sharp log-ratio bound in `(n, k)` coordinates.** For `1 ≤ k < n`,
`k · log(2k/n) + (n − k) · log(2(n − k)/n)
    ≤ 2 · (k − n/2)² / n + (8/3) · |k − n/2|³ / n²`.

This is `kl_to_half_le_sq_sharp` translated via `m = n − k`, using
`(k − m)² = 4(k − n/2)²` and `|k − m|³ = 8|k − n/2|³`. The leading
coefficient `2` is sharp (compare `log_ratio_le_quad_diff` with coefficient
`4`). The additive cubic correction `(8/3)|k − n/2|³/n²` is `o((k − n/2)²/n)`
whenever `|k − n/2| = o(n)`. -/
theorem log_ratio_le_quad_diff_sharp (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (k : ℝ) * Real.log (2 * k / n) + ((n : ℝ) - k) * Real.log (2 * ((n : ℝ) - k) / n)
      ≤ 2 * ((k : ℝ) - n / 2) ^ 2 / n + (8 / 3) * |(k : ℝ) - n / 2| ^ 3 / (n : ℝ) ^ 2 := by
  have hk_le : k ≤ n := hkn.le
  have hn : 1 ≤ n := le_trans hk hk_le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmk_pos : 1 ≤ n - k := Nat.sub_pos_of_lt hkn
  have key := kl_to_half_le_sq_sharp k (n - k) hk hnmk_pos
  have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by rw [Nat.cast_sub hk_le]
  rw [hcast] at key
  have hkn_sum : (k : ℝ) + ((n : ℝ) - k) = n := by ring
  rw [hkn_sum] at key
  -- Rewrite key : L ≤ (k - (n-k))²/(2n) + |k - (n-k)|³/(3n²).
  -- Use (k - (n-k))² = 4(k - n/2)² and |k - (n-k)|³ = 8|k - n/2|³.
  have hsq_eq : ((k : ℝ) - ((n : ℝ) - k)) ^ 2 / (2 * n) = 2 * ((k : ℝ) - n / 2) ^ 2 / n := by
    rw [show ((k : ℝ) - ((n : ℝ) - k)) ^ 2 = 4 * ((k : ℝ) - n / 2) ^ 2 by ring]
    field_simp
    ring
  have habs_eq : |(k : ℝ) - ((n : ℝ) - k)| = 2 * |(k : ℝ) - n / 2| := by
    rw [show ((k : ℝ) - ((n : ℝ) - k)) = 2 * ((k : ℝ) - n / 2) by ring, abs_mul]
    simp
  have hcub_eq : |(k : ℝ) - ((n : ℝ) - k)| ^ 3 / (3 * (n : ℝ) ^ 2) =
      (8 / 3) * |(k : ℝ) - n / 2| ^ 3 / (n : ℝ) ^ 2 := by
    rw [habs_eq]
    rw [show (2 * |(k : ℝ) - n / 2|) ^ 3 = 8 * |(k : ℝ) - n / 2| ^ 3 by ring]
    have hn2_ne : (n : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  linarith [key, hsq_eq.le, hsq_eq.ge, hcub_eq.le, hcub_eq.ge]

/-- **Central binomial PMF lower bound, α = 2 + ε case ε ≥ 2 (trivial).**

For `ε ≥ 2`, the statement with exponent constant `2 + ε ≥ 4` is trivially
implied by `centralBinom_pmf_lower_bound` (which has `α = 4`). This lemma
records the statement in the `α = 2 + ε` form so that downstream callers can
consume it uniformly; the `ε < 2` case — which genuinely requires the sharp
`log_ratio_le_quad_diff_sharp` plumbed through a fresh Stirling analysis —
is future work. -/
theorem centralBinom_pmf_lower_bound_alpha_two_plus (ε : ℝ) (hε : 2 ≤ ε) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
        (n.choose k : ℝ) / (2 : ℝ) ^ n ≥
          c / Real.sqrt (n : ℝ) *
            Real.exp (-(2 + ε) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
  obtain ⟨c, N, hc_pos, hN_one, hbd⟩ := centralBinom_pmf_lower_bound
  refine ⟨c, N, hc_pos, hN_one, ?_⟩
  intro n hnN k hk hkn
  have hbd_nk := hbd n hnN k hk hkn
  have hd_sq_nn : 0 ≤ ((k : ℝ) - (n : ℝ) / 2) ^ 2 := sq_nonneg _
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans hN_one hnN
    exact_mod_cast this
  have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- For ε ≥ 2, we have 2 + ε ≥ 4, so -(2+ε) ≤ -4 and
  -- exp(-(2+ε) d²/n) ≤ exp(-4 d²/n).
  have hexp_le : Real.exp (-(2 + ε) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) ≤
      Real.exp (-(4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hne : -(2 + ε) ≤ -(4 : ℝ) := by linarith
    have hmul : -(2 + ε) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 ≤
        -(4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 := by
      nlinarith [hd_sq_nn]
    have hn_inv_nn : 0 ≤ 1 / (n : ℝ) := by positivity
    have hineq := mul_le_mul_of_nonneg_right hmul hn_inv_nn
    have hrewrite : ∀ (x : ℝ), x * ((k : ℝ) - (n : ℝ) / 2) ^ 2 * (1 / (n : ℝ)) =
        x * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ) := by intro x; ring
    rw [hrewrite, hrewrite] at hineq
    exact hineq
  have hc_sqrt_pos : 0 < c / Real.sqrt n := div_pos hc_pos hsqrt_pos
  calc (n.choose k : ℝ) / (2 : ℝ) ^ n
      ≥ c / Real.sqrt n * Real.exp (-(4 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := hbd_nk
    _ ≥ c / Real.sqrt n * Real.exp (-(2 + ε) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hexp_le hc_sqrt_pos.le

/-!
## Sharp PMF bound (α = 2) with cubic correction term

Using `log_ratio_le_quad_diff_sharp` instead of `log_ratio_le_quad_diff` in the
Stirling analysis yields the sharp exponent constant `α = 2`, at the cost of an
additive cubic correction `(8/3)·|d|³/n²` in the exponent. This correction is
`o(d²/n)` whenever `|d| = o(n)`, so under any sub-linear regime on the offset
we obtain an effective bound with any `α > 2`.
-/

set_option maxHeartbeats 800000 in
/-- **Central binomial PMF lower bound, sharp α = 2 version with cubic
correction.**

This is the sharp analogue of `centralBinom_pmf_lower_bound`: the leading
exponent constant is `2` (rather than `4`), but the exponent carries an
additive term `(8/3)·|k − n/2|³/n²` coming from the cubic remainder in
`log_ratio_le_quad_diff_sharp`. Under any sub-linear regime on `|k − n/2|`,
this cubic term is `o((k − n/2)²/n)` and can be absorbed into the leading
exponent at the cost of replacing `2` by `2 + ε`. -/
private theorem centralBinom_pmf_lower_bound_sharp_raw :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
        (n.choose k : ℝ) / (2 : ℝ) ^ n ≥
          c / Real.sqrt (n : ℝ) *
            Real.exp (-(2 : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)
              - (8 / 3) * |(k : ℝ) - (n : ℝ) / 2| ^ 3 / (n : ℝ) ^ 2) := by
  have hCstir_pos0 : 0 < Real.exp 1 / Real.sqrt (2 * Real.pi) := by positivity
  set Cstir : ℝ := Real.exp 1 / Real.sqrt (2 * Real.pi) with hCstir_def
  have hCstir_pos : 0 < Cstir := hCstir_pos0
  have hsqrt2pi_nn : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hsqrt2pi_pos : 0 < Real.sqrt (2 / Real.pi) := by
    apply Real.sqrt_pos.mpr
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have hc_pos0 : 0 < Real.sqrt (2 / Real.pi) / Cstir ^ 3 := by positivity
  set c : ℝ := Real.sqrt (2 / Real.pi) / Cstir ^ 3 with hc_def
  have hc_pos : 0 < c := hc_pos0
  refine ⟨c, 1, hc_pos, le_refl _, ?_⟩
  intro n hn k hk hkn
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := hn
    exact_mod_cast this
  have hkpos' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk_le_n : k ≤ n := hkn.le
  have hnmkpos : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hnmkpos' : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast hnmkpos
  have hnmk_real : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    rw [Nat.cast_sub hk_le_n]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hone_le_n : 1 ≤ n := hn
  have hone_le_k : 1 ≤ k := hk
  have hone_le_nmk : 1 ≤ n - k := hnmkpos
  have hstN_lo : Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) :=
    sqrt_two_pi_mul_pow_le_factorial n
  have hstK_hi : (k.factorial : ℝ) ≤ Cstir *
      (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k) := by
    have := factorial_le_stirling hone_le_k
    simpa [hCstir_def] using this
  have hnmk_real0 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
    rw [Nat.cast_sub hk_le_n]
  have hstM_hi : ((n - k).factorial : ℝ) ≤ Cstir *
      (Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) * (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k)) := by
    have h := factorial_le_stirling hone_le_nmk
    have hrw_sqrt : Real.sqrt (2 * Real.pi * ((n - k : ℕ) : ℝ)) =
        Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) := by rw [hnmk_real0]
    rw [hrw_sqrt] at h
    simpa [hCstir_def] using h
  have hchoose_eq : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hk_le_n
    exact_mod_cast this
  have hchoose_nonneg : (0 : ℝ) ≤ (n.choose k : ℝ) := by exact_mod_cast Nat.zero_le _
  have hkfact_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmfact_pos : (0 : ℝ) < ((n - k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  set NL : ℝ := Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n with hNL
  set KU : ℝ := Cstir * (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k) with hKU
  set MU : ℝ := Cstir * (Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) *
    (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k)) with hMU
  have hNL_pos : 0 < NL := by
    rw [hNL]
    have : 0 < Real.sqrt (2 * Real.pi * n) := Real.sqrt_pos.mpr (by positivity)
    have h1 : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
    exact mul_pos this h1
  have hKU_pos : 0 < KU := by
    rw [hKU]
    have : 0 < Real.sqrt (2 * Real.pi * k) := Real.sqrt_pos.mpr (by positivity)
    have h1 : 0 < ((k : ℝ) / Real.exp 1) ^ k := by positivity
    exact mul_pos hCstir_pos (mul_pos this h1)
  have hnmk_real_pos : (0 : ℝ) < (n : ℝ) - k := by rw [← hnmk_real0]; exact_mod_cast hnmkpos
  have hMU_pos : 0 < MU := by
    rw [hMU]
    have : 0 < Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) :=
      Real.sqrt_pos.mpr (by positivity)
    have h1 : 0 < (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k) := by positivity
    exact mul_pos hCstir_pos (mul_pos this h1)
  have h_choose_lb : NL / (KU * MU) ≤ (n.choose k : ℝ) := by
    rw [div_le_iff₀ (mul_pos hKU_pos hMU_pos)]
    calc NL ≤ (n.factorial : ℝ) := hstN_lo
      _ = (n.choose k : ℝ) * k.factorial * (n - k).factorial := hchoose_eq.symm
      _ ≤ (n.choose k : ℝ) * KU * MU := by gcongr
      _ = (n.choose k : ℝ) * (KU * MU) := by ring
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hdiv_mono : NL / (KU * MU) / (2 : ℝ) ^ n ≤ (n.choose k : ℝ) / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right h_choose_lb h2n_pos.le
  -- Define the sharp exponent term `E := -2 d²/n - (8/3) |d|³/n²`.
  set d : ℝ := (k : ℝ) - (n : ℝ) / 2 with hd_def
  set E : ℝ := -(2 : ℝ) * d ^ 2 / n - (8 / 3) * |d| ^ 3 / (n : ℝ) ^ 2 with hE_def
  -- Sharp complementary quantity: the log-ratio bound is `-E` (up to sign).
  -- i.e. `k log(2k/n) + (n-k) log(2(n-k)/n) ≤ -E = 2 d²/n + (8/3)|d|³/n²`.
  set RHS : ℝ := c / Real.sqrt (n : ℝ) * Real.exp E with hRHS_def
  show RHS ≤ (n.choose k : ℝ) / (2 : ℝ) ^ n
  apply le_trans _ hdiv_mono
  have hKMN_pos : 0 < KU * MU * (2 : ℝ) ^ n := by positivity
  have hrw : NL / (KU * MU) / (2 : ℝ) ^ n = NL / (KU * MU * (2 : ℝ) ^ n) := by
    rw [div_div]
  rw [hrw]
  rw [le_div_iff₀ hKMN_pos]
  set Kk : ℝ := ((k : ℝ) / Real.exp 1) ^ k with hKk
  set Mm : ℝ := (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k) with hMm
  set Nn : ℝ := ((n : ℝ) / Real.exp 1) ^ n with hNn
  have hKk_pos : 0 < Kk := by rw [hKk]; positivity
  have hMm_pos : 0 < Mm := by rw [hMm]; positivity
  have hNn_pos : 0 < Nn := by rw [hNn]; positivity
  -- Sharp Step A: Kk * Mm * 2^n ≤ Nn * exp(-E).
  have hStepA : Kk * Mm * (2 : ℝ) ^ n ≤ Nn * Real.exp (-E) := by
    have hlhs_pos : 0 < Kk * Mm * (2 : ℝ) ^ n := by positivity
    have hexp_pos : 0 < Real.exp (-E) := Real.exp_pos _
    have hrhs_pos : 0 < Nn * Real.exp (-E) := mul_pos hNn_pos hexp_pos
    rw [← Real.log_le_log_iff hlhs_pos hrhs_pos]
    rw [Real.log_mul (mul_pos hKk_pos hMm_pos).ne' (by positivity : (2 : ℝ) ^ n ≠ 0),
        Real.log_mul hKk_pos.ne' hMm_pos.ne']
    rw [Real.log_mul hNn_pos.ne' hexp_pos.ne', Real.log_exp]
    have hKk_log : Real.log Kk = (k : ℝ) * (Real.log k - 1) := by
      rw [hKk, Real.log_pow, Real.log_div hkpos'.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have hMm_log : Real.log Mm = ((n : ℝ) - k) * (Real.log ((n : ℝ) - k) - 1) := by
      rw [hMm, Real.log_pow,
          Real.log_div hnmkpos'.ne' (Real.exp_pos 1).ne', Real.log_exp, hnmk_real]
    have hNn_log : Real.log Nn = (n : ℝ) * (Real.log n - 1) := by
      rw [hNn, Real.log_pow, Real.log_div hnpos.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have h2n_log : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [hKk_log, hMm_log, hNn_log, h2n_log]
    have hmain := log_ratio_le_quad_diff_sharp n k hone_le_k hkn
    have hnmk_pos : (0 : ℝ) < (n : ℝ) - k := by rw [← hnmk_real]; exact hnmkpos'
    have hklog : (k : ℝ) * Real.log (2 * k / n) =
        (k : ℝ) * Real.log 2 + (k : ℝ) * Real.log k - (k : ℝ) * Real.log n := by
      rw [show (2 * (k : ℝ) / n) = 2 * k * (n : ℝ)⁻¹ by field_simp]
      rw [Real.log_mul (by positivity) (inv_ne_zero hnpos.ne'),
          Real.log_mul (by norm_num) hkpos'.ne',
          Real.log_inv]
      ring
    have hmlog : ((n : ℝ) - k) * Real.log (2 * ((n : ℝ) - k) / n) =
        ((n : ℝ) - k) * Real.log 2 + ((n : ℝ) - k) * Real.log ((n : ℝ) - k) -
        ((n : ℝ) - k) * Real.log n := by
      rw [show (2 * ((n : ℝ) - k) / n) = 2 * ((n : ℝ) - k) * (n : ℝ)⁻¹ by field_simp]
      rw [Real.log_mul (by positivity) (inv_ne_zero hnpos.ne'),
          Real.log_mul (by norm_num) hnmk_pos.ne',
          Real.log_inv]
      ring
    rw [hklog, hmlog] at hmain
    have hlogn_split : (n : ℝ) * Real.log n =
        (k : ℝ) * Real.log n + ((n : ℝ) - k) * Real.log n := by ring
    have hlog2_split : (n : ℝ) * Real.log 2 =
        (k : ℝ) * Real.log 2 + ((n : ℝ) - k) * Real.log 2 := by ring
    -- hmain : k log(2k/n) + (n-k) log(2(n-k)/n) ≤ 2 d²/n + (8/3) |d|³/n²
    -- and `-E = 2 d²/n + (8/3) |d|³/n²`.
    have hminus_E : -E = 2 * d ^ 2 / n + (8 / 3) * |d| ^ 3 / (n : ℝ) ^ 2 := by
      rw [hE_def]; ring
    rw [hminus_E, hd_def]
    linarith [hmain, hlogn_split, hlog2_split]
  have hStepB_sq : Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k))
      ≤ Real.pi * n := by
    have h_amgm : (k : ℝ) * ((n : ℝ) - k) ≤ ((n : ℝ) / 2) ^ 2 := by
      nlinarith [sq_nonneg ((k : ℝ) - ((n : ℝ) - k))]
    have hprod_eq :
        Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) =
          Real.sqrt ((2 * Real.pi) ^ 2 * ((k : ℝ) * ((n : ℝ) - k))) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    rw [hprod_eq]
    have hbd : (2 * Real.pi) ^ 2 * ((k : ℝ) * ((n : ℝ) - k))
        ≤ (2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2 := by
      have h2pi_sq_nn : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_left h_amgm h2pi_sq_nn
    have hbd_sqrt : Real.sqrt ((2 * Real.pi) ^ 2 * ((k : ℝ) * ((n : ℝ) - k)))
        ≤ Real.sqrt ((2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2) :=
      Real.sqrt_le_sqrt hbd
    have heval : Real.sqrt ((2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2) = Real.pi * n := by
      rw [show (2 * Real.pi) ^ 2 * ((n : ℝ) / 2) ^ 2 = (Real.pi * n) ^ 2 by ring]
      rw [Real.sqrt_sq (by positivity)]
    linarith [hbd_sqrt, heval.le, heval.ge]
  have hCstir_ge_one : 1 ≤ Cstir := by
    rw [hCstir_def]
    rw [le_div_iff₀ (Real.sqrt_pos.mpr h2pi)]
    rw [one_mul]
    have hexp1_sq : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    have h2pi_le_e2 : 2 * Real.pi ≤ Real.exp 2 := by
      have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
      have hexp2 : (7.3 : ℝ) ≤ Real.exp 2 := by
        have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        nlinarith [Real.exp_pos 1, hexp1_sq]
      linarith
    have hmono : Real.sqrt (2 * Real.pi) ≤ Real.sqrt (Real.exp 2) :=
      Real.sqrt_le_sqrt h2pi_le_e2
    have h_sqrt_exp2 : Real.sqrt (Real.exp 2) = Real.exp 1 := by
      have hexp2_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [hexp2_eq, Real.sqrt_mul_self (Real.exp_pos 1).le]
    rw [h_sqrt_exp2] at hmono
    exact hmono
  have hfinal : c * Cstir ^ 2 ≤ Real.sqrt (2 / Real.pi) := by
    rw [hc_def]
    have hCube : Cstir ^ 3 = Cstir ^ 2 * Cstir := by ring
    have hCstir2_ne : (Cstir ^ 2 : ℝ) ≠ 0 := by positivity
    rw [show (Real.sqrt (2 / Real.pi) / Cstir ^ 3) * Cstir ^ 2 =
          Real.sqrt (2 / Real.pi) / Cstir by
        rw [hCube]; field_simp]
    have h1 : Real.sqrt (2 / Real.pi) / Cstir ≤ Real.sqrt (2 / Real.pi) / 1 := by
      apply div_le_div_of_nonneg_left hsqrt2pi_nn zero_lt_one hCstir_ge_one
    simpa using h1
  have hKU_expand : KU = Cstir * (Real.sqrt (2 * Real.pi * k) * Kk) := rfl
  have hMU_expand : MU = Cstir * (Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) * Mm) := rfl
  have hKUMU : KU * MU = Cstir ^ 2 *
      (Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k))) *
      (Kk * Mm) := by
    rw [hKU_expand, hMU_expand]; ring
  rw [hKUMU]
  set S : ℝ := Real.sqrt (2 * Real.pi * (k : ℝ)) * Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) with hSdef
  have hS_pos : 0 < S := by
    rw [hSdef]
    have h1 : 0 < Real.sqrt (2 * Real.pi * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    have hnmk_pos : (0 : ℝ) < (n : ℝ) - k := by rw [← hnmk_real]; exact hnmkpos'
    have h2 : 0 < Real.sqrt (2 * Real.pi * ((n : ℝ) - k)) := Real.sqrt_pos.mpr (by positivity)
    exact mul_pos h1 h2
  have hSle : S ≤ Real.pi * n := hStepB_sq
  have hReg : RHS * (Cstir ^ 2 * S * (Kk * Mm) * (2 : ℝ) ^ n) =
      RHS * Cstir ^ 2 * S * (Kk * Mm * (2 : ℝ) ^ n) := by ring
  rw [hReg]
  have hRHS_pos : 0 < RHS := by
    rw [hRHS_def]
    positivity
  have hCstir2_pos : 0 < Cstir ^ 2 := by positivity
  have h_step1 : RHS * Cstir ^ 2 * S * (Kk * Mm * (2 : ℝ) ^ n) ≤
      RHS * Cstir ^ 2 * S * (Nn * Real.exp (-E)) := by
    have hfactor_nn : 0 ≤ RHS * Cstir ^ 2 * S := by
      have := mul_pos (mul_pos hRHS_pos hCstir2_pos) hS_pos
      linarith
    exact mul_le_mul_of_nonneg_left hStepA hfactor_nn
  have h_RHS_exp : RHS * Real.exp (-E) = c / Real.sqrt n := by
    rw [hRHS_def]
    rw [mul_assoc, ← Real.exp_add]
    rw [show E + -E = 0 by ring]
    rw [Real.exp_zero, mul_one]
  have h_step2_eq : RHS * Cstir ^ 2 * S * (Nn * Real.exp (-E))
      = c / Real.sqrt n * Cstir ^ 2 * S * Nn := by
    have : RHS * Cstir ^ 2 * S * (Nn * Real.exp (-E))
        = (RHS * Real.exp (-E)) * Cstir ^ 2 * S * Nn := by ring
    rw [this, h_RHS_exp]
  have h_step3 : c / Real.sqrt n * Cstir ^ 2 * S * Nn ≤
      c / Real.sqrt n * Cstir ^ 2 * (Real.pi * n) * Nn := by
    have hfactor_pos : 0 < c / Real.sqrt n * Cstir ^ 2 :=
      mul_pos (div_pos hc_pos (Real.sqrt_pos.mpr hnpos)) hCstir2_pos
    have hmul_S : c / Real.sqrt n * Cstir ^ 2 * S ≤
        c / Real.sqrt n * Cstir ^ 2 * (Real.pi * n) :=
      mul_le_mul_of_nonneg_left hSle hfactor_pos.le
    exact mul_le_mul_of_nonneg_right hmul_S hNn_pos.le
  have hfinal_ineq : c / Real.sqrt n * Cstir ^ 2 * (Real.pi * n) * Nn ≤ NL := by
    rw [hNL]
    have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsqrt2pi : Real.sqrt (2 * Real.pi * n) = Real.sqrt (2 * Real.pi) * Real.sqrt n := by
      rw [show (2 * Real.pi * (n : ℝ)) = (2 * Real.pi) * n by ring]
      exact Real.sqrt_mul h2pi.le _
    rw [hsqrt2pi]
    have hNn_nn : 0 ≤ Nn := hNn_pos.le
    have hineq_scalar : c * Cstir ^ 2 * Real.pi ≤ Real.sqrt (2 * Real.pi) := by
      have h1 : c * Cstir ^ 2 * Real.pi ≤ Real.sqrt (2 / Real.pi) * Real.pi :=
        mul_le_mul_of_nonneg_right hfinal hpi.le
      have h2 : Real.sqrt (2 / Real.pi) * Real.pi = Real.sqrt (2 * Real.pi) := by
        have hpi_sq : Real.pi = Real.sqrt (Real.pi ^ 2) := by
          rw [Real.sqrt_sq hpi.le]
        rw (occs := [2]) [hpi_sq]
        rw [← Real.sqrt_mul (by positivity)]
        congr 1
        field_simp
      linarith [h1, h2.le, h2.ge]
    have hdiv : (n : ℝ) / Real.sqrt n = Real.sqrt n := by
      rw [div_eq_iff hsqrtn_pos.ne']
      exact (Real.mul_self_sqrt hnpos.le).symm
    calc c / Real.sqrt n * Cstir ^ 2 * (Real.pi * n) * Nn
        = c * Cstir ^ 2 * Real.pi * ((n : ℝ) / Real.sqrt n) * Nn := by ring
      _ = c * Cstir ^ 2 * Real.pi * Real.sqrt n * Nn := by rw [hdiv]
      _ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt n * Nn :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hineq_scalar hsqrtn_pos.le) hNn_nn
  linarith [h_step1, h_step2_eq.le, h_step2_eq.ge, h_step3, hfinal_ineq]

/-- **Central binomial PMF lower bound, sharp α = 2 + ε case (any `ε > 0`).**

Under the sub-linear regime `(k − n/2)² ≤ n · log n`, the sharp exponent
constant `2` from `log_ratio_le_quad_diff_sharp` combines with an `ε`-slack
to absorb the cubic correction. Concretely: if `ε > 0`, there exist `c > 0`
and `N ≥ 1` such that for all `n ≥ N`, for all `1 ≤ k < n` with
`(k − n/2)² ≤ n · log n`, we have
`C(n, k) / 2^n ≥ c · (1/√n) · exp(−(2 + ε) · (k − n/2)² / n)`.

The threshold `N(ε)` is chosen so that `log n / n ≤ (3ε/8)²` for all
`n ≥ N(ε)`; under the regime this forces `(8/3)·|d|/n ≤ ε`, which lets
`ε · d² / n` dominate the cubic term `(8/3)·|d|³/n²`. -/
theorem centralBinom_pmf_lower_bound_alpha_two :
    ∀ ε : ℝ, 0 < ε →
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
        ((k : ℝ) - (n : ℝ) / 2) ^ 2 ≤ (n : ℝ) * Real.log n →
        (n.choose k : ℝ) / (2 : ℝ) ^ n ≥
          c / Real.sqrt (n : ℝ) *
            Real.exp (-(2 + ε) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
  intro ε hε_pos
  obtain ⟨c, N₀, hc_pos, hN₀_one, hbd⟩ := centralBinom_pmf_lower_bound_sharp_raw
  -- Choose N so that for all n ≥ N, `Real.log n / n ≤ (3ε/8)²`.
  -- Crudely: set N = max N₀ (⌈(8/(3ε))⁴⌉ + 2). Under the regime and n ≥ N,
  -- |d| ≤ √(n log n) and log n / n ≤ (3ε/8)², so |d|/n ≤ 3ε/8,
  -- hence (8/3)·|d|/n ≤ ε, hence (8/3)·|d|³/n² ≤ ε·d²/n.
  have h38ε_pos : 0 < 3 * ε / 8 := by positivity
  -- We use the elementary bound `log n ≤ n` for all `n ≥ 1`, which gives
  -- `log n / n ≤ 1`. Combined with `log n / n → 0`, we pick N so that
  -- `log n ≤ ((3ε/8)²) · n`. A convenient sufficient condition is
  -- `n ≥ max N₀ (⌈2 / (3ε/8)²⌉ + 2)`, after which `log n ≤ √n ≤ (3ε/8)² · n`
  -- holds. We avoid that analytic overhead by working with the contrapositive
  -- directly: we ask `|d|/n ≤ 3ε/8`, which in turn follows from
  -- `d² ≤ n · log n` together with `log n ≤ (3ε/8)² · n`.
  -- The bound we use is: there exists `N₁ ≥ 1` such that for `n ≥ N₁`,
  -- `Real.log n ≤ (3ε/8)^2 * n`. Such `N₁` exists since `log n / n → 0`.
  have hexists_N1 : ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ n : ℕ, N₁ ≤ n →
      Real.log n ≤ (3 * ε / 8) ^ 2 * n := by
    -- `Real.log x / x → 0` as `x → ∞`. Use `tendsto_pow_log_div_mul_add_atTop 1 0 1`
    -- which gives `log x ^ 1 / (1 * x + 0) → 0`.
    have htend_real : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
      have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using h
    have htend : Filter.Tendsto (fun n : ℕ => Real.log n / n) Filter.atTop (nhds 0) :=
      htend_real.comp tendsto_natCast_atTop_atTop
    have hbnd_pos : 0 < (3 * ε / 8) ^ 2 := by positivity
    have hev : ∀ᶠ n : ℕ in Filter.atTop, |Real.log n / n - 0| < (3 * ε / 8) ^ 2 := by
      exact (Metric.tendsto_nhds.mp htend) _ hbnd_pos
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N₁', hN₁'⟩ := hev
    refine ⟨max N₁' 1, le_max_right _ _, ?_⟩
    intro n hn
    have hn_ge_N₁' : N₁' ≤ n := le_trans (le_max_left _ _) hn
    have hn_ge_1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn_ge_1
    have habs := hN₁' n hn_ge_N₁'
    simp only [sub_zero] at habs
    have hlogn_nn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have habs' : Real.log n / n < (3 * ε / 8) ^ 2 := by
      have heq : |Real.log n / n| = Real.log n / n :=
        abs_of_nonneg (div_nonneg hlogn_nn hnpos.le)
      linarith [habs, heq.le, heq.ge]
    have hmul : Real.log n / n * n ≤ (3 * ε / 8) ^ 2 * n := by
      have := mul_le_mul_of_nonneg_right habs'.le hnpos.le
      linarith
    have hdivmul : Real.log n / n * n = Real.log n := by
      field_simp
    linarith [hmul, hdivmul.le, hdivmul.ge]
  obtain ⟨N₁, hN₁_one, hN₁⟩ := hexists_N1
  refine ⟨c, max N₀ N₁, hc_pos, le_max_of_le_left hN₀_one, ?_⟩
  intro n hnN k hk hkn hreg
  have hn_ge_N₀ : N₀ ≤ n := le_trans (le_max_left _ _) hnN
  have hn_ge_N₁ : N₁ ≤ n := le_trans (le_max_right _ _) hnN
  have hbd_nk := hbd n hn_ge_N₀ k hk hkn
  -- Set d = k - n/2.
  set d : ℝ := (k : ℝ) - (n : ℝ) / 2 with hd_def
  have hd_sq_nn : 0 ≤ d ^ 2 := sq_nonneg _
  have habs_d_nn : 0 ≤ |d| := abs_nonneg _
  have habs_d_sq : |d| ^ 2 = d ^ 2 := sq_abs d
  have hn_ge_1 : 1 ≤ n := le_trans hN₁_one hn_ge_N₁
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn_ge_1
  have hn_ne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- From the regime: d² ≤ n · log n.
  -- From the N₁ bound: log n ≤ (3ε/8)² · n.
  -- Hence d² ≤ n · (3ε/8)² · n = (3ε/8)² · n².
  -- So |d| ≤ (3ε/8) · n, i.e., |d|/n ≤ 3ε/8, i.e., (8/3)·|d|/n ≤ ε.
  have hlogn_bd : Real.log n ≤ (3 * ε / 8) ^ 2 * n := hN₁ n hn_ge_N₁
  have hd_sq_bd : d ^ 2 ≤ (3 * ε / 8) ^ 2 * (n : ℝ) ^ 2 := by
    calc d ^ 2 ≤ (n : ℝ) * Real.log n := hreg
      _ ≤ (n : ℝ) * ((3 * ε / 8) ^ 2 * n) := by
          exact mul_le_mul_of_nonneg_left hlogn_bd hnpos.le
      _ = (3 * ε / 8) ^ 2 * (n : ℝ) ^ 2 := by ring
  have habs_d_bd : |d| ≤ (3 * ε / 8) * n := by
    have hsq_bd : |d| ^ 2 ≤ ((3 * ε / 8) * n) ^ 2 := by
      rw [habs_d_sq]
      have : ((3 * ε / 8) * n) ^ 2 = (3 * ε / 8) ^ 2 * (n : ℝ) ^ 2 := by ring
      linarith [hd_sq_bd, this.le, this.ge]
    have hrhs_nn : 0 ≤ (3 * ε / 8) * n := by positivity
    exact abs_le_of_sq_le_sq' hsq_bd hrhs_nn |>.2
  -- Key: ε · d² / n ≥ (8/3) · |d|³ / n².
  -- Proof: (8/3)·|d|³/n² = (8/3)·|d|/n · d²/n ≤ ε · d²/n (since (8/3)·|d|/n ≤ ε).
  have h83_bd : (8 / 3 : ℝ) * |d| / n ≤ ε := by
    -- |d| ≤ (3ε/8) n  ⟹  |d|/n ≤ 3ε/8  ⟹  (8/3)·|d|/n ≤ ε.
    have hdiv_bd : |d| / n ≤ 3 * ε / 8 := by
      rw [div_le_iff₀ hnpos]
      linarith [habs_d_bd]
    have := mul_le_mul_of_nonneg_left hdiv_bd (by norm_num : (0 : ℝ) ≤ 8 / 3)
    have hmul_eq : (8 / 3 : ℝ) * (|d| / n) = (8 / 3) * |d| / n := by
      field_simp
    have hrhs_eq : (8 / 3 : ℝ) * (3 * ε / 8) = ε := by ring
    linarith [this, hmul_eq.le, hmul_eq.ge, hrhs_eq.le, hrhs_eq.ge]
  -- Now: (8/3) · |d|³ / n² = ((8/3) · |d| / n) · (d² / n) ≤ ε · d² / n.
  have hcubic_bd : (8 / 3 : ℝ) * |d| ^ 3 / (n : ℝ) ^ 2 ≤ ε * d ^ 2 / n := by
    have habs_d3 : |d| ^ 3 = |d| * d ^ 2 := by
      rw [show (|d| ^ 3 : ℝ) = |d| * |d| ^ 2 by ring, habs_d_sq]
    have hrw : (8 / 3 : ℝ) * |d| ^ 3 / (n : ℝ) ^ 2 =
        ((8 / 3) * |d| / n) * (d ^ 2 / n) := by
      rw [habs_d3]
      field_simp
    rw [hrw]
    have hd_sq_over_n_nn : 0 ≤ d ^ 2 / n := div_nonneg hd_sq_nn hnpos.le
    have := mul_le_mul_of_nonneg_right h83_bd hd_sq_over_n_nn
    have hrhs_eq : ε * (d ^ 2 / n) = ε * d ^ 2 / n := by field_simp
    linarith [this, hrhs_eq.le, hrhs_eq.ge]
  -- Now translate this into the exponent comparison.
  -- raw exponent: -2 d²/n - (8/3) |d|³/n²
  -- target exponent: -(2+ε) d²/n = -2 d²/n - ε d²/n
  -- Since -(8/3)|d|³/n² ≥ -ε d²/n, the raw exponent ≥ the target.
  have hexp_le : Real.exp (-(2 + ε) * d ^ 2 / n) ≤
      Real.exp (-(2 : ℝ) * d ^ 2 / n - (8 / 3) * |d| ^ 3 / (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have : -(2 + ε) * d ^ 2 / n = -(2 : ℝ) * d ^ 2 / n - ε * d ^ 2 / n := by
      field_simp
      ring
    rw [this]
    linarith [hcubic_bd]
  -- Multiply both sides by c/√n > 0.
  have hc_sqrt_pos : 0 < c / Real.sqrt n := div_pos hc_pos hsqrt_n_pos
  calc (n.choose k : ℝ) / (2 : ℝ) ^ n
      ≥ c / Real.sqrt n *
          Real.exp (-(2 : ℝ) * d ^ 2 / n - (8 / 3) * |d| ^ 3 / (n : ℝ) ^ 2) := hbd_nk
    _ ≥ c / Real.sqrt n * Real.exp (-(2 + ε) * d ^ 2 / n) := by
        exact mul_le_mul_of_nonneg_left hexp_le hc_sqrt_pos.le

end Helpers
end Erdos524
