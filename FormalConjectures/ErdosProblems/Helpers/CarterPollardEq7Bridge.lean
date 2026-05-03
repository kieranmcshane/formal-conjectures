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

import FormalConjectures.ErdosProblems.Helpers.CarterPollardHFunction

/-!
# Carter--Pollard equation (7) bridge

This file isolates the raw Beta-integral-to-`h`-integral step in the
Carter--Pollard chain. It deliberately keeps `N` and `ε` abstract through
the two exponent-matching hypotheses, and it does not instantiate the final
Tusnády constants.
-/

namespace FormalConjectures.ErdosProblems.Helpers.CarterPollardH

open Real Set

/-- On the open unit interval, the Carter--Pollard exponential recovers the
Beta-integral polynomial kernel under the abstract exponent-matching
hypotheses. -/
private lemma beta_kernel_eq_exp_carterPollardH_of_params
    {n k : ℕ} {N ε s : ℝ}
    (hleft : N * (1 + ε) / 2 = ((k - 1 : ℕ) : ℝ))
    (hright : N * (1 - ε) / 2 = ((n - k : ℕ) : ℝ))
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - s) ^ (k - 1) * (1 + s) ^ (n - k) =
      Real.exp (N * carterPollardH ε s) := by
  have h1pos : 0 < 1 - s := by linarith [hs.2]
  have h2pos : 0 < 1 + s := by linarith [hs.1]
  have hlog :
      N * carterPollardH ε s =
        ((k - 1 : ℕ) : ℝ) * Real.log (1 - s) +
          ((n - k : ℕ) : ℝ) * Real.log (1 + s) := by
    unfold carterPollardH
    rw [← hleft, ← hright]
    ring
  rw [hlog, Real.exp_add]
  have hpow1 :
      Real.exp (((k - 1 : ℕ) : ℝ) * Real.log (1 - s)) = (1 - s) ^ (k - 1) := by
    rw [mul_comm, ← Real.rpow_def_of_pos h1pos, Real.rpow_natCast]
  have hpow2 :
      Real.exp (((n - k : ℕ) : ℝ) * Real.log (1 + s)) = (1 + s) ^ (n - k) := by
    rw [mul_comm, ← Real.rpow_def_of_pos h2pos, Real.rpow_natCast]
  rw [hpow1, hpow2]

/-- TC15 equation-(7) bridge for the half Beta integral.

This is the affine substitution `x = (1-s)/2`, followed by the abstract
parameter identification
`N(1+ε)/2 = k-1` and `N(1-ε)/2 = n-k`. The right side is still a raw
Carter--Pollard interval integral. -/
theorem betaPartialIntegral_half_eq_carterPollardH_integral_of_params
    {n k : ℕ} {N ε : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n)
    (_hNpos : 0 < N)
    (hleft : N * (1 + ε) / 2 = ((k - 1 : ℕ) : ℝ))
    (hright : N * (1 - ε) / 2 = ((n - k : ℕ) : ℝ)) :
    Erdos524.Helpers.betaPartialIntegral n k (1 / 2) =
      (1 / 2 : ℝ) ^ n * Real.exp (N * ε ^ 2 / 2) *
        ∫ s in (0 : ℝ)..1,
          Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2) := by
  let betaKernel : ℝ → ℝ := fun x => x ^ (k - 1) * (1 - x) ^ (n - k)
  let polyKernel : ℝ → ℝ := fun s => (1 - s) ^ (k - 1) * (1 + s) ^ (n - k)
  let hKernel : ℝ → ℝ := fun s => Real.exp (N * carterPollardH ε s)
  have h_change :
      Erdos524.Helpers.betaPartialIntegral n k (1 / 2) =
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..1, betaKernel ((1 / 2 : ℝ) - (1 / 2) * s) := by
    unfold Erdos524.Helpers.betaPartialIntegral
    have hsubst :=
      (intervalIntegral.smul_integral_comp_sub_mul
        (f := betaKernel) (a := (0 : ℝ)) (b := 1) (c := (1 / 2 : ℝ)) (d := (1 / 2 : ℝ)))
    simpa [betaKernel] using hsubst.symm
  have h_scaled_integrand :
      (fun s : ℝ => (1 / 2 : ℝ) * betaKernel ((1 / 2 : ℝ) - (1 / 2) * s)) =
        fun s : ℝ => (1 / 2 : ℝ) ^ n * polyKernel s := by
    funext s
    dsimp [betaKernel, polyKernel]
    have hn : 1 ≤ n := le_trans hk hkn
    have hpow : (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (n - 1)) = (1 / 2 : ℝ) ^ n := by
      have hn_eq : n = (n - 1) + 1 := by omega
      nth_rw 2 [hn_eq]
      rw [pow_succ]
      ring
    rw [← hpow]
    have h1 : ((1 / 2 : ℝ) - (1 / 2) * s) = (1 / 2 : ℝ) * (1 - s) := by ring
    have h2 : (1 - ((1 / 2 : ℝ) - (1 / 2) * s)) = (1 / 2 : ℝ) * (1 + s) := by ring
    rw [h2, h1, mul_pow, mul_pow]
    have hexp : (k - 1) + (n - k) = n - 1 := by omega
    have hcoeff :
        (1 / 2 : ℝ) ^ (k - 1) * (1 / 2 : ℝ) ^ (n - k) =
          (1 / 2 : ℝ) ^ (n - 1) := by
      rw [← pow_add, hexp]
    calc
      (1 / 2 : ℝ) *
          (((1 / 2 : ℝ) ^ (k - 1) * (1 - s) ^ (k - 1)) *
            ((1 / 2 : ℝ) ^ (n - k) * (1 + s) ^ (n - k))) =
          (1 / 2 : ℝ) *
            (((1 / 2 : ℝ) ^ (k - 1) * (1 / 2 : ℝ) ^ (n - k)) *
              ((1 - s) ^ (k - 1) * (1 + s) ^ (n - k))) := by ring
      _ = (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) ^ (n - 1) *
              ((1 - s) ^ (k - 1) * (1 + s) ^ (n - k))) := by rw [hcoeff]
      _ = (1 / 2 : ℝ) * (1 / 2) ^ (n - 1) *
            ((1 - s) ^ (k - 1) * (1 + s) ^ (n - k)) := by ring
  have h_beta_poly :
      Erdos524.Helpers.betaPartialIntegral n k (1 / 2) =
        (1 / 2 : ℝ) ^ n * ∫ s in (0 : ℝ)..1, polyKernel s := by
    rw [h_change]
    rw [← intervalIntegral.integral_const_mul]
    rw [h_scaled_integrand]
    rw [intervalIntegral.integral_const_mul]
  have h_poly_h :
      ∫ s in (0 : ℝ)..1, polyKernel s = ∫ s in (0 : ℝ)..1, hKernel s := by
    apply intervalIntegral.integral_congr_ae'
    · have h_ae_Ioo : ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
          s ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
        exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc] at h_ae_Ioo
      filter_upwards [h_ae_Ioo] with s hsIoo hsIoc
      dsimp [polyKernel, hKernel]
      exact beta_kernel_eq_exp_carterPollardH_of_params hleft hright (hsIoo hsIoc)
    · filter_upwards with s hs
      exfalso
      exact (not_lt_of_ge hs.2) (lt_trans zero_lt_one hs.1)
  have h_shift :
      ∫ s in (0 : ℝ)..1, hKernel s =
        Real.exp (N * ε ^ 2 / 2) *
          ∫ s in (0 : ℝ)..1,
            Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _hs
    dsimp [hKernel]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_beta_poly, h_poly_h, h_shift]
  ring

/-- TC15 polynomial-tail form of the Carter--Pollard equation-(7) bridge. -/
theorem binomialPolyTail_half_eq_carterPollardH_integral_of_params
    {n k : ℕ} {N ε : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n)
    (hNpos : 0 < N)
    (hleft : N * (1 + ε) / 2 = ((k - 1 : ℕ) : ℝ))
    (hright : N * (1 - ε) / 2 = ((n - k : ℕ) : ℝ)) :
    Erdos524.Helpers.binomialPolyTail n k (1 / 2 : ℝ) =
      ((n : ℝ) * ((n - 1).choose (k - 1) : ℝ)) *
        ((1 / 2 : ℝ) ^ n * Real.exp (N * ε ^ 2 / 2) *
          ∫ s in (0 : ℝ)..1,
            Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2)) := by
  rw [bin_tail_beta_integral_half_poly n k hk hkn]
  rw [betaPartialIntegral_half_eq_carterPollardH_integral_of_params
    hk hkn hNpos hleft hright]

/-- TC15 raw Gaussian-tail upper bound for the analytic binomial-tail
polynomial, still with abstract Carter--Pollard parameters.

The constants `N` and `ε` are not instantiated here; TC16 is responsible for
the final constants audit. -/
theorem binomialPolyTail_half_le_gaussian_tail_of_params
    {n k : ℕ} {N ε : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n)
    (hNpos : 0 < N) (hε0 : 0 ≤ ε)
    (hleft : N * (1 + ε) / 2 = ((k - 1 : ℕ) : ℝ))
    (hright : N * (1 - ε) / 2 = ((n - k : ℕ) : ℝ)) :
    Erdos524.Helpers.binomialPolyTail n k (1 / 2 : ℝ) ≤
      ((n : ℝ) * ((n - 1).choose (k - 1) : ℝ)) *
        ((1 / 2 : ℝ) ^ n * Real.exp (N * ε ^ 2 / 2) *
          ((Real.sqrt N)⁻¹ *
            ∫ t in Set.Ioi (Real.sqrt N * ε), Real.exp (-t ^ 2 / 2))) := by
  have h_eq := binomialPolyTail_half_eq_carterPollardH_integral_of_params
    hk hkn hNpos hleft hright
  rw [h_eq]
  set C : ℝ :=
    ((n : ℝ) * ((n - 1).choose (k - 1) : ℝ)) *
      ((1 / 2 : ℝ) ^ n * Real.exp (N * ε ^ 2 / 2)) with hC
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have htail :=
    carterPollardH_exp_bulk_upper_gaussian_tail (N := N) (ε := ε) hNpos hε0
  simpa [C, mul_assoc] using mul_le_mul_of_nonneg_left htail hC_nonneg

end FormalConjectures.ErdosProblems.Helpers.CarterPollardH
