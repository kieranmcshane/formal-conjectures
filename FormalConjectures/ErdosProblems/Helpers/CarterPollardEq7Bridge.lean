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
import FormalConjectures.ErdosProblems.Helpers.StirlingTwoSided

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

/-- TC16 constants-instantiated Carter--Pollard raw Gaussian-tail bridge.

Under the `binomialPolyTail m k` convention, the Carter--Pollard paper's
parameters are `N = m - 1` and `ε = (2 * k - m - 1) / (m - 1)`. This theorem
only instantiates those constants in the TC15 raw tail bound; it does not
perform any final normal-tail comparison or Tusnády polynomial closure. -/
theorem binomialPolyTail_half_le_gaussian_tail_instantiated
    {m k : ℕ}
    (hm : 2 ≤ m)
    (hk : 1 ≤ k) (hkm : k ≤ m)
    (hε0 :
      0 ≤ (((2 : ℝ) * (k : ℝ) - (m : ℝ) - 1) / ((m : ℝ) - 1))) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      ((m : ℝ) * ((m - 1).choose (k - 1) : ℝ)) *
        ((1 / 2 : ℝ) ^ m *
          Real.exp (((m - 1 : ℕ) : ℝ) *
            (((2 : ℝ) * (k : ℝ) - (m : ℝ) - 1) / ((m : ℝ) - 1)) ^ 2 / 2) *
          ((Real.sqrt ((m - 1 : ℕ) : ℝ))⁻¹ *
            ∫ t in Set.Ioi
              (Real.sqrt ((m - 1 : ℕ) : ℝ) *
                (((2 : ℝ) * (k : ℝ) - (m : ℝ) - 1) / ((m : ℝ) - 1))),
              Real.exp (-t ^ 2 / 2))) := by
  let N : ℝ := ((m - 1 : ℕ) : ℝ)
  let ε : ℝ := (((2 : ℝ) * (k : ℝ) - (m : ℝ) - 1) / ((m : ℝ) - 1))
  have hm1_nat_pos : 0 < m - 1 := by omega
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast hm1_nat_pos
  have hm_cast_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ m by omega)]
    norm_num
  have hden : (m : ℝ) - 1 ≠ 0 := by
    rw [← hm_cast_sub]
    exact ne_of_gt hNpos
  have hk_cast_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  have hmk_cast_sub : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub hkm]
  have hleft : N * (1 + ε) / 2 = ((k - 1 : ℕ) : ℝ) := by
    dsimp [N, ε]
    rw [hm_cast_sub, hk_cast_sub]
    field_simp [hden]
    ring
  have hright : N * (1 - ε) / 2 = ((m - k : ℕ) : ℝ) := by
    dsimp [N, ε]
    rw [hm_cast_sub, hmk_cast_sub]
    field_simp [hden]
    ring
  have htail := binomialPolyTail_half_le_gaussian_tail_of_params
    (n := m) (k := k) (N := N) (ε := ε) hk hkm hNpos hε0 hleft hright
  simpa [N, ε] using htail

/-- Carter--Pollard's instantiated `N = m - 1` parameter. -/
noncomputable def carterPollardN (m : ℕ) : ℝ :=
  ((m - 1 : ℕ) : ℝ)

/-- Carter--Pollard's instantiated `ε = (2*k - m - 1)/(m - 1)` parameter. -/
noncomputable def carterPollardEps (m k : ℕ) : ℝ :=
  (((2 : ℝ) * (k : ℝ) - (m : ℝ) - 1) / ((m : ℝ) - 1))

/-- Carter--Pollard's shifted threshold `K = k - 1`. -/
def carterPollardK (_m k : ℕ) : ℕ :=
  k - 1

/-- Carter--Pollard's complementary exponent `N - K = m - k`. -/
def carterPollardNK (m k : ℕ) : ℕ :=
  m - k

/-- Raw normalized standard-Gaussian upper tail, kept as an interval integral. -/
noncomputable def gaussianTailRaw (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    ∫ t in Set.Ioi x, Real.exp (-t ^ 2 / 2)

/-- The exact raw Carter--Pollard prefactor whose logarithm plays the role of
the paper's `Δ` before any Stirling-error comparison is performed. -/
noncomputable def carterPollardPrefactorRaw (m k : ℕ) : ℝ :=
  ((m : ℝ) * ((m - 1).choose (k - 1) : ℝ)) *
    ((1 / 2 : ℝ) ^ m *
      Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2)) *
    (Real.sqrt (2 * Real.pi) * (Real.sqrt (carterPollardN m))⁻¹)

/-- Raw `Δ` corresponding to the exact Lean prefactor before the paper's
Stirling-expanded `Δ` is bounded or identified. -/
noncomputable def carterPollardDeltaRaw (m k : ℕ) : ℝ :=
  Real.log (carterPollardPrefactorRaw m k)

/-- The positive Stirling core `√(2πj) * (j/e)^j` from formula (3). -/
noncomputable def carterPollardStirlingCore (j : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j

/-- Carter--Pollard's Robbins correction term `λ_j` from formula (3):
`j! = √(2πj) * (j/e)^j * exp(λ_j)`. -/
noncomputable def carterPollardLambdaTerm (j : ℕ) : ℝ :=
  Real.log ((j.factorial : ℝ) / carterPollardStirlingCore j)

/-- The `Λ = λ_N - λ_K - λ_(N-K)` combination used in equation (7). -/
noncomputable def carterPollardLambda (m k : ℕ) : ℝ :=
  carterPollardLambdaTerm (m - 1) -
    carterPollardLambdaTerm (carterPollardK m k) -
      carterPollardLambdaTerm (carterPollardNK m k)

/-- Entropy part of the paper's Δ before introducing the auxiliary `γ(ε)`. -/
noncomputable def carterPollardEntropyDelta (m k : ℕ) : ℝ :=
  - (carterPollardN m / 2) *
    (((1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
      (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k)) -
      carterPollardEps m k ^ 2)

/-- Paper-shaped Δ with the entropy expression left explicit, before the
optional rewrite through `γ(ε)`. -/
noncomputable def carterPollardDeltaPaperShape (m k : ℕ) : ℝ :=
  Real.log (1 + (carterPollardN m)⁻¹) +
    carterPollardLambda m k -
      (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
        carterPollardEntropyDelta m k

/-- In the Carter--Pollard upper-half non-extreme range, all three
Stirling-correction indices `N`, `K`, and `N-K` are positive. -/
theorem carterPollard_lambda_indices_pos
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    1 ≤ m - 1 ∧ 1 ≤ carterPollardK m k ∧ 1 ≤ carterPollardNK m k := by
  dsimp [carterPollardK, carterPollardNK]
  omega

/-- In the Carter--Pollard range, `K + (N-K) = N` at the Nat level. -/
theorem carterPollardK_add_NK_eq_N
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    carterPollardK m k + carterPollardNK m k = m - 1 := by
  dsimp [carterPollardK, carterPollardNK]
  omega

/-- Factorial form of the binomial coefficient in the Carter--Pollard range. -/
theorem carterPollard_choose_eq_factorial_div
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    (((m - 1).choose (k - 1) : ℕ) : ℝ) =
      ((m - 1).factorial : ℝ) /
        (((carterPollardK m k).factorial : ℝ) *
          ((carterPollardNK m k).factorial : ℝ)) := by
  have hle : k - 1 ≤ m - 1 := by omega
  have hsplit : (m - 1) - (k - 1) = carterPollardNK m k := by
    unfold carterPollardNK
    omega
  have hK : k - 1 = carterPollardK m k := by
    unfold carterPollardK
    rfl
  have hchoose_mul_nat :=
    Nat.choose_mul_factorial_mul_factorial (n := m - 1) (k := k - 1) hle
  have hchoose_mul :
      (((m - 1).choose (k - 1) : ℕ) : ℝ) *
          ((carterPollardK m k).factorial : ℝ) *
          ((carterPollardNK m k).factorial : ℝ) =
        ((m - 1).factorial : ℝ) := by
    rw [← hK, ← hsplit]
    exact_mod_cast hchoose_mul_nat
  have hden_pos :
      0 < ((carterPollardK m k).factorial : ℝ) *
        ((carterPollardNK m k).factorial : ℝ) := by
    positivity
  rw [eq_div_iff hden_pos.ne']
  rw [← hchoose_mul]
  ring

/-- The Lean instantiated `N` is the real number `m - 1`. -/
theorem carterPollardN_eq_sub_one
    {m : ℕ} (hm : 2 ≤ m) :
    carterPollardN m = (m : ℝ) - 1 := by
  unfold carterPollardN
  rw [Nat.cast_sub (show 1 ≤ m by omega)]
  norm_num

/-- Exact real form of `K = N(1+ε)/2`. -/
theorem carterPollardK_real_eq_N_mul_one_add_eps_div_two
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    ((carterPollardK m k : ℕ) : ℝ) =
      carterPollardN m * (1 + carterPollardEps m k) / 2 := by
  have hm2 : 2 ≤ m := by omega
  have hk1 : 1 ≤ k := by omega
  have hN_eq := carterPollardN_eq_sub_one (m := m) hm2
  have hden : (m : ℝ) - 1 ≠ 0 := by
    rw [← hN_eq]
    unfold carterPollardN
    exact ne_of_gt (by exact_mod_cast (show (0 : ℕ) < m - 1 by omega) : 0 < ((m - 1 : ℕ) : ℝ))
  have hK_cast : ((carterPollardK m k : ℕ) : ℝ) = (k : ℝ) - 1 := by
    unfold carterPollardK
    rw [Nat.cast_sub hk1]
    norm_num
  rw [hK_cast, hN_eq]
  unfold carterPollardEps
  field_simp [hden]
  ring

/-- Exact real form of `N-K = N(1-ε)/2`. -/
theorem carterPollardNK_real_eq_N_mul_one_sub_eps_div_two
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    ((carterPollardNK m k : ℕ) : ℝ) =
      carterPollardN m * (1 - carterPollardEps m k) / 2 := by
  have hm2 : 2 ≤ m := by omega
  have hkm : k ≤ m := by omega
  have hN_eq := carterPollardN_eq_sub_one (m := m) hm2
  have hden : (m : ℝ) - 1 ≠ 0 := by
    rw [← hN_eq]
    unfold carterPollardN
    exact ne_of_gt (by exact_mod_cast (show (0 : ℕ) < m - 1 by omega) : 0 < ((m - 1 : ℕ) : ℝ))
  have hNK_cast : ((carterPollardNK m k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
    unfold carterPollardNK
    rw [Nat.cast_sub hkm]
  rw [hNK_cast, hN_eq]
  unfold carterPollardEps
  field_simp [hden]
  ring

/-- The factors `1+ε` and `1-ε` are positive in the non-extreme range. -/
theorem carterPollard_one_add_eps_pos
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    0 < 1 + carterPollardEps m k := by
  have hK_pos : (0 : ℝ) < ((carterPollardK m k : ℕ) : ℝ) := by
    exact_mod_cast (carterPollard_lambda_indices_pos hm hk_lower hk_upper).2.1
  have hN_pos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
  have hK := carterPollardK_real_eq_N_mul_one_add_eps_div_two hm hk_lower hk_upper
  have hprod : 0 < carterPollardN m * (1 + carterPollardEps m k) / 2 := by
    simpa [← hK] using hK_pos
  nlinarith [hN_pos]

/-- The factor `1-ε` is positive in the non-extreme range. -/
theorem carterPollard_one_sub_eps_pos
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    0 < 1 - carterPollardEps m k := by
  have hNK_pos : (0 : ℝ) < ((carterPollardNK m k : ℕ) : ℝ) := by
    exact_mod_cast (carterPollard_lambda_indices_pos hm hk_lower hk_upper).2.2
  have hN_pos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
  have hNK := carterPollardNK_real_eq_N_mul_one_sub_eps_div_two hm hk_lower hk_upper
  have hprod : 0 < carterPollardN m * (1 - carterPollardEps m k) / 2 := by
    simpa [← hNK] using hNK_pos
  nlinarith [hN_pos]

/-- The factor `1-ε^2` is positive in the non-extreme range. -/
theorem carterPollard_one_sub_eps_sq_pos
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    0 < 1 - carterPollardEps m k ^ 2 := by
  have hp := carterPollard_one_add_eps_pos hm hk_lower hk_upper
  have hm' := carterPollard_one_sub_eps_pos hm hk_lower hk_upper
  have hfactor :
      1 - carterPollardEps m k ^ 2 =
        (1 + carterPollardEps m k) * (1 - carterPollardEps m k) := by ring
  rw [hfactor]
  positivity

/-- The Stirling core in formula (3) is positive whenever `j ≥ 1`. -/
theorem carterPollardStirlingCore_pos {j : ℕ} (hj : 1 ≤ j) :
    0 < carterPollardStirlingCore j := by
  unfold carterPollardStirlingCore
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  positivity

/-- Formula (3), stated as an exponential identity for the local `λ_j`. -/
theorem carterPollardLambdaTerm_exp_eq
    {j : ℕ} (hj : 1 ≤ j) :
    Real.exp (carterPollardLambdaTerm j) =
      (j.factorial : ℝ) / carterPollardStirlingCore j := by
  unfold carterPollardLambdaTerm
  have hcore_pos := carterPollardStirlingCore_pos hj
  have hratio_pos : 0 < (j.factorial : ℝ) / carterPollardStirlingCore j := by
    positivity
  exact Real.exp_log hratio_pos

/-- Multiplicative form of `exp(Λ)` from formula (3). -/
theorem carterPollardLambda_exp_eq
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    Real.exp (carterPollardLambda m k) =
      ((m - 1).factorial : ℝ) *
        carterPollardStirlingCore (carterPollardK m k) *
        carterPollardStirlingCore (carterPollardNK m k) /
      (((carterPollardK m k).factorial : ℝ) *
        ((carterPollardNK m k).factorial : ℝ) *
        carterPollardStirlingCore (m - 1)) := by
  rcases carterPollard_lambda_indices_pos hm hk_lower hk_upper with ⟨hN, hK, hNK⟩
  have hcoreN := (carterPollardStirlingCore_pos hN).ne'
  have hcoreK := (carterPollardStirlingCore_pos hK).ne'
  have hcoreNK := (carterPollardStirlingCore_pos hNK).ne'
  have hfactK : (((carterPollardK m k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
  have hfactNK : (((carterPollardNK m k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
  unfold carterPollardLambda
  rw [Real.exp_sub, Real.exp_sub]
  rw [carterPollardLambdaTerm_exp_eq hN,
    carterPollardLambdaTerm_exp_eq hK,
    carterPollardLambdaTerm_exp_eq hNK]
  field_simp [hcoreN, hcoreK, hcoreNK, hfactK, hfactNK]

/-- Multiplicative form of the explicit entropy term before the optional
rewrite through `γ(ε)`. -/
theorem carterPollardEntropyDelta_exp_eq
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    Real.exp (carterPollardEntropyDelta m k) =
      Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2) *
        (((1 + carterPollardEps m k) ^ (carterPollardK m k) *
          (1 - carterPollardEps m k) ^ (carterPollardNK m k))⁻¹) := by
  have hp := carterPollard_one_add_eps_pos hm hk_lower hk_upper
  have hm' := carterPollard_one_sub_eps_pos hm hk_lower hk_upper
  have hK := carterPollardK_real_eq_N_mul_one_add_eps_div_two hm hk_lower hk_upper
  have hNK := carterPollardNK_real_eq_N_mul_one_sub_eps_div_two hm hk_lower hk_upper
  have h_entropy :
      carterPollardEntropyDelta m k =
        - ((((carterPollardK m k : ℕ) : ℝ) * Real.log (1 + carterPollardEps m k) +
            (((carterPollardNK m k : ℕ) : ℝ) * Real.log (1 - carterPollardEps m k)))) +
          carterPollardN m * carterPollardEps m k ^ 2 / 2 := by
    unfold carterPollardEntropyDelta
    rw [hK, hNK]
    ring
  rw [h_entropy, Real.exp_add, Real.exp_neg, Real.exp_add]
  have hpowK :
      Real.exp (((carterPollardK m k : ℕ) : ℝ) *
          Real.log (1 + carterPollardEps m k)) =
        (1 + carterPollardEps m k) ^ (carterPollardK m k) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hp, Real.rpow_natCast]
  have hpowNK :
      Real.exp (((carterPollardNK m k : ℕ) : ℝ) *
          Real.log (1 - carterPollardEps m k)) =
        (1 - carterPollardEps m k) ^ (carterPollardNK m k) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hm', Real.rpow_natCast]
  rw [hpowK, hpowNK]
  ring

private lemma exp_neg_half_log_eq_inv_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (-(1 / 2 : ℝ) * Real.log x) = (Real.sqrt x)⁻¹ := by
  have hsqrt :
      Real.exp ((1 / 2 : ℝ) * Real.log x) = Real.sqrt x := by
    rw [show (1 / 2 : ℝ) * Real.log x = Real.log x * (1 / 2 : ℝ) by ring]
    rw [Real.exp_mul, Real.exp_log hx, ← Real.sqrt_eq_rpow]
  rw [show -(1 / 2 : ℝ) * Real.log x = -((1 / 2 : ℝ) * Real.log x) by ring]
  rw [Real.exp_neg, hsqrt]

/-- Exponential factorization of the paper-shaped entropy Δ. This is the safe
multiplicative form used before the final raw-prefactor equality. -/
theorem carterPollardDeltaPaperShape_exp_eq_factorized
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    Real.exp (carterPollardDeltaPaperShape m k) =
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (carterPollardLambda m k) *
        (Real.sqrt (1 - carterPollardEps m k ^ 2))⁻¹ *
        Real.exp (carterPollardEntropyDelta m k) := by
  have hN_pos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
  have hlog_pos : 0 < 1 + (carterPollardN m)⁻¹ := by positivity
  have hsq_pos := carterPollard_one_sub_eps_sq_pos hm hk_lower hk_upper
  unfold carterPollardDeltaPaperShape
  rw [show Real.log (1 + (carterPollardN m)⁻¹) + carterPollardLambda m k -
        (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
          carterPollardEntropyDelta m k =
        Real.log (1 + (carterPollardN m)⁻¹) + carterPollardLambda m k +
          (-(1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2)) +
            carterPollardEntropyDelta m k by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hlog_pos,
    exp_neg_half_log_eq_inv_sqrt hsq_pos]

/-- Debt-free Robbins bounds available from the current local Stirling API.

The paper has the sharper strict lower bound `(12*j+1)⁻¹ < λ_j`; TC19 only
needs the nonnegative lower bound plus the sharp upper bound for infrastructure. -/
theorem carterPollardLambdaTerm_nonneg_le
    {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ carterPollardLambdaTerm j ∧
      carterPollardLambdaTerm j ≤ 1 / (12 * (j : ℝ)) := by
  have hcore_pos := carterPollardStirlingCore_pos hj
  have hratio_pos : 0 < (j.factorial : ℝ) / carterPollardStirlingCore j := by
    positivity
  have hratio_ge_one :
      1 ≤ (j.factorial : ℝ) / carterPollardStirlingCore j := by
    have hlow := Erdos524.Helpers.sqrt_two_pi_mul_pow_le_factorial j
    rw [show Real.sqrt (2 * Real.pi * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j =
        carterPollardStirlingCore j by rfl] at hlow
    exact (le_div_iff₀ hcore_pos).mpr (by simpa using hlow)
  have hnonneg : 0 ≤ carterPollardLambdaTerm j := by
    unfold carterPollardLambdaTerm
    exact Real.log_nonneg hratio_ge_one
  have hratio_le :
      (j.factorial : ℝ) / carterPollardStirlingCore j ≤
        Real.exp (1 / (12 * (j : ℝ))) := by
    have hupper := Erdos524.Helpers.factorial_le_stirling_robbins (n := j) hj
    rw [show Real.sqrt (2 * Real.pi * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j =
        carterPollardStirlingCore j by rfl] at hupper
    exact (div_le_iff₀ hcore_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hupper)
  have hle : carterPollardLambdaTerm j ≤ 1 / (12 * (j : ℝ)) := by
    unfold carterPollardLambdaTerm
    exact (Real.log_le_iff_le_exp hratio_pos).mpr hratio_le
  exact ⟨hnonneg, hle⟩

/-- Robbins bounds for all three `λ` terms that occur in
`Λ = λ_N - λ_K - λ_(N-K)` in the Carter--Pollard range. -/
theorem carterPollardLambdaTerm_bounds_of_range
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    (0 ≤ carterPollardLambdaTerm (m - 1) ∧
        carterPollardLambdaTerm (m - 1) ≤ 1 / (12 * ((m - 1 : ℕ) : ℝ))) ∧
      (0 ≤ carterPollardLambdaTerm (carterPollardK m k) ∧
        carterPollardLambdaTerm (carterPollardK m k) ≤
          1 / (12 * ((carterPollardK m k : ℕ) : ℝ))) ∧
      (0 ≤ carterPollardLambdaTerm (carterPollardNK m k) ∧
        carterPollardLambdaTerm (carterPollardNK m k) ≤
          1 / (12 * ((carterPollardNK m k : ℕ) : ℝ))) := by
  rcases carterPollard_lambda_indices_pos hm hk_lower hk_upper with ⟨hN, hK, hNK⟩
  exact ⟨carterPollardLambdaTerm_nonneg_le hN,
    carterPollardLambdaTerm_nonneg_le hK,
    carterPollardLambdaTerm_nonneg_le hNK⟩

/-- Positivity of the exact raw Carter--Pollard prefactor in the nonempty
binomial-tail range. -/
theorem carterPollardPrefactorRaw_pos
    {m k : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    0 < carterPollardPrefactorRaw m k := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hchoose_pos : (0 : ℝ) < ((m - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast (Nat.choose_pos (show k - 1 ≤ m - 1 by omega))
  have hN_pos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show 0 < m - 1 by omega)
  unfold carterPollardPrefactorRaw
  positivity

lemma carterPollardDeltaRaw_exp_eq_prefactor
    {m k : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    Real.exp (carterPollardDeltaRaw m k) = carterPollardPrefactorRaw m k := by
  unfold carterPollardDeltaRaw
  exact Real.exp_log (carterPollardPrefactorRaw_pos hm hk hkm)

/-- TC18 loose explicit upper bound for the exact raw `exp(Δ)` prefactor.

This uses only the elementary in-tree bound
`m * choose (m-1) (k-1) ≤ m^k/(k-1)!`. It is intentionally weaker than the
paper's Robbins-expanded `Δ` estimate, but it exposes the remaining finite
Stirling/entropy gap without adding debt. -/
theorem carterPollardDeltaRaw_exp_le_stirling_prefactor
    {m k : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    Real.exp (carterPollardDeltaRaw m k) ≤
      ((m : ℝ) ^ k / ((k - 1).factorial : ℝ)) *
        ((1 / 2 : ℝ) ^ m *
          Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2)) *
        (Real.sqrt (2 * Real.pi) * (Real.sqrt (carterPollardN m))⁻¹) := by
  rw [carterPollardDeltaRaw_exp_eq_prefactor hm hk hkm]
  unfold carterPollardPrefactorRaw
  have hcoeff := Erdos524.Helpers.stirling_prefactor_bound (k := k) (m := m) hk hkm
  have hrest_nonneg :
      0 ≤
        ((1 / 2 : ℝ) ^ m *
          Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2)) *
        (Real.sqrt (2 * Real.pi) * (Real.sqrt (carterPollardN m))⁻¹) := by
    have hN_pos : 0 < carterPollardN m := by
      unfold carterPollardN
      exact_mod_cast (show 0 < m - 1 by omega)
    positivity
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hrest_nonneg

/-- Logarithmic form of the loose TC18 prefactor bound. The sharper
Carter--Pollard paper bound still requires the Robbins `λ` and `γ` expansion. -/
theorem carterPollardDeltaRaw_le_log_stirling_prefactor
    {m k : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m) :
    carterPollardDeltaRaw m k ≤
      Real.log
        (((m : ℝ) ^ k / ((k - 1).factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ m *
            Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2)) *
          (Real.sqrt (2 * Real.pi) * (Real.sqrt (carterPollardN m))⁻¹)) := by
  have hbound := carterPollardDeltaRaw_exp_le_stirling_prefactor hm hk hkm
  have hrhs_pos :
      0 <
        ((m : ℝ) ^ k / ((k - 1).factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ m *
            Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2)) *
          (Real.sqrt (2 * Real.pi) * (Real.sqrt (carterPollardN m))⁻¹) := by
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show 0 < m by omega)
    have hN_pos : 0 < carterPollardN m := by
      unfold carterPollardN
      exact_mod_cast (show 0 < m - 1 by omega)
    positivity
  exact (Real.le_log_iff_exp_le hrhs_pos).mpr hbound

/-- TC17 normalized Gaussian-tail version of the TC16 raw bound.

This only rewrites the raw integral tail as
`exp(Δ_raw) * gaussianTailRaw`; it does not compare `Δ_raw` with the paper's
Stirling-expanded `Δ`, and it does not perform quantile inversion. -/
theorem binomialPolyTail_half_le_exp_delta_mul_gaussian_tail_instantiated
    {m k : ℕ}
    (hm : 2 ≤ m)
    (hk : 1 ≤ k) (hkm : k ≤ m)
    (hε0 : 0 ≤ carterPollardEps m k) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      Real.exp (carterPollardDeltaRaw m k) *
        gaussianTailRaw
          (Real.sqrt (carterPollardN m) * carterPollardEps m k) := by
  have hraw := binomialPolyTail_half_le_gaussian_tail_instantiated
    (m := m) (k := k) hm hk hkm (by simpa [carterPollardEps] using hε0)
  have hraw_def :
      Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
        ((m : ℝ) * ((m - 1).choose (k - 1) : ℝ)) *
          ((1 / 2 : ℝ) ^ m *
            Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2) *
            ((Real.sqrt (carterPollardN m))⁻¹ *
              ∫ t in Set.Ioi
                (Real.sqrt (carterPollardN m) * carterPollardEps m k),
                Real.exp (-t ^ 2 / 2))) := by
    simpa [carterPollardN, carterPollardEps] using hraw
  have hnorm :
      ((m : ℝ) * ((m - 1).choose (k - 1) : ℝ)) *
          ((1 / 2 : ℝ) ^ m *
            Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2) *
            ((Real.sqrt (carterPollardN m))⁻¹ *
              ∫ t in Set.Ioi
                (Real.sqrt (carterPollardN m) * carterPollardEps m k),
                Real.exp (-t ^ 2 / 2))) =
        Real.exp (carterPollardDeltaRaw m k) *
          gaussianTailRaw
            (Real.sqrt (carterPollardN m) * carterPollardEps m k) := by
    rw [carterPollardDeltaRaw_exp_eq_prefactor hm hk hkm]
    unfold carterPollardPrefactorRaw gaussianTailRaw
    set A : ℝ :=
      ((m : ℝ) * ((m - 1).choose (k - 1) : ℝ)) *
        ((1 / 2 : ℝ) ^ m *
          Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2))
    set S : ℝ := Real.sqrt (2 * Real.pi)
    set R : ℝ := Real.sqrt (carterPollardN m)
    set T : ℝ :=
      ∫ t in Set.Ioi (Real.sqrt (carterPollardN m) * carterPollardEps m k),
        Real.exp (-t ^ 2 / 2)
    have hS_ne : S ≠ 0 := by
      dsimp [S]
      positivity
    field_simp [hS_ne]
    ring
  rw [hnorm] at hraw_def
  exact hraw_def

end FormalConjectures.ErdosProblems.Helpers.CarterPollardH
