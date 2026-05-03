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
import FormalConjectures.ErdosProblems.Helpers.GaussianMillsRatio
import FormalConjectures.ErdosProblems.Helpers.OneDimKMT
import FormalConjectures.ErdosProblems.Helpers.StirlingTwoSided
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Carter--Pollard equation (7) bridge

This file isolates the raw Beta-integral-to-`h`-integral step in the
Carter--Pollard chain. It deliberately keeps `N` and `ε` abstract through
the two exponent-matching hypotheses, and it does not instantiate the final
Tusnády constants.
-/

namespace FormalConjectures.ErdosProblems.Helpers.CarterPollardH

open Real Set ProbabilityTheory
open scoped NNReal

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
  ring_nf

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

/-! ### TC31 CDF/event bridges -/

/-- TC31 finite-support CDF bridge for the real-valued half-binomial law.

The CDF at `k - 1` is the complement of the analytic upper-tail polynomial. -/
theorem binomialReal_cdf_pred_eq_one_sub_binomialPolyTail_half
    {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    cdf
      ((PMF.binomial (1 / 2 : ℝ≥0) (by norm_num) m).toMeasure.map
        (fun (i : Fin (m + 1)) => (i.val : ℝ)))
      ((k - 1 : ℕ) : ℝ) =
      1 - Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) := by
  classical
  let p : PMF (Fin (m + 1)) := PMF.binomial (1 / 2 : ℝ≥0) (by norm_num) m
  let f : Fin (m + 1) → ℝ := fun i => (i.val : ℝ)
  let tail : Set (Fin (m + 1)) := {i | k ≤ (i : ℕ)}
  have hf : Measurable f := by fun_prop
  haveI : MeasureTheory.IsProbabilityMeasure (p.toMeasure.map f) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hf.aemeasurable
  have htail_meas : MeasurableSet tail :=
    (Set.finite_univ.subset (by intro i hi; trivial)).measurableSet
  have hpre : f ⁻¹' Set.Iic (((k - 1 : ℕ) : ℝ)) = tailᶜ := by
    ext i
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_compl_iff]
    change (((i : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ)) ↔ ¬ k ≤ (i : ℕ)
    constructor
    · intro hi hik
      have hi_nat : (i : ℕ) ≤ k - 1 := by exact_mod_cast hi
      omega
    · intro hnot
      have hi_lt : (i : ℕ) < k := Nat.lt_of_not_ge hnot
      have hi_nat : (i : ℕ) ≤ k - 1 := by omega
      exact_mod_cast hi_nat
  rw [ProbabilityTheory.cdf_eq_real]
  rw [MeasureTheory.map_measureReal_apply hf measurableSet_Iic]
  change p.toMeasure.real (f ⁻¹' Set.Iic (((k - 1 : ℕ) : ℝ))) =
    1 - Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ)
  rw [hpre, MeasureTheory.probReal_compl_eq_one_sub htail_meas]
  congr 1
  have hpoly := Erdos524.Helpers.binomialPolyTail_eq_pmf_tail
    (m := m) (k := k) hk hkm (1 / 2 : ℝ≥0) (by norm_num)
  simpa [p, tail, MeasureTheory.Measure.real,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ htail_meas]
    using hpoly.symm

/-- TC31 standard-Gaussian CDF bridge, proved directly from the local density
and raw-tail integral definitions. -/
theorem gaussianReal_zero_one_cdf_eq_one_sub_gaussianTailRaw
    (x : ℝ) :
    cdf (gaussianReal 0 1) x = 1 - gaussianTailRaw x := by
  have hIoi_real : (gaussianReal 0 1).real (Set.Ioi x) = gaussianTailRaw x := by
    have hpdf_unfold :
        ∀ t : ℝ, gaussianPDFReal 0 1 t =
          (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
      intro t
      show (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
           Real.exp (-(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)
      rw [NNReal.coe_one]
      ring_nf
    have hnonneg : 0 ≤ ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun t => gaussianPDFReal_nonneg 0 1 t)
    have h_int : ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t = gaussianTailRaw x := by
      unfold gaussianTailRaw
      simp_rw [hpdf_unfold]
      rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.Measure.real]
    rw [gaussianReal_apply_eq_integral 0 (v := (1 : ℝ≥0)) (by norm_num) (Set.Ioi x)]
    rw [ENNReal.toReal_ofReal hnonneg]
    exact h_int
  rw [ProbabilityTheory.cdf_eq_real]
  have hcompl := MeasureTheory.probReal_compl_eq_one_sub
    (μ := gaussianReal 0 (1 : ℝ≥0)) (s := Set.Ioi x) measurableSet_Ioi
  have hcompl_set : (Set.Ioi x : Set ℝ)ᶜ = Set.Iic x := by
    ext t
    simp
  rw [← hcompl_set, hcompl, hIoi_real]

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

/-- Exact product form of the Carter--Pollard denominator factor
`1 - ε^2`. -/
theorem carterPollard_one_sub_eps_sq_eq_four_K_mul_NK_div_N_sq
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    1 - carterPollardEps m k ^ 2 =
      4 * ((carterPollardK m k : ℕ) : ℝ) *
        ((carterPollardNK m k : ℕ) : ℝ) / carterPollardN m ^ 2 := by
  have hK := carterPollardK_real_eq_N_mul_one_add_eps_div_two hm hk_lower hk_upper
  have hNK := carterPollardNK_real_eq_N_mul_one_sub_eps_div_two hm hk_lower hk_upper
  have hN_ne : carterPollardN m ≠ 0 := by
    have hN_pos : 0 < carterPollardN m := by
      unfold carterPollardN
      exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
    exact hN_pos.ne'
  rw [hK, hNK]
  field_simp [hN_ne]
  ring

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

private theorem carterPollard_delta_power_cancellation
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    ((((carterPollardK m k : ℝ) / Real.exp 1) ^ carterPollardK m k) *
        (((carterPollardNK m k : ℝ) / Real.exp 1) ^ carterPollardNK m k) /
        ((carterPollardN m / Real.exp 1) ^ (m - 1)) *
        (((1 + carterPollardEps m k) ^ carterPollardK m k *
          (1 - carterPollardEps m k) ^ carterPollardNK m k)⁻¹)) =
      ((1 / 2 : ℝ) ^ (m - 1)) := by
  have hp := carterPollard_one_add_eps_pos hm hk_lower hk_upper
  have hm' := carterPollard_one_sub_eps_pos hm hk_lower hk_upper
  have hNpos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
  have hK_eq := carterPollardK_real_eq_N_mul_one_add_eps_div_two hm hk_lower hk_upper
  have hNK_eq := carterPollardNK_real_eq_N_mul_one_sub_eps_div_two hm hk_lower hk_upper
  have hK_add := carterPollardK_add_NK_eq_N hm hk_lower hk_upper
  have hbaseK :
      (((carterPollardK m k : ℕ) : ℝ) / Real.exp 1) =
        (carterPollardN m / Real.exp 1) * ((1 + carterPollardEps m k) / 2) := by
    rw [hK_eq]
    ring
  have hbaseNK :
      (((carterPollardNK m k : ℕ) : ℝ) / Real.exp 1) =
        (carterPollardN m / Real.exp 1) * ((1 - carterPollardEps m k) / 2) := by
    rw [hNK_eq]
    ring
  rw [hbaseK, hbaseNK]
  rw [mul_pow, mul_pow]
  rw [show (carterPollardN m / Real.exp 1) ^ (carterPollardK m k) *
        ((1 + carterPollardEps m k) / 2) ^ (carterPollardK m k) *
        ((carterPollardN m / Real.exp 1) ^ (carterPollardNK m k) *
          ((1 - carterPollardEps m k) / 2) ^ (carterPollardNK m k)) =
        ((carterPollardN m / Real.exp 1) ^ (carterPollardK m k) *
          (carterPollardN m / Real.exp 1) ^ (carterPollardNK m k)) *
          (((1 + carterPollardEps m k) / 2) ^ (carterPollardK m k) *
            ((1 - carterPollardEps m k) / 2) ^ (carterPollardNK m k)) by ring]
  rw [← pow_add, hK_add]
  have hNdiv_ne : carterPollardN m / Real.exp 1 ≠ 0 := by positivity
  have hp_ne : 1 + carterPollardEps m k ≠ 0 := hp.ne'
  have hm_ne : 1 - carterPollardEps m k ≠ 0 := hm'.ne'
  field_simp [pow_ne_zero _ hNdiv_ne]
  rw [div_pow, div_pow]
  field_simp [hp_ne, hm_ne]
  rw [← pow_add, hK_add]
  rw [show ((1 / 2 : ℝ) ^ (m - 1)) = (((2 : ℝ) ^ (m - 1))⁻¹) by
    rw [one_div, inv_pow]]
  rw [mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]

private theorem carterPollard_delta_sqrt_cancellation
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    (Real.sqrt (2 * Real.pi * ((carterPollardK m k : ℕ) : ℝ)) *
          Real.sqrt (2 * Real.pi * ((carterPollardNK m k : ℕ) : ℝ)) /
        Real.sqrt (2 * Real.pi * carterPollardN m)) *
      (Real.sqrt (1 - carterPollardEps m k ^ 2))⁻¹ =
        Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) / 2 := by
  have hp := carterPollard_one_add_eps_pos hm hk_lower hk_upper
  have hm' := carterPollard_one_sub_eps_pos hm hk_lower hk_upper
  have hsq := carterPollard_one_sub_eps_sq_pos hm hk_lower hk_upper
  have hNpos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
  have hK_eq := carterPollardK_real_eq_N_mul_one_add_eps_div_two hm hk_lower hk_upper
  have hNK_eq := carterPollardNK_real_eq_N_mul_one_sub_eps_div_two hm hk_lower hk_upper
  have hsq_factor :
      1 - carterPollardEps m k ^ 2 =
        (1 + carterPollardEps m k) * (1 - carterPollardEps m k) := by ring
  rw [hK_eq, hNK_eq, hsq_factor]
  have hleft_nonneg :
      0 ≤
        (Real.sqrt (2 * Real.pi * (carterPollardN m * (1 + carterPollardEps m k) / 2)) *
              Real.sqrt (2 * Real.pi * (carterPollardN m * (1 - carterPollardEps m k) / 2)) /
            Real.sqrt (2 * Real.pi * carterPollardN m)) *
          (Real.sqrt ((1 + carterPollardEps m k) * (1 - carterPollardEps m k)))⁻¹ := by
    positivity
  have hright_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) / 2 := by
    positivity
  rw [← mul_self_inj_of_nonneg hleft_nonneg hright_nonneg]
  have hden1 : Real.sqrt (2 * Real.pi * carterPollardN m) ≠ 0 := by positivity
  have hden2 : Real.sqrt ((1 + carterPollardEps m k) * (1 - carterPollardEps m k)) ≠ 0 := by
    positivity
  field_simp [hden1, hden2]
  rw [sq_sqrt (by positivity : 0 ≤ Real.pi * carterPollardN m *
      (1 + carterPollardEps m k))]
  rw [sq_sqrt (by positivity : 0 ≤ Real.pi * carterPollardN m *
      (1 - carterPollardEps m k))]
  rw [sq_sqrt (by positivity : 0 ≤ 2 * Real.pi * carterPollardN m)]
  rw [sq_sqrt (by positivity : 0 ≤ (1 + carterPollardEps m k) *
      (1 - carterPollardEps m k))]
  rw [sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  rw [sq_sqrt hNpos.le]
  ring

private theorem carterPollard_delta_core_cancellation
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    (carterPollardStirlingCore (carterPollardK m k) *
          carterPollardStirlingCore (carterPollardNK m k) /
        carterPollardStirlingCore (m - 1)) *
      (Real.sqrt (1 - carterPollardEps m k ^ 2))⁻¹ *
      (((1 + carterPollardEps m k) ^ (carterPollardK m k) *
        (1 - carterPollardEps m k) ^ (carterPollardNK m k))⁻¹) =
        (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) / 2) *
          ((1 / 2 : ℝ) ^ (m - 1)) := by
  unfold carterPollardStirlingCore
  let A : ℝ := Real.sqrt (2 * Real.pi * ((carterPollardK m k : ℕ) : ℝ))
  let B : ℝ := Real.sqrt (2 * Real.pi * ((carterPollardNK m k : ℕ) : ℝ))
  let C : ℝ := Real.sqrt (2 * Real.pi * carterPollardN m)
  let P : ℝ := (((carterPollardK m k : ℕ) : ℝ) / Real.exp 1) ^ carterPollardK m k
  let Q : ℝ := (((carterPollardNK m k : ℕ) : ℝ) / Real.exp 1) ^ carterPollardNK m k
  let R : ℝ := (carterPollardN m / Real.exp 1) ^ (m - 1)
  let D : ℝ := (Real.sqrt (1 - carterPollardEps m k ^ 2))⁻¹
  let E : ℝ :=
    (((1 + carterPollardEps m k) ^ carterPollardK m k *
      (1 - carterPollardEps m k) ^ carterPollardNK m k)⁻¹)
  let F : ℝ := Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) / 2
  let G : ℝ := (1 / 2 : ℝ) ^ (m - 1)
  have hNpos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
  have hsqrt : (A * B / C) * D = F := by
    dsimp [A, B, C, D, F]
    exact carterPollard_delta_sqrt_cancellation hm hk_lower hk_upper
  have hpower : (P * Q / R) * E = G := by
    dsimp [P, Q, R, E, G]
    exact carterPollard_delta_power_cancellation hm hk_lower hk_upper
  change (A * P * (B * Q) / (C * R)) * D * E = F * G
  calc
    (A * P * (B * Q) / (C * R)) * D * E =
        ((A * B / C) * D) * ((P * Q / R) * E) := by
      have hC : C ≠ 0 := by
        dsimp [C]
        positivity
      have hR : R ≠ 0 := by
        dsimp [R]
        positivity
      field_simp [hC, hR]
    _ = F * G := by
      rw [hsqrt, hpower]

private theorem carterPollard_delta_prefactor_normalization
    {m : ℕ} (hm : 28 ≤ m) :
    (1 + (carterPollardN m)⁻¹) *
        (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) / 2) *
        ((1 / 2 : ℝ) ^ (m - 1)) =
      (m : ℝ) * ((1 / 2 : ℝ) ^ m) *
        (Real.sqrt (2 * Real.pi) * (Real.sqrt (carterPollardN m))⁻¹) := by
  have hm2 : 2 ≤ m := by omega
  have hNpos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show (0 : ℕ) < m - 1 by omega)
  have hN_ne : carterPollardN m ≠ 0 := hNpos.ne'
  have hsqrt_ne : Real.sqrt (carterPollardN m) ≠ 0 := by positivity
  have hN_eq := carterPollardN_eq_sub_one (m := m) hm2
  have hpow :
      ((1 / 2 : ℝ) ^ m) = ((1 / 2 : ℝ) ^ (m - 1)) * (1 / 2 : ℝ) := by
    nth_rewrite 1 [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow]
  rw [show Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) / 2 =
      Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) * (1 / 2 : ℝ) by ring]
  field_simp [hN_ne, hsqrt_ne]
  rw [sq_sqrt hNpos.le]
  rw [hN_eq]
  ring

/-- Exact multiplicative close between the raw Lean prefactor and the
paper-shaped entropy `Δ`, before any `γ` rewrite or tail-ratio estimate. -/
theorem carterPollardPrefactorRaw_eq_exp_deltaPaperShape
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    carterPollardPrefactorRaw m k =
      Real.exp (carterPollardDeltaPaperShape m k) := by
  let F : ℝ :=
    ((m - 1).factorial : ℝ) /
      (((carterPollardK m k).factorial : ℝ) *
        ((carterPollardNK m k).factorial : ℝ))
  let E : ℝ := Real.exp (carterPollardN m * carterPollardEps m k ^ 2 / 2)
  let C : ℝ :=
    (carterPollardStirlingCore (carterPollardK m k) *
          carterPollardStirlingCore (carterPollardNK m k) /
        carterPollardStirlingCore (m - 1)) *
      (Real.sqrt (1 - carterPollardEps m k ^ 2))⁻¹ *
      (((1 + carterPollardEps m k) ^ (carterPollardK m k) *
        (1 - carterPollardEps m k) ^ (carterPollardNK m k))⁻¹)
  let R : ℝ :=
    (m : ℝ) * ((1 / 2 : ℝ) ^ m) *
      (Real.sqrt (2 * Real.pi) * (Real.sqrt (carterPollardN m))⁻¹)
  have hk : 1 ≤ k := by omega
  have hkm : k ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hcoreN : carterPollardStirlingCore (m - 1) ≠ 0 := by
    have hN := (carterPollard_lambda_indices_pos hm hk_lower hk_upper).1
    exact (carterPollardStirlingCore_pos hN).ne'
  have hfactK : (((carterPollardK m k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
  have hfactNK : (((carterPollardNK m k).factorial : ℝ) : ℝ) ≠ 0 := by positivity
  have hraw :
      carterPollardPrefactorRaw m k = F * E * R := by
    unfold carterPollardPrefactorRaw
    rw [carterPollard_choose_eq_factorial_div hm hk_lower hk_upper]
    dsimp [F, E, R]
    ring
  have hpaper :
      Real.exp (carterPollardDeltaPaperShape m k) =
        F * E * ((1 + (carterPollardN m)⁻¹) * C) := by
    rw [carterPollardDeltaPaperShape_exp_eq_factorized hm hk_lower hk_upper,
      carterPollardLambda_exp_eq hm hk_lower hk_upper,
      carterPollardEntropyDelta_exp_eq hm hk_lower hk_upper]
    dsimp [F, E, C]
    field_simp [hcoreN, hfactK, hfactNK]
  have hC :
      C =
        (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) / 2) *
          ((1 / 2 : ℝ) ^ (m - 1)) := by
    dsimp [C]
    exact carterPollard_delta_core_cancellation hm hk_lower hk_upper
  have hnorm :
      (1 + (carterPollardN m)⁻¹) * C = R := by
    rw [hC]
    dsimp [R]
    simpa [mul_assoc] using carterPollard_delta_prefactor_normalization hm
  rw [hraw, hpaper, hnorm]

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

/-- TC22 exact raw/paper entropy-shape `Δ` equality in the Carter--Pollard
non-extreme upper-half range. -/
theorem carterPollardDeltaRaw_eq_deltaPaperShape
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    carterPollardDeltaRaw m k = carterPollardDeltaPaperShape m k := by
  have hk : 1 ≤ k := by omega
  have hkm : k ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  apply Real.exp_injective
  rw [carterPollardDeltaRaw_exp_eq_prefactor hm2 hk hkm,
    carterPollardPrefactorRaw_eq_exp_deltaPaperShape hm hk_lower hk_upper]

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

/-- TC24 direct Robbins upper bound for the Carter--Pollard
`Λ = λ_N - λ_K - λ_(N-K)` term. -/
theorem carterPollardLambda_le_robbins_upper_of_range
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    carterPollardLambda m k ≤ 1 / (12 * ((m - 1 : ℕ) : ℝ)) := by
  rcases carterPollardLambdaTerm_bounds_of_range hm hk_lower hk_upper with
    ⟨hN, hK, hNK⟩
  unfold carterPollardLambda
  linarith [hN.2, hK.1, hNK.1]

/-- TC24 direct entropy-shape upper bound for the paper-shaped
Carter--Pollard `Δ`, using only the Robbins upper bound for `Λ`. -/
theorem carterPollardDeltaPaperShape_le_entropy_shape_robbins_upper
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    carterPollardDeltaPaperShape m k ≤
      Real.log (1 + (carterPollardN m)⁻¹) +
        1 / (12 * ((m - 1 : ℕ) : ℝ)) -
          (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
            carterPollardEntropyDelta m k := by
  have hΛ := carterPollardLambda_le_robbins_upper_of_range hm hk_lower hk_upper
  unfold carterPollardDeltaPaperShape
  linarith

/-- In the Carter--Pollard upper-half range, the instantiated `ε` is
nonnegative. -/
theorem carterPollardEps_nonneg_of_upper_half_range
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) :
    0 ≤ carterPollardEps m k := by
  unfold carterPollardEps
  have hden_pos : 0 < (m : ℝ) - 1 := by
    have hm_real : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show (1 : ℕ) < m by omega)
    linarith
  have hnum_nat : m + 1 ≤ 2 * k := by omega
  have hnum_nonneg : 0 ≤ (2 : ℝ) * (k : ℝ) - (m : ℝ) - 1 := by
    have hcast : ((m + 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast hnum_nat
    norm_num at hcast ⊢
    linarith
  exact div_nonneg hnum_nonneg hden_pos.le

/-- At the odd midpoint edge `2*k = m + 1`, the Carter--Pollard instantiated
`ε` is exactly zero. This is the obstruction to using Mills truncation from
the bare upper-half hypothesis alone. -/
theorem carterPollardEps_eq_zero_of_two_mul_eq_succ
    {m k : ℕ}
    (hmid : 2 * k = m + 1) :
    carterPollardEps m k = 0 := by
  unfold carterPollardEps
  have hnum_zero : (2 : ℝ) * (k : ℝ) - (m : ℝ) - 1 = 0 := by
    have hcast : ((2 * k : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast hmid
    norm_num at hcast ⊢
    linarith
  rw [hnum_zero]
  simp

/-- Strict positivity of the Carter--Pollard instantiated `ε` after excluding
the midpoint edge. -/
theorem carterPollardEps_pos_of_succ_lt_two_mul
    {m k : ℕ}
    (hm : 28 ≤ m) (hstrict : m + 1 < 2 * k) :
    0 < carterPollardEps m k := by
  unfold carterPollardEps
  have hden_pos : 0 < (m : ℝ) - 1 := by
    have hm_real : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show (1 : ℕ) < m by omega)
    linarith
  have hnum_pos : 0 < (2 : ℝ) * (k : ℝ) - (m : ℝ) - 1 := by
    have hcast : ((m + 1 : ℕ) : ℝ) < ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast hstrict
    norm_num at hcast ⊢
    linarith
  exact div_pos hnum_pos hden_pos

/-- Strict positivity of the Mills-truncation argument
`sqrt(N) * ε`, under the strengthened threshold excluding the midpoint edge. -/
theorem carterPollard_sqrtN_mul_eps_pos_of_succ_lt_two_mul
    {m k : ℕ}
    (hm : 28 ≤ m) (hstrict : m + 1 < 2 * k) :
    0 < Real.sqrt (carterPollardN m) * carterPollardEps m k := by
  have hN_pos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show 0 < m - 1 by omega)
  have hsqrt_pos : 0 < Real.sqrt (carterPollardN m) := Real.sqrt_pos_of_pos hN_pos
  have hε_pos := carterPollardEps_pos_of_succ_lt_two_mul (m := m) (k := k) hm hstrict
  positivity

/-! ### TC35 scalar-event audit lemmas -/

/-- TC35 audit algebra: the Carter--Pollard affine center represented by
`Nε/2` is the real midpoint gap `k - (m + 1)/2`. -/
theorem carterPollard_N_mul_eps_div_two_eq_real_center
    {m k : ℕ}
    (hm : 28 ≤ m) :
    carterPollardN m * carterPollardEps m k / 2 =
      (k : ℝ) - ((m : ℝ) + 1) / 2 := by
  have hm1 : 1 ≤ m := by omega
  have hden : (m : ℝ) - 1 ≠ 0 := by
    have hm_real : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (show (1 : ℕ) < m by omega)
    linarith
  unfold carterPollardN carterPollardEps
  rw [Nat.cast_sub hm1]
  field_simp [hden]
  ring_nf

/-- TC35 audit algebra, even case: with `m = 2n`, the real Carter--Pollard
center is half a unit below the natural midpoint gap `k - n`. -/
theorem carterPollard_N_mul_eps_div_two_eq_even_nat_center_sub_half
    {n k : ℕ}
    (hn : 14 ≤ n) :
    carterPollardN (2 * n) * carterPollardEps (2 * n) k / 2 =
      (k : ℝ) - (n : ℝ) - 1 / 2 := by
  rw [carterPollard_N_mul_eps_div_two_eq_real_center
    (m := 2 * n) (k := k) (by omega)]
  have hcast : (((2 * n : ℕ) : ℝ)) = 2 * (n : ℝ) := by norm_num
  rw [hcast]
  ring

/-- TC35 audit algebra, odd case: with `m = 2n + 1`, the real
Carter--Pollard center is exactly the natural midpoint gap. -/
theorem carterPollard_N_mul_eps_div_two_eq_odd_nat_center
    {n k : ℕ}
    (hn : 14 ≤ n) :
    carterPollardN (2 * n + 1) * carterPollardEps (2 * n + 1) k / 2 =
      (k : ℝ) - ((n + 1 : ℕ) : ℝ) := by
  rw [carterPollard_N_mul_eps_div_two_eq_real_center
    (m := 2 * n + 1) (k := k) (by omega)]
  have hcast_m : (((2 * n + 1 : ℕ) : ℝ)) = 2 * (n : ℝ) + 1 := by norm_num
  have hcast_n : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
  rw [hcast_m, hcast_n]
  ring

/-- The stated Tusnády event hypothesis only gives that `z` lies strictly
below the natural midpoint gap. It does not by itself bound the strict
Carter--Pollard quadratic envelope by the Gaussian tail. -/
theorem carterPollard_event_implies_z_lt_nat_center_gap
    {m k : ℕ} {z : ℝ}
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (((m + 1) / 2 : ℕ) : ℝ) ≤
        ((k : ℝ) - (((m + 1) / 2 : ℕ) : ℝ))) :
    z < ((k : ℝ) - (((m + 1) / 2 : ℕ) : ℝ)) := by
  have hquad_nonneg :
      0 ≤ z ^ 2 / (((m + 1) / 2 : ℕ) : ℝ) := by
    positivity
  linarith

/-- The stated Tusnády event hypothesis forces the natural midpoint gap to be
positive. This is the maximal unconditional scalar consequence used by the
TC35 diagnostic. -/
theorem carterPollard_event_implies_nat_center_gap_pos
    {m k : ℕ} {z : ℝ}
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (((m + 1) / 2 : ℕ) : ℝ) ≤
        ((k : ℝ) - (((m + 1) / 2 : ℕ) : ℝ))) :
    0 < ((k : ℝ) - (((m + 1) / 2 : ℕ) : ℝ)) := by
  exact lt_trans hz_pos
    (carterPollard_event_implies_z_lt_nat_center_gap
      (m := m) (k := k) (z := z) hz_pos hz_event)

/-- Even-base TC35 audit: in the `m = 2n` case used by
`tusnady_base_polynomial`, the `0.6` slack in the event hypothesis places `z`
strictly below the real Carter--Pollard center `Nε/2`. This center comparison
is true, but it is still not enough to make the quadratic envelope a Gaussian
tail lower bound near the midpoint. -/
theorem carterPollard_even_event_implies_z_lt_N_mul_eps_div_two
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤
        ((k : ℝ) - (n : ℝ))) :
    z < carterPollardN (2 * n) * carterPollardEps (2 * n) k / 2 := by
  have hquad_nonneg : 0 ≤ z ^ 2 / (n : ℝ) := by positivity
  have hz_center : z < (k : ℝ) - (n : ℝ) - 1 / 2 := by
    nlinarith
  rw [carterPollard_N_mul_eps_div_two_eq_even_nat_center_sub_half
    (n := n) (k := k) hn]
  exact hz_center

/-! ### TC40 scaled Gaussian-tail correction -/

/-- TC40 raw-tail monotonicity, derived from the local standard-Gaussian CDF
bridge and `cdf` monotonicity. -/
theorem gaussianTailRaw_le_of_le {x y : ℝ} (hxy : x ≤ y) :
    gaussianTailRaw y ≤ gaussianTailRaw x := by
  have hcdf := (ProbabilityTheory.monotone_cdf (gaussianReal 0 (1 : ℝ≥0))) hxy
  rw [gaussianReal_zero_one_cdf_eq_one_sub_gaussianTailRaw,
    gaussianReal_zero_one_cdf_eq_one_sub_gaussianTailRaw] at hcdf
  linarith

/-- TC40 antitone form of raw standard-Gaussian upper-tail monotonicity. -/
theorem gaussianTailRaw_antitone : Antitone gaussianTailRaw := by
  intro x y hxy
  exact gaussianTailRaw_le_of_le hxy

/-- TC40 scaled Gaussian CDF bridge for the actual variance `n/2` appearing in
`tusnady_base_polynomial`.

The proof uses the Gaussian scaling map and then the local standard-tail CDF
bridge; it does not use `Real.Gaussian.compl_cdf`. -/
theorem gaussianReal_zero_nat_half_cdf_eq_one_sub_scaled_gaussianTailRaw
    {n : ℕ} (hn : 0 < n) (z : ℝ) :
    cdf (gaussianReal 0 (((n : ℝ≥0) / (2 : ℝ≥0)))) z =
      1 - gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) := by
  let σ : ℝ := Real.sqrt ((n : ℝ) / 2)
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    positivity
  have hσ_sq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hvar_eq :
      (⟨σ ^ 2, hσ_sq_nonneg⟩ : ℝ≥0) = ((n : ℝ≥0) / (2 : ℝ≥0)) := by
    apply Subtype.ext
    change σ ^ 2 = (n : ℝ) / 2
    dsimp [σ]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) / 2)]
  have hmap :
      MeasureTheory.Measure.map (fun x : ℝ => σ * x) (gaussianReal 0 (1 : ℝ≥0)) =
        gaussianReal 0 (((n : ℝ≥0) / (2 : ℝ≥0))) := by
    rw [gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) σ]
    simp [hvar_eq]
  rw [← hmap]
  haveI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.map (fun x : ℝ => σ * x) (gaussianReal 0 (1 : ℝ≥0))) :=
    MeasureTheory.Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable (fun x : ℝ => σ * x)
      (gaussianReal 0 (1 : ℝ≥0)))
  rw [ProbabilityTheory.cdf_eq_real]
  rw [MeasureTheory.map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun x : ℝ => σ * x) ⁻¹' Set.Iic z = Set.Iic (z / σ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact (le_div_iff₀' hσ_pos).symm
  rw [hpre]
  rw [← ProbabilityTheory.cdf_eq_real (gaussianReal 0 (1 : ℝ≥0)) (z / σ)]
  rw [gaussianReal_zero_one_cdf_eq_one_sub_gaussianTailRaw]

/-- TC40 even-case standardized threshold algebra. The corrected event
threshold implies that the physical Gaussian value `z` standardized by the
base variance `n/2` lies below the Carter--Pollard threshold
`sqrt(N) * ε`. -/
theorem carterPollard_even_event_implies_scaled_z_le_sqrtN_eps
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (_hk_upper : k ≤ 2 * n - 1)
    (_hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ))) :
    z / Real.sqrt ((n : ℝ) / 2) ≤
      Real.sqrt (carterPollardN (2 * n)) * carterPollardEps (2 * n) k := by
  let σ : ℝ := Real.sqrt ((n : ℝ) / 2)
  let N : ℝ := carterPollardN (2 * n)
  let ε : ℝ := carterPollardEps (2 * n) k
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    positivity
  have hN_pos : 0 < N := by
    dsimp [N, carterPollardN]
    exact_mod_cast (show 0 < 2 * n - 1 by omega)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact carterPollardEps_pos_of_succ_lt_two_mul
      (m := 2 * n) (k := k) (by omega) (by omega)
  have hz_center :
      z < carterPollardN (2 * n) * carterPollardEps (2 * n) k / 2 :=
    carterPollard_even_event_implies_z_lt_N_mul_eps_div_two
      (n := n) (k := k) (z := z) hn hz_event
  have hz_div :
      z / σ < (N * ε / 2) / σ := by
    exact div_lt_div_of_pos_right (by simpa [N, ε] using hz_center) hσ_pos
  have hN_eq : N = (2 * (n : ℝ)) - 1 := by
    dsimp [N]
    rw [carterPollardN_eq_sub_one (m := 2 * n) (by omega)]
    norm_num
  have hbase_sq :
      (N / 2) ^ 2 ≤ (Real.sqrt N * σ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN_pos.le]
    dsimp [σ]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) / 2)]
    rw [hN_eq]
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℕ) ≤ n by omega)
    nlinarith
  have hbase_nonneg : 0 ≤ N / 2 := by positivity
  have hright_nonneg : 0 ≤ Real.sqrt N * σ := by positivity
  have hbase_le : N / 2 ≤ Real.sqrt N * σ := by
    have h := (sq_le_sq.mp hbase_sq)
    simpa [abs_of_nonneg hbase_nonneg, abs_of_nonneg hright_nonneg] using h
  have hmul : N * ε / 2 ≤ (Real.sqrt N * ε) * σ := by
    have hmul' := mul_le_mul_of_nonneg_right hbase_le hε_pos.le
    nlinarith
  have hcenter_scaled : (N * ε / 2) / σ ≤ Real.sqrt N * ε := by
    exact (div_le_iff₀ hσ_pos).mpr (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  exact (le_of_lt hz_div).trans (by simpa [N, ε, σ] using hcenter_scaled)

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

/-- TC23 normalized Gaussian-tail route with the exact paper-shaped
entropy `Δ` exposed.

This is only the TC17 normalized tail theorem rewritten through the TC22
identity `Δ_raw = Δ_paperShape`; it does not bound `Δ_paperShape` and does not
perform any normal-tail comparison or quantile inversion. -/
theorem binomialPolyTail_half_le_exp_deltaPaperShape_mul_gaussian_tail_instantiated
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      Real.exp (carterPollardDeltaPaperShape m k) *
        gaussianTailRaw
          (Real.sqrt (carterPollardN m) * carterPollardEps m k) := by
  have hm2 : 2 ≤ m := by omega
  have hk : 1 ≤ k := by omega
  have hkm : k ≤ m := by omega
  have hε0 := carterPollardEps_nonneg_of_upper_half_range hm hk_lower
  have htail :=
    binomialPolyTail_half_le_exp_delta_mul_gaussian_tail_instantiated
      (m := m) (k := k) hm2 hk hkm hε0
  simpa [carterPollardDeltaRaw_eq_deltaPaperShape hm hk_lower hk_upper] using htail

/-- TC40 corrected scaled-tail transport for the existing paper-shaped
Carter--Pollard bound.

This is the strongest direct composition currently available without proving a
new Carter--Pollard tail-ratio theorem: the binomial tail is bounded by the
existing `exp(Δ_paperShape)` factor times the corrected scaled Gaussian tail.
Removing that visible factor is the remaining analytic TC41 consumer. -/
theorem binomialPolyTail_half_le_exp_deltaPaperShape_mul_scaled_gaussian_tail_of_event
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ))) :
    Erdos524.Helpers.binomialPolyTail (2 * n) k (1 / 2 : ℝ) ≤
      Real.exp (carterPollardDeltaPaperShape (2 * n) k) *
        gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) := by
  have hm : 28 ≤ 2 * n := by omega
  have hk_cp_lower : (2 * n) / 2 < k := by omega
  have hk_cp_upper : k ≤ 2 * n - 1 := hk_upper
  have htail :=
    binomialPolyTail_half_le_exp_deltaPaperShape_mul_gaussian_tail_instantiated
      (m := 2 * n) (k := k) hm hk_cp_lower hk_cp_upper
  have hscaled :
      z / Real.sqrt ((n : ℝ) / 2) ≤
        Real.sqrt (carterPollardN (2 * n)) * carterPollardEps (2 * n) k :=
    carterPollard_even_event_implies_scaled_z_le_sqrtN_eps
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event
  have htail_mono :
      gaussianTailRaw
          (Real.sqrt (carterPollardN (2 * n)) * carterPollardEps (2 * n) k) ≤
        gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) :=
    gaussianTailRaw_le_of_le hscaled
  have hmul := mul_le_mul_of_nonneg_left htail_mono
    (Real.exp_pos (carterPollardDeltaPaperShape (2 * n) k)).le
  exact le_trans htail hmul

/-- Nonnegativity of the raw normalized Gaussian upper tail. -/
theorem gaussianTailRaw_nonneg (x : ℝ) :
    0 ≤ gaussianTailRaw x := by
  unfold gaussianTailRaw
  have hint_nonneg :
      0 ≤ ∫ t in Set.Ioi x, Real.exp (-t ^ 2 / 2) := by
    exact MeasureTheory.integral_nonneg fun t => by positivity
  positivity

/-- The raw normalized Gaussian tail used by the Carter--Pollard bridge is
exactly the local Mills ratio times the standard Gaussian density. -/
theorem gaussianTailRaw_eq_millsRatio_mul_pdf (x : ℝ) :
    gaussianTailRaw x =
      Erdos524.Helpers.gaussianMillsRatioReal x * gaussianPDFReal 0 1 x := by
  set c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hc_def
  have hpdf_unfold : ∀ t : ℝ, gaussianPDFReal 0 1 t = c * Real.exp (-t ^ 2 / 2) := by
    intro t
    show (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
         Real.exp (-(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) = c * Real.exp (-t ^ 2 / 2)
    rw [hc_def, NNReal.coe_one]
    ring_nf
  have htail_pdf :
      ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t =
        c * ∫ t in Set.Ioi x, Real.exp (-t ^ 2 / 2) := by
    have hfun :
        (fun t : ℝ => gaussianPDFReal 0 1 t) =
          fun t : ℝ => c * Real.exp (-t ^ 2 / 2) := by
      funext t
      exact hpdf_unfold t
    rw [hfun, MeasureTheory.integral_const_mul]
  have hpdf_pos : 0 < gaussianPDFReal 0 1 x :=
    gaussianPDFReal_pos 0 1 x (by norm_num)
  unfold gaussianTailRaw Erdos524.Helpers.gaussianMillsRatioReal
  rw [htail_pdf]
  field_simp [hpdf_pos.ne']
  rw [hc_def]
  field_simp [show Real.sqrt (2 * Real.pi) ≠ 0 by positivity]

/-- Strict positivity of the raw normalized Gaussian upper tail at positive
arguments. -/
theorem gaussianTailRaw_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < gaussianTailRaw x := by
  rw [gaussianTailRaw_eq_millsRatio_mul_pdf]
  exact mul_pos
    (Erdos524.Helpers.gaussianMillsRatioReal_pos hx)
    (gaussianPDFReal_pos 0 1 x (by norm_num))

/-- Explicit density form of the standard-Gaussian PDF used in the
Carter--Pollard envelope. -/
theorem gaussianPDFReal_zero_one_eq_inv_sqrt_mul_exp (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  show (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
       Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
  rw [NNReal.coe_one]
  ring_nf

/-- Mills antitonicity gives the density-ratio part of a Gaussian tail-ratio
comparison. This is true but, near the midpoint edge, not strong enough by
itself to absorb the Carter--Pollard `exp(Δ)` factor. -/
theorem gaussianTailRaw_exp_sq_diff_div_two_mul_le_of_pos_le
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    Real.exp ((x ^ 2 - y ^ 2) / 2) * gaussianTailRaw x ≤
      gaussianTailRaw y := by
  have hmills :
      Erdos524.Helpers.gaussianMillsRatioReal x ≤
        Erdos524.Helpers.gaussianMillsRatioReal y :=
    Erdos524.Helpers.gaussianMillsRatioReal_antitone hy hyx
  have hpdf :
      Real.exp ((x ^ 2 - y ^ 2) / 2) * gaussianPDFReal 0 1 x =
        gaussianPDFReal 0 1 y := by
    rw [gaussianPDFReal_zero_one_eq_inv_sqrt_mul_exp x,
      gaussianPDFReal_zero_one_eq_inv_sqrt_mul_exp y]
    calc
      Real.exp ((x ^ 2 - y ^ 2) / 2) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) =
          (Real.sqrt (2 * Real.pi))⁻¹ *
            (Real.exp ((x ^ 2 - y ^ 2) / 2) * Real.exp (-x ^ 2 / 2)) := by ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (((x ^ 2 - y ^ 2) / 2) + (-x ^ 2 / 2)) := by
        rw [Real.exp_add]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
        congr 1
        ring_nf
  rw [gaussianTailRaw_eq_millsRatio_mul_pdf x,
    gaussianTailRaw_eq_millsRatio_mul_pdf y]
  calc
    Real.exp ((x ^ 2 - y ^ 2) / 2) *
        (Erdos524.Helpers.gaussianMillsRatioReal x * gaussianPDFReal 0 1 x) =
        Erdos524.Helpers.gaussianMillsRatioReal x *
          (Real.exp ((x ^ 2 - y ^ 2) / 2) * gaussianPDFReal 0 1 x) := by ring
    _ = Erdos524.Helpers.gaussianMillsRatioReal x * gaussianPDFReal 0 1 y := by
      rw [hpdf]
    _ ≤ Erdos524.Helpers.gaussianMillsRatioReal y * gaussianPDFReal 0 1 y :=
      mul_le_mul_of_nonneg_right hmills (gaussianPDFReal_nonneg 0 1 y)

/-- A log-density-ratio sufficient condition for absorbing a multiplicative
factor into a raw Gaussian tail. -/
theorem gaussianTailRaw_exp_mul_le_of_delta_le_sq_diff_div_two
    {δ x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hδ : δ ≤ (x ^ 2 - y ^ 2) / 2) :
    Real.exp δ * gaussianTailRaw x ≤ gaussianTailRaw y := by
  have hexp : Real.exp δ ≤ Real.exp ((x ^ 2 - y ^ 2) / 2) :=
    Real.exp_le_exp.mpr hδ
  exact le_trans
    (mul_le_mul_of_nonneg_right hexp (gaussianTailRaw_nonneg x))
    (gaussianTailRaw_exp_sq_diff_div_two_mul_le_of_pos_le hy hyx)

/-- Tail-ratio adapter: if the multiplicative factor is bounded by the exact
raw-tail ratio, then it can be absorbed into the larger tail. -/
theorem gaussianTailRaw_exp_mul_le_of_exp_le_tail_ratio
    {δ x y : ℝ} (hx : 0 < x)
    (hδ :
      Real.exp δ ≤ gaussianTailRaw y / gaussianTailRaw x) :
    Real.exp δ * gaussianTailRaw x ≤ gaussianTailRaw y := by
  have htail_pos := gaussianTailRaw_pos_of_pos hx
  exact (le_div_iff₀ htail_pos).mp hδ

/-- Log-tail-ratio adapter, convenient for Carter--Pollard `Δ` estimates. -/
theorem gaussianTailRaw_exp_mul_le_of_delta_le_log_tail_ratio
    {δ x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hδ :
      δ ≤ Real.log (gaussianTailRaw y / gaussianTailRaw x)) :
    Real.exp δ * gaussianTailRaw x ≤ gaussianTailRaw y := by
  have htail_x_pos := gaussianTailRaw_pos_of_pos hx
  have htail_y_pos := gaussianTailRaw_pos_of_pos hy
  have hratio_pos :
      0 < gaussianTailRaw y / gaussianTailRaw x :=
    div_pos htail_y_pos htail_x_pos
  have hexp :
      Real.exp δ ≤ gaussianTailRaw y / gaussianTailRaw x := by
    calc
      Real.exp δ ≤ Real.exp (Real.log (gaussianTailRaw y / gaussianTailRaw x)) :=
        Real.exp_le_exp.mpr hδ
      _ = gaussianTailRaw y / gaussianTailRaw x :=
        Real.exp_log hratio_pos
  exact gaussianTailRaw_exp_mul_le_of_exp_le_tail_ratio hx hexp

/-! ### TC42 Mills-gain log decomposition -/

/-- Explicit standard-Gaussian density ratio. -/
theorem gaussianPDFReal_zero_one_div_eq_exp_sq_diff_div_two
    {x y : ℝ} :
    gaussianPDFReal 0 1 y / gaussianPDFReal 0 1 x =
      Real.exp ((x ^ 2 - y ^ 2) / 2) := by
  rw [gaussianPDFReal_zero_one_eq_inv_sqrt_mul_exp y,
    gaussianPDFReal_zero_one_eq_inv_sqrt_mul_exp x]
  have hsqrt_ne : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  have hexp_ne : Real.exp (-x ^ 2 / 2) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hsqrt_ne, hexp_ne]
  rw [← Real.exp_add]
  congr 1
  ring

/-- TC42 route-B decomposition: the log Gaussian-tail ratio is exactly the
density-ratio exponent plus the logarithmic Mills-ratio gain. -/
theorem gaussianTailRaw_log_ratio_eq_sq_diff_div_two_add_log_millsRatio_ratio
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (gaussianTailRaw y / gaussianTailRaw x) =
      (x ^ 2 - y ^ 2) / 2 +
        Real.log
          (Erdos524.Helpers.gaussianMillsRatioReal y /
            Erdos524.Helpers.gaussianMillsRatioReal x) := by
  have htail_x_pos := gaussianTailRaw_pos_of_pos hx
  have hmills_x_pos := Erdos524.Helpers.gaussianMillsRatioReal_pos hx
  have hmills_y_pos := Erdos524.Helpers.gaussianMillsRatioReal_pos hy
  have hpdf_x_pos : 0 < gaussianPDFReal 0 1 x :=
    gaussianPDFReal_pos 0 1 x (by norm_num)
  have hratio :
      gaussianTailRaw y / gaussianTailRaw x =
        (Erdos524.Helpers.gaussianMillsRatioReal y /
            Erdos524.Helpers.gaussianMillsRatioReal x) *
          Real.exp ((x ^ 2 - y ^ 2) / 2) := by
    rw [gaussianTailRaw_eq_millsRatio_mul_pdf y,
      gaussianTailRaw_eq_millsRatio_mul_pdf x]
    rw [← gaussianPDFReal_zero_one_div_eq_exp_sq_diff_div_two (x := x) (y := y)]
    field_simp [hmills_x_pos.ne', hpdf_x_pos.ne']
  rw [hratio]
  have hmills_ratio_pos :
      0 <
        Erdos524.Helpers.gaussianMillsRatioReal y /
          Erdos524.Helpers.gaussianMillsRatioReal x :=
    div_pos hmills_y_pos hmills_x_pos
  rw [Real.log_mul hmills_ratio_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Existing Mills antitonicity contributes only the nonnegative part of the
Mills-gain term, recovering the TC41 density-ratio lower bound in log form. -/
theorem gaussianTailRaw_log_ratio_ge_sq_diff_div_two_of_pos_le
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (x ^ 2 - y ^ 2) / 2 ≤
      Real.log (gaussianTailRaw y / gaussianTailRaw x) := by
  have hx : 0 < x := lt_of_lt_of_le hy hyx
  have hdecomp :=
    gaussianTailRaw_log_ratio_eq_sq_diff_div_two_add_log_millsRatio_ratio
      (x := x) (y := y) hx hy
  have hmills_x_pos := Erdos524.Helpers.gaussianMillsRatioReal_pos hx
  have hmills_mono :
      Erdos524.Helpers.gaussianMillsRatioReal x ≤
        Erdos524.Helpers.gaussianMillsRatioReal y :=
    Erdos524.Helpers.gaussianMillsRatioReal_antitone hy hyx
  have hratio_ge_one :
      1 ≤
        Erdos524.Helpers.gaussianMillsRatioReal y /
          Erdos524.Helpers.gaussianMillsRatioReal x := by
    exact (le_div_iff₀ hmills_x_pos).mpr (by simpa using hmills_mono)
  have hlog_nonneg :
      0 ≤
        Real.log
          (Erdos524.Helpers.gaussianMillsRatioReal y /
            Erdos524.Helpers.gaussianMillsRatioReal x) :=
    Real.log_nonneg hratio_ge_one
  linarith

/-! ### TC41 delta/tail-ratio scaffold -/

/-- TC41 event data needed for the remaining Carter--Pollard tail-ratio
hypothesis: in the even base case, both standardized thresholds are positive
and the scaled physical threshold lies to the left of the Carter--Pollard
threshold. -/
theorem carterPollard_even_event_tail_ratio_thresholds
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ))) :
    0 < z / Real.sqrt ((n : ℝ) / 2) ∧
      0 <
        Real.sqrt (carterPollardN (2 * n)) *
          carterPollardEps (2 * n) k ∧
      z / Real.sqrt ((n : ℝ) / 2) ≤
        Real.sqrt (carterPollardN (2 * n)) *
          carterPollardEps (2 * n) k := by
  have hσ_pos : 0 < Real.sqrt ((n : ℝ) / 2) := by
    positivity
  have hy_pos : 0 < z / Real.sqrt ((n : ℝ) / 2) :=
    div_pos hz_pos hσ_pos
  have hx_pos :
      0 <
        Real.sqrt (carterPollardN (2 * n)) *
          carterPollardEps (2 * n) k :=
    carterPollard_sqrtN_mul_eps_pos_of_succ_lt_two_mul
      (m := 2 * n) (k := k) (by omega) (by omega)
  have hle :
      z / Real.sqrt ((n : ℝ) / 2) ≤
        Real.sqrt (carterPollardN (2 * n)) *
          carterPollardEps (2 * n) k :=
    carterPollard_even_event_implies_scaled_z_le_sqrtN_eps
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event
  exact ⟨hy_pos, hx_pos, hle⟩

/-- TC41 fallback close: the desired Carter--Pollard `exp(Δ)` absorption
under the single remaining explicit log tail-ratio hypothesis.

This theorem intentionally keeps the analytic obstruction isolated as
`h_delta_log_ratio`; proving that hypothesis from the Carter--Pollard
paper-shaped bounds is the exact next consumer. -/
theorem carterPollard_exp_deltaPaperShape_mul_tail_le_scaled_tail_of_event_of_delta_le_log_tail_ratio
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)))
    (h_delta_log_ratio :
      carterPollardDeltaPaperShape (2 * n) k ≤
        Real.log
          (gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) /
            gaussianTailRaw
              (Real.sqrt (carterPollardN (2 * n)) *
                carterPollardEps (2 * n) k))) :
    Real.exp (carterPollardDeltaPaperShape (2 * n) k) *
      gaussianTailRaw
        (Real.sqrt (carterPollardN (2 * n)) *
          carterPollardEps (2 * n) k) ≤
      gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) := by
  rcases carterPollard_even_event_tail_ratio_thresholds
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event with
    ⟨hy_pos, hx_pos, _hle⟩
  exact gaussianTailRaw_exp_mul_le_of_delta_le_log_tail_ratio
    (δ := carterPollardDeltaPaperShape (2 * n) k)
    (x :=
      Real.sqrt (carterPollardN (2 * n)) *
        carterPollardEps (2 * n) k)
    (y := z / Real.sqrt ((n : ℝ) / 2))
    hx_pos hy_pos h_delta_log_ratio

/-- TC41 fallback composition with the TC40 Carter--Pollard scaled-tail
transport, again under the single explicit log tail-ratio hypothesis. -/
theorem binomialPolyTail_half_le_scaled_gaussian_event_tail_of_event_of_delta_le_log_tail_ratio
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)))
    (h_delta_log_ratio :
      carterPollardDeltaPaperShape (2 * n) k ≤
        Real.log
          (gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) /
            gaussianTailRaw
              (Real.sqrt (carterPollardN (2 * n)) *
                carterPollardEps (2 * n) k))) :
    Erdos524.Helpers.binomialPolyTail (2 * n) k (1 / 2 : ℝ) ≤
      gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) := by
  have hcp :=
    binomialPolyTail_half_le_exp_deltaPaperShape_mul_gaussian_tail_instantiated
      (m := 2 * n) (k := k) (by omega) (by omega) hk_upper
  exact le_trans hcp
    (carterPollard_exp_deltaPaperShape_mul_tail_le_scaled_tail_of_event_of_delta_le_log_tail_ratio
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event h_delta_log_ratio)

/-! ### TC42 Carter--Pollard Mills-gain scaffold -/

/-- TC42 conditional scalar close under the exact remaining Mills-gain
inequality exposed by the route-B decomposition. -/
theorem carterPollardDeltaPaperShape_even_le_log_tail_ratio_of_event_of_remainder_le_mills_gain
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)))
    (h_mills_gain :
      carterPollardDeltaPaperShape (2 * n) k -
          (((Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k) ^ 2 -
            (z / Real.sqrt ((n : ℝ) / 2)) ^ 2) / 2) ≤
        Real.log
          (Erdos524.Helpers.gaussianMillsRatioReal
              (z / Real.sqrt ((n : ℝ) / 2)) /
            Erdos524.Helpers.gaussianMillsRatioReal
              (Real.sqrt (carterPollardN (2 * n)) *
                carterPollardEps (2 * n) k))) :
    carterPollardDeltaPaperShape (2 * n) k ≤
      Real.log
        (gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) /
          gaussianTailRaw
            (Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k)) := by
  rcases carterPollard_even_event_tail_ratio_thresholds
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event with
    ⟨hy_pos, hx_pos, _hyx⟩
  have hdecomp :=
    gaussianTailRaw_log_ratio_eq_sq_diff_div_two_add_log_millsRatio_ratio
      (x :=
        Real.sqrt (carterPollardN (2 * n)) *
          carterPollardEps (2 * n) k)
      (y := z / Real.sqrt ((n : ℝ) / 2)) hx_pos hy_pos
  rw [hdecomp]
  linarith

/-- TC42 conditional composition: the corrected scaled binomial/Gaussian event
theorem follows from the exact remaining Mills-gain scalar inequality. -/
theorem binomialPolyTail_half_le_scaled_gaussian_event_tail_of_event_of_remainder_le_mills_gain
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)))
    (h_mills_gain :
      carterPollardDeltaPaperShape (2 * n) k -
          (((Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k) ^ 2 -
            (z / Real.sqrt ((n : ℝ) / 2)) ^ 2) / 2) ≤
        Real.log
          (Erdos524.Helpers.gaussianMillsRatioReal
              (z / Real.sqrt ((n : ℝ) / 2)) /
            Erdos524.Helpers.gaussianMillsRatioReal
              (Real.sqrt (carterPollardN (2 * n)) *
                carterPollardEps (2 * n) k))) :
    Erdos524.Helpers.binomialPolyTail (2 * n) k (1 / 2 : ℝ) ≤
      gaussianTailRaw (z / Real.sqrt ((n : ℝ) / 2)) := by
  have hlog :=
    carterPollardDeltaPaperShape_even_le_log_tail_ratio_of_event_of_remainder_le_mills_gain
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event h_mills_gain
  exact binomialPolyTail_half_le_scaled_gaussian_event_tail_of_event_of_delta_le_log_tail_ratio
    (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event hlog

/-- TC43 reduction: the quantitative Mills-gain bound reduces the exact
remaining Mills-gain consumer to a finite Carter--Pollard scalar gap estimate.

The additional hypothesis is precisely
`Δ <= m(0)⁻¹ * (x - y)`, where
`x = sqrt(N) * eps` and `y = z / sqrt(n/2)`. Under this hypothesis, the
density-ratio term cancels against the quadratic part of the Mills-gain lower
bound. -/
theorem carterPollardDeltaPaperShape_even_remainder_le_mills_gain_of_event_of_delta_le_zero_value_gap
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)))
    (h_delta_gap :
      carterPollardDeltaPaperShape (2 * n) k ≤
        (Erdos524.Helpers.gaussianMillsRatioReal 0)⁻¹ *
          (Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k -
            z / Real.sqrt ((n : ℝ) / 2))) :
    carterPollardDeltaPaperShape (2 * n) k -
        (((Real.sqrt (carterPollardN (2 * n)) *
            carterPollardEps (2 * n) k) ^ 2 -
          (z / Real.sqrt ((n : ℝ) / 2)) ^ 2) / 2) ≤
      Real.log
        (Erdos524.Helpers.gaussianMillsRatioReal
            (z / Real.sqrt ((n : ℝ) / 2)) /
          Erdos524.Helpers.gaussianMillsRatioReal
            (Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k)) := by
  rcases carterPollard_even_event_tail_ratio_thresholds
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event with
    ⟨hy_pos, _hx_pos, hyx⟩
  have hgain :=
    Erdos524.Helpers.gaussianMillsRatioReal_log_ratio_ge_zero_value_bound
      (x :=
        Real.sqrt (carterPollardN (2 * n)) *
          carterPollardEps (2 * n) k)
      (y := z / Real.sqrt ((n : ℝ) / 2)) hy_pos hyx
  linarith

/-- TC44 sufficient finite scalar gap: the exact TC43 zero-value gap follows
from the stronger rational gap bound with constant `3/4`.

This isolates the remaining Carter--Pollard scalar work after the Mills
constant has been made explicit. -/
theorem carterPollardDeltaPaperShape_even_le_zero_value_gap_of_gap_bound
    {n k : ℕ} {z : ℝ}
    (hn : 14 ≤ n) (hk_lower : n < k) (hk_upper : k ≤ 2 * n - 1)
    (hz_pos : 0 < z)
    (hz_event :
      z + (0.6 : ℝ) + z ^ 2 / (n : ℝ) ≤ ((k : ℝ) - (n : ℝ)))
    (h_gap_bound :
      carterPollardDeltaPaperShape (2 * n) k ≤
        (3 / 4 : ℝ) *
          (Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k -
            z / Real.sqrt ((n : ℝ) / 2))) :
    carterPollardDeltaPaperShape (2 * n) k ≤
      (Erdos524.Helpers.gaussianMillsRatioReal 0)⁻¹ *
        (Real.sqrt (carterPollardN (2 * n)) *
            carterPollardEps (2 * n) k -
          z / Real.sqrt ((n : ℝ) / 2)) := by
  rcases carterPollard_even_event_tail_ratio_thresholds
      (n := n) (k := k) (z := z) hn hk_lower hk_upper hz_pos hz_event with
    ⟨_hy_pos, _hx_pos, hyx⟩
  have hgap_nonneg :
      0 ≤
        Real.sqrt (carterPollardN (2 * n)) *
            carterPollardEps (2 * n) k -
          z / Real.sqrt ((n : ℝ) / 2) := by
    exact sub_nonneg.mpr hyx
  have hconst :
      (3 / 4 : ℝ) ≤ (Erdos524.Helpers.gaussianMillsRatioReal 0)⁻¹ :=
    Erdos524.Helpers.gaussianMillsRatioReal_zero_inv_ge_three_fourths
  have hmul :
      (3 / 4 : ℝ) *
          (Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k -
            z / Real.sqrt ((n : ℝ) / 2)) ≤
        (Erdos524.Helpers.gaussianMillsRatioReal 0)⁻¹ *
          (Real.sqrt (carterPollardN (2 * n)) *
              carterPollardEps (2 * n) k -
            z / Real.sqrt ((n : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_right hconst hgap_nonneg
  exact le_trans h_gap_bound hmul

/-- Explicit density-over-argument form after applying the first Mills
truncation. -/
theorem gaussianPDFReal_zero_one_div_eq_inv_sqrt_mul_exp_div (x : ℝ) :
    gaussianPDFReal 0 1 x / x =
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) / x := by
  rw [gaussianPDFReal_zero_one_eq_inv_sqrt_mul_exp]

/-- First one-sided Mills truncation consequence for the raw normalized
Gaussian tail. -/
theorem gaussianTailRaw_le_pdf_div_of_pos {x : ℝ} (hx : 0 < x) :
    gaussianTailRaw x ≤ gaussianPDFReal 0 1 x / x := by
  rw [gaussianTailRaw_eq_millsRatio_mul_pdf]
  have htrunc := Erdos524.Helpers.gaussianMillsRatioReal_truncation hx
  have hpdf_nonneg : 0 ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  have hmul := mul_le_mul_of_nonneg_right htrunc hpdf_nonneg
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- TC24 normalized tail route after applying the direct Robbins upper bound
to the paper-shaped entropy `Δ`.

This keeps the entropy term explicit and does not introduce the optional
`γ(ε)` rewrite or any normal-tail ratio estimate. -/
theorem binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_gaussian_tail
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      Real.exp
        (Real.log (1 + (carterPollardN m)⁻¹) +
          1 / (12 * ((m - 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
              carterPollardEntropyDelta m k) *
        gaussianTailRaw
          (Real.sqrt (carterPollardN m) * carterPollardEps m k) := by
  have htail :=
    binomialPolyTail_half_le_exp_deltaPaperShape_mul_gaussian_tail_instantiated
      (m := m) (k := k) hm hk_lower hk_upper
  have hΔ := carterPollardDeltaPaperShape_le_entropy_shape_robbins_upper hm hk_lower hk_upper
  have hmul :
      Real.exp (carterPollardDeltaPaperShape m k) *
          gaussianTailRaw
            (Real.sqrt (carterPollardN m) * carterPollardEps m k) ≤
        Real.exp
          (Real.log (1 + (carterPollardN m)⁻¹) +
            1 / (12 * ((m - 1 : ℕ) : ℝ)) -
              (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
                carterPollardEntropyDelta m k) *
          gaussianTailRaw
            (Real.sqrt (carterPollardN m) * carterPollardEps m k) := by
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hΔ)
      (gaussianTailRaw_nonneg _)
  exact le_trans htail hmul

/-- TC25 Mills-ratio-ready form of the TC24 normal-tail bound.

The Gaussian factor is now exposed as `Mills(x) * φ(x)`, where
`x = sqrt(N) * ε`. This is the intended input shape for a later
quantile/envelope round; no quantile inversion is performed here. -/
theorem binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_millsRatio_pdf
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      Real.exp
        (Real.log (1 + (carterPollardN m)⁻¹) +
          1 / (12 * ((m - 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
              carterPollardEntropyDelta m k) *
        (Erdos524.Helpers.gaussianMillsRatioReal
            (Real.sqrt (carterPollardN m) * carterPollardEps m k) *
          gaussianPDFReal 0 1
            (Real.sqrt (carterPollardN m) * carterPollardEps m k)) := by
  have htail :=
    binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_gaussian_tail
      (m := m) (k := k) hm hk_lower hk_upper
  rw [gaussianTailRaw_eq_millsRatio_mul_pdf] at htail
  exact htail

/-- TC25 first one-sided truncation of the TC24 normal-tail factor.

This consumes the existing Mills truncation bound at
`x = sqrt(N) * ε`; the positivity assumption is left explicit for TC26's
quantile/envelope consumer. -/
theorem binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_pdf_div
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hx : 0 < Real.sqrt (carterPollardN m) * carterPollardEps m k) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      Real.exp
        (Real.log (1 + (carterPollardN m)⁻¹) +
          1 / (12 * ((m - 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
              carterPollardEntropyDelta m k) *
        (gaussianPDFReal 0 1
            (Real.sqrt (carterPollardN m) * carterPollardEps m k) /
          (Real.sqrt (carterPollardN m) * carterPollardEps m k)) := by
  have htail :=
    binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_gaussian_tail
      (m := m) (k := k) hm hk_lower hk_upper
  have htail_factor :=
    gaussianTailRaw_le_pdf_div_of_pos
      (x := Real.sqrt (carterPollardN m) * carterPollardEps m k) hx
  have hexp_nonneg :
      0 ≤
        Real.exp
          (Real.log (1 + (carterPollardN m)⁻¹) +
            1 / (12 * ((m - 1 : ℕ) : ℝ)) -
              (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
                carterPollardEntropyDelta m k) := by
    positivity
  exact le_trans htail (mul_le_mul_of_nonneg_left htail_factor hexp_nonneg)

/-- TC26 version of the TC25 Mills-truncation tail theorem using the strict
threshold that excludes the midpoint edge. -/
theorem binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_pdf_div_of_succ_lt_two_mul
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      Real.exp
        (Real.log (1 + (carterPollardN m)⁻¹) +
          1 / (12 * ((m - 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
              carterPollardEntropyDelta m k) *
        (gaussianPDFReal 0 1
            (Real.sqrt (carterPollardN m) * carterPollardEps m k) /
          (Real.sqrt (carterPollardN m) * carterPollardEps m k)) := by
  exact binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_pdf_div
    (m := m) (k := k) hm hk_lower hk_upper
    (carterPollard_sqrtN_mul_eps_pos_of_succ_lt_two_mul
      (m := m) (k := k) hm hstrict)

/-- TC26 expanded-density envelope shape after the first Mills truncation.

This is the first form ready for a future envelope inequality: the Gaussian
tail has been replaced by the explicit density divided by
`sqrt(N) * ε`. -/
theorem binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_exp_density_div
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      Real.exp
        (Real.log (1 + (carterPollardN m)⁻¹) +
          1 / (12 * ((m - 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
              carterPollardEntropyDelta m k) *
        (((Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2)) /
          (Real.sqrt (carterPollardN m) * carterPollardEps m k)) := by
  have htail :=
    binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_pdf_div_of_succ_lt_two_mul
      (m := m) (k := k) hm hk_lower hk_upper hstrict
  simpa [gaussianPDFReal_zero_one_div_eq_inv_sqrt_mul_exp_div] using htail

/-- TC27 exact cancellation of the Gaussian density exponent against the
`+ N * ε^2 / 2` contribution inside `carterPollardEntropyDelta`.

This is purely an algebraic refactor of the TC26 expanded-density right hand
side; it does not introduce a gamma rewrite, endpoint handling, or quantile
inversion. -/
theorem carterPollard_entropy_density_exponent_cancel
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    Real.exp
        (Real.log (1 + (carterPollardN m)⁻¹) +
          1 / (12 * ((m - 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
              carterPollardEntropyDelta m k) *
        (((Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2)) /
          (Real.sqrt (carterPollardN m) * carterPollardEps m k)) =
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
          Real.exp
            (-(carterPollardN m / 2) *
              ((1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
                (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k))) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
              carterPollardEps m k *
                Real.sqrt (1 - carterPollardEps m k ^ 2)) := by
  have hN_pos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show 0 < m - 1 by omega)
  have hN_ne : carterPollardN m ≠ 0 := hN_pos.ne'
  have hsqrtN_ne : Real.sqrt (carterPollardN m) ≠ 0 := by positivity
  have hε_pos := carterPollardEps_pos_of_succ_lt_two_mul
    (m := m) (k := k) hm hstrict
  have hε_ne : carterPollardEps m k ≠ 0 := hε_pos.ne'
  have hlog_pos : 0 < 1 + (carterPollardN m)⁻¹ := by positivity
  have hsq_pos := carterPollard_one_sub_eps_sq_pos hm hk_lower hk_upper
  have hsqrt_sq_ne : Real.sqrt (1 - carterPollardEps m k ^ 2) ≠ 0 := by positivity
  have hsqrt_two_pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hdensity_sq :
      (Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 =
        carterPollardN m * carterPollardEps m k ^ 2 := by
    rw [mul_pow, sq_sqrt hN_pos.le]
  have hentropy_density :
      carterPollardEntropyDelta m k -
          (Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2 =
        -(carterPollardN m / 2) *
          ((1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
            (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k)) := by
    unfold carterPollardEntropyDelta
    rw [hdensity_sq]
    ring
  rw [show
      Real.exp
          (Real.log (1 + (carterPollardN m)⁻¹) +
            1 / (12 * ((m - 1 : ℕ) : ℝ)) -
              (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
                carterPollardEntropyDelta m k) *
          (((Real.sqrt (2 * Real.pi))⁻¹ *
              Real.exp (-(Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2)) /
            (Real.sqrt (carterPollardN m) * carterPollardEps m k)) =
        (Real.exp (Real.log (1 + (carterPollardN m)⁻¹)) *
          Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
            Real.exp (-(1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2)) *
              Real.exp
                (carterPollardEntropyDelta m k -
                  (Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2)) *
          ((Real.sqrt (2 * Real.pi))⁻¹ /
            (Real.sqrt (carterPollardN m) * carterPollardEps m k)) by
      conv_lhs =>
        rw [Real.exp_add]
        rw [Real.exp_sub]
        rw [Real.exp_add]
      rw [show -(Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2 =
          -((Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2) by ring]
      rw [show -(1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) =
          -((1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2)) by ring]
      rw [Real.exp_sub]
      rw [show
          Real.exp (-((1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2))) =
            (Real.exp ((1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2)))⁻¹ by
        rw [Real.exp_neg]]
      rw [show
          Real.exp (-((Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2)) =
            (Real.exp ((Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2))⁻¹ by
        rw [Real.exp_neg]]
      ring_nf]
  rw [Real.exp_log hlog_pos, exp_neg_half_log_eq_inv_sqrt hsq_pos,
    hentropy_density]
  field_simp [hsqrt_two_pi_ne, hsqrtN_ne, hε_ne, hsqrt_sq_ne]

/-- TC27 first factorized strict-tail Carter--Pollard envelope.

This is the TC26 expanded-density envelope with the Gaussian density exponent
cancelled into the entropy exponent. -/
theorem carterPollard_first_envelope_factorized
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    Real.exp
        (Real.log (1 + (carterPollardN m)⁻¹) +
          1 / (12 * ((m - 1 : ℕ) : ℝ)) -
            (1 / 2 : ℝ) * Real.log (1 - carterPollardEps m k ^ 2) +
              carterPollardEntropyDelta m k) *
        (((Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(Real.sqrt (carterPollardN m) * carterPollardEps m k) ^ 2 / 2)) /
          (Real.sqrt (carterPollardN m) * carterPollardEps m k)) =
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
          Real.exp
            (-(carterPollardN m / 2) *
              ((1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
                (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k))) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
              carterPollardEps m k *
                Real.sqrt (1 - carterPollardEps m k ^ 2)) := by
  exact carterPollard_entropy_density_exponent_cancel
    (m := m) (k := k) hm hk_lower hk_upper hstrict

/-- TC27 binomial-tail consequence of the first factorized strict-tail
Carter--Pollard envelope. -/
theorem binomialPolyTail_half_le_carterPollard_first_factorized_envelope
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
          Real.exp
            (-(carterPollardN m / 2) *
              ((1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
                (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k))) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
              carterPollardEps m k *
                Real.sqrt (1 - carterPollardEps m k ^ 2)) := by
  have htail :=
    binomialPolyTail_half_le_exp_entropy_shape_robbins_upper_mul_exp_density_div
      (m := m) (k := k) hm hk_lower hk_upper hstrict
  rw [← carterPollard_entropy_density_exponent_cancel hm hk_lower hk_upper hstrict]
  exact htail

private lemma entropy_shape_ge_sq_of_nonneg_lt_one
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ε ^ 2 ≤
      (1 + ε) * Real.log (1 + ε) +
        (1 - ε) * Real.log (1 - ε) := by
  let F : ℝ → ℝ := fun x =>
    (1 + x) * Real.log (1 + x) +
      (1 - x) * Real.log (1 - x) - x ^ 2
  have hF_deriv :
      ∀ y ∈ Set.Icc (0 : ℝ) ε,
        HasDerivAt F
          (Real.log (1 + y) - Real.log (1 - y) - 2 * y) y := by
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hε1
    have h_one_add_ne : 1 + y ≠ 0 := by linarith
    have h_one_sub_ne : 1 - y ≠ 0 := by linarith
    have h_add : HasDerivAt (fun x : ℝ => 1 + x) 1 y := by
      simpa using (hasDerivAt_const (x := y) (c := (1 : ℝ))).add (hasDerivAt_id y)
    have h_sub : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
      simpa using (hasDerivAt_const (x := y) (c := (1 : ℝ))).sub (hasDerivAt_id y)
    have h_plus :
        HasDerivAt (fun x : ℝ => (1 + x) * Real.log (1 + x))
          (Real.log (1 + y) + 1) y := by
      have h := (Real.hasDerivAt_mul_log h_one_add_ne).comp y h_add
      convert h using 1
      ring
    have h_minus :
        HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
          (-(Real.log (1 - y) + 1)) y := by
      have h := (Real.hasDerivAt_mul_log h_one_sub_ne).comp y h_sub
      convert h using 1
      ring
    have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h := (h_plus.add h_minus).sub h_sq
    convert h using 1
    ring
  have hF_mono : MonotoneOn F (Set.Icc (0 : ℝ) ε) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) ε)
      (fun y hy => (hF_deriv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hF_deriv y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Icc] at hy
    rcases hy with ⟨hy0, hyε⟩
    have hy1 : y < 1 := lt_trans hyε hε1
    have hsum := Real.sum_range_le_log_div hy0.le hy1 1
    have hsum_eq :
        (∑ i ∈ Finset.range 1, y ^ (2 * i + 1) / (2 * i + 1)) = y := by
      norm_num
    have hlogdiv :
        Real.log ((1 + y) / (1 - y)) =
          Real.log (1 + y) - Real.log (1 - y) := by
      rw [Real.log_div (by linarith : 1 + y ≠ 0) (by linarith : 1 - y ≠ 0)]
    rw [hsum_eq, hlogdiv] at hsum
    linarith
  have hF0 : F 0 = 0 := by
    simp [F]
  have hFε_nonneg : 0 ≤ F ε := by
    have hmono := hF_mono ⟨le_rfl, hε0⟩ ⟨hε0, le_rfl⟩ hε0
    simpa [hF0] using hmono
  dsimp [F] at hFε_nonneg
  linarith

/-- TC28 scalar entropy lower bound in the strict Carter--Pollard upper-tail
range. -/
theorem carterPollard_entropy_shape_ge_eps_sq
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    carterPollardEps m k ^ 2 ≤
      (1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
        (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k) := by
  have hε0 : 0 ≤ carterPollardEps m k :=
    (carterPollardEps_pos_of_succ_lt_two_mul (m := m) (k := k) hm hstrict).le
  have hε1 : carterPollardEps m k < 1 := by
    have h := carterPollard_one_sub_eps_pos hm hk_lower hk_upper
    linarith
  exact entropy_shape_ge_sq_of_nonneg_lt_one hε0 hε1

/-- Positivity of the denominator in the TC27 factorized strict-tail envelope. -/
theorem carterPollard_first_factorized_den_pos
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    0 <
      Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
        carterPollardEps m k *
          Real.sqrt (1 - carterPollardEps m k ^ 2) := by
  have hN_pos : 0 < carterPollardN m := by
    unfold carterPollardN
    exact_mod_cast (show 0 < m - 1 by omega)
  have hε_pos := carterPollardEps_pos_of_succ_lt_two_mul
    (m := m) (k := k) hm hstrict
  have hsq_pos := carterPollard_one_sub_eps_sq_pos hm hk_lower hk_upper
  positivity

/-- TC28 scalar comparison from the TC27 entropy-factorized envelope to the
quadratic Gaussian envelope, using
`ε² ≤ (1+ε)log(1+ε)+(1-ε)log(1-ε)`. -/
theorem carterPollard_first_factorized_envelope_le_quadratic_envelope
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
          Real.exp
            (-(carterPollardN m / 2) *
              ((1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
                (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k))) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
              carterPollardEps m k *
                Real.sqrt (1 - carterPollardEps m k ^ 2)) ≤
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
          Real.exp (-(carterPollardN m * carterPollardEps m k ^ 2) / 2) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
              carterPollardEps m k *
                Real.sqrt (1 - carterPollardEps m k ^ 2)) := by
  set A : ℝ :=
    (1 + (carterPollardN m)⁻¹) *
      Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ)))
  set H : ℝ :=
    (1 + carterPollardEps m k) * Real.log (1 + carterPollardEps m k) +
      (1 - carterPollardEps m k) * Real.log (1 - carterPollardEps m k)
  set D : ℝ :=
    Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
      carterPollardEps m k *
        Real.sqrt (1 - carterPollardEps m k ^ 2)
  have hN_nonneg : 0 ≤ carterPollardN m / 2 := by
    unfold carterPollardN
    positivity
  have hH := carterPollard_entropy_shape_ge_eps_sq
    (m := m) (k := k) hm hk_lower hk_upper hstrict
  have hexp :
      Real.exp (-(carterPollardN m / 2) * H) ≤
        Real.exp (-(carterPollardN m * carterPollardEps m k ^ 2) / 2) := by
    apply Real.exp_le_exp.mpr
    dsimp [H] at hH ⊢
    nlinarith [mul_le_mul_of_nonneg_left hH hN_nonneg]
  have hA_nonneg : 0 ≤ A := by
    have hN_pos : 0 < carterPollardN m := by
      unfold carterPollardN
      exact_mod_cast (show 0 < m - 1 by omega)
    dsimp [A]
    exact mul_nonneg (by positivity) (Real.exp_pos _).le
  have hD_nonneg : 0 ≤ D :=
    (carterPollard_first_factorized_den_pos hm hk_lower hk_upper hstrict).le
  have hnum := mul_le_mul_of_nonneg_left hexp hA_nonneg
  exact div_le_div_of_nonneg_right hnum hD_nonneg

/-- TC28 first scalar strict-tail envelope with the entropy exponent bounded
by its quadratic lower approximation. -/
theorem binomialPolyTail_half_le_carterPollard_quadratic_strict_envelope
    {m k : ℕ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k) :
    Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
          Real.exp (-(carterPollardN m * carterPollardEps m k ^ 2) / 2) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
              carterPollardEps m k *
                Real.sqrt (1 - carterPollardEps m k ^ 2)) := by
  exact le_trans
    (binomialPolyTail_half_le_carterPollard_first_factorized_envelope
      (m := m) (k := k) hm hk_lower hk_upper hstrict)
    (carterPollard_first_factorized_envelope_le_quadratic_envelope
      (m := m) (k := k) hm hk_lower hk_upper hstrict)

/-! ### TC32 strict-tail event/quantile adapter -/

/-- TC32 event bridge from the strict Carter--Pollard quadratic envelope to a
shared-uniform upper-tail quantile comparison, conditional on the remaining
scalar Gaussian event-tail comparison.

The scalar hypothesis is exactly the analytic comparison still needed before
the `tusnady_base_polynomial` scaffold can consume this adapter without an
extra assumption. -/
theorem carterPollard_quadratic_strict_envelope_event_quantile_gt
    {m k : ℕ} {z u : ℝ} {qB qZ : ℝ → ℝ}
    (hm : 28 ≤ m) (hk_lower : m / 2 < k) (hk_upper : k ≤ m - 1)
    (hstrict : m + 1 < 2 * k)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hGaloisB :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ x : ℝ,
        qB u ≤ x ↔
          u ≤ cdf
            ((PMF.binomial (1 / 2 : ℝ≥0) (by norm_num) m).toMeasure.map
              (fun (i : Fin (m + 1)) => (i.val : ℝ))) x)
    (hGaloisZ :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ x : ℝ,
        qZ u ≤ x ↔ u ≤ cdf (gaussianReal 0 1) x)
    (hscalar :
      (1 + (carterPollardN m)⁻¹) *
        Real.exp (1 / (12 * ((m - 1 : ℕ) : ℝ))) *
          Real.exp (-(carterPollardN m * carterPollardEps m k ^ 2) / 2) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (carterPollardN m) *
              carterPollardEps m k *
                Real.sqrt (1 - carterPollardEps m k ^ 2)) ≤
          gaussianTailRaw z)
    (hB_event : ((k - 1 : ℕ) : ℝ) < qB u) :
    z < qZ u := by
  have hk : 1 ≤ k := by omega
  have hkm : k ≤ m := by omega
  have hmeas_binomial_val : Measurable (fun (i : Fin (m + 1)) => (i.val : ℝ)) := by
    fun_prop
  let μB : MeasureTheory.Measure ℝ :=
    (PMF.binomial (1 / 2 : ℝ≥0) (by norm_num) m).toMeasure.map
      (fun (i : Fin (m + 1)) => (i.val : ℝ))
  haveI : MeasureTheory.IsProbabilityMeasure μB :=
    MeasureTheory.Measure.isProbabilityMeasure_map hmeas_binomial_val.aemeasurable
  have htail :
      Erdos524.Helpers.binomialPolyTail m k (1 / 2 : ℝ) ≤ gaussianTailRaw z := by
    exact le_trans
      (binomialPolyTail_half_le_carterPollard_quadratic_strict_envelope
        (m := m) (k := k) hm hk_lower hk_upper hstrict)
      hscalar
  have hcdfB_lt : cdf μB ((k - 1 : ℕ) : ℝ) < u :=
    (Erdos524.Helpers.Erdos524.Helpers.quantile_gt_iff_cdf_lt
      (μ := μB) (q := qB) hGaloisB hu).mp hB_event
  have hcdfZ_le_cdfB :
      cdf (gaussianReal 0 1) z ≤ cdf μB ((k - 1 : ℕ) : ℝ) := by
    dsimp [μB]
    rw [gaussianReal_zero_one_cdf_eq_one_sub_gaussianTailRaw,
      binomialReal_cdf_pred_eq_one_sub_binomialPolyTail_half (m := m) (k := k) hk hkm]
    linarith
  have hcdfZ_lt : cdf (gaussianReal 0 1) z < u :=
    lt_of_le_of_lt hcdfZ_le_cdfB hcdfB_lt
  exact Erdos524.Helpers.Erdos524.Helpers.quantile_gt_of_cdf_lt hGaloisZ hu hcdfZ_lt

end FormalConjectures.ErdosProblems.Helpers.CarterPollardH
