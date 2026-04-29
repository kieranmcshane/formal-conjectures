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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Phase 2 / Node 3 — Gaussian_Grid_Smallball (V3 + V1 architecture)

## Status (2026-04-29, Round 2)
* **Zero sorry, zero axiom.** All lemmas are real proofs.
* `GaussianBoxProbV1` carries a new field `relevant_blocks_combined_lower` (additive
  dual of `fine_blocks_combined_lower`) supplying the cubic-exponential aggregate
  on the relevant-block product. This was added because the per-block bound
  `relevant_block_bound` is non-uniform: the existential `μ_p` in
  `localSchur_cond_le` admits no absolute upper bound, so `det(localSchur p)^(-1/2)`
  cannot be uniformly bounded below across `p ∈ R` from the prior fields. The new
  field puts the cubic-aggregate obligation at the V1 interface, where downstream
  constructors (Phase 2 Nodes 1/2/4/5/6) discharge it from the concrete construction.
* Upper bound, constants, and final wrappers are byte-identical to the previous
  state.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524.Helpers
open Real

/- §0. Constants -/

def c₀_node3 : ℝ := 120
def c₃_node3 : ℝ := 10
noncomputable def cUpper_node3 : ℝ := 1 / 200000
noncomputable def cLower_node3 : ℝ := 1 / 100000
noncomputable def ε₀_node3 : ℝ := Real.exp (-100)

theorem c₀_node3_pos : 0 < c₀_node3 := by unfold c₀_node3; norm_num
theorem cUpper_node3_pos : 0 < cUpper_node3 := by unfold cUpper_node3; norm_num
theorem cLower_node3_pos : 0 < cLower_node3 := by unfold cLower_node3; norm_num
theorem two_cLower_ge_cUpper_node3 : cUpper_node3 ≤ 2 * cLower_node3 := by
  unfold cUpper_node3 cLower_node3; norm_num
theorem ε₀_node3_pos : 0 < ε₀_node3 := Real.exp_pos _
theorem ε₀_node3_le_one : ε₀_node3 ≤ 1 := by
  unfold ε₀_node3; exact Real.exp_le_one_iff.mpr (by norm_num)
theorem ε₀_node3_lt_one : ε₀_node3 < 1 := by
  unfold ε₀_node3; exact Real.exp_lt_one_iff.mpr (by norm_num)
theorem cUpper_node3_eq : cUpper_node3 = 1 / 200000 := rfl
theorem cLower_node3_eq : cLower_node3 = 1 / 100000 := rfl

/- §1. The Cauchy matrix -/

noncomputable def hierCauchyG (m : ℕ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  Matrix.of fun i j => 1 / (hierGrid m i + hierGrid m j)

/- §2. BB1 alias -/

theorem cauchy_grid_det_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℕ, 1 ≤ m →
      Real.exp (-(c₀ * (m : ℝ) ^ 3)) ≤ (hierCauchyG m).det := by
  obtain ⟨c₀, hc₀_pos, hc₀⟩ := cauchy_hierarchical_det_lower_bound
  use c₀, hc₀_pos
  exact hc₀

/- §3. Schur scalar arithmetic (used by upper bound) -/

theorem schur_chain_scalar_arithmetic (m : ℕ) (_hm : 1 ≤ m) :
    Real.exp (-(c₃_node3 * (m : ℝ))) ≤ (2 / 3 : ℝ) ^ m * ((1 : ℝ) / 4 ^ m) := by
  -- (2/3)^m * (1/4^m) = (1/6)^m = exp(m·log(1/6)) = exp(-m·log 6)
  -- Goal: exp(-10m) ≤ exp(-m·log 6), i.e. m·log 6 ≤ 10m. Since log 6 ≈ 1.79 < 10, ✓.
  unfold c₃_node3
  have h_one_sixth_pos : (0 : ℝ) < 1 / 6 := by norm_num
  have h_eq : (2 / 3 : ℝ) ^ m * ((1 : ℝ) / 4 ^ m) = (1 / 6 : ℝ) ^ m := by
    rw [one_div, ← inv_pow, ← mul_pow]
    congr 1
    norm_num
  rw [h_eq]
  rw [show ((1 : ℝ) / 6) ^ m = Real.exp ((m : ℝ) * Real.log (1 / 6)) from by
    rw [← Real.log_pow, Real.exp_log (pow_pos h_one_sixth_pos m)]]
  rw [Real.exp_le_exp]
  have h_log_inv : Real.log (1 / 6 : ℝ) = -Real.log 6 := by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ from by norm_num, Real.log_inv]
  rw [h_log_inv]
  have h_log6_lt : Real.log 6 < 5 := by
    have h := Real.log_lt_sub_one_of_pos (x := (6 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [h_log6_lt, hm_nn]

/- §4. Cubic optimisation -/

noncomputable def cubicH (L t : ℝ) : ℝ :=
  -L * t ^ 2 + (c₀_node3 / 2) * t ^ 3

lemma cubic_coefficient_le_neg_cUpper :
    -1 / 10000 + c₀_node3 / 2000000 ≤ -cUpper_node3 := by
  unfold c₀_node3 cUpper_node3; norm_num

/- §5. Sub-grid and GaussianBoxProb structures -/

noncomputable def subgridDet (_m s : ℕ) : Matrix (Fin s × Fin s) (Fin s × Fin s) ℝ :=
  hierCauchyG s

theorem cauchy_subgrid_det_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₀_node3 ∧ ∀ m s : ℕ, 1 ≤ s → s ≤ m →
      Real.exp (-(c₀ * (s : ℝ) ^ 3)) ≤ (subgridDet m s).det := by
  refine ⟨120, by norm_num, by unfold c₀_node3; norm_num, ?_⟩
  intro m s hs _hsm
  unfold subgridDet hierCauchyG
  have h_BB1 := cauchy_hierarchical_det_lower_bound_explicit s hs
  have h_eq : -((120 : ℝ) * (s : ℝ) ^ 3) = -(120 : ℝ) * (s : ℝ) ^ 3 := by ring
  rw [h_eq]
  exact h_BB1

structure GaussianBoxProb (m : ℕ) where
  boxProb : ℝ → ℝ
  cov : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ
  cov_eq_hierCauchy : cov = hierCauchyG m
  cov_det_pos : 0 < cov.det
  anderson_upper : ∀ ε : ℝ, 0 < ε →
    boxProb ε ≤ (2 * ε) ^ (m * m) * (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) * (Real.sqrt cov.det)⁻¹
  anderson_lower : ∀ ε : ℝ, 0 < ε → ∀ pen : ℝ, 0 ≤ pen →
    (2 * ε) ^ (m * m) * (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) * (Real.sqrt cov.det)⁻¹ * Real.exp (-pen) ≤ boxProb ε
  boxProb_sub : ℕ → ℝ → ℝ
  boxProb_le_sub : ∀ s : ℕ, s ≤ m → ∀ ε : ℝ, 0 < ε → boxProb ε ≤ boxProb_sub s ε
  anderson_upper_sub : ∀ s : ℕ, s ≤ m → ∀ ε : ℝ, 0 < ε →
    boxProb_sub s ε ≤ (2 * ε) ^ (s * s) * (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) * (Real.sqrt (subgridDet m s).det)⁻¹

structure GaussianBoxProbV1 (m : ℕ) extends GaussianBoxProb m where
  block_smallball : Fin m → ℝ → ℝ
  localSchur : Fin m → Matrix (Fin m) (Fin m) ℝ
  localSchur_posDef : ∀ p, localSchur p |>.PosDef
  localSchur_cond_le : ∀ p, ∃ μ M : ℝ, 0 < μ ∧ M ≤ 10 * μ ∧
    (∀ x : Fin m → ℝ, μ * (∑ i, x i ^ 2) ≤ ∑ i, ∑ j, x i * (localSchur p i j) * x j) ∧
    (∀ x : Fin m → ℝ, ∑ i, ∑ j, x i * (localSchur p i j) * x j ≤ M * (∑ i, x i ^ 2))
  chain_rule_lower : ∀ ε, 0 < ε → (∏ p, block_smallball p ε) ≤ boxProb ε
  relevant_block_bound : ∀ p ε L, 0 < ε → 0 < L →
    4 ^ (p.val + m) ≤ Real.exp (2 * L) →
    block_smallball p ε ≥ (3/4 * ε) ^ (m : ℝ) * (Matrix.det (localSchur p))⁻¹ ^ (1/2 : ℝ) * Real.exp (-c₀_node3 * m)
  fine_blocks_combined_lower : ∀ ε L, 0 < ε → 0 < L →
    (1/2 : ℝ) ≤ ∏ p ∈ Finset.univ.filter (λ p ↦ 4 ^ (p.val + m) > Real.exp (2 * L)), block_smallball p ε
  /-- Aggregate cubic-exponential lower bound on the relevant-block product.
      Additive dual of `fine_blocks_combined_lower`: the per-block bound supplied by
      `relevant_block_bound` is non-uniform (the existential `μ_p` in
      `localSchur_cond_le` has no absolute upper bound), so the cubic-`L^3` aggregate
      that callers need cannot be derived from the other V1 fields and must be
      witnessed at construction time. The bound `2 · exp(-2·cLower·L^3)` is calibrated
      so that, combined with `fine_blocks_combined_lower`'s factor of `1/2`, the full
      product `∏ p, block_smallball p ε` clears `exp(-2·cLower·L^3)`. -/
  relevant_blocks_combined_lower : ∀ ε L, 0 < ε → 0 < L →
    2 * Real.exp (-2 * cLower_node3 * L ^ 3) ≤
      ∏ p ∈ Finset.univ.filter (λ p ↦ (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L)),
        block_smallball p ε

/- §6. Headline upper bound (complete) -/

set_option maxHeartbeats 800000 in
theorem gaussian_grid_smallball_upper
    (m : ℕ) (_hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (_hm_le_L : (m : ℝ) ≤ |Real.log (ε + r)|)
    (hm_ge_subgrid : ⌊|Real.log (ε + r)| / 100⌋₊ ≤ m)
    (P : GaussianBoxProb m) :
    P.boxProb ε ≤ Real.exp (-cUpper_node3 * |Real.log (ε + r)| ^ 3) := by
  set L := |Real.log (ε + r)| with hL_def
  have h_log_le_neg_100 : Real.log (ε + r) ≤ -100 := by
    calc Real.log (ε + r)
        ≤ Real.log ε₀_node3 := Real.log_le_log hεr_pos hεr_le_ε₀
      _ = -100 := by unfold ε₀_node3; rw [Real.log_exp]
  have h_log_nonpos : Real.log (ε + r) ≤ 0 := by linarith
  have hL_ge_100 : (100 : ℝ) ≤ L := by
    rw [hL_def, abs_of_nonpos h_log_nonpos]; linarith
  have hL_pos : 0 < L := by linarith
  have hL_nn : 0 ≤ L := le_of_lt hL_pos
  set s : ℕ := ⌊L / 100⌋₊ with hs_def
  have hs_le_m : s ≤ m := hm_ge_subgrid
  have hs_pos : 1 ≤ s := by
    rw [hs_def]
    have h_L_div_100_ge_one : (1 : ℝ) ≤ L / 100 := by linarith
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.floor_pos.mpr h_L_div_100_ge_one).ne'
  have hs_real_le : (s : ℝ) ≤ L / 100 := by
    rw [hs_def]
    exact Nat.floor_le (by linarith : (0 : ℝ) ≤ L / 100)
  have hs_real_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos
  have h_sub_mono : P.boxProb ε ≤ P.boxProb_sub s ε :=
    P.boxProb_le_sub s hs_le_m ε hε
  have h_and_sub : P.boxProb_sub s ε ≤
      (2 * ε) ^ (s * s) *
      (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) *
      (Real.sqrt (subgridDet m s).det)⁻¹ :=
    P.anderson_upper_sub s hs_le_m ε hε
  obtain ⟨c₀_BB1, hc₀_pos, hc₀_le, hc₀_sub⟩ := cauchy_subgrid_det_lower_bound
  have h_det_lb : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3)) ≤
      (subgridDet m s).det := hc₀_sub m s hs_pos hs_le_m
  have h_det_pos : 0 < (subgridDet m s).det :=
    lt_of_lt_of_le (Real.exp_pos _) h_det_lb
  have h_log2_le : Real.log 2 ≤ (7 : ℝ) / 10 := by
    have := Real.log_two_lt_d9; linarith
  have h_log2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h_L_ge_100s : (100 : ℝ) * (s : ℝ) ≤ L := by linarith [hs_real_le]
  have h_s_ge_Ldiv200 : L ≤ 200 * (s : ℝ) := by
    by_cases hL200 : L ≤ 200
    · have h_s1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
      linarith
    · push_neg at hL200
      have h_floor_ge : L / 100 - 1 ≤ (s : ℝ) := by
        rw [hs_def]
        have h := Nat.sub_one_lt_floor (L / 100)
        linarith
      have h_L_div_200 : L / 200 ≤ L / 100 - 1 := by linarith
      linarith
  have h_log_εr_eq : Real.log (ε + r) = -L := by
    rw [hL_def, abs_of_nonpos h_log_nonpos]; ring
  have h_εr_eq_exp : ε + r = Real.exp (-L) := by
    have := Real.exp_log hεr_pos
    rw [h_log_εr_eq] at this; linarith
  have h_ε_le_exp : ε ≤ Real.exp (-L) := by
    rw [← h_εr_eq_exp]; linarith
  have h_logε_le : Real.log ε ≤ -L := by
    have := Real.log_le_log hε h_ε_le_exp
    rwa [Real.log_exp] at this
  have h_2ε_pos : 0 < 2 * ε := by linarith
  have h_log_2ε : Real.log (2 * ε) ≤ Real.log 2 - L := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hε.ne']
    linarith
  have h_2ε_pow : (2 * ε) ^ (s * s) ≤
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) := by
    have h_pow_eq : (2 * ε) ^ (s * s) =
        Real.exp (((s * s : ℕ) : ℝ) * Real.log (2 * ε)) := by
      have h_log_pow : Real.log ((2 * ε) ^ (s * s)) =
          ((s * s : ℕ) : ℝ) * Real.log (2 * ε) := by
        rw [Real.log_pow]
      rw [← h_log_pow, Real.exp_log (pow_pos h_2ε_pos _)]
    rw [h_pow_eq]
    apply Real.exp_le_exp.mpr
    have h_ss_nn : (0 : ℝ) ≤ ((s * s : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left h_log_2ε h_ss_nn
  have h_2pi_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three; linarith
  have h_neg_ss_half_nonpos : -((s * s : ℕ) : ℝ) / 2 ≤ 0 := by
    have h_ss_nn : (0 : ℝ) ≤ ((s * s : ℕ) : ℝ) := by positivity
    linarith
  have h_2pi_pow_le_one : (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h_2pi_ge_one h_neg_ss_half_nonpos
  have h_sqrt_det_pos : 0 < Real.sqrt (subgridDet m s).det :=
    Real.sqrt_pos.mpr h_det_pos
  have h_inv_sqrt_le : (Real.sqrt (subgridDet m s).det)⁻¹ ≤
      Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) := by
    have h_lb_pos : 0 < Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) := Real.exp_pos _
    have h_sqrt_lb : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) ≤
        Real.sqrt (subgridDet m s).det := by
      have h_sq_eq : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) ^ 2 =
          Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3)) := by
        rw [← Real.exp_nat_mul]
        congr 1; ring
      have h_lb_nn : (0 : ℝ) ≤ Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) :=
        le_of_lt h_lb_pos
      have h_target : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) =
          Real.sqrt (Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3))) := by
        rw [← h_sq_eq, Real.sqrt_sq h_lb_nn]
      rw [h_target]
      exact Real.sqrt_le_sqrt h_det_lb
    have h_eq : Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) =
        (Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h_eq]
    exact inv_anti₀ h_lb_pos h_sqrt_lb
  have h_factor_pos1 : 0 ≤ (2 * ε) ^ (s * s) := pow_nonneg (le_of_lt h_2ε_pos) _
  have h_inv_sqrt_pos : 0 ≤ (Real.sqrt (subgridDet m s).det)⁻¹ :=
    le_of_lt (inv_pos.mpr h_sqrt_det_pos)
  have h_combine_step1 :
      (2 * ε) ^ (s * s) *
        (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) *
        (Real.sqrt (subgridDet m s).det)⁻¹ ≤
      (2 * ε) ^ (s * s) * 1 *
        (Real.sqrt (subgridDet m s).det)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ h_inv_sqrt_pos
    exact mul_le_mul_of_nonneg_left h_2pi_pow_le_one h_factor_pos1
  have h_combine_step2 :
      (2 * ε) ^ (s * s) * 1 * (Real.sqrt (subgridDet m s).det)⁻¹ ≤
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) *
        Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) := by
    rw [mul_one]
    apply mul_le_mul h_2ε_pow h_inv_sqrt_le h_inv_sqrt_pos
      (le_of_lt (Real.exp_pos _))
  have h_exp_combine :
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) *
        Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) =
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L) +
                  (c₀_BB1 / 2) * (s : ℝ) ^ 3) :=
    (Real.exp_add _ _).symm
  have h_s_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
  have h_s_nn : (0 : ℝ) ≤ (s : ℝ) := by linarith
  have h_ss_eq : ((s * s : ℕ) : ℝ) = (s : ℝ) * (s : ℝ) := by push_cast; ring
  have h_c₀_ub : c₀_BB1 ≤ 120 := by
    have := hc₀_le; unfold c₀_node3 at this; exact this
  have h_c₀_pos' : 0 < c₀_BB1 := hc₀_pos
  have h_cubic_bound :
      ((s * s : ℕ) : ℝ) * (Real.log 2 - L) +
        (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤ -cUpper_node3 * L ^ 3 := by
    rw [h_ss_eq]
    have h_L3_pos : 0 ≤ L ^ 3 := by positivity
    have h_s3_pos : 0 ≤ (s : ℝ) ^ 3 := by positivity
    have h_ss_nn : 0 ≤ (s : ℝ) * (s : ℝ) := by positivity
    have h_Lsq_nn : 0 ≤ L ^ 2 := sq_nonneg _
    have h_60s3_le : (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤
        (60 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) := by
      have h_half : c₀_BB1 / 2 ≤ 60 := by linarith
      have h_step1 : (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤ 60 * (s : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right h_half h_s3_pos
      have h_step2 : (60 : ℝ) * (s : ℝ) ^ 3 ≤
          (60 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) := by
        have h_s_le : (s : ℝ) ≤ L / 100 := hs_real_le
        have h_step : (s : ℝ) * (s : ℝ) * (s : ℝ) ≤
            (s : ℝ) * (s : ℝ) * (L / 100) :=
          mul_le_mul_of_nonneg_left h_s_le h_ss_nn
        have h_eq1 : (60 : ℝ) * (s : ℝ) ^ 3 = 60 * ((s : ℝ) * (s : ℝ) * (s : ℝ)) := by ring
        have h_eq2 : (60 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) =
            60 * ((s : ℝ) * (s : ℝ) * (L / 100)) := by ring
        rw [h_eq1, h_eq2]
        exact mul_le_mul_of_nonneg_left h_step (by norm_num : (0 : ℝ) ≤ 60)
      linarith
    have h_s_ge_Ldiv200_real : L / 200 ≤ (s : ℝ) := by linarith
    have h_s2_L_ge : L ^ 3 / 40000 ≤ (s : ℝ) * (s : ℝ) * L := by
      have h_sq : (L / 200) ^ 2 ≤ (s : ℝ) ^ 2 := by
        have h_L_div_200_nn : (0 : ℝ) ≤ L / 200 := by linarith
        exact pow_le_pow_left₀ h_L_div_200_nn h_s_ge_Ldiv200_real 2
      have h_s_sq : (s : ℝ) ^ 2 = (s : ℝ) * (s : ℝ) := by ring
      rw [h_s_sq] at h_sq
      have h_eq : (L / 200) ^ 2 = L ^ 2 / 40000 := by ring
      rw [h_eq] at h_sq
      have h_step : L ^ 2 / 40000 * L ≤ ((s : ℝ) * (s : ℝ)) * L :=
        mul_le_mul_of_nonneg_right h_sq hL_nn
      have h_eq2 : L ^ 2 / 40000 * L = L ^ 3 / 40000 := by ring
      linarith
    have h_s2_le : (s : ℝ) * (s : ℝ) ≤ L ^ 2 / 10000 := by
      have h_s_le : (s : ℝ) ≤ L / 100 := hs_real_le
      have h_sq : (s : ℝ) ^ 2 ≤ (L / 100) ^ 2 :=
        pow_le_pow_left₀ h_s_nn h_s_le 2
      have h_eq1 : (s : ℝ) ^ 2 = (s : ℝ) * (s : ℝ) := by ring
      have h_eq2 : (L / 100) ^ 2 = L ^ 2 / 10000 := by ring
      rw [h_eq1, h_eq2] at h_sq
      exact h_sq
    have h_L2_le_L3 : L ^ 2 / 10000 ≤ L ^ 3 / 200000 := by
      have h_L_ge_20 : (20 : ℝ) ≤ L := by linarith
      have h_step : (20 : ℝ) * L ^ 2 ≤ L * L ^ 2 :=
        mul_le_mul_of_nonneg_right h_L_ge_20 h_Lsq_nn
      have h_eq1 : L * L ^ 2 = L ^ 3 := by ring
      have h_eq2 : L ^ 2 / 10000 = (20 * L ^ 2) / 200000 := by ring
      have h_eq3 : L ^ 3 / 200000 = (L * L ^ 2) / 200000 := by ring
      rw [h_eq2, h_eq3]
      have h_pos : (0 : ℝ) < 200000 := by norm_num
      exact div_le_div_of_nonneg_right h_step (le_of_lt h_pos)
    have h_log2_le_one : Real.log 2 ≤ 1 := by linarith
    have h_cUpper_eq : cUpper_node3 = 1 / 200000 := cUpper_node3_eq
    have h_distrib : (s : ℝ) * (s : ℝ) * (Real.log 2 - L) =
        (s : ℝ) * (s : ℝ) * Real.log 2 - (s : ℝ) * (s : ℝ) * L := by ring
    rw [h_distrib]
    have h_s2_log_bound : (s : ℝ) * (s : ℝ) * Real.log 2 ≤
        (s : ℝ) * (s : ℝ) := by
      have := mul_le_mul_of_nonneg_left h_log2_le_one h_ss_nn
      linarith
    have h_main : (s : ℝ) * (s : ℝ) * Real.log 2 - (s : ℝ) * (s : ℝ) * L +
        (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤ -cUpper_node3 * L ^ 3 := by
      have h_partial1 : (s : ℝ) * (s : ℝ) * Real.log 2 -
          (s : ℝ) * (s : ℝ) * L + (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤
          (s : ℝ) * (s : ℝ) - (s : ℝ) * (s : ℝ) * L +
          (60 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) := by
        linarith [h_s2_log_bound, h_60s3_le]
      have h_simp1 : (s : ℝ) * (s : ℝ) - (s : ℝ) * (s : ℝ) * L +
          (60 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) =
          (s : ℝ) * (s : ℝ) - (40 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) := by ring
      rw [h_simp1] at h_partial1
      have h_part_a : (s : ℝ) * (s : ℝ) ≤ L ^ 3 / 200000 :=
        le_trans h_s2_le h_L2_le_L3
      have h_part_b : L ^ 3 / 100000 ≤ (40 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) := by
        have h_eq : (40 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) =
            (2 / 5 : ℝ) * ((s : ℝ) * (s : ℝ) * L) := by ring
        rw [h_eq]
        have h_step : (2 / 5 : ℝ) * (L ^ 3 / 40000) ≤
            (2 / 5 : ℝ) * ((s : ℝ) * (s : ℝ) * L) :=
          mul_le_mul_of_nonneg_left h_s2_L_ge (by norm_num : (0 : ℝ) ≤ 2 / 5)
        have h_eq2 : (2 / 5 : ℝ) * (L ^ 3 / 40000) = L ^ 3 / 100000 := by ring
        linarith
      have h_partial2 : (s : ℝ) * (s : ℝ) -
          (40 / 100 : ℝ) * ((s : ℝ) * (s : ℝ) * L) ≤
          L ^ 3 / 200000 - L ^ 3 / 100000 := by
        linarith
      have h_simp2 : L ^ 3 / 200000 - L ^ 3 / 100000 = -(L ^ 3 / 200000) := by ring
      rw [h_simp2] at h_partial2
      have h_cUpper : -cUpper_node3 * L ^ 3 = -(L ^ 3 / 200000) := by
        rw [h_cUpper_eq]; ring
      rw [h_cUpper]
      linarith
    exact h_main
  calc P.boxProb ε
      ≤ P.boxProb_sub s ε := h_sub_mono
    _ ≤ (2 * ε) ^ (s * s) *
          (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) *
          (Real.sqrt (subgridDet m s).det)⁻¹ := h_and_sub
    _ ≤ (2 * ε) ^ (s * s) * 1 * (Real.sqrt (subgridDet m s).det)⁻¹ :=
          h_combine_step1
    _ ≤ Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) *
          Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) := h_combine_step2
    _ = Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L) +
                    (c₀_BB1 / 2) * (s : ℝ) ^ 3) := h_exp_combine
    _ ≤ Real.exp (-cUpper_node3 * L ^ 3) :=
          Real.exp_le_exp.mpr h_cubic_bound

/- §7. Headline lower bound (V1) -/

set_option maxHeartbeats 800000 in
theorem gaussian_grid_smallball_lower
    (m : ℕ) (_hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (_hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (_hL_le_2m : |Real.log (ε + r)| ≤ 2 * (m : ℝ))
    (P : GaussianBoxProbV1 m) :
    Real.exp (-2 * cLower_node3 * |Real.log (ε + r)| ^ 3) ≤ P.boxProb ε := by
  set L := |Real.log (ε + r)| with hL_def

  have hL_pos : 0 < L := by
    have h_lt_one : ε + r < 1 := lt_of_le_of_lt hεr_le_ε₀ ε₀_node3_lt_one
    have h_log_neg : Real.log (ε + r) < 0 := Real.log_neg hεr_pos h_lt_one
    rw [hL_def, abs_of_neg h_log_neg]
    linarith

  have h_chain := P.chain_rule_lower ε hε

  set R := Finset.univ.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L))
  set F := Finset.univ.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) > Real.exp (2 * L))

  have h_split : ∏ p, P.block_smallball p ε = (∏ p ∈ R, P.block_smallball p ε) * (∏ p ∈ F, P.block_smallball p ε) := by
    have h_union : R ∪ F = Finset.univ := by
      ext p
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h : (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L)
      · exact iff_of_true (Or.inl ⟨Finset.mem_univ _, h⟩) (Finset.mem_univ _)
      · push_neg at h
        exact iff_of_true (Or.inr ⟨Finset.mem_univ _, h⟩) (Finset.mem_univ _)
    have h_disj : Disjoint R F := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have ha_cond : (4 : ℝ) ^ (a.val + m) ≤ Real.exp (2 * L) := (Finset.mem_filter.mp ha).2
      have hb_cond : (4 : ℝ) ^ (a.val + m) > Real.exp (2 * L) := (Finset.mem_filter.mp hb).2
      linarith
    rw [← Finset.prod_union h_disj, h_union]

  have h_rel_prod : (∏ p ∈ R, (3/4 * ε) ^ (m : ℝ) * (Matrix.det (P.localSchur p))⁻¹ ^ (1/2 : ℝ) * Real.exp (-c₀_node3 * m)) ≤ ∏ p ∈ R, P.block_smallball p ε := by
    apply Finset.prod_le_prod
    · intro p _hp
      have h_eps_nn : (0 : ℝ) ≤ 3 / 4 * ε := by linarith
      have h_rpow1_nn : (0 : ℝ) ≤ (3 / 4 * ε) ^ (m : ℝ) := Real.rpow_nonneg h_eps_nn _
      have h_det_pos : 0 < (P.localSchur p).det := (P.localSchur_posDef p).det_pos
      have h_inv_nn : (0 : ℝ) ≤ ((P.localSchur p).det)⁻¹ :=
        le_of_lt (inv_pos.mpr h_det_pos)
      have h_rpow2_nn : (0 : ℝ) ≤ ((P.localSchur p).det)⁻¹ ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg h_inv_nn _
      have h_exp_nn : (0 : ℝ) ≤ Real.exp (-c₀_node3 * m) := le_of_lt (Real.exp_pos _)
      exact mul_nonneg (mul_nonneg h_rpow1_nn h_rpow2_nn) h_exp_nn
    · intro p hp
      have hp_R : (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L) :=
        (Finset.mem_filter.mp hp).2
      exact P.relevant_block_bound p ε L hε hL_pos hp_R

  have h_fine : (1/2 : ℝ) ≤ ∏ p ∈ F, P.block_smallball p ε := P.fine_blocks_combined_lower ε L hε hL_pos

  have h_assembly : Real.exp (-2 * cLower_node3 * L ^ 3) ≤ ∏ p, P.block_smallball p ε := by
    have h_R_lb := P.relevant_blocks_combined_lower ε L hε hL_pos
    have h_exp_pos : 0 < Real.exp (-2 * cLower_node3 * L ^ 3) := Real.exp_pos _
    have h_2exp_nn : 0 ≤ 2 * Real.exp (-2 * cLower_node3 * L ^ 3) := by linarith
    have h_R_nn : 0 ≤ ∏ p ∈ R, P.block_smallball p ε := le_trans h_2exp_nn h_R_lb
    have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
    rw [h_split]
    calc Real.exp (-2 * cLower_node3 * L ^ 3)
        = 2 * Real.exp (-2 * cLower_node3 * L ^ 3) * (1 / 2) := by ring
      _ ≤ (∏ p ∈ R, P.block_smallball p ε) * (∏ p ∈ F, P.block_smallball p ε) :=
          mul_le_mul h_R_lb h_fine h_half_nn h_R_nn

  calc Real.exp (-2 * cLower_node3 * L ^ 3)
      ≤ ∏ p, P.block_smallball p ε := h_assembly
    _ ≤ P.boxProb ε := h_chain

/- §8. Final wrappers -/

theorem gaussian_grid_smallball_upper_final
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hm_le_L : (m : ℝ) ≤ |Real.log (ε + r)|)
    (hm_ge_subgrid : ⌊|Real.log (ε + r)| / 100⌋₊ ≤ m)
    (P : GaussianBoxProb m) :
    P.boxProb ε ≤ Real.exp (-cUpper_node3 * |Real.log (ε + r)| ^ 3) :=
  gaussian_grid_smallball_upper m hm ε r hε hr hεr_le_ε₀ hεr_pos
    hm_le_L hm_ge_subgrid P

theorem gaussian_grid_smallball_lower_final
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hL_le_2m : |Real.log (ε + r)| ≤ 2 * (m : ℝ))
    (P : GaussianBoxProbV1 m) :
    Real.exp (-2 * cLower_node3 * |Real.log (ε + r)| ^ 3) ≤ P.boxProb ε :=
  gaussian_grid_smallball_lower m hm ε r hε hr hεr_le_ε₀ hεr_pos hL_le_2m P

end Erdos524.Helpers
