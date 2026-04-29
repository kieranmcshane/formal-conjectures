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

import FormalConjectures.Util.ProblemImports

/-!
# Asymptotics of the cubic subsequence `n_m := ⌊exp(m³)⌋`

Chojecki's Theorem 18 (used in Erdős problem 524) operates on the cubic
subsequence `n_m := ⌊exp(m³)⌋`. This file provides the analogous asymptotic
lemmas to those in `LilNormAsymptotics.lean` (which handles the geometric
subsequence `⌊c^k⌋`).

The main results are:

* `cubicSubseq_tendsto_atTop` — `n_m → ∞`.
* `log_cubicSubseq_div_cube_tendsto` — `log(n_m) / m³ → 1`.
* `log_cubicSubseq_ge_half_cube` — `log(n_m) ≥ m³/2` eventually.
* `loglog_cubicSubseq_div_3log_tendsto` — `log log(n_m) / (3 log m) → 1`.
* `loglog_cubicSubseq_ge_log` — `log log(n_m) ≥ log m` eventually.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524.Helpers

open Filter Topology

/-- The cubic subsequence `n_m := ⌊exp(m³)⌋`. -/
noncomputable def cubicSubseq (m : ℕ) : ℕ := ⌊Real.exp ((m : ℝ) ^ 3)⌋₊

/-- `exp(m³) → ∞` as `m → ∞`. -/
private lemma exp_cube_tendsto_atTop :
    Tendsto (fun m : ℕ => Real.exp ((m : ℝ) ^ 3)) atTop atTop := by
  have hcube : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat
  exact Real.tendsto_exp_atTop.comp hcube

/-- `cubicSubseq` tends to infinity. -/
theorem cubicSubseq_tendsto_atTop :
    Tendsto cubicSubseq atTop atTop := by
  -- `cubicSubseq m : ℕ`; we show for every `b : ℕ`, eventually `b ≤ cubicSubseq m`.
  refine tendsto_atTop.mpr fun b => ?_
  have hexp := tendsto_atTop.mp exp_cube_tendsto_atTop ((b : ℝ) + 1)
  filter_upwards [hexp] with m hm
  have hsub : (b : ℝ) ≤ Real.exp ((m : ℝ) ^ 3) - 1 := by linarith
  have hfloor : Real.exp ((m : ℝ) ^ 3) - 1 < (⌊Real.exp ((m : ℝ) ^ 3)⌋₊ : ℝ) :=
    mod_cast Nat.sub_one_lt_floor (Real.exp ((m : ℝ) ^ 3))
  have : (b : ℝ) < (cubicSubseq m : ℝ) := lt_of_le_of_lt hsub hfloor
  exact_mod_cast this.le

/-- `cubicSubseq m` (as a real) tends to infinity. -/
private lemma cubicSubseq_real_tendsto_atTop :
    Tendsto (fun m : ℕ => (cubicSubseq m : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp cubicSubseq_tendsto_atTop

/-- Eventually `cubicSubseq m ≥ 1`. -/
private lemma eventually_cubicSubseq_pos :
    ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (cubicSubseq m : ℝ) :=
  cubicSubseq_real_tendsto_atTop.eventually_gt_atTop 0

/-- Upper bound: `(cubicSubseq m : ℝ) ≤ exp(m³)` for all `m`. -/
private lemma cubicSubseq_le_exp (m : ℕ) :
    (cubicSubseq m : ℝ) ≤ Real.exp ((m : ℝ) ^ 3) :=
  Nat.floor_le (le_of_lt (Real.exp_pos _))

/-- Lower bound: `(cubicSubseq m : ℝ) > exp(m³) - 1` for all `m`. -/
private lemma cubicSubseq_gt_exp_sub_one (m : ℕ) :
    Real.exp ((m : ℝ) ^ 3) - 1 < (cubicSubseq m : ℝ) := by
  unfold cubicSubseq
  exact_mod_cast Nat.sub_one_lt_floor (Real.exp ((m : ℝ) ^ 3))

/-- `log(cubicSubseq m) ≤ m³` eventually (when `cubicSubseq m > 0`). -/
private lemma log_cubicSubseq_le_cube :
    ∀ᶠ m : ℕ in atTop, Real.log (cubicSubseq m : ℝ) ≤ (m : ℝ) ^ 3 := by
  filter_upwards [eventually_cubicSubseq_pos] with m hm
  have hle := cubicSubseq_le_exp m
  have := Real.log_le_log hm hle
  rwa [Real.log_exp] at this

/-- `log(cubicSubseq m) ≥ m³ / 2` eventually. -/
theorem log_cubicSubseq_ge_half_cube :
    ∀ᶠ m : ℕ in atTop, Real.log (cubicSubseq m : ℝ) ≥ (m : ℝ) ^ 3 / 2 := by
  -- Strategy: for large m, `exp(m³) - 1 ≥ exp(m³)/2`, so
  -- `cubicSubseq m > exp(m³)/2`, hence `log(cubicSubseq m) > m³ - log 2 ≥ m³/2` for large m.
  -- Precisely: we need `exp(m³) ≥ 2`, i.e. `m³ ≥ log 2`.
  -- And `m³ - log 2 ≥ m³/2` iff `m³/2 ≥ log 2`, i.e. `m³ ≥ 2 log 2`.
  have hcube_top : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat
  have hcube_large : ∀ᶠ m : ℕ in atTop, (2 * Real.log 2 : ℝ) ≤ (m : ℝ) ^ 3 :=
    hcube_top.eventually_ge_atTop (2 * Real.log 2)
  filter_upwards [hcube_large] with m hm
  -- Set x = m^3.
  set x : ℝ := (m : ℝ) ^ 3 with hx_def
  -- `log 2 ≤ x/2` and `log 2 ≤ x`.
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_half : Real.log 2 ≤ x / 2 := by linarith
  have hlog2_le_x : Real.log 2 ≤ x := by linarith [hlog2_pos.le]
  -- So `exp x ≥ 2`, and `exp x - 1 ≥ exp x / 2`.
  have hexp_ge_two : (2 : ℝ) ≤ Real.exp x := by
    have : Real.exp (Real.log 2) ≤ Real.exp x := Real.exp_le_exp.mpr hlog2_le_x
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
  have hexp_pos : (0 : ℝ) < Real.exp x := Real.exp_pos _
  have hhalf : Real.exp x / 2 ≤ Real.exp x - 1 := by linarith
  -- `cubicSubseq m > exp x - 1 ≥ exp x / 2 > 0`.
  have hcs_gt : Real.exp x - 1 < (cubicSubseq m : ℝ) := cubicSubseq_gt_exp_sub_one m
  have hcs_ge_halfexp : Real.exp x / 2 ≤ (cubicSubseq m : ℝ) := le_of_lt (lt_of_le_of_lt hhalf hcs_gt)
  have hhalf_pos : (0 : ℝ) < Real.exp x / 2 := by positivity
  have hcs_pos : (0 : ℝ) < (cubicSubseq m : ℝ) := lt_of_lt_of_le hhalf_pos hcs_ge_halfexp
  -- Take log.
  have hlog_le := Real.log_le_log hhalf_pos hcs_ge_halfexp
  -- log(exp x / 2) = x - log 2.
  have hlogrewrite : Real.log (Real.exp x / 2) = x - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hexp_pos) (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp]
  rw [hlogrewrite] at hlog_le
  -- `x - log 2 ≥ x/2`.
  have : x / 2 ≤ x - Real.log 2 := by linarith
  exact this.trans hlog_le

/-- `log(cubicSubseq m) / m³ → 1`. -/
theorem log_cubicSubseq_div_cube_tendsto :
    Tendsto (fun m : ℕ => Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3)
      atTop (𝓝 1) := by
  -- Sandwich between `(m³/2)/m³ = 1/2` and `m³/m³ = 1`. But we need the limit to be exactly 1.
  -- Refine: `log(cubicSubseq m) ≥ log(exp(m³) - 1)`, and `log(exp(m³) - 1)/m³ → 1`.
  -- Upper bound: `log(cubicSubseq m) ≤ m³`, so ratio ≤ 1.
  -- Lower bound: `log(cubicSubseq m) ≥ log(exp(m³) - 1) = m³ + log(1 - exp(-m³)) → m³`.
  -- Ratio ≥ (m³ + log(1 - exp(-m³)))/m³ = 1 + log(1 - exp(-m³))/m³ → 1.
  have hcube_top : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat
  -- `exp(-m³) → 0`.
  have hnegcube : Tendsto (fun m : ℕ => -(m : ℝ) ^ 3) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hcube_top
  have hexp_neg : Tendsto (fun m : ℕ => Real.exp (-(m : ℝ) ^ 3)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegcube
  -- `1 - exp(-m³) → 1`.
  have h1_minus : Tendsto (fun m : ℕ => 1 - Real.exp (-(m : ℝ) ^ 3)) atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => (1 : ℝ) - Real.exp (-(m : ℝ) ^ 3)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hexp_neg
    simpa using this
  -- `log(1 - exp(-m³)) → log 1 = 0`.
  have hcontlog : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
  have h_log_1_minus :
      Tendsto (fun m : ℕ => Real.log (1 - Real.exp (-(m : ℝ) ^ 3))) atTop (𝓝 0) := by
    have := hcontlog.tendsto.comp h1_minus
    simpa [Real.log_one] using this
  -- `log(1 - exp(-m³)) / m³ → 0`.
  have hsmall :
      Tendsto (fun m : ℕ => Real.log (1 - Real.exp (-(m : ℝ) ^ 3)) / (m : ℝ) ^ 3)
        atTop (𝓝 0) := by
    have := h_log_1_minus.div_atTop hcube_top
    simpa using this
  -- Eventually `exp(-m³) < 1/2 < 1` so `1 - exp(-m³) > 1/2 > 0`.
  have h1minus_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < 1 - Real.exp (-(m : ℝ) ^ 3) := by
    have hlim : Tendsto (fun m : ℕ => (1 : ℝ) - Real.exp (-(m : ℝ) ^ 3)) atTop (𝓝 1) := h1_minus
    exact hlim.eventually_const_lt (by norm_num : (0 : ℝ) < 1)
  -- `log(exp(m³) - 1) = m³ + log(1 - exp(-m³))` when `exp(m³) > 1`.
  have hcube_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (m : ℝ) ^ 3 :=
    hcube_top.eventually_gt_atTop 0
  -- Lower bound for the ratio: L m := (m^3 + log(1 - exp(-m³)))/m³ → 1.
  have hL_tendsto :
      Tendsto (fun m : ℕ =>
        ((m : ℝ) ^ 3 + Real.log (1 - Real.exp (-(m : ℝ) ^ 3))) / (m : ℝ) ^ 3)
        atTop (𝓝 1) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) +
        Real.log (1 - Real.exp (-(m : ℝ) ^ 3)) / (m : ℝ) ^ 3) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hsmall
    have : ∀ᶠ m : ℕ in atTop,
        (1 : ℝ) + Real.log (1 - Real.exp (-(m : ℝ) ^ 3)) / (m : ℝ) ^ 3 =
          ((m : ℝ) ^ 3 + Real.log (1 - Real.exp (-(m : ℝ) ^ 3))) / (m : ℝ) ^ 3 := by
      filter_upwards [hcube_pos] with m hm
      have hne : ((m : ℝ) ^ 3) ≠ 0 := ne_of_gt hm
      rw [add_div, div_self hne]
    have hres : Tendsto (fun m : ℕ =>
        ((m : ℝ) ^ 3 + Real.log (1 - Real.exp (-(m : ℝ) ^ 3))) / (m : ℝ) ^ 3) atTop (𝓝 (1 + 0)) :=
      h1.congr' this
    simpa using hres
  -- Upper bound for the ratio: U m := 1 (constant).
  have hU_tendsto : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  -- Squeeze: L ≤ target ≤ U eventually.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL_tendsto hU_tendsto ?_ ?_
  · -- L m ≤ target m: we need
    -- `(m^3 + log(1 - e^{-m³}))/m³ ≤ log(cubicSubseq m)/m³`.
    filter_upwards [hcube_pos, h1minus_pos, eventually_cubicSubseq_pos] with m hmcube hminus hcs
    have hexp_pos : (0 : ℝ) < Real.exp ((m : ℝ) ^ 3) := Real.exp_pos _
    -- `exp(m³) - 1 > 0` since `exp(m³) > 1` (because `m³ > 0`).
    have hexp_gt_one : (1 : ℝ) < Real.exp ((m : ℝ) ^ 3) := by
      have := Real.exp_lt_exp.mpr hmcube
      -- exp(0) = 1 < exp(m³) since 0 < m³.
      rwa [Real.exp_zero] at this
    have hexp_sub_pos : (0 : ℝ) < Real.exp ((m : ℝ) ^ 3) - 1 := by linarith
    -- `log(exp(m³) - 1) = m³ + log(1 - exp(-m³))`.
    have hlogrew : Real.log (Real.exp ((m : ℝ) ^ 3) - 1) =
        (m : ℝ) ^ 3 + Real.log (1 - Real.exp (-(m : ℝ) ^ 3)) := by
      have hrewrite : Real.exp ((m : ℝ) ^ 3) - 1 =
          Real.exp ((m : ℝ) ^ 3) * (1 - Real.exp (-(m : ℝ) ^ 3)) := by
        have hsum : Real.exp ((m : ℝ) ^ 3) * Real.exp (-(m : ℝ) ^ 3) = 1 := by
          rw [← Real.exp_add]; simp
        have : Real.exp ((m : ℝ) ^ 3) * (1 - Real.exp (-(m : ℝ) ^ 3)) =
            Real.exp ((m : ℝ) ^ 3) - Real.exp ((m : ℝ) ^ 3) * Real.exp (-(m : ℝ) ^ 3) := by ring
        rw [this, hsum]
      rw [hrewrite, Real.log_mul (ne_of_gt hexp_pos) (ne_of_gt hminus), Real.log_exp]
    -- `log(exp(m³) - 1) ≤ log(cubicSubseq m)`.
    have hcs_gt : Real.exp ((m : ℝ) ^ 3) - 1 < (cubicSubseq m : ℝ) := cubicSubseq_gt_exp_sub_one m
    have hlog_le : Real.log (Real.exp ((m : ℝ) ^ 3) - 1) ≤ Real.log (cubicSubseq m : ℝ) :=
      (Real.log_le_log hexp_sub_pos hcs_gt.le)
    -- Divide by `m³ > 0`.
    have := div_le_div_of_nonneg_right hlog_le (le_of_lt hmcube)
    rw [hlogrew] at this
    exact this
  · -- target m ≤ 1: `log(cubicSubseq m)/m³ ≤ 1`.
    filter_upwards [log_cubicSubseq_le_cube, hcube_pos] with m hle hmcube
    have hne : ((m : ℝ) ^ 3) ≠ 0 := ne_of_gt hmcube
    rw [div_le_one hmcube]
    exact hle

/-- `log(cubicSubseq m) / m³ → 1` implies eventually `log(cubicSubseq m) > 0`. -/
private lemma eventually_log_cubicSubseq_pos :
    ∀ᶠ m : ℕ in atTop, (0 : ℝ) < Real.log (cubicSubseq m : ℝ) := by
  filter_upwards [log_cubicSubseq_ge_half_cube,
    (show Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop by
      have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      exact (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat).eventually_gt_atTop 0]
    with m hhalf hcube
  have : (0 : ℝ) < (m : ℝ) ^ 3 / 2 := by linarith
  linarith

/-- `log log(cubicSubseq m) / (3 log m) → 1`. -/
theorem loglog_cubicSubseq_div_3log_tendsto :
    Tendsto (fun m : ℕ =>
      Real.log (Real.log (cubicSubseq m : ℝ)) / (3 * Real.log (m : ℝ)))
      atTop (𝓝 1) := by
  -- We use: `log(cubicSubseq m)/m³ → 1`, so `log log(cubicSubseq m) = log(m³ · (log(cs)/m³))
  --   = 3 log m + log(log(cs)/m³) → 3 log m` in ratio.
  have hcube_top : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop := by
    have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat
  have hnat_top : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogm_top : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat_top
  have hratio_to_one : Tendsto (fun m : ℕ =>
      Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3) atTop (𝓝 1) :=
    log_cubicSubseq_div_cube_tendsto
  -- `log(log(cs)/m³) → log 1 = 0`.
  have hcontlog : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
  have hlog_ratio : Tendsto (fun m : ℕ =>
      Real.log (Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3)) atTop (𝓝 0) := by
    have := hcontlog.tendsto.comp hratio_to_one
    simpa [Real.log_one] using this
  -- Divide by `3 log m → ∞`.
  have h3logm_top : Tendsto (fun m : ℕ => 3 * Real.log (m : ℝ)) atTop atTop := by
    have := hlogm_top.atTop_mul_const (show (0 : ℝ) < 3 by norm_num)
    simpa [mul_comm] using this
  have hsmall : Tendsto (fun m : ℕ =>
      Real.log (Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3) / (3 * Real.log (m : ℝ)))
      atTop (𝓝 0) := by
    have := hlog_ratio.div_atTop h3logm_top
    simpa using this
  -- Now show ratio = 1 + small eventually.
  have hcube_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (m : ℝ) ^ 3 :=
    hcube_top.eventually_gt_atTop 0
  have hm_gt_one : ∀ᶠ m : ℕ in atTop, (1 : ℝ) < (m : ℝ) :=
    hnat_top.eventually_gt_atTop 1
  have hlogm_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < Real.log (m : ℝ) := by
    filter_upwards [hm_gt_one] with m hm
    exact Real.log_pos hm
  have hlogcs_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < Real.log (cubicSubseq m : ℝ) :=
    eventually_log_cubicSubseq_pos
  have hrewrite : ∀ᶠ m : ℕ in atTop,
      Real.log (Real.log (cubicSubseq m : ℝ)) / (3 * Real.log (m : ℝ)) =
        1 + Real.log (Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3) /
          (3 * Real.log (m : ℝ)) := by
    filter_upwards [hcube_pos, hlogm_pos, hlogcs_pos] with m hmcube hlogm hlogcs
    have hmcube_ne : ((m : ℝ) ^ 3) ≠ 0 := ne_of_gt hmcube
    have hlogm_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlogm
    have hlogcs_ne : Real.log (cubicSubseq m : ℝ) ≠ 0 := ne_of_gt hlogcs
    have h3logm_ne : (3 * Real.log (m : ℝ)) ≠ 0 := by positivity
    -- `log(cs) = m³ · (log(cs) / m³)`.
    have hsplit : Real.log (cubicSubseq m : ℝ) =
        (m : ℝ) ^ 3 * (Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3) := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hmcube_ne]
    -- Take log of both sides.
    have hfactor_pos : (0 : ℝ) < Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3 :=
      div_pos hlogcs hmcube
    have hstep1 : Real.log (Real.log (cubicSubseq m : ℝ)) =
        Real.log ((m : ℝ) ^ 3) + Real.log (Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3) := by
      conv_lhs => rw [hsplit]
      exact Real.log_mul hmcube_ne (ne_of_gt hfactor_pos)
    have hlog_pow : Real.log ((m : ℝ) ^ 3) = 3 * Real.log (m : ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    -- Now: target is `(3 log m + log(ratio)) / (3 log m) = 1 + log(ratio) / (3 log m)`.
    rw [hstep1, hlog_pow]
    rw [add_div, div_self h3logm_ne]
  -- Apply congr' + the fact that `1 + small → 1 + 0 = 1`.
  have hgoal : Tendsto (fun m : ℕ => (1 : ℝ) +
      Real.log (Real.log (cubicSubseq m : ℝ) / (m : ℝ) ^ 3) / (3 * Real.log (m : ℝ)))
      atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hsmall
  have hgoal' : Tendsto (fun m : ℕ =>
      Real.log (Real.log (cubicSubseq m : ℝ)) / (3 * Real.log (m : ℝ))) atTop (𝓝 (1 + 0)) :=
    hgoal.congr' (hrewrite.mono (fun m hm => hm.symm))
  simpa using hgoal'

/-- Asymptotically `log(cubicSubseq m) ≥ (m:ℝ)^3 / 2` for large `m`, hence for any
fixed `α > 1/3`, the reciprocal-power `(log n_m)^{-3α}` is `IsBigO` to `m^{-9α}`
which is summable since `9α > 3 > 1`.

Actually the cleaner form used by the consumer is: for any `β > 1/3`, the
sequence `m ↦ (log(cubicSubseq m))^{-β}` is summable. We prove that using
`log(cubicSubseq m) ≥ m^3/2`, so `(log(cubicSubseq m))^{-β} ≤ (m^3/2)^{-β}
= 2^β · m^{-3β}`, and `m^{-3β}` is summable iff `3β > 1` iff `β > 1/3`. -/
theorem cubic_subseq_log_power_summability {β : ℝ} (hβ : 1/3 < β) :
    Summable (fun m : ℕ => (Real.log (cubicSubseq m : ℝ)) ^ (-β)) := by
  -- Reduce to p-series summability for `m ↦ (m:ℝ)^(-3β)`.
  -- Step 1: p-series `Summable (fun m : ℕ => (m : ℝ)^(-3β))` since `3β > 1`.
  have h3β : (1 : ℝ) < 3 * β := by linarith
  have hneg3β_lt : (-(3 * β) : ℝ) < -1 := by linarith
  have hpseries : Summable (fun m : ℕ => (m : ℝ) ^ (-(3 * β))) := by
    rw [Real.summable_nat_rpow]; exact hneg3β_lt
  -- Step 2: eventually, `(log(cubicSubseq m))^{-β} ≤ 2^β · m^{-3β}`.
  -- Using `log(cs m) ≥ m³/2` and monotonicity of `x ↦ x^{-β}` on positives
  -- (equivalently, `x^{-β}` is decreasing for `β > 0`).
  have hβ_pos : 0 < β := by linarith
  have h_bound : ∀ᶠ m : ℕ in atTop,
      ‖(Real.log (cubicSubseq m : ℝ)) ^ (-β)‖ ≤
        Real.rpow 2 β * (m : ℝ) ^ (-(3 * β)) := by
    have hnat_top : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hm_pos : ∀ᶠ m : ℕ in atTop, (1 : ℝ) ≤ (m : ℝ) :=
      hnat_top.eventually_ge_atTop 1
    filter_upwards [log_cubicSubseq_ge_half_cube, eventually_log_cubicSubseq_pos, hm_pos]
      with m hhalf hlogcs_pos hm_pos
    -- `log(cs m) ≥ m^3/2 > 0` (since m ≥ 1 implies m^3 ≥ 1 > 0).
    have hm_cube_pos : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
    have hm_cube_half_pos : (0 : ℝ) < (m : ℝ) ^ 3 / 2 := by positivity
    -- `(log cs m)^{-β} ≤ (m³/2)^{-β}` since `x ↦ x^{-β}` is decreasing on
    -- positives for `β > 0`, AND log cs m ≥ m³/2 > 0.
    have hmono : (Real.log (cubicSubseq m : ℝ)) ^ (-β) ≤
        ((m : ℝ) ^ 3 / 2) ^ (-β) := by
      -- From m³/2 ≤ log cs m, get (m³/2)^(-β) ≥ (log cs m)^(-β).
      have hle : (m : ℝ) ^ 3 / 2 ≤ Real.log (cubicSubseq m : ℝ) := hhalf
      have hpow_mono : ((m : ℝ) ^ 3 / 2) ^ β ≤ (Real.log (cubicSubseq m : ℝ)) ^ β :=
        Real.rpow_le_rpow (le_of_lt hm_cube_half_pos) hle (le_of_lt hβ_pos)
      have hcube_β_pos : (0 : ℝ) < ((m : ℝ) ^ 3 / 2) ^ β :=
        Real.rpow_pos_of_pos hm_cube_half_pos β
      have hcs_neg : (Real.log (cubicSubseq m : ℝ)) ^ (-β) =
          ((Real.log (cubicSubseq m : ℝ)) ^ β)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hlogcs_pos)]
      have hcube_neg : ((m : ℝ) ^ 3 / 2) ^ (-β) = (((m : ℝ) ^ 3 / 2) ^ β)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hm_cube_half_pos)]
      rw [hcs_neg, hcube_neg]
      exact inv_anti₀ hcube_β_pos hpow_mono
    -- Now rewrite `(m³/2)^{-β}` as `2^β · m^{-3β}`.
    have hm_pos_real : (0 : ℝ) < (m : ℝ) := by linarith
    have hm_pos' : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hm_pos_real
    have hrewrite : ((m : ℝ) ^ 3 / 2) ^ (-β) = Real.rpow 2 β * (m : ℝ) ^ (-(3 * β)) := by
      -- (m³/2)^(-β) = m^(-3β) · 2^β, since x^(-β) = 1/x^β and (m³)^β = m^(3β).
      have hm3_pos : (0 : ℝ) < (m : ℝ)^3 := hm_cube_pos
      have h2_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
      have hdiv := Real.div_rpow (x := (m : ℝ)^3) (y := 2) hm3_pos.le h2_pos.le (-β)
      have hpow3_rpow : ((m : ℝ) ^ 3) ^ (-β) = (m : ℝ) ^ (-(3 * β)) := by
        rw [← Real.rpow_natCast (m : ℝ) 3, ← Real.rpow_mul hm_pos']
        congr 1; push_cast; ring
      rw [hdiv, hpow3_rpow]
      -- Goal: m^(-3β) / 2^(-β) = Real.rpow 2 β * m^(-3β). (and 2^(-β) = (2^β)⁻¹.)
      have h2neg : (2 : ℝ) ^ (-β) = ((2 : ℝ)^β)⁻¹ :=
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) β
      have hrpow_eq : Real.rpow 2 β = (2 : ℝ)^β := rfl
      rw [h2neg, hrpow_eq]
      have h2pow_pos : (0 : ℝ) < (2:ℝ)^β := Real.rpow_pos_of_pos (by norm_num) β
      field_simp
    -- `‖x^(-β)‖` for x ≥ 0 and (-β negative): x^(-β) = 1/x^β ≥ 0.
    have hcs_neg_nonneg : 0 ≤ (Real.log (cubicSubseq m : ℝ)) ^ (-β) :=
      Real.rpow_nonneg (le_of_lt hlogcs_pos) _
    rw [Real.norm_eq_abs, abs_of_nonneg hcs_neg_nonneg]
    calc (Real.log (cubicSubseq m : ℝ)) ^ (-β)
        ≤ ((m : ℝ) ^ 3 / 2) ^ (-β) := hmono
      _ = Real.rpow 2 β * (m : ℝ) ^ (-(3 * β)) := hrewrite
  -- Step 3: apply `Summable.of_norm_bounded_eventually_nat` with `g m = 2^β · m^(-3β)`.
  have hg_summable : Summable (fun m : ℕ => Real.rpow 2 β * (m : ℝ) ^ (-(3 * β))) :=
    hpseries.mul_left (Real.rpow 2 β)
  exact Summable.of_norm_bounded_eventually_nat hg_summable h_bound

/-- **Not-summability companion.** For `0 < β < 1/3`, the sequence
`m ↦ (log(cubicSubseq m))^{-β}` is **not** summable.

This is used in the lower-half (BC2) assembly of Chojecki's Theorem 18 to
ensure `Σ_m ℙ(E_m^★(q)) = ∞`: with `β := glw.lower · (α_- - q/2)^3 < 1/3`
(since `2 glw.lower ≤ glw.upper` makes `glw.lower/(2·glw.upper) ≤ 1/4`),
the block small-ball lower bound gives probabilities `≥ C · (log n_m)^{-β}`,
and non-summability of these provides the BC2 hypothesis.

*Proof.* Using `log(cubicSubseq m) ≤ m³` eventually, we get
`(log(cubicSubseq m))^{-β} ≥ (m³)^{-β} = m^{-3β}`. Since `3β < 1`,
`∑ m^{-3β}` diverges. If the target were summable, then by eventual
domination (via `Summable.of_norm_bounded_eventually_nat`) the p-series
`∑ m^{-3β}` would also be summable — contradiction. -/
theorem cubic_subseq_log_power_not_summable {β : ℝ} (hβ_pos : 0 < β) (hβ_lt : β < 1/3) :
    ¬ Summable (fun m : ℕ => (Real.log (cubicSubseq m : ℝ)) ^ (-β)) := by
  intro hsum
  -- The p-series `m ↦ m^(-3β)` is NOT summable when `3β ≤ 1`.
  have h3β_lt : 3 * β < 1 := by linarith
  have hpseries_not : ¬ Summable (fun m : ℕ => (m : ℝ) ^ (-(3 * β))) := by
    rw [Real.summable_nat_rpow]
    intro hlt; linarith
  -- Domination bound: eventually `(m : ℝ)^(-(3*β)) ≤ (log cs m)^(-β)`.
  have h_bound : ∀ᶠ m : ℕ in atTop,
      ‖(m : ℝ) ^ (-(3 * β))‖ ≤ (Real.log (cubicSubseq m : ℝ)) ^ (-β) := by
    have hnat_top : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hm_pos : ∀ᶠ m : ℕ in atTop, (1 : ℝ) ≤ (m : ℝ) :=
      hnat_top.eventually_ge_atTop 1
    filter_upwards [log_cubicSubseq_le_cube, eventually_log_cubicSubseq_pos, hm_pos]
      with m hle_cube hlog_pos hm_pos
    have hm_pos_real : (0 : ℝ) < (m : ℝ) := by linarith
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hm_pos_real
    have hm_cube_pos : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
    have hlogcs_nn : (0 : ℝ) ≤ Real.log (cubicSubseq m : ℝ) := le_of_lt hlog_pos
    have hpow_mono : (Real.log (cubicSubseq m : ℝ)) ^ β ≤ ((m : ℝ) ^ 3) ^ β :=
      Real.rpow_le_rpow hlogcs_nn hle_cube (le_of_lt hβ_pos)
    have hlog_β_pos : (0 : ℝ) < (Real.log (cubicSubseq m : ℝ)) ^ β :=
      Real.rpow_pos_of_pos hlog_pos β
    have hcube_β_pos : (0 : ℝ) < ((m : ℝ) ^ 3) ^ β :=
      Real.rpow_pos_of_pos hm_cube_pos β
    -- Reciprocals flip: 1/(m^3)^β ≤ 1/(log cs m)^β.
    have hinv_le : (((m : ℝ) ^ 3) ^ β)⁻¹ ≤ ((Real.log (cubicSubseq m : ℝ)) ^ β)⁻¹ := by
      exact one_div_le_one_div_of_le hlog_β_pos hpow_mono |>.trans_eq' (by rw [one_div]) |>.trans_eq (by rw [one_div])
    have hcs_neg : (Real.log (cubicSubseq m : ℝ)) ^ (-β) =
        ((Real.log (cubicSubseq m : ℝ)) ^ β)⁻¹ := by
      rw [Real.rpow_neg hlogcs_nn]
    have hcube_neg : ((m : ℝ) ^ 3) ^ (-β) = (((m : ℝ) ^ 3) ^ β)⁻¹ := by
      rw [Real.rpow_neg hm_cube_pos.le]
    have hcube_rpow : ((m : ℝ) ^ 3) ^ (-β) = (m : ℝ) ^ (-(3 * β)) := by
      rw [← Real.rpow_natCast (m : ℝ) 3, ← Real.rpow_mul hm_nn]
      congr 1; push_cast; ring
    have hmain : (m : ℝ) ^ (-(3 * β)) ≤ (Real.log (cubicSubseq m : ℝ)) ^ (-β) := by
      rw [hcs_neg, ← hcube_rpow, hcube_neg]
      exact hinv_le
    have hlhs_nn : (0 : ℝ) ≤ (m : ℝ) ^ (-(3 * β)) :=
      Real.rpow_nonneg hm_nn _
    rw [Real.norm_eq_abs, abs_of_nonneg hlhs_nn]
    exact hmain
  -- If the target is summable, then by domination so is `m ↦ m^(-3β)`.
  have hpseries_sum : Summable (fun m : ℕ => (m : ℝ) ^ (-(3 * β))) :=
    Summable.of_norm_bounded_eventually_nat hsum h_bound
  exact hpseries_not hpseries_sum

/-- KMT error is negligible at the `(log log n_m)^{1/3}` scale.

The KMT coupling error for the cubic subsequence is `Δ_{n_m} = O(log n_m / √n_m)`.
We show `log(log n_m / √n_m) / (log log n_m)^{1/3} → -∞`.

Proof sketch. `log(log n_m / √n_m) = log log n_m - (1/2) log n_m`. Using
`log n_m ≥ m³/2` and `log log n_m ≤ log(m³) = 3 log m ≤ m`, the numerator is
eventually `≤ -m³/8`, while the denominator `(log log n_m)^{1/3} ≤ m`. So the
ratio is `≤ -m²/8 → -∞`. -/
theorem kmt_error_negligible_at_loglog_cube_root :
    Filter.Tendsto (fun m : ℕ =>
        Real.log (Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m)) /
          (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3))
      atTop atBot := by
  -- Strategy: for large m, log cs m ≥ m³/2, sqrt cs m ≥ sqrt(exp(m³)-1) close to
  -- exp(m³/2). So log(log cs m / sqrt cs m) ≤ log(m³) - log sqrt cs m
  -- ≤ 3 log m - m³/4 (say). And (log log cs m)^{1/3} ≤ (m³)^{1/3} = m (crude).
  -- So ratio ≤ (3 log m - m³/4)/m → -∞.
  -- Provide a tendsto with a dominating upper bound that tends to -∞.
  have hnat_top : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcube_top : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop :=
    (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat_top
  -- UPPER BOUND: crude but effective. We show the quantity is eventually
  -- ≤ (3 log m - m³/4) / 1 when the denominator is ≥ 1, and → -∞.
  -- Actually simpler: show the numerator is eventually ≤ -m³/8 and the
  -- denominator is eventually ≤ m (say), so ratio ≤ -m²/8 → -∞.
  --
  -- Numerator upper bound:
  --   log(log cs m / sqrt cs m) = log log cs m - log(sqrt cs m)
  --                              = log log cs m - (1/2) log cs m
  --   ≤ log(m³) - (1/2)(m³/2) = 3 log m - m³/4.
  -- For large m, m³/4 ≥ 3 log m + m³/8, so this ≤ -m³/8.
  --
  -- Denominator upper bound:
  --   (log log cs m)^{1/3} ≤ (m³)^{1/3} = m (using log log cs m ≤ log(m³) = 3 log m ≤ m
  --   for m large). But (log log cs m) might be smaller than m even. Safely bound by any
  --   eventually bounded above quantity that's positive.
  --
  -- So numerator/denominator ≤ -m³/8 / m = -m²/8 → -∞. ✓
  apply Filter.tendsto_atBot_mono'
  show ∀ᶠ m : ℕ in atTop,
      Real.log (Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m)) /
          (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤
        -(m : ℝ)^2 / 8
  · -- Eventual bound: ratio ≤ -m²/8.
    -- We need: numerator ≤ -m²/8 · denominator, with denominator ≥ 0, and numerator ≤ 0.
    have hm_large : ∀ᶠ m : ℕ in atTop, (1024 : ℝ) ≤ (m : ℝ) :=
      hnat_top.eventually_ge_atTop 1024
    have hcs_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (cubicSubseq m : ℝ) :=
      eventually_cubicSubseq_pos
    have hlogcs_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < Real.log (cubicSubseq m : ℝ) :=
      eventually_log_cubicSubseq_pos
    have hloglogcs_pos : ∀ᶠ m : ℕ in atTop,
        (0 : ℝ) < Real.log (Real.log (cubicSubseq m : ℝ)) := by
      -- log log cs m > 0 iff log cs m > 1. For m ≥ 2, m³ ≥ 8 so m³/2 ≥ 4, and
      -- log cs m ≥ m³/2 ≥ 4 > 1.
      filter_upwards [log_cubicSubseq_ge_half_cube,
        hnat_top.eventually_ge_atTop 2] with m hhalf hm
      have hm_cube_ge : (4 : ℝ) ≤ (m : ℝ) ^ 3 / 2 := by nlinarith [sq_nonneg ((m:ℝ) - 2), hm]
      have hlogcs_gt_1 : (1 : ℝ) < Real.log (cubicSubseq m : ℝ) := by linarith
      exact Real.log_pos hlogcs_gt_1
    filter_upwards [hm_large, hcs_pos, hlogcs_pos, hloglogcs_pos,
      log_cubicSubseq_ge_half_cube, log_cubicSubseq_le_cube] with
      m hm hcs hlogcs hlloglogcs hhalf hle
    -- m ≥ 1024, so m ≥ 1 and m³ ≥ 1024³ very large.
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
    have hm_ge_1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
    have hm_cube_pos : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
    have hm_sq_pos : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
    have hm_cube : (m : ℝ) ^ 3 / 2 ≤ Real.log (cubicSubseq m : ℝ) := hhalf
    have hlogcs_le : Real.log (cubicSubseq m : ℝ) ≤ (m : ℝ) ^ 3 := hle
    -- sqrt cs m > 0.
    have hsqrt_pos : (0 : ℝ) < Real.sqrt (cubicSubseq m : ℝ) :=
      Real.sqrt_pos.mpr hcs
    -- log sqrt cs m = (1/2) log cs m.
    have hlog_sqrt : Real.log (Real.sqrt (cubicSubseq m : ℝ)) =
        (1/2) * Real.log (cubicSubseq m : ℝ) := by
      rw [Real.log_sqrt hcs.le]; ring
    -- ratio = log log cs m - (1/2) log cs m.
    have hfrac_pos : (0 : ℝ) < Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m : ℝ) :=
      div_pos hlogcs hsqrt_pos
    have hnumsplit : Real.log (Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m : ℝ)) =
        Real.log (Real.log (cubicSubseq m : ℝ)) - (1/2) * Real.log (cubicSubseq m : ℝ) := by
      rw [Real.log_div hlogcs.ne' hsqrt_pos.ne', hlog_sqrt]
    -- Upper bound for numerator: log log cs m ≤ log(m³) = 3 log m (since log cs m ≤ m³).
    have hloglog_le : Real.log (Real.log (cubicSubseq m : ℝ)) ≤ 3 * Real.log (m : ℝ) := by
      have hle : Real.log (Real.log (cubicSubseq m : ℝ)) ≤ Real.log ((m : ℝ) ^ 3) :=
        Real.log_le_log hlogcs hlogcs_le
      have heq : Real.log ((m : ℝ) ^ 3) = 3 * Real.log (m : ℝ) := by
        rw [Real.log_pow]; push_cast; ring
      linarith
    -- Lower bound for (1/2) log cs m: ≥ (1/2)(m³/2) = m³/4.
    have hhalflog : (m : ℝ) ^ 3 / 4 ≤ (1/2) * Real.log (cubicSubseq m : ℝ) := by
      have : (1/2) * ((m : ℝ) ^ 3 / 2) ≤ (1/2) * Real.log (cubicSubseq m : ℝ) := by
        have hhalf_pos : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
        exact mul_le_mul_of_nonneg_left hm_cube hhalf_pos.le
      linarith
    -- Numerator ≤ 3 log m - m³/4.
    have hnum_bound : Real.log (Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m : ℝ)) ≤
        3 * Real.log (m : ℝ) - (m : ℝ) ^ 3 / 4 := by
      rw [hnumsplit]; linarith
    -- Crude: log m ≤ m. (for m ≥ 1)
    have hlogm_le_m : Real.log (m : ℝ) ≤ (m : ℝ) :=
      (Real.log_le_sub_one_of_pos hm_pos).trans (by linarith)
    -- So 3 log m ≤ 3m, and 3 log m - m³/4 ≤ 3m - m³/4.
    -- For m ≥ 1024, m³/4 ≥ 256 m³ >> 3m + m²·(m/8) roughly.
    -- We want numerator ≤ -m²/8 · denominator with denominator ≤ m (say).
    -- A cleaner bound: we show numerator ≤ -m³/8 and denominator ≤ m.
    -- Claim: 3 log m - m³/4 ≤ -m³/8, i.e., 3 log m ≤ m³/8.
    -- For m ≥ 1024 (say), m³/8 ≥ 1024³/8 = 128·1024² = enormous, and 3 log m small.
    -- More precisely: m³/8 ≥ 3m (since m² ≥ 24 for m ≥ 5) ≥ 3 log m.
    have h3log_le_mcube_over_8 : 3 * Real.log (m : ℝ) ≤ (m : ℝ) ^ 3 / 8 := by
      have h3logm_le_3m : 3 * Real.log (m : ℝ) ≤ 3 * (m : ℝ) := by linarith
      -- 3m ≤ m³/8 iff 24 ≤ m², which holds for m ≥ 5 (since 25 ≥ 24).
      have hm2_ge : (24 : ℝ) ≤ (m : ℝ)^2 := by nlinarith [hm]
      have h3m_le : 3 * (m : ℝ) ≤ (m : ℝ)^3 / 8 := by nlinarith [hm, hm2_ge]
      linarith
    have hnum_ultimate : Real.log (Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m : ℝ)) ≤
        -((m : ℝ) ^ 3 / 8) := by
      calc Real.log (Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m : ℝ))
          ≤ 3 * Real.log (m : ℝ) - (m : ℝ) ^ 3 / 4 := hnum_bound
        _ ≤ (m : ℝ) ^ 3 / 8 - (m : ℝ) ^ 3 / 4 := by linarith
        _ = -((m : ℝ) ^ 3 / 8) := by ring
    -- Denominator upper bound: (log log cs m)^{1/3} ≤ (3 log m)^{1/3} ≤ (3m)^{1/3} ≤ m (for m ≥ 3).
    -- Actually cleaner: use (log log cs m)^{1/3} ≤ m (for large m).
    have hloglog_nonneg : (0 : ℝ) ≤ Real.log (Real.log (cubicSubseq m : ℝ)) := hlloglogcs.le
    have hdenom_le : (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤ (m : ℝ) := by
      -- (x)^{1/3} ≤ m iff x ≤ m^3 (both sides nonneg).
      have hx_le : Real.log (Real.log (cubicSubseq m : ℝ)) ≤ (m : ℝ) ^ 3 := by
        linarith [hloglog_le, hlogm_le_m, (mul_le_mul_of_nonneg_left hlogm_le_m (by norm_num : (0:ℝ) ≤ 3))]
      -- rpow monotone on ≥ 0.
      have h13nn : (0 : ℝ) ≤ (1 : ℝ) / 3 := by norm_num
      have hstep := Real.rpow_le_rpow hloglog_nonneg hx_le h13nn
      have hmcubepow : ((m : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (m : ℝ) := by
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hm_pos
        rw [← Real.rpow_natCast (m : ℝ) 3, ← Real.rpow_mul hmnn]
        have : (3 : ℕ) * ((1 : ℝ) / 3) = 1 := by push_cast; ring
        rw [this, Real.rpow_one]
      rw [hmcubepow] at hstep
      exact hstep
    have hdenom_nonneg : (0 : ℝ) ≤ (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg hloglog_nonneg _
    -- Denominator positive:
    have hdenom_pos : (0 : ℝ) < (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hlloglogcs _
    -- Combine: ratio = num/denom ≤ -m³/8 / denom.
    -- And -m³/8/denom ≤ -m²/8 iff -m³/8 ≤ -m² denom/8 iff m³/8 ≥ m² denom/8
    -- iff m ≥ denom, which holds. Since denom > 0, divide both sides.
    have hratio_le : Real.log (Real.log (cubicSubseq m : ℝ) / Real.sqrt (cubicSubseq m)) /
        (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤
        -((m : ℝ) ^ 3 / 8) / (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) :=
      div_le_div_of_nonneg_right hnum_ultimate hdenom_pos.le
    -- -m³/8/denom ≤ -m²/8 when denom ≤ m.
    -- -m³/8/denom = -(m³/8)/denom. For denom ≤ m and positive:
    -- (m³/8)/denom ≥ (m³/8)/m = m²/8, so -(m³/8)/denom ≤ -m²/8.
    have hineq : -((m : ℝ) ^ 3 / 8) /
        (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤ -(m : ℝ)^2 / 8 := by
      have hm3_nn : (0 : ℝ) ≤ (m : ℝ) ^ 3 / 8 := by positivity
      have hdenom_le_m : (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤ (m : ℝ) :=
        hdenom_le
      -- (m³/8)/denom ≥ (m³/8)/m = m²/8
      have hstep := div_le_div_of_nonneg_left hm3_nn hdenom_pos hdenom_le_m
      -- hstep: (m³/8) / m ≤ (m³/8) / denom
      have hsimp : (m : ℝ)^3 / 8 / (m : ℝ) = (m : ℝ)^2 / 8 := by
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
        field_simp
      rw [hsimp] at hstep
      -- hstep: m²/8 ≤ (m³/8)/denom. Taking negatives:
      have hneg_eq : -((m : ℝ)^3 / 8) /
          (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) =
          -((m : ℝ)^3 / 8 / (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) := by
        ring
      rw [hneg_eq]
      linarith
    linarith
  · -- -m²/8 → -∞.
    have hm_sq_top : Tendsto (fun m : ℕ => (m : ℝ)^2) atTop atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp hnat_top
    have hneg : Tendsto (fun m : ℕ => -((m : ℝ)^2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hm_sq_top
    have := hneg.atBot_div_const (by norm_num : (0 : ℝ) < 8)
    simpa [neg_div] using this

/-- `log log(cubicSubseq m) ≥ log m` eventually. -/
theorem loglog_cubicSubseq_ge_log :
    ∀ᶠ m : ℕ in atTop, Real.log (Real.log (cubicSubseq m : ℝ)) ≥ Real.log (m : ℝ) := by
  -- Strategy: eventually `log(cubicSubseq m) ≥ m³/2`, so
  -- `log log(cubicSubseq m) ≥ log(m³/2) = 3 log m - log 2 ≥ log m` when `2 log m ≥ log 2`, i.e. `m ≥ √2`.
  have hnat_top : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm_ge : ∀ᶠ m : ℕ in atTop, Real.log 2 / 2 ≤ Real.log (m : ℝ) := by
    have hlogm_top : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hnat_top
    exact hlogm_top.eventually_ge_atTop _
  have hcube_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (m : ℝ) ^ 3 := by
    have hcube_top : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop :=
      (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat_top
    exact hcube_top.eventually_gt_atTop 0
  have hm_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (m : ℝ) :=
    hnat_top.eventually_gt_atTop 0
  filter_upwards [log_cubicSubseq_ge_half_cube, hm_ge, hcube_pos, hm_pos, eventually_log_cubicSubseq_pos]
    with m hhalf hlogm_ge hmcube hm_pos hlogcs_pos
  -- `log(cubicSubseq m) ≥ m³/2 > 0`.
  have hmcube_half_pos : (0 : ℝ) < (m : ℝ) ^ 3 / 2 := by linarith
  -- So `log log(cubicSubseq m) ≥ log(m³/2)`.
  have hlog_mono : Real.log ((m : ℝ) ^ 3 / 2) ≤ Real.log (Real.log (cubicSubseq m : ℝ)) :=
    Real.log_le_log hmcube_half_pos hhalf
  -- `log(m³/2) = 3 log m - log 2`.
  have hlog_split : Real.log ((m : ℝ) ^ 3 / 2) = 3 * Real.log (m : ℝ) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num : (2 : ℝ) ≠ 0), Real.log_pow]
    push_cast; ring
  -- Need `3 log m - log 2 ≥ log m`, i.e. `2 log m ≥ log 2`, i.e. `log m ≥ log 2 / 2`.
  have : Real.log (m : ℝ) ≤ 3 * Real.log (m : ℝ) - Real.log 2 := by linarith
  linarith [hlog_mono, hlog_split.symm ▸ this]

/-- `log(n+1)/√n → 0` as `n → ∞`. This is the KMT-error growth rate from
`two_dim_KMT_coupling`, used in `polynomial_sup_small_ball_upper/_lower` to
pin the KMT-absorption threshold `N₀`.

Strategy. For `n ≥ 4` we have `log(n+1) ≤ log(2n) = log 2 + log n`, and
`log n ≤ 2 · √n − 2` (a standard calculus bound; or simpler, use
`Real.add_pow_le_pow_mul_pow_of_sq`-style comparisons). So
`log(n+1)/√n ≤ (log 2 + 2√n − 2)/√n = (log 2 − 2)/√n + 2 → 2`. That's
bounded, not → 0. For the → 0 conclusion we use the more refined
inequality `Real.log x ≤ 2 * Real.sqrt x` for `x ≥ 1`: applied at
`x = n+1`, we get `log(n+1) ≤ 2 √(n+1)`, and the ratio √(n+1)/√n → 1,
so `log(n+1)/√n ≤ 2 · √(n+1)/√n → 2` is still bounded.

The correct asymptotic `log x / √x → 0` as `x → ∞` comes from
`Real.isLittleO_log_rpow_atTop` with exponent `1/2`, which says
`log x = o(x^{1/2}) = o(√x)`. -/
theorem log_succ_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / Real.sqrt n)
      atTop (nhds 0) := by
  -- Pass through `(log x / √x) ∘ (x ↦ x + 1)` and bound the ratio.
  -- Key fact: `Real.log x = o[atTop] Real.sqrt x`.
  have hnat_top : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  -- Use `Real.log_isLittleO_rpow` with exponent `(1/2)`: `log x =o x^(1/2)`,
  -- and `x^(1/2) = √x` for `x ≥ 0`.
  have h_log_io_sqrt :
      Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    -- `Real.isLittleO_log_rpow_atTop (1/2) : log =o[atTop] fun x => x^(1/2)`.
    -- `IsLittleO.tendsto_div_nhds_zero` gives `log x / x^(1/2) → 0`.
    have h_io : Real.log =o[atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
      _root_.isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    have h_rpow : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ))
        atTop (nhds 0) := h_io.tendsto_div_nhds_zero
    -- `x^(1/2) = √x` for `x ≥ 0`.
    have hev : ∀ᶠ x : ℝ in atTop,
        Real.log x / x ^ (1 / 2 : ℝ) = Real.log x / Real.sqrt x := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      rw [Real.sqrt_eq_rpow]
    exact h_rpow.congr' hev
  -- Now pass `n ↦ n + 1`. First show `log((n:ℝ)+1) / √((n:ℝ)+1) → 0`.
  have hsucc_top : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    have := hnat_top
    exact this.atTop_add tendsto_const_nhds
  have h_succ :
      Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1))
        atTop (nhds 0) := h_log_io_sqrt.comp hsucc_top
  -- Second, `√((n:ℝ)+1) / √n ≤ √2` eventually.
  have h_ratio_bd :
      ∀ᶠ n : ℕ in atTop, Real.sqrt ((n : ℝ) + 1) / Real.sqrt n ≤ 2 := by
    filter_upwards [hnat_top.eventually_ge_atTop (1 : ℝ)] with n hn
    have hn_pos : (0 : ℝ) < n := by linarith
    have hsqn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    rw [div_le_iff₀ hsqn_pos]
    -- √(n+1) ≤ √(2n) = √2 · √n ≤ 2·√n (since √2 ≤ 2).
    have h1 : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (2 * n) := by
      apply Real.sqrt_le_sqrt; linarith
    have h2 : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt n :=
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
    have h3 : Real.sqrt 2 ≤ 2 := by
      have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    calc Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt n := by rw [← h2]; exact h1
      _ ≤ 2 * Real.sqrt n :=
        mul_le_mul_of_nonneg_right h3 hsqn_pos.le
  -- Third, pointwise identity `log(n+1)/√n = (log(n+1)/√(n+1)) · (√(n+1)/√n)`.
  have h_factor :
      ∀ᶠ n : ℕ in atTop,
        Real.log ((n : ℝ) + 1) / Real.sqrt n =
          (Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)) *
            (Real.sqrt ((n : ℝ) + 1) / Real.sqrt n) := by
    filter_upwards [hnat_top.eventually_ge_atTop (1 : ℝ)] with n hn
    have hn_pos : (0 : ℝ) < n := by linarith
    have hsucc_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hsqn_ne : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn_pos)
    have hssn_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hsucc_pos)
    field_simp
  -- Final squeeze.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : ∀ᶠ n : ℕ in atTop,
      dist (Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)) 0 < ε / 2 :=
    Metric.tendsto_nhds.mp h_succ (ε / 2) (by linarith)
  filter_upwards [hhalf, h_factor, h_ratio_bd,
      hnat_top.eventually_ge_atTop (1 : ℝ)]
    with n hclose heq hratio _hn_ge
  rw [dist_zero_right] at hclose ⊢
  rw [heq]
  have hratio_nn : 0 ≤ Real.sqrt ((n : ℝ) + 1) / Real.sqrt n :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hprod_norm :
      ‖(Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)) *
        (Real.sqrt ((n : ℝ) + 1) / Real.sqrt n)‖
      = ‖Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)‖ *
          ‖Real.sqrt ((n : ℝ) + 1) / Real.sqrt n‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  have habs_ratio : ‖Real.sqrt ((n : ℝ) + 1) / Real.sqrt n‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hratio_nn]; exact hratio
  rw [hprod_norm]
  -- A * C < ε where A < ε/2 (hclose), C ≤ 2 (habs_ratio), A, C ≥ 0.
  -- Case split on C = 0 or C > 0. If C = 0, product is 0 < ε.
  -- If C > 0, then A*C < (ε/2)*C ≤ (ε/2)*2 = ε (strict via A < ε/2).
  set A := ‖Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)‖
  set C := ‖Real.sqrt ((n : ℝ) + 1) / Real.sqrt n‖
  have hA_nn : 0 ≤ A := norm_nonneg _
  have hC_nn : 0 ≤ C := norm_nonneg _
  rcases eq_or_lt_of_le hC_nn with hC0 | hC_pos
  · -- C = 0: A * C = 0 < ε.
    rw [← hC0, mul_zero]; linarith
  · -- C > 0: strict mul.
    have hAC : A * C < (ε / 2) * 2 :=
      mul_lt_mul hclose habs_ratio hC_pos (by linarith)
    linarith

/-- Auxiliary. For `m ≥ 1`, `(m - 1 : ℕ)` as a real equals `(m : ℝ) - 1`. -/
private lemma natCast_sub_one_of_pos {m : ℕ} (hm : 1 ≤ m) :
    ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
  have h := Nat.cast_sub (R := ℝ) hm
  simpa using h

/-- `(m - 1 : ℕ) ^ 3 ≤ m³` as a real, for any `m`. -/
private lemma cube_pred_le_cube (m : ℕ) :
    (((m - 1 : ℕ) : ℝ)) ^ 3 ≤ (m : ℝ) ^ 3 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · rw [natCast_sub_one_of_pos hm]
    have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hm_le : (m : ℝ) - 1 ≤ (m : ℝ) := by linarith
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact pow_le_pow_left₀ hm1 hm_le 3

set_option maxHeartbeats 800000 in
/-- **Helper for Erdős 524 upper half, Step H5 ("old blocks negligible").**

The ratio of prior-block sqrt-size to current-block sqrt-size, times the
log-log correction, decays super-exponentially.

Specifically, as `m → ∞`,
`√(n_{m-1}) · √(log log n_{m-1}) / (exp(-α · (log log n_m)^{1/3}) · √(n_m))
 → 0`,
where `n_m := cubicSubseq m = ⌊exp(m³)⌋`. This is consumed by
`old_blocks_negligible` to dominate the "old block" (indices `≤ n_{m-1}`)
by a constant multiple of the small-ball scale
`ε_m · √(n_m) := exp(-α (log log n_m)^{1/3}) · √(n_m)`.

*Proof.* Reduce to showing the log of the expression tends to `-∞`.
Concretely:
* `log √(n_{m-1}) ≤ (m-1)³/2` (since `n_{m-1} ≤ exp((m-1)³)`).
* `log √(n_m) ≥ (m³ - 1)/2` eventually, via `n_m ≥ exp(m³)/2` and
  `log(exp(m³)/2) = m³ - log 2 ≥ m³ - 1`.
* `log √(log log n_{m-1}) ≤ log(3m)/2` (eventually, using the crude bound
  `log log n_m ≤ 3m`).
* `α · (log log n_m)^{1/3} ≤ |α| · m` (eventually).

Putting these together, the log of the expression is eventually at most
`(m-1)³/2 + log(3m)/2 + |α|·m - (m³ - 1)/2 = -3m²/2 + O(m) + O(log m) → -∞`. -/
theorem cubicSubseq_sqrt_ratio_decay (α : ℝ) :
    Filter.Tendsto
      (fun m : ℕ =>
        Real.sqrt (cubicSubseq (m - 1)) * Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1))))
          / (Real.exp (-α * (Real.log (Real.log (cubicSubseq m))) ^ ((1:ℝ)/3))
              * Real.sqrt (cubicSubseq m)))
      Filter.atTop (𝓝 0) := by
  -- Strategy. Take the log of the LHS expression and show it tends to -∞.
  -- Then `exp ∘ log = id` on positives gives tendsto (LHS) → 0 via
  -- `Real.tendsto_exp_atBot`.
  --
  -- Set
  --   N m := √(cs (m-1)) · √(log log cs (m-1))  (eventually positive)
  --   D m := exp(-α · (log log cs m)^{1/3}) · √(cs m)   (eventually positive)
  -- Then log(N/D) = (1/2) log cs (m-1) + (1/2) log log log cs (m-1)
  --                 + α (log log cs m)^{1/3} - (1/2) log cs m.
  -- Bounding each term in terms of m, we get log(N/D) ≤ -m eventually,
  -- so N/D ≤ exp(-m) → 0.
  have hnat_top : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcube_top : Tendsto (fun m : ℕ => ((m : ℝ) ^ 3)) atTop atTop :=
    (tendsto_pow_atTop (n := 3) (by norm_num)).comp hnat_top
  -- Tendsto of m-1 to atTop.
  have hpred_top : Tendsto (fun m : ℕ => m - 1) atTop atTop :=
    Filter.tendsto_sub_atTop_nat 1
  -- Goal reformulation: ratio ≤ exp(-m) eventually.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnat_top)) ?hlb ?hub
  · -- Lower bound: 0 ≤ LHS.
    filter_upwards with m
    -- Exp and sqrt are nonneg; the quotient has nonneg numerator and positive
    -- denominator (exp positive, sqrt nonneg). Result nonneg by `div_nonneg`.
    have hexp_pos :
        0 < Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) :=
      Real.exp_pos _
    have hsm_nn : 0 ≤ Real.sqrt (cubicSubseq m : ℝ) := Real.sqrt_nonneg _
    have hnum_nn : 0 ≤ Real.sqrt (cubicSubseq (m - 1) : ℝ) *
        Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact div_nonneg hnum_nn (mul_nonneg hexp_pos.le hsm_nn)
  · -- Upper bound: LHS ≤ exp(-m) eventually.
    -- Collect all eventual ingredients.
    have hm_nat_ge2 : ∀ᶠ m : ℕ in atTop, 2 ≤ m := Filter.eventually_ge_atTop 2
    have hm_ge2 : ∀ᶠ m : ℕ in atTop, (2 : ℝ) ≤ (m : ℝ) :=
      hnat_top.eventually_ge_atTop 2
    -- Need m ≥ some big constant C(α). Precise threshold: we need
    --   3m²/2 ≥ m + 3m/2 + |α|·m + (1/2) log(3m) + (log 2)/2 + 1/2 + log(m)/2 + ...
    -- A crude threshold m ≥ 8 + 4|α| + 20 will suffice (nlinarith will close).
    have hm_big : ∀ᶠ m : ℕ in atTop, (30 : ℝ) + 4 * |α| ≤ (m : ℝ) := by
      have : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := hnat_top
      exact this.eventually_ge_atTop _
    -- cs m positive and > 1 for m large, so log cs m > 0 and log log cs m > 0.
    have hcs_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (cubicSubseq m : ℝ) :=
      eventually_cubicSubseq_pos
    have hlogcs_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < Real.log (cubicSubseq m : ℝ) :=
      eventually_log_cubicSubseq_pos
    have hloglogcs_pos : ∀ᶠ m : ℕ in atTop,
        (0 : ℝ) < Real.log (Real.log (cubicSubseq m : ℝ)) := by
      filter_upwards [log_cubicSubseq_ge_half_cube, hm_ge2] with m hhalf hm
      have hm_cube_ge : (4 : ℝ) ≤ (m : ℝ) ^ 3 / 2 := by nlinarith [sq_nonneg ((m:ℝ) - 2), hm]
      have hlogcs_gt_1 : (1 : ℝ) < Real.log (cubicSubseq m : ℝ) := by linarith
      exact Real.log_pos hlogcs_gt_1
    have hlog_le : ∀ᶠ m : ℕ in atTop, Real.log (cubicSubseq m : ℝ) ≤ (m : ℝ) ^ 3 :=
      log_cubicSubseq_le_cube
    have hlog_ge : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ 3 / 2 ≤ Real.log (cubicSubseq m : ℝ) :=
      log_cubicSubseq_ge_half_cube
    -- Shifted to m-1: we need eventual positivity of cs (m-1), log cs (m-1), log log cs (m-1).
    have hcs_pm1_pos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (cubicSubseq (m - 1) : ℝ) :=
      hpred_top.eventually eventually_cubicSubseq_pos
    have hlogcs_pm1_pos :
        ∀ᶠ m : ℕ in atTop, (0 : ℝ) < Real.log (cubicSubseq (m - 1) : ℝ) :=
      hpred_top.eventually eventually_log_cubicSubseq_pos
    have hloglogcs_pm1_pos : ∀ᶠ m : ℕ in atTop,
        (0 : ℝ) < Real.log (Real.log (cubicSubseq (m - 1) : ℝ)) := by
      have h_src : ∀ᶠ k : ℕ in atTop,
          (0 : ℝ) < Real.log (Real.log (cubicSubseq k : ℝ)) := by
        filter_upwards [log_cubicSubseq_ge_half_cube, hnat_top.eventually_ge_atTop 2]
          with k hhalf hk
        have hk_cube_ge : (4 : ℝ) ≤ (k : ℝ) ^ 3 / 2 := by nlinarith [sq_nonneg ((k:ℝ) - 2), hk]
        exact Real.log_pos (by linarith)
      exact hpred_top.eventually h_src
    -- `(m-1 : ℕ)^3 ≤ m^3` as a real (via `cube_pred_le_cube`).
    have hlog_pm1_le : ∀ᶠ m : ℕ in atTop,
        Real.log (cubicSubseq (m - 1) : ℝ) ≤ (m : ℝ) ^ 3 := by
      filter_upwards [hpred_top.eventually log_cubicSubseq_le_cube] with m hm
      exact hm.trans (cube_pred_le_cube m)
    -- Upper bound on (1/2) log cs (m-1): ≤ m³/2 (since log cs (m-1) ≤ m³).
    -- Lower bound on (1/2) log cs m: ≥ m³/4.
    -- Upper bound on (log log cs m)^{1/3}: ≤ m (eventually).
    have hdenom_le_m : ∀ᶠ m : ℕ in atTop,
        (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤ (m : ℝ) := by
      filter_upwards [hloglogcs_pos, hlogcs_pos, hlog_le, hm_ge2] with
        m hllcs hlcs hle_m3 hm
      have hloglog_le : Real.log (Real.log (cubicSubseq m : ℝ)) ≤ 3 * Real.log (m : ℝ) := by
        have hle : Real.log (Real.log (cubicSubseq m : ℝ)) ≤ Real.log ((m : ℝ) ^ 3) :=
          Real.log_le_log hlcs hle_m3
        have heq : Real.log ((m : ℝ) ^ 3) = 3 * Real.log (m : ℝ) := by
          rw [Real.log_pow]; push_cast; ring
        linarith
      have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
      have hlogm_le_m : Real.log (m : ℝ) ≤ (m : ℝ) :=
        (Real.log_le_sub_one_of_pos hm_pos).trans (by linarith)
      have hx_le : Real.log (Real.log (cubicSubseq m : ℝ)) ≤ (m : ℝ) ^ 3 := by
        have h1 : 3 * Real.log (m : ℝ) ≤ 3 * (m : ℝ) := by linarith
        have hksq : (3 : ℝ) ≤ (m : ℝ)^2 := by nlinarith [hm]
        have hmulstep := mul_le_mul_of_nonneg_left hksq hm_pos.le
        have h2 : 3 * (m : ℝ) ≤ (m : ℝ) ^ 3 := by nlinarith [hmulstep, hm]
        linarith
      have hloglog_nn : (0 : ℝ) ≤ Real.log (Real.log (cubicSubseq m : ℝ)) := hllcs.le
      have h13nn : (0 : ℝ) ≤ (1 : ℝ) / 3 := by norm_num
      have hstep := Real.rpow_le_rpow hloglog_nn hx_le h13nn
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := hm_pos.le
      have hmcubepow : ((m : ℝ) ^ 3) ^ ((1 : ℝ) / 3) = (m : ℝ) := by
        rw [← Real.rpow_natCast (m : ℝ) 3, ← Real.rpow_mul hmnn]
        have : (3 : ℕ) * ((1 : ℝ) / 3) = 1 := by push_cast; ring
        rw [this, Real.rpow_one]
      rw [hmcubepow] at hstep
      exact hstep
    -- log log cs (m-1) ≤ m³ eventually (reuse chain).
    have hloglog_pm1_le : ∀ᶠ m : ℕ in atTop,
        Real.log (Real.log (cubicSubseq (m - 1) : ℝ)) ≤ (m : ℝ) ^ 3 := by
      have h_src : ∀ᶠ k : ℕ in atTop,
          Real.log (Real.log (cubicSubseq k : ℝ)) ≤ (k : ℝ) ^ 3 := by
        filter_upwards [eventually_log_cubicSubseq_pos, log_cubicSubseq_le_cube,
          hnat_top.eventually_ge_atTop 2] with k hlcs hle_k3 hk
        have hloglog_le : Real.log (Real.log (cubicSubseq k : ℝ)) ≤ 3 * Real.log (k : ℝ) := by
          have hle : Real.log (Real.log (cubicSubseq k : ℝ)) ≤ Real.log ((k : ℝ) ^ 3) :=
            Real.log_le_log hlcs hle_k3
          have heq : Real.log ((k : ℝ) ^ 3) = 3 * Real.log (k : ℝ) := by
            rw [Real.log_pow]; push_cast; ring
          linarith
        have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
        have hlogk_le_k : Real.log (k : ℝ) ≤ (k : ℝ) :=
          (Real.log_le_sub_one_of_pos hk_pos).trans (by linarith)
        have h3k : 3 * (k : ℝ) ≤ (k : ℝ) ^ 3 := by
          have hksq : (3 : ℝ) ≤ (k : ℝ)^2 := by nlinarith [hk]
          have := mul_le_mul_of_nonneg_left hksq (by linarith : (0 : ℝ) ≤ (k : ℝ))
          nlinarith [this, hk]
        linarith
      filter_upwards [hpred_top.eventually h_src] with m hm
      exact hm.trans (cube_pred_le_cube m)
    -- Main argument.
    filter_upwards [hm_big, hm_nat_ge2, hcs_pos, hlogcs_pos, hloglogcs_pos,
      hlog_le, hlog_ge, hcs_pm1_pos, hlogcs_pm1_pos, hloglogcs_pm1_pos, hlog_pm1_le,
      hdenom_le_m, hloglog_pm1_le] with
      m hmbig hmn hcs hlcs hllcs hle_m3 hge_m3 hcs_pm1 hlcs_pm1 hllcs_pm1 hlog_pm1
      hdenbd hll_pm1_bd
    -- Basic positivities.
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith [abs_nonneg α]
    have hsqrt_m_pos : 0 < Real.sqrt (cubicSubseq m : ℝ) := Real.sqrt_pos.mpr hcs
    have hsqrt_pm1_nn : 0 ≤ Real.sqrt (cubicSubseq (m-1) : ℝ) := Real.sqrt_nonneg _
    have hsqrt_pm1_pos : 0 < Real.sqrt (cubicSubseq (m-1) : ℝ) := Real.sqrt_pos.mpr hcs_pm1
    have hllogsqrt_pos : 0 < Real.sqrt (Real.log (Real.log (cubicSubseq (m-1) : ℝ))) :=
      Real.sqrt_pos.mpr hllcs_pm1
    have hexp_pos :
        0 < Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) :=
      Real.exp_pos _
    have hnum_pos : 0 < Real.sqrt (cubicSubseq (m-1) : ℝ) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m-1) : ℝ))) :=
      mul_pos hsqrt_pm1_pos hllogsqrt_pos
    have hdenom_pos :
        0 < Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3))
              * Real.sqrt (cubicSubseq m : ℝ) :=
      mul_pos hexp_pos hsqrt_m_pos
    -- Take log of the ratio.
    set f : ℝ := Real.sqrt (cubicSubseq (m - 1) : ℝ) *
        Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) /
        (Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) *
          Real.sqrt (cubicSubseq m : ℝ)) with hf_def
    have hf_pos : 0 < f := div_pos hnum_pos hdenom_pos
    -- It suffices to show log f ≤ -m (since exp is monotone).
    suffices hlog_f : Real.log f ≤ -(m : ℝ) by
      have hstep : Real.log f ≤ Real.log (Real.exp (-(m : ℝ))) := by
        rw [Real.log_exp]; exact hlog_f
      have := (Real.log_le_log_iff hf_pos (Real.exp_pos _)).mp hstep
      exact this
    -- Compute log f = log_num - log_denom.
    have hlog_f_eq : Real.log f =
        Real.log (Real.sqrt (cubicSubseq (m - 1) : ℝ) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) -
        Real.log (Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) *
          Real.sqrt (cubicSubseq m : ℝ)) := by
      rw [hf_def, Real.log_div hnum_pos.ne' hdenom_pos.ne']
    -- Unfold log of each product.
    have hlog_num : Real.log (Real.sqrt (cubicSubseq (m - 1) : ℝ) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) =
        Real.log (Real.sqrt (cubicSubseq (m - 1) : ℝ)) +
        Real.log (Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) :=
      Real.log_mul hsqrt_pm1_pos.ne' hllogsqrt_pos.ne'
    have hlog_denom : Real.log
          (Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) *
          Real.sqrt (cubicSubseq m : ℝ)) =
        (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) +
        Real.log (Real.sqrt (cubicSubseq m : ℝ)) := by
      rw [Real.log_mul (ne_of_gt hexp_pos) hsqrt_m_pos.ne', Real.log_exp]
    -- log √x = (1/2) log x.
    have hlog_sqrt_cs_pm1 : Real.log (Real.sqrt (cubicSubseq (m - 1) : ℝ)) =
        (1/2) * Real.log (cubicSubseq (m - 1) : ℝ) := by
      rw [Real.log_sqrt hcs_pm1.le]; ring
    have hlog_sqrt_cs_m : Real.log (Real.sqrt (cubicSubseq m : ℝ)) =
        (1/2) * Real.log (cubicSubseq m : ℝ) := by
      rw [Real.log_sqrt hcs.le]; ring
    have hlog_sqrt_ll_pm1 :
        Real.log (Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) =
        (1/2) * Real.log (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) := by
      rw [Real.log_sqrt hllcs_pm1.le]; ring
    -- Assemble:
    --   log f = (1/2) log cs (m-1) + (1/2) log log log cs (m-1)
    --           + α (log log cs m)^{1/3} - (1/2) log cs m.
    -- Bounds we'll apply:
    --   (1/2) log cs (m-1) ≤ (1/2) · m³      (from hlog_pm1)
    --   -(1/2) log cs m ≤ -(1/2) · m³/2 = -m³/4   (from hge_m3)
    --   α (log log cs m)^{1/3} ≤ α · m ≤ |α| · m  (from hdenbd, if α ≥ 0)
    --                     or ≤ 0 + something (if α < 0, the term is nonpositive
    --                     but we bound it by 0 ≤ |α| · m).
    --   (1/2) log log log cs (m-1): log log cs (m-1) ≤ m³, so
    --     log log log cs (m-1) ≤ log m³ = 3 log m ≤ 3m, giving ≤ 3m/2.
    -- Total: ≤ m³/2 - m³/4 + |α| m + 3m/2 = m³/4 + |α| m + 3m/2.
    -- That's POSITIVE for large m! My bound is too weak.
    --
    -- FIX: Need tighter bound on log cs (m-1).
    -- Use: cs (m-1) ≤ exp((m-1)³), so log cs (m-1) ≤ (m-1)³.
    -- Then (1/2) log cs (m-1) ≤ (m-1)³/2.
    -- (1/2) log cs (m-1) - (1/2) log cs m ≤ (m-1)³/2 - m³/4.
    -- (m-1)³/2 - m³/4: for m large, (m-1)³ ≈ m³, so (m-1)³/2 - m³/4 ≈ m³/4 > 0.
    -- Still not working with log cs m ≥ m³/2.
    --
    -- NEED: log cs m ≥ m³ - 1 (or m³ - log 2), using n_m ≥ exp(m³) - 1 ≥ exp(m³ - 1).
    -- Actually easier: log cs m ≥ m³ - log 2 (since cs m ≥ exp(m³)/2, so log cs m ≥ m³ - log 2).
    -- Then -(1/2) log cs m ≤ -(m³ - log 2)/2 = -m³/2 + (log 2)/2.
    -- So total log f ≤ (m-1)³/2 + |α| m + 3m/2 - m³/2 + (log 2)/2
    --               = (m-1)³/2 - m³/2 + |α| m + 3m/2 + (log 2)/2
    --               = -3m²/2 + 3m/2 - 1/2 + |α| m + 3m/2 + (log 2)/2
    --               = -3m²/2 + 3m + |α| m - 1/2 + (log 2)/2
    --               ≤ -3m²/2 + (3 + |α|) m + 1/2
    --               ≤ -m    (for 3m²/2 ≥ (3 + |α| + 1) m + 1/2,
    --                         i.e., m ≥ (2(4 + |α|) + 1) / 3 ≈ 3 + 2|α|/3 + ε).
    -- Our threshold m ≥ 30 + 4|α| comfortably handles this.
    --
    -- Replace hge_m3 with a tighter lower bound: log cs m ≥ m³ - log 2 (for m ≥ 2).
    have hlog_ge_tight : (m : ℝ) ^ 3 - Real.log 2 ≤ Real.log (cubicSubseq m : ℝ) := by
      -- cs m ≥ exp(m³)/2, so log cs m ≥ log(exp(m³)/2) = m³ - log 2.
      have hm_ge2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn
      have hm3_ge : (8 : ℝ) ≤ (m : ℝ)^3 := by
        have h2sq : (4 : ℝ) ≤ (m : ℝ)^2 := by nlinarith [hm_ge2r]
        have : (m : ℝ)^2 * 2 ≤ (m : ℝ)^2 * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hm_ge2r (by positivity)
        nlinarith [h2sq, this, hm_ge2r]
      have hexp_ge_two : (2 : ℝ) ≤ Real.exp ((m : ℝ)^3) := by
        have : Real.exp 1 ≤ Real.exp ((m : ℝ)^3) :=
          Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_d9])
        linarith [Real.exp_one_gt_d9]
      have hcs_ge_halfexp : Real.exp ((m : ℝ)^3) / 2 ≤ (cubicSubseq m : ℝ) := by
        have hgt := cubicSubseq_gt_exp_sub_one m
        linarith
      have hhalfexp_pos : 0 < Real.exp ((m : ℝ)^3) / 2 := by positivity
      have := Real.log_le_log hhalfexp_pos hcs_ge_halfexp
      have hrw : Real.log (Real.exp ((m : ℝ)^3) / 2) = (m : ℝ)^3 - Real.log 2 := by
        rw [Real.log_div (Real.exp_pos _).ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp]
      linarith [hrw.symm ▸ this]
    -- Upper bound on (1/2) log cs (m-1).
    have hlog_pm1_strict : Real.log (cubicSubseq (m - 1) : ℝ) ≤ ((m - 1 : ℕ) : ℝ)^3 := by
      -- n_{m-1} ≤ exp((m-1)³), so log n_{m-1} ≤ (m-1)³.
      have h := cubicSubseq_le_exp (m - 1)
      have := Real.log_le_log hcs_pm1 h
      rwa [Real.log_exp] at this
    -- (m-1 : ℕ) as real equals m - 1 (since m ≥ 2 ≥ 1).
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := natCast_sub_one_of_pos (by linarith)
    have hlog_pm1_real : Real.log (cubicSubseq (m - 1) : ℝ) ≤ ((m : ℝ) - 1)^3 := by
      rw [← hcast]; exact hlog_pm1_strict
    -- α · (log log cs m)^{1/3} ≤ |α| · m, since (log log cs m)^{1/3} ≥ 0 and ≤ m.
    have hα_bd : α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤ |α| * (m : ℝ) := by
      -- α · t ≤ |α| · t when t ≥ 0 (since α ≤ |α|). Then |α| · t ≤ |α| · m since t ≤ m.
      have ht_nn : 0 ≤ (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) :=
        Real.rpow_nonneg hllcs.le _
      have hα_le_abs : α ≤ |α| := le_abs_self α
      have habs_nn : 0 ≤ |α| := abs_nonneg α
      have h1 : α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤
          |α| * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hα_le_abs ht_nn
      have h2 : |α| * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3) ≤ |α| * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hdenbd habs_nn
      linarith
    -- Assemble log f ≤ -m.
    -- log f = (1/2) log cs (m-1) + (1/2) log log log cs (m-1)
    --         - (-α) ... wait: log f = log_num - log_denom, and log_denom has the α term
    --         NEGATED in the additive sense (since log_denom = (-α ·...) + log √cs m, and
    --         log_num - log_denom subtracts that).
    -- Rewrite explicitly:
    have hlog_f_explicit :
        Real.log f = (1/2) * Real.log (cubicSubseq (m - 1) : ℝ) +
          (1/2) * Real.log (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) -
          ((-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1 : ℝ) / 3)) +
            (1/2) * Real.log (cubicSubseq m : ℝ)) := by
      rw [hlog_f_eq, hlog_num, hlog_denom, hlog_sqrt_cs_pm1, hlog_sqrt_ll_pm1, hlog_sqrt_cs_m]
    rw [hlog_f_explicit]
    -- Apply bounds.
    -- (1/2) log cs (m-1) ≤ (1/2)(m-1)^3.
    have h1 : (1/2) * Real.log (cubicSubseq (m - 1) : ℝ) ≤ (1/2) * ((m : ℝ) - 1)^3 := by
      have := hlog_pm1_real
      linarith
    -- (1/2) log log log cs (m-1) ≤ (3/2) m.
    have h2 : (1/2) * Real.log (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) ≤
        (3/2) * (m : ℝ) := by
      -- log log log cs (m-1) ≤ log(3m). But we have log log cs (m-1) ≤ m³, so
      -- log log log cs (m-1) ≤ log(m³) = 3 log m ≤ 3m.
      have hloglog_pos : 0 < Real.log (Real.log (cubicSubseq (m - 1) : ℝ)) := hllcs_pm1
      -- Need log log log cs (m-1) to be well-defined: need log log cs (m-1) > 0.
      have hll_pos : 0 < Real.log (Real.log (cubicSubseq (m - 1) : ℝ)) := hllcs_pm1
      have hlll_le : Real.log (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) ≤
          Real.log ((m : ℝ)^3) := Real.log_le_log hll_pos hll_pm1_bd
      have heq : Real.log ((m : ℝ) ^ 3) = 3 * Real.log (m : ℝ) := by
        rw [Real.log_pow]; push_cast; ring
      have hlogm_le_m : Real.log (m : ℝ) ≤ (m : ℝ) :=
        (Real.log_le_sub_one_of_pos hm_pos).trans (by linarith)
      linarith
    -- -(1/2) log cs m ≤ -(1/2)(m³ - log 2) = -m³/2 + (log 2)/2 ≤ -m³/2 + 1.
    have h3 : -((1/2) * Real.log (cubicSubseq m : ℝ)) ≤ -((1/2) * ((m : ℝ)^3 - Real.log 2)) := by
      have := hlog_ge_tight
      linarith
    have hlog2_le_one : Real.log 2 ≤ 1 := by
      have h1 : Real.log 2 ≤ 2 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    -- Target: assemble and show ≤ -m.
    -- LHS = (1/2) log cs (m-1) + (1/2) log log log cs(m-1) + α·t - (1/2) log cs m
    --     ≤ (1/2)(m-1)³ + (3/2)m + |α|·m - (1/2)(m³ - log 2)
    --     = (1/2)[(m-1)³ - m³] + (3/2)m + |α|·m + (log 2)/2
    -- Expand (m-1)³ - m³ = -3m² + 3m - 1:
    --     = (1/2)(-3m² + 3m - 1) + (3/2)m + |α|·m + (log 2)/2
    --     = -3m²/2 + 3m/2 - 1/2 + 3m/2 + |α|·m + (log 2)/2
    --     = -3m²/2 + 3m + |α|·m + (log 2)/2 - 1/2
    --     ≤ -3m²/2 + (3 + |α|) m            (since (log 2)/2 ≤ 1/2)
    -- For m ≥ 30 + 4|α|: need 3m²/2 + (-m) ≥ (3 + |α|) m, i.e., 3m²/2 ≥ (4 + |α|) m.
    -- For m ≥ 30 + 4|α| ≥ 4 + |α| (since |α| ≥ 0), 3m/2 ≥ 3(30+4|α|)/2 = 45 + 6|α| ≥ 4 + |α|,
    -- so 3m²/2 = m · (3m/2) ≥ m · (4 + |α|), giving the bound.
    have habs_nn : 0 ≤ |α| := abs_nonneg α
    -- Explicit expansion of (m-1)³ = m³ - 3m² + 3m - 1.
    have hexp : ((m : ℝ) - 1)^3 = (m : ℝ)^3 - 3*(m : ℝ)^2 + 3*(m : ℝ) - 1 := by ring
    -- h1': (1/2) log cs (m-1) ≤ (1/2) (m³ - 3m² + 3m - 1).
    have h1' : (1/2) * Real.log (cubicSubseq (m - 1) : ℝ) ≤
        (1/2) * ((m : ℝ)^3 - 3*(m : ℝ)^2 + 3*(m : ℝ) - 1) := by
      rw [← hexp]; exact h1
    -- Key inequality: 3m²/2 ≥ (4 + |α|)·m, for m ≥ 30 + 4|α|.
    have hkey : (4 + |α|) * (m : ℝ) ≤ 3 * (m : ℝ)^2 / 2 := by
      -- From m ≥ 30 + 4|α|, we have 3m ≥ 90 + 12|α| ≥ 2(4 + |α|), so 3m/2 ≥ 4 + |α|.
      have h_bound : 2 * (4 + |α|) ≤ 3 * (m : ℝ) := by linarith
      have h_pos : (0 : ℝ) < 2 := by norm_num
      have hkey0 : 2 * ((4 + |α|) * (m : ℝ)) ≤ 3 * (m : ℝ) * (m : ℝ) := by
        have := mul_le_mul_of_nonneg_right h_bound hm_pos.le
        nlinarith [this]
      nlinarith [hkey0]
    linarith [h1', h2, h3, hα_bd, habs_nn, hlog2_le_one, hkey]
