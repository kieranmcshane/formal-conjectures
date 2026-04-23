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

end Erdos524.Helpers
