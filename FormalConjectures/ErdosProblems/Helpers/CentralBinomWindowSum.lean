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

import FormalConjectures.ErdosProblems.Helpers.CentralBinomLower

/-!
# Central-binomial tail-sum lower bound at the LIL scale
(helper for Erdős problem 524)
-/

namespace Erdos524
namespace Helpers

/-- Pure algebraic core. By keeping `u = √(2s)` as a hypothesis, the body is
a polynomial inequality and closes with `nlinarith`. -/
theorem margin_absorbs_sqrt_core (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (s : ℝ) (hs : 10000 / δ ^ 2 ≤ s)
    (u : ℝ) (hu : 0 ≤ u) (hu_sq : u ^ 2 = 2 * s) :
    (2 + δ / 4) * u + 3 * (2 + δ / 4) ≤ (δ - (δ / 8) * (1 - δ) ^ 2) * s := by
  have hδ2_pos : 0 < δ ^ 2 := by positivity
  have hs_pos : 0 < s := by
    have h1 : 0 < 10000 / δ ^ 2 := by positivity
    linarith
  -- Show u ≥ 100/δ using u² = 2s ≥ 20000/δ² = 2·(100/δ)²
  have h100δ_pos : 0 < 100 / δ := by positivity
  have h100δ_nn : 0 ≤ 100 / δ := h100δ_pos.le
  have hu_sq_bd : (100 / δ) ^ 2 ≤ u ^ 2 := by
    have h1 : (100 / δ) ^ 2 = 10000 / δ ^ 2 := by field_simp; ring
    rw [h1, hu_sq]; linarith
  have hu_large : 100 / δ ≤ u := by
    by_contra hlt
    push_neg at hlt
    have : u ^ 2 < (100 / δ) ^ 2 := by nlinarith [hu, h100δ_pos]
    linarith
  -- Margin: δ − (δ/8)(1-δ)² ≥ 7δ/8
  have h_margin : 7 * δ / 8 ≤ δ - (δ / 8) * (1 - δ) ^ 2 := by
    have hsub : (1 - δ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [hsub]
  -- Reduce to: (7δ/8)·s ≥ (2+δ/4)·u + 3(2+δ/4)
  suffices h : (2 + δ / 4) * u + 3 * (2 + δ / 4) ≤ 7 * δ / 8 * s by
    have hbump : 7 * δ / 8 * s ≤ (δ - δ / 8 * (1 - δ) ^ 2) * s :=
      mul_le_mul_of_nonneg_right h_margin hs_pos.le
    linarith
  -- Via u² = 2s, s = u²/2, so (7δ/8)·s = (7δ/16)·u²
  -- We use u ≥ 100/δ to get u² ≥ u · (100/δ), hence (7δ/16)·u² ≥ (700/16)·u = 43.75u
  -- RHS ≤ 3·u + 9 (since 2+δ/4 ≤ 3 for δ ≤ 4)
  have hCoeff_le : 2 + δ / 4 ≤ 3 := by linarith
  have hCoeff_pos : 0 < 2 + δ / 4 := by linarith
  -- (2+δ/4)·u ≤ 3·u
  have hRHS1 : (2 + δ / 4) * u ≤ 3 * u := by nlinarith [hu]
  have hRHS2 : 3 * (2 + δ / 4) ≤ 9 := by linarith
  have hRHS_bd : (2 + δ / 4) * u + 3 * (2 + δ / 4) ≤ 3 * u + 9 := by linarith
  -- LHS: (7δ/8)·s = (7δ/16)·u² ≥ (7δ/16)·u·(100/δ) = 700·u/16 = 43.75·u
  have hu_nn_u : u * (100 / δ) ≤ u ^ 2 := by
    have := mul_le_mul_of_nonneg_left hu_large hu
    nlinarith [this]
  have hLHS_step : 7 * δ / 8 * s = 7 * δ / 16 * u ^ 2 := by
    have hs_eq : s = u ^ 2 / 2 := by linarith
    rw [hs_eq]; ring
  -- (7δ/16)·u² ≥ (7δ/16)·u·(100/δ)
  have hδ_pos_16 : 0 < 7 * δ / 16 := by positivity
  have hLHS_bd : 7 * δ / 16 * (u * (100 / δ)) ≤ 7 * δ / 16 * u ^ 2 :=
    mul_le_mul_of_nonneg_left hu_nn_u hδ_pos_16.le
  have hsimp : 7 * δ / 16 * (u * (100 / δ)) = 700 / 16 * u := by field_simp; ring
  -- Need: 3u + 9 ≤ 700/16 · u, i.e., (700/16 - 3) u = (652/16) u ≥ 9
  -- Since u ≥ 100/δ ≥ 100 (as δ ≤ 1), u ≥ 100, so (652/16)·100 = 4075 ≥ 9. ✓
  have hu_big : u ≥ 100 := by
    have h100 : 100 ≤ 100 / δ := by
      rw [le_div_iff₀ hδ]; linarith
    linarith
  have h_final : 3 * u + 9 ≤ 700 / 16 * u := by nlinarith [hu_big]
  linarith [hLHS_step, hLHS_bd, hsimp, h_final, hRHS_bd]

/-- Scaled version of `margin_absorbs_sqrt_core`: absorbs `(4+δ/2)·u + 7`
by doubling the threshold. -/
theorem margin_absorbs_sqrt_core_scaled (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (s : ℝ) (hs : 40000 / δ ^ 2 ≤ s)
    (u : ℝ) (hu : 0 ≤ u) (hu_sq : u ^ 2 = 2 * s) :
    (4 + δ / 2) * u + 7 ≤ (δ - (δ / 8) * (1 - δ) ^ 2) * s := by
  -- Set s' := s/2, u' := u/√2. But simpler: rescale s to s/2 and u to u/√2.
  -- Even simpler: work directly. Show u ≥ 200/δ.
  have hδ2_pos : 0 < δ ^ 2 := by positivity
  have hs_pos : 0 < s := by
    have h1 : 0 < 40000 / δ ^ 2 := by positivity
    linarith
  have h200δ_pos : 0 < 200 / δ := by positivity
  have hu_sq_bd : (200 / δ) ^ 2 ≤ u ^ 2 := by
    have h1 : (200 / δ) ^ 2 = 40000 / δ ^ 2 := by field_simp; ring
    rw [h1, hu_sq]; linarith
  have hu_large : 200 / δ ≤ u := by
    by_contra hlt
    push_neg at hlt
    have : u ^ 2 < (200 / δ) ^ 2 := by nlinarith [hu, h200δ_pos]
    linarith
  have h_margin : 7 * δ / 8 ≤ δ - (δ / 8) * (1 - δ) ^ 2 := by
    have hsub : (1 - δ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [hsub]
  suffices h : (4 + δ / 2) * u + 7 ≤ 7 * δ / 8 * s by
    have hbump : 7 * δ / 8 * s ≤ (δ - δ / 8 * (1 - δ) ^ 2) * s :=
      mul_le_mul_of_nonneg_right h_margin hs_pos.le
    linarith
  have hu_nn_u : u * (200 / δ) ≤ u ^ 2 := by
    have := mul_le_mul_of_nonneg_left hu_large hu
    nlinarith [this]
  have hLHS_step : 7 * δ / 8 * s = 7 * δ / 16 * u ^ 2 := by
    have hs_eq : s = u ^ 2 / 2 := by linarith
    rw [hs_eq]; ring
  have hδ_pos_16 : 0 < 7 * δ / 16 := by positivity
  have hLHS_bd : 7 * δ / 16 * (u * (200 / δ)) ≤ 7 * δ / 16 * u ^ 2 :=
    mul_le_mul_of_nonneg_left hu_nn_u hδ_pos_16.le
  have hsimp : 7 * δ / 16 * (u * (200 / δ)) = 1400 / 16 * u := by field_simp; ring
  have hu_big : u ≥ 200 := by
    have h200 : 200 ≤ 200 / δ := by
      rw [le_div_iff₀ hδ]; linarith
    linarith
  have hCoeff_le : 4 + δ / 2 ≤ 5 := by linarith
  have hRHS1 : (4 + δ / 2) * u ≤ 5 * u := by nlinarith [hu]
  -- Need: 5u + 7 ≤ (1400/16) · u = 87.5 · u, i.e., 7 ≤ 82.5 u. Since u ≥ 200, 82.5·200 ≥ 7. ✓
  have h_final : 5 * u + 7 ≤ 1400 / 16 * u := by nlinarith [hu_big]
  linarith [hLHS_step, hLHS_bd, hsimp, h_final, hRHS1]

/-- The exponent bound for the LIL lower-tail window.

Takes a pre-split bound expressed purely in terms of `u = √(2L)` and `v = √n`.
This avoids `Real.sqrt (2*n*L)` issues by letting the caller do the sqrt
product expansion once. -/
theorem exponent_window_bound_uv (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (n : ℝ) (hn : 16 ≤ n) (L : ℝ) (hL : 40000 / δ ^ 2 ≤ L)
    (M : ℝ) (v : ℝ) (hv_sq : v ^ 2 = n) (_hv_nn : 0 ≤ v) (hv_ge : 4 ≤ v)
    (u : ℝ) (hu_sq : u ^ 2 = 2 * L) (hu_nn : 0 ≤ u)
    (hM_bd : M ^ 2 ≤ (1 - δ) ^ 2 * n * L / 2 +
              (1 - δ) * (u * v) * (v + 2) +
              (v + 2) ^ 2) :
    (2 + δ / 4) * M ^ 2 / n ≤ ((1 - δ) ^ 2 + δ) * L := by
  have hδ2_pos : 0 < δ ^ 2 := by positivity
  have hL_pos : 0 < L := by
    have h1 : 0 < 40000 / δ ^ 2 := by positivity
    linarith
  have hn_pos : 0 < n := by linarith
  have h1δ_nn : 0 ≤ 1 - δ := by linarith
  -- Bound each term of M² directly (without dividing by n yet).
  -- term1: (1-δ)²·n·L/2
  -- term2: (1-δ)·u·v·(v+2) = (1-δ)·u·v² + 2·(1-δ)·u·v = (1-δ)·u·n + 2·(1-δ)·u·v
  -- term3: (v+2)² = v² + 4v + 4 = n + 4v + 4
  have hterm2_expand : (1 - δ) * (u * v) * (v + 2) = (1 - δ) * u * n + 2 * (1 - δ) * u * v := by
    have : (1 - δ) * (u * v) * (v + 2) = (1 - δ) * u * (v * v) + 2 * (1 - δ) * u * v := by ring
    rw [this]
    have hvv : v * v = n := by rw [← sq]; exact hv_sq
    rw [hvv]
  have hterm3_expand : (v + 2) ^ 2 = n + 4 * v + 4 := by
    have : (v + 2) ^ 2 = v ^ 2 + 4 * v + 4 := by ring
    rw [this, hv_sq]
  have hM_bd2 : M ^ 2 ≤ (1 - δ) ^ 2 * n * L / 2 +
      ((1 - δ) * u * n + 2 * (1 - δ) * u * v) + (n + 4 * v + 4) := by
    rw [← hterm2_expand, ← hterm3_expand]; exact hM_bd
  -- Now bound 2·(1-δ)·u·v ≤ (1-δ)·u·n/4 using v = sqrt n, so v ≤ n/4 (since v ≥ 4 means v² = n ≥ 4v)
  -- Actually simpler: 2·(1-δ)·u·v + 4v + 4 ≤ c·n for some c. But we want the final form.
  -- Cleaner: divide by n at the end. M²/n ≤ (1-δ)²·L/2 + (1-δ)·u + 2·(1-δ)·u·v/n + 1 + 4v/n + 4/n.
  -- v/n = v/v² = 1/v, 4v/n = 4/v, 4/n = 4/v². For v ≥ 4: 2u·v/n = 2u/v ≤ u/2.
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hv_pos : 0 < v := by linarith
  have hv_ne : v ≠ 0 := hv_pos.ne'
  -- n / v = v, n / v² = 1 (since v² = n)
  have hnv : n / v = v := by
    rw [div_eq_iff hv_ne, ← sq, hv_sq]
  have hnv2 : n / v ^ 2 = 1 := by
    rw [hv_sq]; exact div_self hn_ne
  -- Write M² / n ≤ bounded form via: multiply up by n and use hM_bd2.
  -- Key insight: (1-δ)·u·n/n = (1-δ)·u;
  --             2(1-δ)u·v/n = 2(1-δ)u · v/n = 2(1-δ)u · (1/v);
  --             n/n = 1; 4v/n = 4/v; 4/n = 4/v²
  have hMsq_div : M ^ 2 / n ≤ (1 - δ) ^ 2 * L / 2 + (1 - δ) * u +
      2 * (1 - δ) * u / v + 1 + 4 / v + 4 / v ^ 2 := by
    have hbase : M ^ 2 / n ≤ ((1 - δ) ^ 2 * n * L / 2 +
        ((1 - δ) * u * n + 2 * (1 - δ) * u * v) + (n + 4 * v + 4)) / n := by
      exact div_le_div_of_nonneg_right hM_bd2 hn_pos.le |>.trans (le_refl _) |>.trans (le_refl _)
    have hsplit : ((1 - δ) ^ 2 * n * L / 2 +
        ((1 - δ) * u * n + 2 * (1 - δ) * u * v) + (n + 4 * v + 4)) / n
        = (1 - δ) ^ 2 * L / 2 + (1 - δ) * u + 2 * (1 - δ) * u * v / n + 1
          + 4 * v / n + 4 / n := by
      field_simp
      ring
    have hv_over_n : v / n = 1 / v := by
      rw [div_eq_div_iff hn_ne hv_ne, one_mul, ← sq, hv_sq]
    have hv_rewrite : 2 * (1 - δ) * u * v / n = 2 * (1 - δ) * u / v := by
      rw [show 2 * (1 - δ) * u * v / n = 2 * (1 - δ) * u * (v / n) from by ring]
      rw [hv_over_n]; ring
    have h4v : 4 * v / n = 4 / v := by
      rw [show 4 * v / n = 4 * (v / n) from by ring]
      rw [hv_over_n]; ring
    have h4n : (4 : ℝ) / n = 4 / v ^ 2 := by rw [hv_sq]
    calc M ^ 2 / n ≤ _ := hbase
      _ = _ := hsplit
      _ = _ := by rw [hv_rewrite, h4v, h4n]
  -- Now bound the small terms: 2·(1-δ)·u/v + 1 + 4/v + 4/v² ≤ (1-δ)·u/2 + 3
  -- Since v ≥ 4: u/v ≤ u/4, so 2(1-δ)u/v ≤ (1-δ)u/2.
  -- 1 + 4/v + 4/v² ≤ 1 + 1 + 1 = 3 (since v ≥ 4 gives 4/v ≤ 1 and 4/v² ≤ 1/4 ≤ 1)
  have h4_v : 4 / v ≤ 1 := by
    rw [div_le_iff₀ hv_pos]; linarith
  have h4_v2 : 4 / v ^ 2 ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < v^2)]
    have : v ^ 2 ≥ 16 := by nlinarith [hv_ge]
    linarith
  have hu_v : u / v ≤ u / 4 := by
    apply div_le_div_of_nonneg_left hu_nn (by norm_num : (0:ℝ) < 4) hv_ge
  have h2smallu : 2 * (1 - δ) * u / v ≤ (1 - δ) * u / 2 := by
    have h1 : 2 * (1 - δ) * u / v = 2 * (1 - δ) * (u / v) := by ring
    rw [h1]
    have : 2 * (1 - δ) * (u / v) ≤ 2 * (1 - δ) * (u / 4) := by
      apply mul_le_mul_of_nonneg_left hu_v
      nlinarith [h1δ_nn]
    linarith [this]
  -- Combine: M²/n ≤ (1-δ)²·L/2 + (1-δ)·u + (1-δ)·u/2 + 3
  --               = (1-δ)²·L/2 + (3/2)·(1-δ)·u + 3
  have hMsq_div' : M ^ 2 / n ≤ (1 - δ) ^ 2 * L / 2 + (3 / 2) * (1 - δ) * u + 3 := by
    have : (1 - δ) * u + (1 - δ) * u / 2 = (3 / 2) * (1 - δ) * u := by ring
    linarith [hMsq_div, h2smallu, h4_v, h4_v2]
  have hCoeff_pos : 0 < 2 + δ / 4 := by linarith
  have hCoeff_nn : 0 ≤ 2 + δ / 4 := hCoeff_pos.le
  -- (2+δ/4) · M²/n ≤ (2+δ/4) · [(1-δ)²·L/2 + (3/2)·(1-δ)·u + 3]
  have hprod_le : (2 + δ / 4) * (M ^ 2 / n) ≤
      (2 + δ / 4) * ((1 - δ) ^ 2 * L / 2 + (3 / 2) * (1 - δ) * u + 3) :=
    mul_le_mul_of_nonneg_left hMsq_div' hCoeff_nn
  -- Expand: = (1+δ/8)(1-δ)²·L + (3+3δ/8)(1-δ)·u + 3(2+δ/4)
  have hexpand : (2 + δ / 4) * ((1 - δ) ^ 2 * L / 2 + (3 / 2) * (1 - δ) * u + 3) =
      (1 + δ / 8) * (1 - δ) ^ 2 * L + (3 + 3 * δ / 8) * (1 - δ) * u + 3 * (2 + δ / 4) := by
    ring
  have heq : (2 + δ / 4) * M ^ 2 / n = (2 + δ / 4) * (M ^ 2 / n) := by ring
  -- (3 + 3δ/8)·(1-δ) ≤ (4 + δ/2) since (3+3δ/8)(1-δ) = 3 - 3δ + 3δ/8 - 3δ²/8 ≤ 3 ≤ 4+δ/2.
  have hCoeff_u : (3 + 3 * δ / 8) * (1 - δ) * u ≤ (4 + δ / 2) * u := by
    have : (3 + 3 * δ / 8) * (1 - δ) ≤ 4 + δ / 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hu_nn
  have h3coeff_le_7 : 3 * (2 + δ / 4) ≤ 7 := by linarith
  -- Combine:
  have hMul' : (2 + δ / 4) * M ^ 2 / n ≤
      (1 + δ / 8) * (1 - δ) ^ 2 * L + (4 + δ / 2) * u + 7 := by
    linarith [hprod_le, hexpand, heq, hCoeff_u, h3coeff_le_7]
  -- Apply scaled core:
  have habs := margin_absorbs_sqrt_core_scaled δ hδ hδ1 L hL u hu_nn hu_sq
  have hident : (1 + δ / 8) * (1 - δ) ^ 2 * L + (δ - (δ / 8) * (1 - δ) ^ 2) * L =
      ((1 - δ) ^ 2 + δ) * L := by ring
  linarith [hMul', habs, hident]

/-! ## Existential LIL-scale window-sum lower bound -/

/-- A concrete numerical threshold: for `n ≥ M_of δ`, we have
`log log n ≥ 40000/δ²`, `n ≥ 256`, and `n` is so astronomically large that all
lower-order terms are dominated. -/
private noncomputable def M_of (δ : ℝ) : ℕ :=
  Nat.ceil (Real.exp (Real.exp (40000 / δ ^ 2))) + 256

/-- The window width: `⌊√n⌋`. -/
private noncomputable def W_of (n : ℕ) : ℕ := Nat.floor (Real.sqrt (n : ℝ))

/-- The window left endpoint. -/
private noncomputable def kStar_of (δ : ℝ) (n : ℕ) : ℕ :=
  n / 2 + Nat.ceil ((1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) / 2) + 2

private lemma exp_one_ge : Real.exp 1 ≥ (2.7 : ℝ) := by
  have := Real.exp_one_gt_d9
  linarith

private lemma exp5_ge_100 : Real.exp 5 ≥ (100 : ℝ) := by
  have h : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 : Real.exp 1 ^ 5 ≥ (2.7 : ℝ) ^ 5 := by
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) exp_one_ge 5
  have h2 : (2.7 : ℝ) ^ 5 ≥ 100 := by norm_num
  linarith

private lemma exp10_ge_16 : Real.exp 10 ≥ (16 : ℝ) := by
  have h1 : Real.exp 10 ≥ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)
  linarith [exp5_ge_100]

private lemma exp40000_ge_100 : Real.exp 40000 ≥ (100 : ℝ) := by
  have h1 : Real.exp 40000 ≥ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)
  linarith [exp5_ge_100]

set_option maxHeartbeats 400000 in
/-- **Lemma 1.** Numerical facts implied by `n ≥ M_of δ`. -/
private lemma window_lil_M_bounds (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (n : ℕ) (hn : M_of δ ≤ n) :
    40000 / δ ^ 2 ≤ Real.log (Real.log n) ∧
    (16 : ℝ) ≤ Real.sqrt (n : ℝ) ∧
    (256 : ℝ) ≤ (n : ℝ) ∧
    (0 : ℝ) < Real.log (Real.log n) ∧
    Real.exp 100 ≤ (n : ℝ) := by
  have hδ2_pos : 0 < δ ^ 2 := by positivity
  have hbnd_pos : 0 < 40000 / δ ^ 2 := by positivity
  have hn256 : 256 ≤ n := by unfold M_of at hn; omega
  have hn256R : (256 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn256
  have hsqrt16 : (16 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h16sq : (16 : ℝ) = Real.sqrt 256 := by
      rw [show (256 : ℝ) = 16^2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 16)]
    rw [h16sq]; exact Real.sqrt_le_sqrt hn256R
  have hexp_part : Real.exp (Real.exp (40000 / δ ^ 2)) ≤ (n : ℝ) := by
    have h₁ : Real.exp (Real.exp (40000 / δ ^ 2)) ≤
        (Nat.ceil (Real.exp (Real.exp (40000 / δ ^ 2))) : ℝ) := Nat.le_ceil _
    have h₂ : (Nat.ceil (Real.exp (Real.exp (40000 / δ ^ 2))) : ℝ) ≤ (n : ℝ) := by
      have : Nat.ceil (Real.exp (Real.exp (40000 / δ ^ 2))) ≤ n := by
        unfold M_of at hn; omega
      exact_mod_cast this
    linarith
  have hn_pos : (0 : ℝ) < n := by linarith [Real.exp_pos (Real.exp (40000 / δ ^ 2))]
  have hlog_n : Real.exp (40000 / δ ^ 2) ≤ Real.log n := by
    rw [← Real.log_exp (Real.exp (40000 / δ ^ 2))]
    exact Real.log_le_log (Real.exp_pos _) hexp_part
  have hlog_n_pos : (0 : ℝ) < Real.log n := by
    have := Real.exp_pos (40000 / δ ^ 2); linarith
  have hllog : 40000 / δ ^ 2 ≤ Real.log (Real.log n) := by
    rw [← Real.log_exp (40000 / δ ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) hlog_n
  have hllog_pos : (0 : ℝ) < Real.log (Real.log n) := by linarith
  -- n ≥ exp(exp(40000/δ²)) ≥ exp(100) (since δ ≤ 1 → exp(40000/δ²) ≥ exp(40000) ≥ 100)
  have hexp_big : Real.exp 40000 ≤ Real.exp (40000 / δ ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ hδ2_pos]; nlinarith
  have hlog_n_big : (100 : ℝ) ≤ Real.log (n : ℝ) := by linarith [exp40000_ge_100]
  have hn_huge : Real.exp 100 ≤ (n : ℝ) := by
    rw [← Real.exp_log hn_pos]; exact Real.exp_le_exp.mpr hlog_n_big
  exact ⟨hllog, hsqrt16, hn256R, hllog_pos, hn_huge⟩

/-- Elementary: `log x ≤ 2 √x` for `x ≥ 1`. -/
private lemma log_le_two_sqrt (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx_pos.le
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [show x = Real.sqrt x * Real.sqrt x from hsqrt_sq.symm]
    rw [Real.log_mul hsqrt_pos.ne' hsqrt_pos.ne']; ring
  rw [h1]
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x :=
    (Real.log_le_sub_one_of_pos hsqrt_pos).trans (by linarith)
  linarith

set_option maxHeartbeats 400000 in
/-- `log n ≤ n/128` when `n ≥ exp(100)`. -/
private lemma log_le_n_div_128 (n : ℕ) (hn : Real.exp 100 ≤ (n : ℝ)) :
    Real.log (n : ℝ) ≤ (n : ℝ) / 128 := by
  -- n ≥ exp(100) ≥ 65536 (since exp(100) ≥ exp(10)^10 ≥ 16^10 ≥ 65536)
  have hn_ge : (65536 : ℝ) ≤ (n : ℝ) := by
    have h1 : Real.exp 10 ^ 10 ≥ (16 : ℝ) ^ 10 :=
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 16) exp10_ge_16 10
    have h2 : (16 : ℝ) ^ 10 ≥ 65536 := by norm_num
    have h3 : Real.exp 100 = Real.exp 10 ^ 10 := by
      rw [← Real.exp_nat_mul]; norm_num
    linarith
  -- √n ≥ 256 (since 65536 = 256²)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith [Real.exp_pos (100 : ℝ)]
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hsqrt_ge : Real.sqrt (n : ℝ) ≥ 256 := by
    have h : Real.sqrt 65536 = 256 := by
      rw [show (65536 : ℝ) = 256^2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 256)]
    rw [← h]; exact Real.sqrt_le_sqrt hn_ge
  have hsqrt_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ n)
  -- 2 √n ≤ n/128 (from √n ≥ 256)
  have h2sqrt_bd : 2 * Real.sqrt (n : ℝ) ≤ (n : ℝ) / 128 := by
    have : 2 * Real.sqrt (n : ℝ) * 128 ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
      nlinarith [hsqrt_ge, Real.sqrt_nonneg (n : ℝ)]
    rw [hsqrt_sq] at this
    linarith
  calc Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := log_le_two_sqrt _ hn_ge_one
    _ ≤ (n : ℝ) / 128 := h2sqrt_bd

set_option maxHeartbeats 600000 in
/-- **Lemma 2.** Basic Nat bounds for `kStar_of` and `W_of`. -/
private lemma window_lil_k_star_bounds (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (n : ℕ) (hn : M_of δ ≤ n) :
    1 ≤ kStar_of δ n ∧
    1 ≤ W_of n ∧
    kStar_of δ n + W_of n ≤ n + 1 ∧
    n / 2 ≤ kStar_of δ n ∧
    kStar_of δ n + W_of n ≤ n := by
  obtain ⟨hllog_ge, hsqrt16, hn256R, hllog_pos, hn_huge⟩ :=
    window_lil_M_bounds δ hδ hδ1 n hn
  -- Abbreviate the ceil argument
  set t := (1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) with ht_def
  have hn_ge : 256 ≤ n := by unfold M_of at hn; omega
  -- 1 ≤ kStar_of δ n trivially
  have h_ks_ge2 : 2 ≤ kStar_of δ n := by
    unfold kStar_of; omega
  have h_ks_ge1 : 1 ≤ kStar_of δ n := by omega
  -- 1 ≤ W_of n since √n ≥ 16
  have hW_ge_16 : 16 ≤ W_of n := by
    unfold W_of
    have : Nat.floor ((16 : ℝ)) ≤ Nat.floor (Real.sqrt (n : ℝ)) :=
      Nat.floor_le_floor hsqrt16
    simpa [Nat.floor_ofNat] using this
  have hW_ge1 : 1 ≤ W_of n := by omega
  -- t nonneg
  have hllog_nn : (0 : ℝ) ≤ Real.log (Real.log n) := hllog_pos.le
  have h1mδ_nn : (0 : ℝ) ≤ 1 - δ := by linarith
  have ht_arg_nn : (0 : ℝ) ≤ 2 * (n : ℝ) * Real.log (Real.log n) := by
    have : (0 : ℝ) ≤ (n : ℝ) := by linarith
    positivity
  have ht_nn : (0 : ℝ) ≤ t := by rw [ht_def]; positivity
  -- t ≤ √(2n log log n) (since 1-δ ≤ 1)
  have ht_le_sqrt : t ≤ Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) := by
    rw [ht_def]
    have hs_nn : (0 : ℝ) ≤ Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) :=
      Real.sqrt_nonneg _
    nlinarith [hs_nn, h1mδ_nn]
  -- log log n ≤ n/128 (using log n ≤ n/128 from log_le_n_div_128)
  have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) / 128 := log_le_n_div_128 n hn_huge
  have hlog_n_pos : (0 : ℝ) < Real.log (n : ℝ) := by
    -- log n ≥ 100 since n ≥ exp 100
    have : Real.log (Real.exp 100) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Real.exp_pos _) hn_huge
    rw [Real.log_exp] at this; linarith
  have hllog_le : Real.log (Real.log n) ≤ Real.log n :=
    (Real.log_le_sub_one_of_pos hlog_n_pos).trans (by linarith)
  have hllog_le_n128 : Real.log (Real.log n) ≤ (n : ℝ) / 128 := by linarith
  -- So 2n log log n ≤ 2n · n/128 = n²/64 → √(...) ≤ n/8
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hsq_bd : 2 * (n : ℝ) * Real.log (Real.log n) ≤ ((n : ℝ) / 8) ^ 2 := by
    have h1 : 2 * (n : ℝ) * Real.log (Real.log n) ≤ 2 * (n : ℝ) * ((n : ℝ) / 128) := by
      nlinarith [hllog_le_n128, hn_nn]
    have h2 : 2 * (n : ℝ) * ((n : ℝ) / 128) = (n : ℝ)^2 / 64 := by ring
    have h3 : ((n : ℝ) / 8) ^ 2 = (n : ℝ)^2 / 64 := by ring
    linarith
  have hn8_nn : (0 : ℝ) ≤ (n : ℝ) / 8 := by linarith
  have hts_bd : Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) ≤ (n : ℝ) / 8 := by
    have := Real.sqrt_le_sqrt hsq_bd
    rwa [Real.sqrt_sq hn8_nn] at this
  have ht_le_n8 : t ≤ (n : ℝ) / 8 := le_trans ht_le_sqrt hts_bd
  -- ⌈t/2⌉ ≤ t/2 + 1 ≤ n/16 + 1
  have hceil_t2 : (Nat.ceil (t / 2) : ℝ) ≤ (n : ℝ) / 16 + 1 := by
    have hceil_bd : (Nat.ceil (t / 2) : ℝ) ≤ t / 2 + 1 := by
      have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ t/2)
      linarith
    linarith
  -- W_of n ≤ √n ≤ n/8
  have hW_le_sqrt : (W_of n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    unfold W_of; exact Nat.floor_le (Real.sqrt_nonneg _)
  have hsqrt_sq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt hn_nn
  have hsqrt_le_n8 : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 8 := by
    have : 8 * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
      nlinarith [hsqrt16, Real.sqrt_nonneg (n : ℝ)]
    rw [hsqrt_sq] at this; linarith
  have hW_le_n8 : (W_of n : ℝ) ≤ (n : ℝ) / 8 := le_trans hW_le_sqrt hsqrt_le_n8
  -- ks + W ≤ n. ks = (n/2 : nat) + ⌈t/2⌉ + 2, so (ks : ℝ) ≤ n/2 + n/16 + 1 + 2 = n/2 + n/16 + 3
  -- ks + W ≤ n/2 + n/16 + 3 + n/8 ≤ n (for n ≥ 48 or so)
  have hn_div2_le : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have : 2 * (n / 2) ≤ n := by omega
    have : ((2 * (n / 2) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hks_cast : (kStar_of δ n : ℝ) = ((n / 2 : ℕ) : ℝ) + (Nat.ceil (t / 2) : ℝ) + 2 := by
    show ((n / 2 + Nat.ceil ((1 - δ) *
      Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) / 2) + 2 : ℕ) : ℝ) =
      ((n / 2 : ℕ) : ℝ) + (Nat.ceil (t / 2) : ℝ) + 2
    rw [ht_def]; push_cast; ring
  have hks_W_bd : ((kStar_of δ n : ℝ) + W_of n) ≤
      (n : ℝ) / 2 + (n : ℝ) / 16 + 1 + 2 + (n : ℝ) / 8 := by
    rw [hks_cast]
    linarith [hn_div2_le, hceil_t2, hW_le_n8]
  have hsum_small : (n : ℝ) / 2 + (n : ℝ) / 16 + 1 + 2 + (n : ℝ) / 8 ≤ (n : ℝ) := by
    nlinarith [hn256R]
  have hks_W_le_n_R : ((kStar_of δ n : ℝ) + W_of n) ≤ (n : ℝ) :=
    le_trans hks_W_bd hsum_small
  have hks_W_le_n_Nat : kStar_of δ n + W_of n ≤ n := by
    have : ((kStar_of δ n + W_of n : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; exact hks_W_le_n_R
    exact_mod_cast this
  have hks_W_le_n1 : kStar_of δ n + W_of n ≤ n + 1 := by omega
  have hks_ge_n2 : n / 2 ≤ kStar_of δ n := by
    unfold kStar_of; omega
  exact ⟨h_ks_ge1, hW_ge1, hks_W_le_n1, hks_ge_n2, hks_W_le_n_Nat⟩

set_option maxHeartbeats 400000 in
/-- **Lemma 3.** For every `k` in the window, `2·k - n ≥ (1-δ)·√(2n·log log n)`. -/
private lemma window_lil_k_above_t (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (n : ℕ) (hn : M_of δ ≤ n) :
    ∀ k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n),
      (1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) ≤
        2 * (k : ℝ) - (n : ℝ) := by
  intro k hk
  rw [Finset.mem_Ico] at hk
  obtain ⟨hk_lo, _⟩ := hk
  -- ks = (n/2 : nat) + ⌈t/2⌉ + 2
  -- 2 * (k : ℝ) - n ≥ 2 * ks - n ≥ 2 * ((n/2 nat) + ⌈t/2⌉ + 2) - n
  -- Use: 2 * (n/2 : nat) ≥ n - 1 and ⌈t/2⌉ ≥ t/2.
  have hks_cast : (kStar_of δ n : ℝ) = ((n / 2 : ℕ) : ℝ) +
      (Nat.ceil ((1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) / 2) : ℝ) + 2 := by
    unfold kStar_of; push_cast; ring
  have hk_ge : (kStar_of δ n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_lo
  have hceil_ge :
      ((1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) / 2 : ℝ) ≤
      (Nat.ceil ((1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) / 2) : ℝ) :=
    Nat.le_ceil _
  have hn_div2_ge : (n : ℝ) - 1 ≤ 2 * ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  linarith

set_option maxHeartbeats 800000 in
/-- **Lemma 4.** Exponent bound: for every `k` in the window,
`(2 + δ/4) · (k - n/2)² / n ≤ ((1-δ)² + δ) · log log n`. -/
private lemma window_lil_k_exponent_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (n : ℕ) (hn : M_of δ ≤ n) :
    ∀ k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n),
      (2 + δ / 4) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ) ≤
        ((1 - δ) ^ 2 + δ) * Real.log (Real.log n) := by
  intro k hk
  rw [Finset.mem_Ico] at hk
  obtain ⟨hk_lo, hk_hi⟩ := hk
  obtain ⟨hllog_ge, hsqrt16, hn256R, hllog_pos, _⟩ := window_lil_M_bounds δ hδ hδ1 n hn
  -- Named values
  let L := Real.log (Real.log (n : ℝ))
  let v := Real.sqrt (n : ℝ)
  let u := Real.sqrt (2 * L)
  let M := (k : ℝ) - (n : ℝ) / 2
  let t := (1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n))
  have hL_def : L = Real.log (Real.log (n : ℝ)) := rfl
  have hv_def : v = Real.sqrt (n : ℝ) := rfl
  have hu_def : u = Real.sqrt (2 * L) := rfl
  have hM_def : M = (k : ℝ) - (n : ℝ) / 2 := rfl
  have ht_def : t = (1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) := rfl
  have hL_nn : (0 : ℝ) ≤ L := hllog_pos.le
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have h2L_nn : (0 : ℝ) ≤ 2 * L := by linarith
  have hu_nn : (0 : ℝ) ≤ u := Real.sqrt_nonneg _
  have hv_nn : (0 : ℝ) ≤ v := Real.sqrt_nonneg _
  have hv_sq : v ^ 2 = (n : ℝ) := by rw [hv_def, sq]; exact Real.mul_self_sqrt hn_nn
  have hu_sq : u ^ 2 = 2 * L := by rw [hu_def, sq]; exact Real.mul_self_sqrt h2L_nn
  have hv_ge : (4 : ℝ) ≤ v := by rw [hv_def]; linarith
  have hn_ge16 : (16 : ℝ) ≤ (n : ℝ) := by linarith
  have hL_ge : (40000 : ℝ) / δ ^ 2 ≤ L := hllog_ge
  -- sqrt product: √(2nL) = u·v
  have huv_nn : (0 : ℝ) ≤ u * v := mul_nonneg hu_nn hv_nn
  have huv_sq_eq : (u * v) ^ 2 = 2 * L * (n : ℝ) := by
    rw [show (u*v)^2 = u^2 * v^2 from by ring, hu_sq, hv_sq]
  have hsqrt_prod : Real.sqrt (2 * (n : ℝ) * L) = u * v := by
    rw [show 2 * (n : ℝ) * L = 2 * L * (n : ℝ) from by ring]
    have : Real.sqrt ((u * v) ^ 2) = u * v := Real.sqrt_sq huv_nn
    rw [← huv_sq_eq]; exact this
  have ht_eq : t = (1 - δ) * (u * v) := by
    rw [ht_def]
    show (1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) = (1 - δ) * (u * v)
    rw [show Real.log (Real.log (n : ℝ)) = L from rfl, hsqrt_prod]
  have h1mδ_nn : (0 : ℝ) ≤ 1 - δ := by linarith
  have ht_nn : (0 : ℝ) ≤ t := by
    rw [ht_eq]; exact mul_nonneg h1mδ_nn huv_nn
  -- k upper bound: k ≤ ks + W - 1
  have hk_le : (k : ℝ) ≤ (kStar_of δ n : ℝ) + (W_of n : ℝ) - 1 := by
    have h : (k + 1 : ℕ) ≤ kStar_of δ n + W_of n := hk_hi
    have := (by exact_mod_cast h : ((k + 1 : ℕ) : ℝ) ≤
      ((kStar_of δ n + W_of n : ℕ) : ℝ))
    push_cast at this; linarith
  -- W ≤ v
  have hW_le_v : (W_of n : ℝ) ≤ v := by
    unfold W_of; rw [hv_def]; exact Nat.floor_le (Real.sqrt_nonneg _)
  -- ks ≤ n/2 + t/2 + 3
  have hceil_t2 : (Nat.ceil (t / 2) : ℝ) ≤ t / 2 + 1 := by
    have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ t/2)
    linarith
  have hn_div2_le : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have : 2 * (n / 2) ≤ n := by omega
    have : ((2 * (n / 2) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hks_cast : (kStar_of δ n : ℝ) = ((n / 2 : ℕ) : ℝ) + (Nat.ceil (t / 2) : ℝ) + 2 := by
    show ((n / 2 + Nat.ceil ((1 - δ) *
      Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) / 2) + 2 : ℕ) : ℝ) =
      ((n / 2 : ℕ) : ℝ) + (Nat.ceil (t / 2) : ℝ) + 2
    rw [ht_def]; push_cast; ring
  have hks_le : (kStar_of δ n : ℝ) ≤ (n : ℝ) / 2 + t / 2 + 3 := by
    rw [hks_cast]; linarith
  have hM_le : M ≤ t / 2 + v + 2 := by rw [hM_def]; linarith
  -- k ≥ ks ≥ n/2 + 2
  have hks_ge_n2 : n / 2 ≤ kStar_of δ n := by unfold kStar_of; omega
  have hk_ge_ks : (kStar_of δ n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_lo
  have h_ks_ge : ((n / 2 : ℕ) : ℝ) + 2 ≤ (kStar_of δ n : ℝ) := by
    rw [hks_cast]
    have : (0 : ℝ) ≤ (Nat.ceil (t / 2) : ℝ) := Nat.cast_nonneg _
    linarith
  have hn_div2_ge : (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hM_nn : (0 : ℝ) ≤ M := by rw [hM_def]; linarith
  -- M² ≤ (t/2 + v + 2)²
  have htv_nn : (0 : ℝ) ≤ t / 2 + v + 2 := by linarith
  have hM_sq_bd : M ^ 2 ≤ (t / 2 + v + 2) ^ 2 := by
    nlinarith [hM_nn, hM_le, htv_nn]
  -- (t/2 + v + 2)² = (1-δ)²·n·L/2 + (1-δ)·uv·(v+2) + (v+2)²
  have hform : (t / 2 + v + 2) ^ 2 =
      (1 - δ) ^ 2 * (n : ℝ) * L / 2 +
      (1 - δ) * (u * v) * (v + 2) +
      (v + 2) ^ 2 := by
    rw [ht_eq]
    have step : ((1 - δ) * (u * v) / 2 + v + 2) ^ 2 =
        (1 - δ) ^ 2 * (u * v) ^ 2 / 4 +
        (1 - δ) * (u * v) * (v + 2) +
        (v + 2) ^ 2 := by ring
    rw [step]
    have h_uv_sq : (1 - δ) ^ 2 * (u * v) ^ 2 / 4 = (1 - δ) ^ 2 * (n : ℝ) * L / 2 := by
      rw [show (u*v)^2 = u^2 * v^2 from by ring, hu_sq, hv_sq]; ring
    linarith
  have hM_sq_form : M ^ 2 ≤ (1 - δ) ^ 2 * (n : ℝ) * L / 2 +
      (1 - δ) * (u * v) * (v + 2) + (v + 2) ^ 2 := by
    linarith [hM_sq_bd, hform]
  -- Apply exponent_window_bound_uv
  exact exponent_window_bound_uv δ hδ hδ1 (n : ℝ) hn_ge16 L hL_ge M v hv_sq hv_nn hv_ge
    u hu_sq hu_nn hM_sq_form

set_option maxHeartbeats 800000 in
/-- **Lemma 4b.** Regime check: for every `k` in the window,
`(k - n/2)² ≤ n · log n`. -/
private lemma window_lil_k_regime (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (n : ℕ) (hn : M_of δ ≤ n) :
    ∀ k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n),
      ((k : ℝ) - (n : ℝ) / 2) ^ 2 ≤ (n : ℝ) * Real.log n := by
  intro k hk
  rw [Finset.mem_Ico] at hk
  obtain ⟨hk_lo, hk_hi⟩ := hk
  obtain ⟨hllog_ge, hsqrt16, hn256R, hllog_pos, hn_huge⟩ :=
    window_lil_M_bounds δ hδ hδ1 n hn
  let L := Real.log (Real.log (n : ℝ))
  let v := Real.sqrt (n : ℝ)
  let u := Real.sqrt (2 * L)
  let t := (1 - δ) * Real.sqrt (2 * (n : ℝ) * L)
  have hL_def : L = Real.log (Real.log (n : ℝ)) := rfl
  have hv_def : v = Real.sqrt (n : ℝ) := rfl
  have hu_def : u = Real.sqrt (2 * L) := rfl
  have ht_def : t = (1 - δ) * Real.sqrt (2 * (n : ℝ) * L) := rfl
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hL_nn : (0 : ℝ) ≤ L := hllog_pos.le
  have h2L_nn : (0 : ℝ) ≤ 2 * L := by linarith
  have hu_nn : (0 : ℝ) ≤ u := Real.sqrt_nonneg _
  have hv_nn : (0 : ℝ) ≤ v := Real.sqrt_nonneg _
  have hv_sq : v ^ 2 = (n : ℝ) := by rw [hv_def, sq]; exact Real.mul_self_sqrt hn_nn
  have hu_sq : u ^ 2 = 2 * L := by rw [hu_def, sq]; exact Real.mul_self_sqrt h2L_nn
  have hv_ge : (4 : ℝ) ≤ v := by rw [hv_def]; linarith
  have h1mδ_nn : (0 : ℝ) ≤ 1 - δ := by linarith
  have hk_le_ksW : (k : ℝ) ≤ (kStar_of δ n : ℝ) + (W_of n : ℝ) - 1 := by
    have h : (k + 1 : ℕ) ≤ kStar_of δ n + W_of n := hk_hi
    have := (by exact_mod_cast h : ((k + 1 : ℕ) : ℝ) ≤
      ((kStar_of δ n + W_of n : ℕ) : ℝ))
    push_cast at this; linarith
  have huv_nn : (0 : ℝ) ≤ u * v := mul_nonneg hu_nn hv_nn
  have huv_sq_eq : (u * v) ^ 2 = 2 * L * (n : ℝ) := by
    rw [show (u*v)^2 = u^2 * v^2 from by ring, hu_sq, hv_sq]
  have hsqrt_prod : Real.sqrt (2 * (n : ℝ) * L) = u * v := by
    have h1 : Real.sqrt ((u * v) ^ 2) = u * v := Real.sqrt_sq huv_nn
    have h2 : (u * v) ^ 2 = 2 * (n : ℝ) * L := by
      rw [huv_sq_eq]; ring
    rw [← h2]; exact h1
  have ht_eq : t = (1 - δ) * (u * v) := by rw [ht_def, ← hsqrt_prod]
  have ht_nn : (0 : ℝ) ≤ t := by
    rw [ht_eq]; exact mul_nonneg h1mδ_nn huv_nn
  have hceil_t2 : (Nat.ceil (t / 2) : ℝ) ≤ t / 2 + 1 := by
    have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ t/2)
    linarith
  have hn_div2_le : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have : 2 * (n / 2) ≤ n := by omega
    have : ((2 * (n / 2) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have hks_cast : (kStar_of δ n : ℝ) = ((n / 2 : ℕ) : ℝ) +
      (Nat.ceil (t / 2) : ℝ) + 2 := by
    show ((n / 2 + Nat.ceil ((1 - δ) *
      Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) / 2) + 2 : ℕ) : ℝ) =
      ((n / 2 : ℕ) : ℝ) + (Nat.ceil (t / 2) : ℝ) + 2
    rw [ht_def]; push_cast; ring
  have hks_le : (kStar_of δ n : ℝ) ≤ (n : ℝ) / 2 + t / 2 + 3 := by
    rw [hks_cast]; linarith
  have hW_le_v : (W_of n : ℝ) ≤ v := by
    unfold W_of; rw [hv_def]; exact Nat.floor_le (Real.sqrt_nonneg _)
  have hM_le : (k : ℝ) - (n : ℝ) / 2 ≤ t / 2 + v + 2 := by linarith
  have hks_ge_n2 : n / 2 ≤ kStar_of δ n := by unfold kStar_of; omega
  have hk_ge_ks : (kStar_of δ n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_lo
  have h_ks_ge : ((n / 2 : ℕ) : ℝ) + 2 ≤ (kStar_of δ n : ℝ) := by
    rw [hks_cast]
    have : (0 : ℝ) ≤ (Nat.ceil (t / 2) : ℝ) := Nat.cast_nonneg _
    linarith
  have hn_div2_ge : (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hM_nn : (0 : ℝ) ≤ (k : ℝ) - (n : ℝ) / 2 := by linarith
  have htv_nn : (0 : ℝ) ≤ t / 2 + v + 2 := by linarith
  have hM_sq_bd : ((k : ℝ) - (n : ℝ) / 2) ^ 2 ≤ (t / 2 + v + 2) ^ 2 :=
    sq_le_sq' (by linarith) hM_le
  have hL_big : (40000 : ℝ) ≤ L := by
    have hδ2_pos : 0 < δ ^ 2 := by positivity
    have hδ2_le : δ ^ 2 ≤ 1 := by nlinarith
    have h1 : (40000 : ℝ) ≤ 40000 / δ^2 := by
      rw [le_div_iff₀ hδ2_pos]; nlinarith
    linarith
  have h1mδ_sq_le : (1 - δ)^2 ≤ 1 := by nlinarith
  have ht2_nn : (0:ℝ) ≤ t/2 := by linarith
  have hsqrt_sum_sq : (t / 2 + v + 2) ^ 2 ≤ 3 * ((t/2)^2 + v^2 + 4) := by
    nlinarith [ht2_nn, hv_nn, sq_nonneg (t/2 - v), sq_nonneg (t/2 - 2), sq_nonneg (v - 2)]
  have ht2_sq : (t / 2)^2 = (1 - δ) ^ 2 * (n : ℝ) * L / 2 := by
    have h1 : (t / 2)^2 = (1 - δ)^2 * (u*v)^2 / 4 := by
      rw [ht_eq]; ring
    rw [h1, huv_sq_eq]; ring
  have hnL_nn : (0 : ℝ) ≤ (n : ℝ) * L / 2 := by positivity
  have ht2_sq_le : (t / 2)^2 ≤ (n : ℝ) * L / 2 := by
    rw [ht2_sq]
    calc (1 - δ)^2 * (n : ℝ) * L / 2 = (1-δ)^2 * ((n : ℝ) * L / 2) := by ring
      _ ≤ 1 * ((n : ℝ) * L / 2) := mul_le_mul_of_nonneg_right h1mδ_sq_le hnL_nn
      _ = (n : ℝ) * L / 2 := by ring
  have htotal_bd : (t / 2 + v + 2) ^ 2 ≤ 3 * (n : ℝ) * L / 2 + 3 * (n : ℝ) + 12 := by
    have step2 : 3 * ((t/2)^2 + v^2 + 4) ≤ 3 * ((n : ℝ) * L / 2 + (n : ℝ) + 4) := by
      have : (t/2)^2 + v^2 + 4 ≤ (n : ℝ) * L / 2 + (n : ℝ) + 4 := by
        linarith [ht2_sq_le, hv_sq]
      linarith
    linarith [hsqrt_sum_sq, step2]
  -- Now need: 3 n L / 2 + 3n + 12 ≤ n · log n. Divide: 3L/2 + 3 + 12/n ≤ log n.
  have hlog_n_ge100 : (100 : ℝ) ≤ Real.log (n : ℝ) := by
    have : Real.log (Real.exp 100) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Real.exp_pos _) hn_huge
    rw [Real.log_exp] at this; linarith
  have hlog_n_pos : (0 : ℝ) < Real.log (n : ℝ) := by linarith
  have hllog_le_2sqrt : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log n) :=
    log_le_two_sqrt (Real.log n) (by linarith)
  have hsqrt_logn_ge : (10 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
    have h100eq : Real.sqrt (100 : ℝ) = 10 := by
      rw [show (100 : ℝ) = 10^2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10)]
    rw [← h100eq]; exact Real.sqrt_le_sqrt hlog_n_ge100
  have hsqrt_logn_sq : Real.sqrt (Real.log n) * Real.sqrt (Real.log n) = Real.log n :=
    Real.mul_self_sqrt hlog_n_pos.le
  -- y · y ≥ 10 · y ≥ 10 · 10 = 100. Also y² = log n.
  have h3sqrt_bd : 3 * Real.sqrt (Real.log n) + 4 ≤ Real.log n := by
    have hy_ge : 10 ≤ Real.sqrt (Real.log n) := hsqrt_logn_ge
    have h10y : 10 * Real.sqrt (Real.log n) ≤
        Real.sqrt (Real.log n) * Real.sqrt (Real.log n) := by
      have := mul_le_mul_of_nonneg_right hy_ge
        (by linarith : (0:ℝ) ≤ Real.sqrt (Real.log n))
      linarith
    linarith [h10y, hsqrt_logn_sq, hy_ge]
  -- n ≥ exp(100), so 12/n is tiny
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith [Real.exp_pos (100 : ℝ)]
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hn_ge_exp100 : (1 : ℝ) ≤ (n : ℝ) := by
    have := Real.exp_pos (100 : ℝ); linarith [exp5_ge_100]
  have h12_n_le : (12 : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hn_pos]
    -- n ≥ exp(100) ≥ 100 > 12
    have : (100 : ℝ) ≤ Real.exp 100 := exp5_ge_100.trans (Real.exp_le_exp.mpr (by norm_num))
    linarith
  have hL_le : L ≤ 2 * Real.sqrt (Real.log n) := hllog_le_2sqrt
  have h3L2_le : 3 * L / 2 ≤ 3 * Real.sqrt (Real.log n) := by linarith
  have hmain : 3 * L / 2 + 3 + 12 / (n : ℝ) ≤ Real.log n := by
    linarith [h3sqrt_bd, h12_n_le]
  have h1_mul := mul_le_mul_of_nonneg_left hmain hn_pos.le
  have hdist : (n : ℝ) * (3 * L / 2 + 3 + 12 / (n : ℝ)) =
      3 * (n : ℝ) * L / 2 + 3 * (n : ℝ) + (n : ℝ) * (12 / (n : ℝ)) := by ring
  have hsimp_12 : (n : ℝ) * (12 / (n : ℝ)) = 12 := by
    rw [mul_div_cancel₀ 12 hn_ne]
  have hfinal : 3 * (n : ℝ) * L / 2 + 3 * (n : ℝ) + 12 ≤ (n : ℝ) * Real.log n := by
    rw [hdist, hsimp_12] at h1_mul
    exact h1_mul
  linarith [hM_sq_bd, htotal_bd, hfinal]

set_option maxHeartbeats 800000 in
/-- **Lemma 5.** For every `k` in the window, the PMF satisfies a Gaussian
lower bound in terms of `((1-δ)² + δ) · log log n`. -/
private lemma window_lil_pmf_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (c₁ : ℝ) (hc₁_pos : 0 < c₁) (N₁ : ℕ)
    (hpmf : ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
        ((k : ℝ) - (n : ℝ) / 2) ^ 2 ≤ (n : ℝ) * Real.log n →
        (n.choose k : ℝ) / (2 : ℝ) ^ n ≥
          c₁ / Real.sqrt (n : ℝ) *
            Real.exp (-(2 + δ/4) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)))
    (n : ℕ) (hnM : M_of δ ≤ n) (hnN : N₁ ≤ n) :
    ∀ k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n),
      c₁ / Real.sqrt (n : ℝ) *
        Real.exp (-((1 - δ) ^ 2 + δ) * Real.log (Real.log n)) ≤
      (n.choose k : ℝ) / (2 : ℝ) ^ n := by
  intro k hk
  obtain ⟨h1, h2, _, hks_ge, hks_W_le⟩ :=
    window_lil_k_star_bounds δ hδ hδ1 n hnM
  obtain ⟨hllog_ge, hsqrt16, hn256R, hllog_pos, hn_huge⟩ :=
    window_lil_M_bounds δ hδ hδ1 n hnM
  have hkIco : k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n) := hk
  rw [Finset.mem_Ico] at hk
  obtain ⟨hk_lo, hk_hi⟩ := hk
  have hk_ge1 : 1 ≤ k := le_trans h1 hk_lo
  have hk_lt_n : k < n := by
    have : k + 1 ≤ kStar_of δ n + W_of n := hk_hi
    omega
  -- Exponent bound from Lemma 4
  have hexp_bd := window_lil_k_exponent_bound δ hδ hδ1 n hnM k hkIco
  -- Regime check from Lemma 4b
  have hM_regime := window_lil_k_regime δ hδ hδ1 n hnM k hkIco
  -- Apply PMF
  have h_target_k := hpmf n hnN k hk_ge1 hk_lt_n hM_regime
  -- Combine with exponent monotonicity
  have h_exp_mono : Real.exp (-((1 - δ) ^ 2 + δ) * Real.log (Real.log n)) ≤
      Real.exp (-(2 + δ/4) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_eq : -(2 + δ/4) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ) =
        -((2 + δ/4) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by ring
    rw [h_eq]
    linarith [hexp_bd]
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (n : ℝ) := by
    have : (0 : ℝ) < (n : ℝ) := by linarith
    exact Real.sqrt_pos.mpr this
  have hc1_over_sqrt_pos : (0 : ℝ) ≤ c₁ / Real.sqrt (n : ℝ) :=
    div_nonneg hc₁_pos.le hsqrt_pos.le
  calc c₁ / Real.sqrt (n : ℝ) *
          Real.exp (-((1 - δ) ^ 2 + δ) * Real.log (Real.log n)) ≤
        c₁ / Real.sqrt (n : ℝ) *
          Real.exp (-(2 + δ/4) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left h_exp_mono hc1_over_sqrt_pos
    _ ≤ (n.choose k : ℝ) / (2 : ℝ) ^ n := h_target_k

set_option maxHeartbeats 800000 in
/-- Existential LIL-scale window-sum lower bound. For each `δ ∈ (0,1)`,
there exist constants `c > 0` and `N` such that for all `n ≥ N`, there is a
window `[k_star, k_star + W - 1]` of indices (within `[1, n]`) on which:
(a) every `k` in the window satisfies `2k - n ≥ (1-δ)·√(2n·log log n)`;
(b) the sum of PMF contributions exceeds `c · exp(-((1-δ)² + δ) · log log n)`. -/
theorem window_sum_at_LIL_scale
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        ∃ (k_star W : ℕ),
          1 ≤ k_star ∧ 1 ≤ W ∧ k_star + W ≤ n + 1 ∧
          (∀ k ∈ Finset.Ico k_star (k_star + W),
            (1 - δ) * Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n)) ≤
              2 * (k : ℝ) - n) ∧
          c * Real.exp (-((1 - δ) ^ 2 + δ) * Real.log (Real.log n)) ≤
            ∑ k ∈ Finset.Ico k_star (k_star + W),
              (n.choose k : ℝ) / (2 : ℝ) ^ n := by
  obtain ⟨c₁, N₁, hc₁_pos, hN₁_one, hpmf⟩ :=
    centralBinom_pmf_lower_bound_alpha_two (δ / 4) (by linarith)
  -- Convert PMF statement to the form we need (2 + δ/4 instead of 2 + δ/4)
  have hpmf' : ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
      ((k : ℝ) - (n : ℝ) / 2) ^ 2 ≤ (n : ℝ) * Real.log n →
      (n.choose k : ℝ) / (2 : ℝ) ^ n ≥
        c₁ / Real.sqrt (n : ℝ) *
          Real.exp (-(2 + δ/4) * ((k : ℝ) - (n : ℝ) / 2) ^ 2 / (n : ℝ)) := by
    intro n' hn' k hk hkn hreg
    exact hpmf n' hn' k hk hkn hreg
  refine ⟨c₁ / 2, max N₁ (M_of δ), by positivity, ?_, ?_⟩
  · exact le_max_of_le_left hN₁_one
  intro n hn
  have hnN : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M_of δ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨h1, h2, hsum_bd, hks_ge, hks_W_le⟩ :=
    window_lil_k_star_bounds δ hδ hδ1 n hnM
  obtain ⟨hllog_ge, hsqrt16, hn256R, hllog_pos, hn_huge⟩ :=
    window_lil_M_bounds δ hδ hδ1 n hnM
  refine ⟨kStar_of δ n, W_of n, h1, h2, hsum_bd, ?_, ?_⟩
  · exact window_lil_k_above_t δ hδ hδ1 n hnM
  · -- Sum bound
    have hbd_pointwise := window_lil_pmf_bound δ hδ hδ1 c₁ hc₁_pos N₁ hpmf' n hnM hnN
    -- W ≥ √n - 1 ≥ √n / 2 (since √n ≥ 2)
    have hsqrt_pos : (0 : ℝ) < Real.sqrt (n : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) := by linarith
      exact Real.sqrt_pos.mpr this
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have hW_lt : Real.sqrt (n : ℝ) < (W_of n : ℝ) + 1 := by
      unfold W_of; exact Nat.lt_floor_add_one _
    have hW_ge_half : Real.sqrt (n : ℝ) / 2 ≤ (W_of n : ℝ) := by
      -- √n - 1 < W_of n, so W_of n ≥ √n - 1 + (something infinitesimal); we use W_of n > √n - 1.
      -- Since W_of n is an integer and √n - 1 may not be, W_of n ≥ ⌈√n - 1⌉ ≥ √n - 1 exactly when...
      -- Simpler: W ≥ √n - 1, and √n - 1 ≥ √n / 2 (since √n ≥ 2).
      -- But W > √n - 1, so W ≥ √n - 1 (as real since W is nat cast).
      -- Actually hW_lt says √n < W + 1, i.e., W ≥ √n - 1 (as reals).
      linarith [hW_lt, hsqrt16]
    -- Sum ≥ W * (c₁/√n · exp(-E))
    have hsum_const_bd : ∑ _k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n),
          (c₁ / Real.sqrt (n : ℝ) *
            Real.exp (-((1 - δ)^2 + δ) * Real.log (Real.log n))) =
        (W_of n : ℝ) * (c₁ / Real.sqrt (n : ℝ) *
            Real.exp (-((1 - δ)^2 + δ) * Real.log (Real.log n))) := by
      rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left]
      rw [nsmul_eq_mul]
    have hsum_lb : (W_of n : ℝ) * (c₁ / Real.sqrt (n : ℝ) *
          Real.exp (-((1 - δ)^2 + δ) * Real.log (Real.log n))) ≤
        ∑ k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n),
          (n.choose k : ℝ) / (2:ℝ)^n := by
      rw [← hsum_const_bd]
      exact Finset.sum_le_sum (fun k hk => hbd_pointwise k hk)
    -- c₁/2 ≤ W · c₁ / √n (since W / √n ≥ 1/2)
    have hS_pos : (0 : ℝ) < Real.exp (-((1 - δ)^2 + δ) * Real.log (Real.log n)) :=
      Real.exp_pos _
    have hkey : c₁ / 2 ≤ (W_of n : ℝ) * (c₁ / Real.sqrt (n : ℝ)) := by
      have hmul_bd : Real.sqrt (n : ℝ) / 2 * c₁ ≤ (W_of n : ℝ) * c₁ :=
        mul_le_mul_of_nonneg_right hW_ge_half hc₁_pos.le
      have hdiv : Real.sqrt (n : ℝ) / 2 * c₁ / Real.sqrt (n : ℝ) = c₁ / 2 := by
        field_simp
      have h_final : c₁ / 2 ≤ (W_of n : ℝ) * c₁ / Real.sqrt (n : ℝ) := by
        rw [← hdiv]
        exact div_le_div_of_nonneg_right hmul_bd hsqrt_pos.le
      have : (W_of n : ℝ) * c₁ / Real.sqrt (n : ℝ) =
          (W_of n : ℝ) * (c₁ / Real.sqrt (n : ℝ)) := by
        rw [mul_div_assoc]
      linarith
    -- Final chain
    calc c₁ / 2 * Real.exp (-((1 - δ)^2 + δ) * Real.log (Real.log n))
        ≤ (W_of n : ℝ) * (c₁ / Real.sqrt (n : ℝ)) *
            Real.exp (-((1 - δ)^2 + δ) * Real.log (Real.log n)) := by
          exact mul_le_mul_of_nonneg_right hkey hS_pos.le
      _ = (W_of n : ℝ) * (c₁ / Real.sqrt (n : ℝ) *
            Real.exp (-((1 - δ)^2 + δ) * Real.log (Real.log n))) := by ring
      _ ≤ ∑ k ∈ Finset.Ico (kStar_of δ n) (kStar_of δ n + W_of n),
            (n.choose k : ℝ) / (2:ℝ)^n := hsum_lb

end Helpers
end Erdos524
