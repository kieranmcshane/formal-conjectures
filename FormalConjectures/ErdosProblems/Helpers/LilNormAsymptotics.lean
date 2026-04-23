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
# Asymptotics of the LIL normalisation along exponential subsequences

For the Law of the Iterated Logarithm (LIL) normalisation
`φ(n) = √(2 n log log n)`, this file establishes the asymptotic ratios along
exponential subsequences `n_k = ⌊c^k⌋₊` for `c > 1`:

* `Erdos524.Helpers.lilNormAux_block_ratio_tendsto` — the ratio of block scale
  over full scale tends to `√((c-1)/c)`.
* `Erdos524.Helpers.lilNormAux_scale_ratio_tendsto` — the ratio of short scale
  over long scale tends to `1 / √c`.

These are used in the Erdős problem 524 formalisation (Kolmogorov LIL upper
bound via Borel–Cantelli along a geometric subsequence).
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524.Helpers

open Filter Topology

/-- The LIL normalisation `φ(x) = √(2 x log log x)`, taking a real argument
for convenience. -/
noncomputable def lilNormAux (x : ℝ) : ℝ :=
  Real.sqrt (2 * x * Real.log (Real.log x))

/-- `⌊c^k⌋₊ → ∞` as `k → ∞`, for `c > 1`. -/
lemma floor_pow_tendsto_atTop {c : ℝ} (hc : 1 < c) :
    Tendsto (fun k : ℕ => (⌊c ^ k⌋₊ : ℝ)) atTop atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  have hpow := tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt hc) (b + 1)
  exact hpow.mono fun k hk =>
    le_trans (by linarith : b ≤ c ^ k - 1)
      (le_of_lt (mod_cast Nat.sub_one_lt_floor (c ^ k)))

/-- `⌊c^k⌋₊ / c^k → 1` as `k → ∞`, for `c > 1`. -/
lemma floor_pow_div_pow_tendsto {c : ℝ} (hc : 1 < c) :
    Tendsto (fun k : ℕ => (⌊c ^ k⌋₊ : ℝ) / c ^ k) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => c ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hc
  exact (tendsto_nat_floor_div_atTop (R := ℝ)).comp h1

/-- `c^k > 0` for `c > 1`. -/
lemma pow_pos_of_one_lt {c : ℝ} (hc : 1 < c) (k : ℕ) : (0 : ℝ) < c ^ k :=
  pow_pos (zero_lt_one.trans hc) k

/-- Eventually `(⌊c^k⌋₊ : ℝ) > 0` for `c > 1`. -/
lemma eventually_floor_pow_pos {c : ℝ} (hc : 1 < c) :
    ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (⌊c ^ k⌋₊ : ℝ) :=
  (floor_pow_tendsto_atTop hc).eventually_gt_atTop (0 : ℝ)

/-- `(⌊c^(k+1)⌋₊ - ⌊c^k⌋₊ : ℝ) / c^(k+1) → (c - 1) / c` for `c > 1`. -/
lemma block_over_pow_tendsto {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun k : ℕ => ((⌊c ^ (k + 1)⌋₊ : ℝ) - (⌊c ^ k⌋₊ : ℝ)) / c ^ (k + 1))
      atTop (𝓝 ((c - 1) / c)) := by
  have hcpos : (0 : ℝ) < c := zero_lt_one.trans hc
  have hne : (c : ℝ) ≠ 0 := ne_of_gt hcpos
  have hA : Tendsto (fun k : ℕ => (⌊c ^ (k + 1)⌋₊ : ℝ) / c ^ (k + 1)) atTop (𝓝 1) :=
    (floor_pow_div_pow_tendsto hc).comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto (fun k : ℕ => (⌊c ^ k⌋₊ : ℝ) / c ^ k) atTop (𝓝 1) :=
    floor_pow_div_pow_tendsto hc
  have hBC :
      Tendsto (fun k : ℕ => ((⌊c ^ k⌋₊ : ℝ) / c ^ k) * (1 / c)) atTop
        (𝓝 (1 * (1 / c))) :=
    hB.mul tendsto_const_nhds
  have hAB :
      Tendsto
        (fun k : ℕ => (⌊c ^ (k + 1)⌋₊ : ℝ) / c ^ (k + 1) -
          ((⌊c ^ k⌋₊ : ℝ) / c ^ k) * (1 / c)) atTop
        (𝓝 (1 - 1 * (1 / c))) := hA.sub hBC
  have hrewrite : ∀ k : ℕ,
      ((⌊c ^ (k + 1)⌋₊ : ℝ) - (⌊c ^ k⌋₊ : ℝ)) / c ^ (k + 1) =
        (⌊c ^ (k + 1)⌋₊ : ℝ) / c ^ (k + 1) -
          ((⌊c ^ k⌋₊ : ℝ) / c ^ k) * (1 / c) := by
    intro k
    have hck : (0 : ℝ) < c ^ k := pow_pos_of_one_lt hc k
    have hck1 : (0 : ℝ) < c ^ (k + 1) := pow_pos_of_one_lt hc (k + 1)
    have hckne : (c ^ k : ℝ) ≠ 0 := ne_of_gt hck
    have hck1ne : (c ^ (k + 1) : ℝ) ≠ 0 := ne_of_gt hck1
    have hstep : (c ^ (k + 1) : ℝ) = c ^ k * c := by rw [pow_succ]
    field_simp
    rw [hstep]
    ring
  have hlim : (1 : ℝ) - 1 * (1 / c) = (c - 1) / c := by field_simp
  rw [← hlim]
  exact hAB.congr (fun k => (hrewrite k).symm)

/-- `(⌊c^k⌋₊ : ℝ) / ⌊c^(k+1)⌋₊ → 1/c` for `c > 1`. -/
lemma short_over_long_floor_tendsto {c : ℝ} (hc : 1 < c) :
    Tendsto (fun k : ℕ => (⌊c ^ k⌋₊ : ℝ) / (⌊c ^ (k + 1)⌋₊ : ℝ))
      atTop (𝓝 (1 / c)) := by
  have hcpos : (0 : ℝ) < c := zero_lt_one.trans hc
  have hne : (c : ℝ) ≠ 0 := ne_of_gt hcpos
  have hA : Tendsto (fun k : ℕ => (⌊c ^ k⌋₊ : ℝ) / c ^ k) atTop (𝓝 1) :=
    floor_pow_div_pow_tendsto hc
  have hB : Tendsto (fun k : ℕ => (⌊c ^ (k + 1)⌋₊ : ℝ) / c ^ (k + 1)) atTop (𝓝 1) :=
    (floor_pow_div_pow_tendsto hc).comp (tendsto_add_atTop_nat 1)
  have hone_ne : (1 : ℝ) ≠ 0 := one_ne_zero
  have hdiv :
      Tendsto
        (fun k : ℕ => ((⌊c ^ k⌋₊ : ℝ) / c ^ k) / ((⌊c ^ (k + 1)⌋₊ : ℝ) / c ^ (k + 1)))
        atTop (𝓝 (1 / 1)) := hA.div hB hone_ne
  have hmul :
      Tendsto
        (fun k : ℕ =>
          (((⌊c ^ k⌋₊ : ℝ) / c ^ k) / ((⌊c ^ (k + 1)⌋₊ : ℝ) / c ^ (k + 1))) * (1 / c))
        atTop (𝓝 ((1 / 1) * (1 / c))) := hdiv.mul tendsto_const_nhds
  have hposk1 : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (⌊c ^ (k + 1)⌋₊ : ℝ) :=
    ((floor_pow_tendsto_atTop hc).comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop 0
  have heq : ∀ᶠ k : ℕ in atTop,
      (((⌊c ^ k⌋₊ : ℝ) / c ^ k) / ((⌊c ^ (k + 1)⌋₊ : ℝ) / c ^ (k + 1))) * (1 / c)
        = (⌊c ^ k⌋₊ : ℝ) / (⌊c ^ (k + 1)⌋₊ : ℝ) := by
    filter_upwards [eventually_floor_pow_pos hc, hposk1] with k _ _
    have hck : (0 : ℝ) < c ^ k := pow_pos_of_one_lt hc k
    have hck1 : (0 : ℝ) < c ^ (k + 1) := pow_pos_of_one_lt hc (k + 1)
    have hstep : (c ^ (k + 1) : ℝ) = c ^ k * c := by rw [pow_succ]
    rw [hstep]
    field_simp
  have hlim : (1 : ℝ) / 1 * (1 / c) = 1 / c := by ring
  rw [← hlim]
  exact hmul.congr' heq

/-- `log (⌊c^k⌋₊ : ℝ) → ∞` for `c > 1`. -/
lemma tendsto_log_floor_pow_atTop {c : ℝ} (hc : 1 < c) :
    Tendsto (fun k : ℕ => Real.log (⌊c ^ k⌋₊ : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (floor_pow_tendsto_atTop hc)

/-- `log log (⌊c^k⌋₊ : ℝ) → ∞` for `c > 1`. -/
lemma tendsto_loglog_floor_pow_atTop {c : ℝ} (hc : 1 < c) :
    Tendsto (fun k : ℕ => Real.log (Real.log (⌊c ^ k⌋₊ : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_log_floor_pow_atTop hc)

/- ### A general helper

The key insight is: if `a_k → ∞`, `b_k → ∞`, and `a_k / b_k → r > 0`, then
`log log a_k / log log b_k → 1`, and hence
`(a_k log log a_k) / (b_k log log b_k) → r`. Taking square roots then gives
`lilNormAux(a_k) / lilNormAux(b_k) → √r`. -/

/-- If `a_k → ∞`, `b_k → ∞`, and `a_k / b_k → r` with `r > 0`, then
`log log a_k / log log b_k → 1`. -/
lemma loglog_ratio_tendsto_one_of_ratio {a b : ℕ → ℝ} {r : ℝ}
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hab : Tendsto (fun k => a k / b k) atTop (𝓝 r)) (hr : 0 < r) :
    Tendsto (fun k => Real.log (Real.log (a k)) / Real.log (Real.log (b k)))
      atTop (𝓝 1) := by
  -- Log of a_k / b_k tends to log r (finite).
  have h_log_ratio : Tendsto (fun k => Real.log (a k / b k)) atTop (𝓝 (Real.log r)) := by
    have hcont : ContinuousAt Real.log r := Real.continuousAt_log (ne_of_gt hr)
    exact hcont.tendsto.comp hab
  -- log b_k → ∞, log log b_k → ∞.
  have hlog_b : Tendsto (fun k => Real.log (b k)) atTop atTop := Real.tendsto_log_atTop.comp hb
  have hlog_a : Tendsto (fun k => Real.log (a k)) atTop atTop := Real.tendsto_log_atTop.comp ha
  have hll_b : Tendsto (fun k => Real.log (Real.log (b k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog_b
  have hll_a : Tendsto (fun k => Real.log (Real.log (a k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog_a
  -- Rewrite: log a = log b + log(a/b) eventually.
  have ha_pos : ∀ᶠ k in atTop, (0 : ℝ) < a k := ha.eventually_gt_atTop 0
  have hb_pos : ∀ᶠ k in atTop, (0 : ℝ) < b k := hb.eventually_gt_atTop 0
  -- log(a/b)/log(b) → 0 (bounded / ∞).
  have h_small : Tendsto (fun k => Real.log (a k / b k) / Real.log (b k))
      atTop (𝓝 0) := by
    have := h_log_ratio.div_atTop hlog_b
    simpa using this
  -- 1 + log(a/b)/log(b) → 1.
  have h_1plus : Tendsto (fun k => 1 + Real.log (a k / b k) / Real.log (b k))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.add h_small
  -- log(1 + …) → log 1 = 0.
  have hcontlog1 : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
  have h_log_1plus :
      Tendsto (fun k => Real.log (1 + Real.log (a k / b k) / Real.log (b k)))
        atTop (𝓝 0) := by
    have := hcontlog1.tendsto.comp h_1plus
    simpa [Real.log_one] using this
  -- Eventually log log a = log log b + log (1 + log(a/b)/log b).
  -- log a = log b + log (a/b) = log b * (1 + log(a/b)/log b) (when log b ≠ 0).
  -- So log log a = log (log b) + log (1 + log(a/b)/log b),
  -- provided `1 + log(a/b)/log b > 0`, i.e. `log a / log b > 0`,
  -- which holds when log a > 0, log b > 0.
  have hrew :
      ∀ᶠ k in atTop,
        Real.log (Real.log (a k)) =
          Real.log (Real.log (b k)) +
            Real.log (1 + Real.log (a k / b k) / Real.log (b k)) := by
    filter_upwards [ha_pos, hb_pos,
      hlog_a.eventually_gt_atTop (0 : ℝ),
      hlog_b.eventually_gt_atTop (0 : ℝ)] with k hak hbk hloga hlogb
    have hlogb_ne : Real.log (b k) ≠ 0 := ne_of_gt hlogb
    have hfactor_eq : 1 + Real.log (a k / b k) / Real.log (b k) =
        Real.log (a k) / Real.log (b k) := by
      rw [Real.log_div (ne_of_gt hak) (ne_of_gt hbk)]
      field_simp
      ring
    have hfactor_pos : 0 < Real.log (a k) / Real.log (b k) := div_pos hloga hlogb
    -- `log a = log b * (log a / log b)`, so `log log a = log (log b * (log a / log b))
    -- = log log b + log (log a / log b) = log log b + log (1 + small)`.
    have hloga_eq : Real.log (a k) = Real.log (b k) * (Real.log (a k) / Real.log (b k)) := by
      field_simp
    conv_lhs => rw [hloga_eq]
    rw [Real.log_mul hlogb_ne (ne_of_gt hfactor_pos), ← hfactor_eq]
  -- Divide by log log b.
  have h_second :
      Tendsto (fun k =>
          Real.log (1 + Real.log (a k / b k) / Real.log (b k)) /
            Real.log (Real.log (b k))) atTop (𝓝 0) := by
    have := h_log_1plus.div_atTop hll_b
    simpa using this
  have hrewratio :
      ∀ᶠ k in atTop,
        Real.log (Real.log (a k)) / Real.log (Real.log (b k)) =
          1 + Real.log (1 + Real.log (a k / b k) / Real.log (b k)) /
            Real.log (Real.log (b k)) := by
    filter_upwards [hrew, hll_b.eventually_gt_atTop (0 : ℝ)] with k hk hllb
    have hne : Real.log (Real.log (b k)) ≠ 0 := ne_of_gt hllb
    rw [hk]
    field_simp
  have hlim : Tendsto
      (fun k => 1 + Real.log (1 + Real.log (a k / b k) / Real.log (b k)) /
          Real.log (Real.log (b k)))
      atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add h_second
  have : (1 : ℝ) + 0 = 1 := by ring
  rw [← this]
  exact hlim.congr' (hrewratio.mono (fun k hk => hk.symm))

/-- Main workhorse: if `a_k → ∞`, `b_k → ∞`, `a_k / b_k → r`, and `r > 0`, then
`lilNormAux(a_k) / lilNormAux(b_k) → √r`. -/
lemma lilNormAux_ratio_tendsto_of_ratio {a b : ℕ → ℝ} {r : ℝ}
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hab : Tendsto (fun k => a k / b k) atTop (𝓝 r)) (hr : 0 < r) :
    Tendsto (fun k => lilNormAux (a k) / lilNormAux (b k)) atTop
      (𝓝 (Real.sqrt r)) := by
  -- Prove that `(2 a log log a) / (2 b log log b) → r`, then apply sqrt.
  have hll_ratio : Tendsto (fun k => Real.log (Real.log (a k)) /
      Real.log (Real.log (b k))) atTop (𝓝 1) :=
    loglog_ratio_tendsto_one_of_ratio ha hb hab hr
  have hll_b : Tendsto (fun k => Real.log (Real.log (b k))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hb)
  -- `(a / b) * (log log a / log log b) → r * 1`.
  have hratio : Tendsto
      (fun k => (a k / b k) * (Real.log (Real.log (a k)) / Real.log (Real.log (b k))))
      atTop (𝓝 (r * 1)) := hab.mul hll_ratio
  -- Rewrite to `(2 a log log a) / (2 b log log b)`.
  have hbposf : ∀ᶠ k in atTop, (0 : ℝ) < b k := hb.eventually_gt_atTop 0
  have hllbposf : ∀ᶠ k in atTop, (0 : ℝ) < Real.log (Real.log (b k)) :=
    hll_b.eventually_gt_atTop 0
  have hrew : ∀ᶠ k in atTop,
      (a k / b k) * (Real.log (Real.log (a k)) / Real.log (Real.log (b k))) =
      (2 * a k * Real.log (Real.log (a k))) /
        (2 * b k * Real.log (Real.log (b k))) := by
    filter_upwards [hbposf, hllbposf] with k hbk hllb
    have hbne : b k ≠ 0 := ne_of_gt hbk
    have hllne : Real.log (Real.log (b k)) ≠ 0 := ne_of_gt hllb
    field_simp
  have hratio2 : Tendsto
      (fun k => (2 * a k * Real.log (Real.log (a k))) /
        (2 * b k * Real.log (Real.log (b k))))
      atTop (𝓝 r) := by
    have hr1 : r * 1 = r := by ring
    rw [← hr1]
    exact hratio.congr' hrew
  -- Apply sqrt.
  have hsqrt := hratio2.sqrt
  -- Rewrite: sqrt(ratio) = lilNormAux a / lilNormAux b when denominator ≥ 0.
  refine hsqrt.congr' ?_
  have haposf : ∀ᶠ k in atTop, (0 : ℝ) < a k := ha.eventually_gt_atTop 0
  have hllaposf : ∀ᶠ k in atTop, (0 : ℝ) < Real.log (Real.log (a k)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp ha)).eventually_gt_atTop 0
  filter_upwards [haposf, hbposf, hllaposf, hllbposf] with k hak hbk hlla hllb
  have hnum_nn : (0 : ℝ) ≤ 2 * a k * Real.log (Real.log (a k)) := by positivity
  have hden_nn : (0 : ℝ) ≤ 2 * b k * Real.log (Real.log (b k)) := by positivity
  show Real.sqrt ((2 * a k * Real.log (Real.log (a k))) /
      (2 * b k * Real.log (Real.log (b k)))) =
    lilNormAux (a k) / lilNormAux (b k)
  unfold lilNormAux
  exact Real.sqrt_div' _ hden_nn

/-- **Target 1.** Block scale over full scale: the ratio
`lilNormAux(⌊c^(k+1)⌋₊ - ⌊c^k⌋₊) / lilNormAux(⌊c^(k+1)⌋₊)` tends to
`√((c-1)/c)` as `k → ∞`. -/
theorem lilNormAux_block_ratio_tendsto (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun k : ℕ =>
        lilNormAux ((⌊c ^ (k + 1)⌋₊ : ℝ) - (⌊c ^ k⌋₊ : ℝ)) /
          lilNormAux ((⌊c ^ (k + 1)⌋₊ : ℝ)))
      atTop (𝓝 (Real.sqrt ((c - 1) / c))) := by
  have hcpos : (0 : ℝ) < c := zero_lt_one.trans hc
  have hc1pos : (0 : ℝ) < c - 1 := by linarith
  have hr : 0 < (c - 1) / c := div_pos hc1pos hcpos
  -- Let N k = block, M k = ⌊c^(k+1)⌋₊.
  set N : ℕ → ℝ := fun k => (⌊c ^ (k + 1)⌋₊ : ℝ) - (⌊c ^ k⌋₊ : ℝ) with hN_def
  set M : ℕ → ℝ := fun k => (⌊c ^ (k + 1)⌋₊ : ℝ) with hM_def
  have hpow_top : Tendsto (fun k : ℕ => (c : ℝ) ^ (k + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hc).comp (tendsto_add_atTop_nat 1)
  have hM_top : Tendsto M atTop atTop :=
    (floor_pow_tendsto_atTop hc).comp (tendsto_add_atTop_nat 1)
  have hblock_over_pow : Tendsto (fun k : ℕ => N k / c ^ (k + 1))
      atTop (𝓝 ((c - 1) / c)) := block_over_pow_tendsto hc
  have hM_over_pow : Tendsto (fun k : ℕ => M k / c ^ (k + 1)) atTop (𝓝 1) :=
    (floor_pow_div_pow_tendsto hc).comp (tendsto_add_atTop_nat 1)
  -- N → ∞ since N / c^{k+1} → (c-1)/c > 0 and c^{k+1} → ∞.
  have hN_top : Tendsto N atTop atTop := by
    have h : Tendsto (fun k : ℕ => (N k / c ^ (k + 1)) * c ^ (k + 1)) atTop atTop :=
      Filter.Tendsto.pos_mul_atTop hr hblock_over_pow hpow_top
    refine h.congr' ?_
    filter_upwards [hpow_top.eventually_gt_atTop (0 : ℝ)] with k hk
    have hne : (c : ℝ) ^ (k + 1) ≠ 0 := ne_of_gt hk
    field_simp
  -- N k / M k → (c-1)/c.
  have hN_over_M : Tendsto (fun k => N k / M k) atTop (𝓝 ((c - 1) / c)) := by
    have h := hblock_over_pow.div hM_over_pow one_ne_zero
    have hlim : (c - 1) / c / 1 = (c - 1) / c := by ring
    rw [← hlim]
    refine h.congr' ?_
    filter_upwards [hpow_top.eventually_gt_atTop (0 : ℝ)] with k hk
    have hne : (c : ℝ) ^ (k + 1) ≠ 0 := ne_of_gt hk
    show (N k / c ^ (k + 1)) / (M k / c ^ (k + 1)) = N k / M k
    field_simp
  exact lilNormAux_ratio_tendsto_of_ratio hN_top hM_top hN_over_M hr

/-- **Target 2.** Short scale over long scale: the ratio
`lilNormAux(⌊c^k⌋₊) / lilNormAux(⌊c^(k+1)⌋₊)` tends to `1 / √c`. -/
theorem lilNormAux_scale_ratio_tendsto (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun k : ℕ => lilNormAux ((⌊c ^ k⌋₊ : ℝ)) / lilNormAux ((⌊c ^ (k + 1)⌋₊ : ℝ)))
      atTop (𝓝 (1 / Real.sqrt c)) := by
  have hcpos : (0 : ℝ) < c := zero_lt_one.trans hc
  have hr : 0 < (1 : ℝ) / c := one_div_pos.mpr hcpos
  have hN_top : Tendsto (fun k : ℕ => (⌊c ^ k⌋₊ : ℝ)) atTop atTop :=
    floor_pow_tendsto_atTop hc
  have hM_top : Tendsto (fun k : ℕ => (⌊c ^ (k + 1)⌋₊ : ℝ)) atTop atTop :=
    (floor_pow_tendsto_atTop hc).comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun k : ℕ =>
      (⌊c ^ k⌋₊ : ℝ) / (⌊c ^ (k + 1)⌋₊ : ℝ)) atTop (𝓝 (1 / c)) :=
    short_over_long_floor_tendsto hc
  have hmain := lilNormAux_ratio_tendsto_of_ratio hN_top hM_top hratio hr
  -- `sqrt(1/c) = 1/sqrt c` by `Real.sqrt_one_div`.
  have hrewlim : Real.sqrt (1 / c) = 1 / Real.sqrt c := by
    rw [Real.sqrt_div' 1 (le_of_lt hcpos), Real.sqrt_one]
  rw [hrewlim] at hmain
  exact hmain

end Erdos524.Helpers
