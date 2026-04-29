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
import FormalConjectures.ErdosProblems.Helpers.PolynomialSupBlock
import FormalConjectures.ErdosProblems.Helpers.CubicSubseqAsymptotics

/-!
# Old blocks negligible (helper for Erdős 524 upper half, Step H5)

Chojecki's Lemma 16 (Step H5 of the upper-half Borel–Cantelli argument).

On the cubic subsequence `n_m := ⌊exp(m³)⌋`, for any `α ∈ ℝ`, almost surely
the "old block" `polynomialSupBlock a (Icc 1 n_{m-1})` is eventually
dominated by `(1/2) · ε_m · √(n_m)`, where
`ε_m := exp(-α · (log log n_m)^{1/3})` is the small-ball scale.

Structure of this file.

The deterministic core — that the LIL upper envelope `supNorm a n ≤ C √(n·log log n)`
combined with the cubic super-exponential ratio decay dominates the old block
— is captured in the helper `old_blocks_negligible_of_ub`. This takes as a
hypothesis an **LIL-style upper envelope** already specialized to the cubic
subsequence:
```
∀ᶠ m in atTop, polynomialSupBlock a (Icc 1 (n_{m-1})) ω ≤
    2 * √(2 * n_{m-1} * log log n_{m-1})
```
and produces the desired bound. The upstream supply of this envelope is a
thin wrapper around `sharp_upper_envelope_le` from `524.lean` plus
`polynomialSupBlock_Icc_eq_supNorm` (both essentially definitional).

Why parameterize? `supNorm` and `lilNorm` are private to `524.lean`, so the
downstream consumer supplies the LIL bound specialized through
`polynomialSupBlock` (which is public, in `Helpers/PolynomialSupBlock.lean`).

The key sorry-free quantitative piece is `cubicSubseq_sqrt_ratio_decay`
(from `CubicSubseqAsymptotics.lean`), which provides the super-exponential
decay of `√(n_{m-1}) · √(log log n_{m-1}) / (ε_m · √(n_m))`.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Deterministic core of "old blocks negligible".**

Given an upper envelope hypothesis `hLIL` — almost surely, eventually
`polynomialSupBlock a (Icc 1 (n_{m-1})) ω ≤ 2 √(2 · n_{m-1} · log log n_{m-1})`
— we deduce that the old block is eventually bounded by
`(1/2) · ε_m · √(n_m)`, where `ε_m := exp(-α (log log n_m)^{1/3})`.

*Proof.* Write `B := 2 √(2 · n_{m-1} · log log n_{m-1})` and
`D := ε_m · √(n_m)`. Then `B / D = 2 √2 · √(n_{m-1}) · √(log log n_{m-1}) /
(ε_m · √(n_m))`, which tends to `0` as `m → ∞` by
`cubicSubseq_sqrt_ratio_decay`. In particular the ratio is eventually
≤ `1/2`, i.e. `B ≤ (1/2) · D`. Combining with the hypothesis yields the
claim. -/
theorem old_blocks_negligible_of_ub
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (α : ℝ)
    (hLIL : ∀ᵐ ω, ∀ᶠ m : ℕ in atTop,
      polynomialSupBlock a (Finset.Icc 1 (cubicSubseq (m - 1))) ω ≤
        2 * Real.sqrt (2 * (cubicSubseq (m - 1) : ℝ) *
          Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) :
    ∀ᵐ ω, ∀ᶠ m : ℕ in atTop,
      polynomialSupBlock a (Finset.Icc 1 (cubicSubseq (m - 1))) ω
        ≤ (1/2) * Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1:ℝ)/3))
            * Real.sqrt (cubicSubseq m : ℝ) := by
  -- Deterministic ratio decay: the bound 2√(2 · cs(m-1) · log log cs(m-1))
  -- divided by ε_m · √(cs m) tends to 0.
  -- More directly: 2 √2 times `cubicSubseq_sqrt_ratio_decay α` tends to 0,
  -- so eventually ≤ 1/2, hence B ≤ (1/2) D.
  have hdecay := _root_.Erdos524.Helpers.cubicSubseq_sqrt_ratio_decay α
  -- Scale by constant 2√2.
  have hscale : Tendsto (fun m : ℕ =>
      2 * Real.sqrt 2 *
        (Real.sqrt (cubicSubseq (m - 1)) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1)))) /
          (Real.exp (-α * (Real.log (Real.log (cubicSubseq m))) ^ ((1:ℝ)/3))
              * Real.sqrt (cubicSubseq m))))
        atTop (𝓝 (2 * Real.sqrt 2 * 0)) :=
    hdecay.const_mul _
  -- Simplify the limit `2√2 · 0 = 0`.
  have hscale' : Tendsto (fun m : ℕ =>
      2 * Real.sqrt 2 *
        (Real.sqrt (cubicSubseq (m - 1)) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1)))) /
          (Real.exp (-α * (Real.log (Real.log (cubicSubseq m))) ^ ((1:ℝ)/3))
              * Real.sqrt (cubicSubseq m))))
        atTop (𝓝 0) := by simpa using hscale
  -- Eventually the scaled expression is < 1/2 (in absolute value); we just
  -- need it ≤ 1/2. Use `Tendsto.eventually_const_le` or a direct argument via
  -- `Metric.tendsto_nhds`.
  have hrat_le_half : ∀ᶠ m : ℕ in atTop,
      2 * Real.sqrt 2 *
        (Real.sqrt (cubicSubseq (m - 1)) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1)))) /
          (Real.exp (-α * (Real.log (Real.log (cubicSubseq m))) ^ ((1:ℝ)/3))
              * Real.sqrt (cubicSubseq m))) ≤ (1/2 : ℝ) := by
    -- Tendsto to 0 implies eventually ≤ 1/2 (via |·| < 1/2 ⇒ · ≤ 1/2).
    have htends := Metric.tendsto_nhds.mp hscale' (1/2) (by norm_num : (0:ℝ) < 1/2)
    filter_upwards [htends] with m hm
    rw [Real.dist_eq, sub_zero] at hm
    -- hm: |…| < 1/2 implies … ≤ 1/2 via `le_of_abs_le` (need `|·| ≤ 1/2`).
    exact le_of_lt (lt_of_abs_lt hm)
  -- Eventually cubicSubseq m > 0.
  have hcs_m_pos_ev : ∀ᶠ m : ℕ in atTop, 0 < cubicSubseq m := by
    have := cubicSubseq_tendsto_atTop.eventually_gt_atTop 0
    exact this
  -- Combine with the upstream LIL a.s. eventual bound.
  filter_upwards [hLIL] with ω hω
  filter_upwards [hω, hrat_le_half, hcs_m_pos_ev] with m hω_m hrat hcs_pos
  -- Abbreviate.
  set B : ℝ := 2 * Real.sqrt (2 * (cubicSubseq (m - 1) : ℝ) *
      Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) with hB_def
  set D : ℝ := Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1:ℝ)/3)) *
      Real.sqrt (cubicSubseq m : ℝ) with hD_def
  -- D > 0.
  have hexp_pos :
      0 < Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1:ℝ)/3)) :=
    Real.exp_pos _
  have hsq_m_nn : 0 ≤ Real.sqrt (cubicSubseq m : ℝ) := Real.sqrt_nonneg _
  have hD_nn : 0 ≤ D := by
    rw [hD_def]; exact mul_nonneg hexp_pos.le hsq_m_nn
  -- Unpack B in terms of √(cs(m-1)) and √(log log cs(m-1)).
  -- Algebra: B = 2 · √2 · √(cs(m-1)) · √(log log cs(m-1)).
  have hB_eq : B = 2 * Real.sqrt 2 *
      (Real.sqrt (cubicSubseq (m - 1) : ℝ) *
        Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) := by
    rw [hB_def]
    rcases le_or_gt 0 (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) with hll_nn | hll_neg
    · -- standard case.
      have hcs_nn : (0 : ℝ) ≤ (cubicSubseq (m - 1) : ℝ) := by exact_mod_cast Nat.zero_le _
      have h2nn : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h_mul_nn : 0 ≤ 2 * (cubicSubseq (m - 1) : ℝ) := mul_nonneg h2nn hcs_nn
      rw [show (2 * (cubicSubseq (m - 1) : ℝ) *
            Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) =
            2 * ((cubicSubseq (m - 1) : ℝ) *
              Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) by ring]
      rw [Real.sqrt_mul h2nn]
      rw [Real.sqrt_mul hcs_nn]
      ring
    · -- If `log log cs(m-1) < 0`, then `2 cs log log = 2 cs · (negative)`. The LHS
      -- sqrt of a negative is 0 (Real.sqrt convention). The RHS product has a
      -- sqrt of negative = 0. So both sides are 0.
      have hcs_nn : (0 : ℝ) ≤ (cubicSubseq (m - 1) : ℝ) := by exact_mod_cast Nat.zero_le _
      have hprod_nonpos : 2 * (cubicSubseq (m - 1) : ℝ) *
          Real.log (Real.log (cubicSubseq (m - 1) : ℝ)) ≤ 0 := by
        have h2cs_nn : 0 ≤ 2 * (cubicSubseq (m - 1) : ℝ) := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos h2cs_nn hll_neg.le
      rw [Real.sqrt_eq_zero'.mpr hprod_nonpos]
      rw [Real.sqrt_eq_zero'.mpr hll_neg.le]
      ring
  -- D > 0 (since cs m > 0 eventually).
  have hcs_real_pos : (0 : ℝ) < (cubicSubseq m : ℝ) := by exact_mod_cast hcs_pos
  have hsq_m_pos : 0 < Real.sqrt (cubicSubseq m : ℝ) := Real.sqrt_pos.mpr hcs_real_pos
  have hD_pos : 0 < D := by rw [hD_def]; exact mul_pos hexp_pos hsq_m_pos
  have hD_ne : D ≠ 0 := hD_pos.ne'
  -- Main chain.
  have hkey :
      2 * Real.sqrt 2 *
        (Real.sqrt (cubicSubseq (m - 1) : ℝ) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) ≤ (1/2 : ℝ) * D := by
    have hprod_eq : 2 * Real.sqrt 2 *
        (Real.sqrt (cubicSubseq (m - 1) : ℝ) *
          Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) =
        (2 * Real.sqrt 2 *
          (Real.sqrt (cubicSubseq (m - 1) : ℝ) *
            Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ))) / D)) * D := by
      field_simp
    rw [hprod_eq]
    have hmul_le := mul_le_mul_of_nonneg_right hrat hD_pos.le
    linarith
  calc polynomialSupBlock a (Finset.Icc 1 (cubicSubseq (m - 1))) ω
      ≤ B := hω_m
    _ = 2 * Real.sqrt 2 *
          (Real.sqrt (cubicSubseq (m - 1) : ℝ) *
            Real.sqrt (Real.log (Real.log (cubicSubseq (m - 1) : ℝ)))) := hB_eq
    _ ≤ (1/2 : ℝ) * D := hkey
    _ = (1/2 : ℝ) *
          Real.exp (-α * (Real.log (Real.log (cubicSubseq m : ℝ))) ^ ((1:ℝ)/3)) *
          Real.sqrt (cubicSubseq m : ℝ) := by rw [hD_def]; ring

end Erdos524.Helpers
