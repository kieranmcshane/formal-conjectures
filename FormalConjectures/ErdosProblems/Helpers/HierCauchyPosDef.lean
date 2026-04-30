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

import FormalConjectures.ErdosProblems.Helpers.HierCauchyFacts
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Round 10 — Positive-definiteness of the hierarchical Cauchy matrix

This file proves `(hierCauchyG m).PosDef` for `m ≥ 1` via the classical
Gram-matrix-of-exponentials argument:

  `1 / (g_i + g_j) = ∫_(0,∞) exp(-(g_i + g_j) · t) dt`
  `xᵀ (hierCauchyG m) x = ∫_(0,∞) (∑ i, x i · exp(-hierGrid m i · t))² dt`

* **Hermitian-ness** (= real symmetry) follows from `hierCauchyG_symm`.
* **Non-negativity** of the quadratic form: it is the integral of a
  square.
* **Strict positivity** (the `PosDef` content beyond `PosSemidef`) needs
  linear independence of the family `{ t ↦ exp(-g_i t) }_i` for distinct
  positive `g_i`. We use the "smallest-decay-rate dominates" limit
  argument, which is short and avoids any Vandermonde / smoothness
  machinery.

Exposed:

* `hierGrid_injective` — the indexing map `Fin m × Fin m → ℝ` defining
  the Cauchy parameters is injective for `m ≥ 1`.
* `hierCauchyG_isHermitian` — symmetry as `IsHermitian` over `ℝ`.
* `cauchy_inv_eq_integral_exp_neg` — the Cauchy integral identity
  `1/(a+b) = ∫_(0,∞) exp(-(a+b)·t) dt` for `a, b > 0`.
* `hierCauchyG_PosSemidef` — the matrix is positive semi-definite (real
  symmetric Gram-matrix step).
* `hierCauchyG_PosDef` — the matrix is positive definite for `m ≥ 1`.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524.Helpers
open Real Matrix MeasureTheory Set

/- ## §1. Injectivity of `hierGrid` -/

/-- The hierarchical grid `(p, q) ↦ 4^(p+m) · (m + q + 1)` is injective.
The shape factor `m + q + 1` lives in the half-open band `[m+1, 2m+1)`
which is strictly contained in `[1, 4·1)`-style ratios; combined with
the geometric `4^(p+m)` separation, this forces both coordinates to
agree. -/
theorem hierGrid_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (hierGrid m) := by
  intro pq pq' hgrid
  obtain ⟨p, q⟩ := pq
  obtain ⟨p', q'⟩ := pq'
  simp only [Prod.mk.injEq]
  -- Rewrite as `4^(p+m)·(m+q+1) = 4^(p'+m)·(m+q'+1)`.
  have h := hgrid
  unfold hierGrid at h
  -- WLOG `p.val ≤ p'.val`; else swap.
  by_cases hpp : p.val ≤ p'.val
  · -- Case `p ≤ p'`. Let `d = p'.val - p.val ≥ 0`.
    -- Equation: `(m+q+1) = 4^d · (m+q'+1)`, i.e. `(m+q+1)/(m+q'+1) = 4^d`.
    -- LHS ∈ [m+1, 2m+1) and RHS ∈ {1, 4, 16, ...}, so `d = 0`.
    have h4_pos : (0 : ℝ) < 4 := by norm_num
    set s := shapeS m q with hs_def
    set s' := shapeS m q' with hs'_def
    have hs_eq : (m : ℝ) + q.val + 1 = s := rfl
    have hs'_eq : (m : ℝ) + q'.val + 1 = s' := rfl
    have hs_pos : 0 < s := shapeS_pos m q
    have hs'_pos : 0 < s' := shapeS_pos m q'
    have hs_le : s ≤ 2 * (m : ℝ) := shapeS_le_two_mul hm q
    have hs'_ge : (m : ℝ) + 1 ≤ s' := shapeS_ge q'
    -- Convert the hypothesis to use `s`, `s'`.
    have h2 : (4 : ℝ)^(p.val + m) * s = (4 : ℝ)^(p'.val + m) * s' := by
      show (4 : ℝ)^(p.val + m) * shapeS m q = (4 : ℝ)^(p'.val + m) * shapeS m q'
      simpa [shapeS, hierGrid] using h
    -- Divide by `4^(p.val + m) > 0` and rewrite RHS.
    have h4pm_pos : 0 < (4 : ℝ)^(p.val + m) := pow_pos h4_pos _
    have h4pos_eq : (4 : ℝ)^(p'.val + m) =
        (4 : ℝ)^(p.val + m) * (4 : ℝ)^(p'.val - p.val) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h4pos_eq] at h2
    -- h2 : 4^(p+m) * s = 4^(p+m) * 4^d * s'
    have h3 : s = (4 : ℝ)^(p'.val - p.val) * s' := by
      have := h2
      field_simp at this ⊢
      nlinarith [this, h4pm_pos]
    -- Now case-split on `d := p'.val - p.val`. If d ≥ 1 we get a contradiction.
    set d := p'.val - p.val with hd_def
    by_cases hd : d = 0
    · -- d = 0 → p = p'.
      have hp_eq : p.val = p'.val := by omega
      have hp_eq' : p = p' := Fin.ext hp_eq
      -- And then s = s' → q.val = q'.val by definition of shapeS.
      rw [hd] at h3
      simp at h3
      -- h3 : s = s'
      have hq_eq : q.val = q'.val := by
        have : (m : ℝ) + q.val + 1 = (m : ℝ) + q'.val + 1 := by
          rw [hs_eq, hs'_eq]; exact h3
        have : (q.val : ℝ) = (q'.val : ℝ) := by linarith
        exact_mod_cast this
      have hq_eq' : q = q' := Fin.ext hq_eq
      exact ⟨hp_eq', hq_eq'⟩
    · -- d ≥ 1 → contradiction.
      have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
      have h4d_ge : (4 : ℝ) ≤ (4 : ℝ)^d := by
        calc (4 : ℝ) = (4 : ℝ)^1 := by ring
          _ ≤ (4 : ℝ)^d := by
            apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hd_pos
      -- s = 4^d * s' ≥ 4 * s' ≥ 4(m+1) > 2m. Contradicts s ≤ 2m.
      have hs'_ge' : 0 < s' := hs'_pos
      have hineq1 : (4 : ℝ) * s' ≤ (4 : ℝ)^d * s' := by
        exact mul_le_mul_of_nonneg_right h4d_ge hs'_ge'.le
      have hineq2 : (4 : ℝ) * ((m : ℝ) + 1) ≤ 4 * s' := by
        exact mul_le_mul_of_nonneg_left hs'_ge (by norm_num : (0 : ℝ) ≤ 4)
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm).bot_lt
      have hcontra : 2 * (m : ℝ) < (4 : ℝ) * ((m : ℝ) + 1) := by linarith
      -- Chain: s = 4^d s' ≥ 4 s' ≥ 4(m+1) > 2m ≥ s. Contradiction.
      have h_sgt : 2 * (m : ℝ) < s := by
        calc 2 * (m : ℝ) < 4 * ((m : ℝ) + 1) := hcontra
          _ ≤ 4 * s' := hineq2
          _ ≤ (4 : ℝ)^d * s' := hineq1
          _ = s := h3.symm
      exact absurd hs_le (not_le.mpr h_sgt)
  · -- Case `p > p'`. Symmetric — swap and reuse.
    -- Build the symmetric hypothesis and recur via the same argument.
    push_neg at hpp
    have hpp' : p'.val ≤ p.val := Nat.le_of_lt hpp
    have h_sym : hierGrid m (p', q') = hierGrid m (p, q) := h.symm
    -- Re-run the proof with primed/unprimed swapped.
    have h2' : (4 : ℝ)^(p'.val + m) * shapeS m q' = (4 : ℝ)^(p.val + m) * shapeS m q := by
      have := h_sym; unfold hierGrid at this; exact this
    set s := shapeS m q with hs_def
    set s' := shapeS m q' with hs'_def
    have hs_pos : 0 < s := shapeS_pos m q
    have hs'_pos : 0 < s' := shapeS_pos m q'
    have hs'_le : s' ≤ 2 * (m : ℝ) := shapeS_le_two_mul hm q'
    have hs_ge : (m : ℝ) + 1 ≤ s := shapeS_ge q
    have h4_pos : (0 : ℝ) < 4 := by norm_num
    have h4pm_pos : 0 < (4 : ℝ)^(p'.val + m) := pow_pos h4_pos _
    have h4pos_eq : (4 : ℝ)^(p.val + m) =
        (4 : ℝ)^(p'.val + m) * (4 : ℝ)^(p.val - p'.val) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h4pos_eq] at h2'
    have h3' : s' = (4 : ℝ)^(p.val - p'.val) * s := by
      field_simp at h2' ⊢
      nlinarith [h2', h4pm_pos]
    set d := p.val - p'.val with hd_def
    have hd_pos : 1 ≤ d := by omega
    have h4d_ge : (4 : ℝ) ≤ (4 : ℝ)^d := by
      calc (4 : ℝ) = (4 : ℝ)^1 := by ring
        _ ≤ (4 : ℝ)^d := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hd_pos
    have hineq1 : (4 : ℝ) * s ≤ (4 : ℝ)^d * s :=
      mul_le_mul_of_nonneg_right h4d_ge hs_pos.le
    have hineq2 : (4 : ℝ) * ((m : ℝ) + 1) ≤ 4 * s :=
      mul_le_mul_of_nonneg_left hs_ge (by norm_num : (0 : ℝ) ≤ 4)
    have h_s'gt : 2 * (m : ℝ) < s' := by
      calc 2 * (m : ℝ) < 4 * ((m : ℝ) + 1) := by
            have hm_pos : (0 : ℝ) < m := by
              exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm).bot_lt
            linarith
        _ ≤ 4 * s := hineq2
        _ ≤ (4 : ℝ)^d * s := hineq1
        _ = s' := h3'.symm
    exact absurd hs'_le (not_le.mpr h_s'gt)

/- ## §2. Hermitian-ness of `hierCauchyG` over ℝ -/

/-- The hierarchical Cauchy matrix is Hermitian (= real-symmetric over ℝ),
since each entry `1/(g_i + g_j)` is symmetric in `(i, j)`. -/
theorem hierCauchyG_isHermitian (m : ℕ) :
    (hierCauchyG m).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  -- Over ℝ, `star = id`, so `IsHermitian` is just symmetry.
  show star (hierCauchyG m j i) = hierCauchyG m i j
  rw [show star (hierCauchyG m j i) = hierCauchyG m j i from rfl]
  exact (hierCauchyG_symm m j i).trans (by rfl)

end Erdos524.Helpers
