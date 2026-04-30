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

## Consumer-facing API (Round 10)

Headline theorems:

* `hierCauchyG_isHermitian` — symmetry as `IsHermitian` over `ℝ`.
* `hierCauchyG_PosSemidef` — the matrix is positive semi-definite.
* `hierCauchyG_PosDef` — the matrix is positive definite for `m ≥ 1`.

Building blocks (often useful directly):

* `hierGrid_injective` — the indexing map `Fin m × Fin m → ℝ` defining
  the Cauchy parameters is injective for `m ≥ 1`.
* `cauchy_inv_eq_integral_exp_neg` — the Cauchy integral identity
  `1/(a+b) = ∫_(0,∞) exp(-(a+b)·t) dt` for `a, b > 0`.
* `hierCauchyG_quadForm_eq_integral_sq` — the Gram representation
  `xᵀ M x = ∫ (∑ x_i exp(-g_i t))² dt`.
* `expProfile m x t := ∑ i, x i · exp(-(hierGrid m i) · t)` — the
  exponential profile whose squared integral is the quadratic form.

Mathlib-PR-quality general lemma:

* `PosDef_of_PosSemidef_of_det_pos` — for any real Hermitian PSD matrix
  with strictly positive determinant, the matrix is PosDef. (This is the
  short-circuit that bypasses the analytic strict-positivity argument.)

Corollaries:

* `hierCauchyG_isUnit` — invertibility for `m ≥ 1`.
* `hierCauchyG_inv_PosDef` — the inverse is also PosDef.
* `hierCauchyG_quadForm_pos_of_ne_zero` — strict positivity `0 < xᵀMx`
  for `x ≠ 0`.
* `expProfile_sq_integral_pos_of_ne_zero` — recovers the analytic
  strict-positivity result.
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

/- ## §3. Cauchy integral identity `1/(a+b) = ∫₀^∞ exp(-(a+b) t) dt` -/

/-- Real version of the Cauchy integral identity: for `c > 0`,
`∫_(0,∞) exp(-c t) dt = 1/c`. Direct corollary of Mathlib's
`integral_exp_mul_Ioi` applied with `a = -c < 0`. -/
theorem integral_exp_neg_mul_Ioi_zero {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi 0, Real.exp (-c * t) = 1 / c := by
  have h := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  -- h : ∫ x in Ioi 0, rexp (-c * x) = -rexp (-c * 0) / -c
  rw [show (-c : ℝ) * (0 : ℝ) = 0 from by ring, Real.exp_zero] at h
  -- Now h : ∫ x in Ioi 0, rexp (-c * x) = -1 / -c
  rw [h]
  have hc_ne : c ≠ 0 := ne_of_gt hc
  field_simp

/-- The Cauchy integral identity: for `a, b > 0`,
`1/(a + b) = ∫_(0,∞) exp(-(a+b) t) dt`. This is the analytic core of the
Cauchy-matrix Gram representation. -/
theorem cauchy_inv_eq_integral_exp_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / (a + b) = ∫ t : ℝ in Ioi 0, Real.exp (-(a + b) * t) := by
  have hab : 0 < a + b := add_pos ha hb
  rw [integral_exp_neg_mul_Ioi_zero hab]

/-- Integrability of `t ↦ exp(-c t)` on `Ioi 0` for `c > 0`. -/
theorem integrableOn_exp_neg_mul_Ioi_zero {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0

/- ## §4. Gram-matrix integral representation

The key identity `xᵀ M x = ∫_(0,∞) (∑ i, x i · exp(-g_i t))²` is broken
into pieces: scalar multiplication of integrals, exchanging integral
and finite sum, factoring `(∑ a_i)² = ∑∑ a_i a_j`, and combining
exponentials. -/

/-- The "exponential profile" `f x t := ∑ i, x i · exp(-(hierGrid m i) · t)`,
the function whose integrated square equals the quadratic form. -/
noncomputable def expProfile (m : ℕ) (x : Fin m × Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin m × Fin m, x i * Real.exp (-(hierGrid m i) * t)

/-- `expProfile` evaluated at `t = 0` equals `∑ i, x i`. -/
theorem expProfile_at_zero (m : ℕ) (x : Fin m × Fin m → ℝ) :
    expProfile m x 0 = ∑ i : Fin m × Fin m, x i := by
  unfold expProfile
  simp [Real.exp_zero]

/-- `expProfile` is continuous in `t`. -/
theorem expProfile_continuous (m : ℕ) (x : Fin m × Fin m → ℝ) :
    Continuous (expProfile m x) := by
  unfold expProfile
  apply continuous_finset_sum
  intro i _
  have h_inner : Continuous fun t : ℝ => -(hierGrid m i) * t :=
    continuous_const.mul continuous_id'
  exact continuous_const.mul (Real.continuous_exp.comp h_inner)

/-- Integrability of each summand `t ↦ exp(-(g_i + g_j) t)` on `Ioi 0`. -/
theorem integrableOn_exp_neg_sum_Ioi_zero (m : ℕ) (i j : Fin m × Fin m) :
    IntegrableOn (fun t : ℝ => Real.exp (-(hierGrid m i + hierGrid m j) * t)) (Ioi 0) :=
  integrableOn_exp_neg_mul_Ioi_zero (hierGrid_sum_pos m i j)

/-- Integrability of the scaled summand `t ↦ x i * x j * exp(-(g_i + g_j) t)`. -/
theorem integrableOn_pair_term (m : ℕ) (x : Fin m × Fin m → ℝ) (i j : Fin m × Fin m) :
    IntegrableOn
      (fun t : ℝ => x i * x j * Real.exp (-(hierGrid m i + hierGrid m j) * t))
      (Ioi 0) := by
  exact (integrableOn_exp_neg_sum_Ioi_zero m i j).const_mul (x i * x j)

/-- Each per-pair Cauchy entry equals the integral of the scaled exponential. -/
theorem hierCauchyG_entry_eq_integral (m : ℕ) (i j : Fin m × Fin m) :
    hierCauchyG m i j =
      ∫ t : ℝ in Ioi 0, Real.exp (-(hierGrid m i + hierGrid m j) * t) := by
  rw [hierCauchyG_apply]
  exact cauchy_inv_eq_integral_exp_neg (hierGrid_pos m i) (hierGrid_pos m j)

/-- The factored form: `exp(-(g_i + g_j) t) = exp(-g_i t) * exp(-g_j t)`. -/
theorem exp_neg_sum_factor (g h t : ℝ) :
    Real.exp (-(g + h) * t) = Real.exp (-g * t) * Real.exp (-h * t) := by
  rw [← Real.exp_add]; ring_nf

/-- Quadratic-form-as-integral-of-square identity (the heart of the Gram
representation). For all `x : Fin m × Fin m → ℝ`,
`∑ i ∑ j, x i * (hierCauchyG m i j) * x j = ∫_(0,∞) (expProfile m x t)² dt`. -/
theorem hierCauchyG_quadForm_eq_integral_sq (m : ℕ) (x : Fin m × Fin m → ℝ) :
    ∑ i, ∑ j, x i * hierCauchyG m i j * x j =
      ∫ t : ℝ in Ioi 0, (expProfile m x t)^2 := by
  -- Step 1: rewrite each entry as the integral.
  have h_entry_eq : ∀ i j : Fin m × Fin m,
      x i * hierCauchyG m i j * x j =
        ∫ t : ℝ in Ioi 0, x i * x j *
          Real.exp (-(hierGrid m i + hierGrid m j) * t) := by
    intro i j
    rw [hierCauchyG_entry_eq_integral m i j]
    rw [MeasureTheory.integral_const_mul]
    ring
  -- Step 2: substitute into the double sum and exchange with integral.
  calc ∑ i, ∑ j, x i * hierCauchyG m i j * x j
      = ∑ i, ∑ j, ∫ t : ℝ in Ioi 0, x i * x j *
          Real.exp (-(hierGrid m i + hierGrid m j) * t) := by
        congr 1; ext i; congr 1; ext j; exact h_entry_eq i j
    _ = ∫ t : ℝ in Ioi 0, ∑ i, ∑ j, x i * x j *
          Real.exp (-(hierGrid m i + hierGrid m j) * t) := by
        -- Pull the inner integral out of ∑ j first, then the outer.
        have step1 : ∀ i : Fin m × Fin m,
            ∑ j : Fin m × Fin m,
              ∫ t : ℝ in Ioi 0,
                x i * x j * Real.exp (-(hierGrid m i + hierGrid m j) * t) =
            ∫ t : ℝ in Ioi 0,
              ∑ j : Fin m × Fin m,
                x i * x j * Real.exp (-(hierGrid m i + hierGrid m j) * t) := by
          intro i
          rw [← integral_finset_sum]
          intro j _
          exact integrableOn_pair_term m x i j
        simp_rw [step1]
        rw [← integral_finset_sum]
        intro i _
        apply integrable_finset_sum
        intro j _
        exact integrableOn_pair_term m x i j
    _ = ∫ t : ℝ in Ioi 0, (expProfile m x t)^2 := by
        congr 1; ext t
        unfold expProfile
        -- ∑ i ∑ j, x i x j exp(-(g_i+g_j)t) = (∑ i, x i exp(-g_i t))^2
        have h_factor : ∀ i j : Fin m × Fin m,
            x i * x j * Real.exp (-(hierGrid m i + hierGrid m j) * t) =
              (x i * Real.exp (-(hierGrid m i) * t)) *
                (x j * Real.exp (-(hierGrid m j) * t)) := by
          intro i j
          rw [exp_neg_sum_factor]; ring
        simp_rw [h_factor]
        rw [sq, ← Finset.sum_mul_sum]

/- ## §5. Non-negativity → `PosSemidef` -/

/-- Integrability of the squared profile: `t ↦ (∑ x_i exp(-g_i t))²`.

The squared profile expands to a finite double sum of integrable
exponentials, so it is itself integrable. -/
theorem integrableOn_expProfile_sq (m : ℕ) (x : Fin m × Fin m → ℝ) :
    IntegrableOn (fun t => (expProfile m x t)^2) (Ioi 0) := by
  -- Expand the square as a finite sum of pair-products.
  have h_eq : (fun t => (expProfile m x t)^2) =
      fun t => ∑ i : Fin m × Fin m, ∑ j : Fin m × Fin m,
        x i * x j * Real.exp (-(hierGrid m i + hierGrid m j) * t) := by
    ext t
    unfold expProfile
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [exp_neg_sum_factor]; ring
  rw [h_eq]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact integrableOn_pair_term m x i j

/-- The hierarchical Cauchy matrix is positive semi-definite (over ℝ). -/
theorem hierCauchyG_PosSemidef (m : ℕ) :
    (hierCauchyG m).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hierCauchyG_isHermitian m, ?_⟩
  intro x
  -- Over ℝ, `star x = x`. Reduce `x ⬝ᵥ M *ᵥ x` to `∑ i ∑ j, x i * M i j * x j`.
  show 0 ≤ x ⬝ᵥ (hierCauchyG m) *ᵥ x
  have h_quad : x ⬝ᵥ (hierCauchyG m) *ᵥ x =
      ∑ i, ∑ j, x i * hierCauchyG m i j * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_quad, hierCauchyG_quadForm_eq_integral_sq m x]
  -- `∫ (expProfile m x t)² dt ≥ 0`.
  apply MeasureTheory.integral_nonneg
  intro t
  exact sq_nonneg _

/- ## §6. Strict positivity (PosDef) via PosSemidef + det > 0

The eigenvalue characterization `posDef_iff_eigenvalues_pos` reduces
PosDef-ness to "all eigenvalues > 0". For a real Hermitian PosSemidef
matrix, all eigenvalues are `≥ 0`. If additionally the determinant
(= product of eigenvalues) is strictly positive, then no eigenvalue
can be zero, so all are strictly positive — hence PosDef.

The hierarchical Cauchy matrix has strictly positive determinant for
`m ≥ 1` by `hierCauchyG_det_pos`, so this argument applies. This
sidesteps the analytic strict-positivity-of-quadratic-form argument
(which would require linear independence of `{exp(-g_i ·)}` for distinct
positive `g_i`) entirely. -/

/-- For a real Hermitian PosSemidef matrix with strictly positive
determinant, all eigenvalues are strictly positive.

(Mathlib-PR-shaped lemma: this could be upstreamed as a general
`Matrix.PosSemidef.eigenvalues_pos_of_det_pos`. The proof is short:
the eigenvalues product equals the determinant, all are non-negative
by PSD, and a product of non-negative reals is positive iff none is
zero.) -/
theorem eigenvalues_pos_of_PosSemidef_of_det_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hH : A.IsHermitian) (hPSD : A.PosSemidef) (hDet : 0 < A.det)
    (i : n) : 0 < hH.eigenvalues i := by
  -- All eigenvalues are ≥ 0 from PSD.
  have h_nonneg : ∀ j, 0 ≤ hH.eigenvalues j := fun j => by
    have := hPSD.eigenvalues_nonneg j
    -- `hPSD.eigenvalues_nonneg j` returns `0 ≤ hPSD.1.eigenvalues j`,
    -- but `hPSD.1 = hH` since both encode the Hermitian-ness.
    have h_eq : hPSD.1 = hH := Subsingleton.elim _ _
    rw [h_eq] at this
    exact this
  -- The product of eigenvalues is `det > 0`.
  have h_prod : 0 < ∏ j, hH.eigenvalues j := by
    have h_eq := hH.det_eq_prod_eigenvalues
    -- For 𝕜 = ℝ, the coercion `(eigenvalues j : ℝ)` is identity.
    push_cast at h_eq
    rw [h_eq] at hDet
    exact hDet
  -- If `eigenvalues i = 0`, the product would be 0, contradicting `h_prod > 0`.
  have h_ne : hH.eigenvalues i ≠ 0 := by
    intro h_eq_zero
    have h_zero : ∏ j, hH.eigenvalues j = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i) h_eq_zero
    linarith
  -- Combine `0 ≤` and `≠ 0` to get `0 <`.
  exact lt_of_le_of_ne (h_nonneg i) (Ne.symm h_ne)

/-- General-form `PosSemidef + det > 0 ⇒ PosDef` over ℝ. This is the
key short-circuit that bypassed the analytic strict-positivity argument
in our PosDef derivation; it is Mathlib-PR-quality and could replace
significantly more elaborate arguments anywhere a PSD-with-positive-det
matrix needs to be shown PosDef. -/
theorem PosDef_of_PosSemidef_of_det_pos
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hPSD : A.PosSemidef) (hDet : 0 < A.det) : A.PosDef := by
  have hH : A.IsHermitian := hPSD.isHermitian
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  exact eigenvalues_pos_of_PosSemidef_of_det_pos hH hPSD hDet i

/-- The hierarchical Cauchy matrix is positive definite for `m ≥ 1`. -/
theorem hierCauchyG_PosDef (m : ℕ) (hm : 1 ≤ m) :
    (hierCauchyG m).PosDef := by
  classical
  exact PosDef_of_PosSemidef_of_det_pos (hierCauchyG_PosSemidef m)
    (hierCauchyG_det_pos m hm)

/- ## §7. Corollaries of PosDef -/

/-- The hierarchical Cauchy matrix is invertible for `m ≥ 1`. -/
theorem hierCauchyG_isUnit (m : ℕ) (hm : 1 ≤ m) : IsUnit (hierCauchyG m) := by
  classical
  exact (hierCauchyG_PosDef m hm).isUnit

/-- The inverse of the hierarchical Cauchy matrix is also positive definite. -/
theorem hierCauchyG_inv_PosDef (m : ℕ) (hm : 1 ≤ m) :
    ((hierCauchyG m)⁻¹).PosDef := by
  classical
  exact (hierCauchyG_PosDef m hm).inv

/-- Strict positivity of the quadratic form: for `m ≥ 1` and `x ≠ 0`,
the quadratic form `xᵀ (hierCauchyG m) x` is strictly positive. -/
theorem hierCauchyG_quadForm_pos_of_ne_zero (m : ℕ) (hm : 1 ≤ m)
    {x : Fin m × Fin m → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (hierCauchyG m) *ᵥ x :=
  (hierCauchyG_PosDef m hm).dotProduct_mulVec_pos hx

/-- Strict positivity of the quadratic-form integral. For `m ≥ 1` and
`x ≠ 0`, `∫_(0,∞) (expProfile m x t)² dt > 0`. -/
theorem expProfile_sq_integral_pos_of_ne_zero (m : ℕ) (hm : 1 ≤ m)
    {x : Fin m × Fin m → ℝ} (hx : x ≠ 0) :
    0 < ∫ t : ℝ in Ioi 0, (expProfile m x t)^2 := by
  -- Apply hierCauchyG_quadForm_pos_of_ne_zero combined with the integral
  -- representation `xᵀ M x = ∫ (expProfile m x t)² dt`.
  have hdot := hierCauchyG_quadForm_pos_of_ne_zero m hm hx
  have h_quad : x ⬝ᵥ (hierCauchyG m) *ᵥ x =
      ∑ i, ∑ j, x i * hierCauchyG m i j * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_quad, hierCauchyG_quadForm_eq_integral_sq m x] at hdot
  exact hdot

/-- Sanity-check example: the `m = 1` case of `hierCauchyG_PosDef`. The
matrix is the `1 × 1` matrix with single entry `1 / (2·hierGrid 1 (0,0))`,
which is strictly positive. -/
example : (hierCauchyG 1).PosDef := hierCauchyG_PosDef 1 (by norm_num)

/-- Sanity-check example: the `m = 2` case of `hierCauchyG_PosDef`. -/
example : (hierCauchyG 2).PosDef := hierCauchyG_PosDef 2 (by norm_num)

/-- Sanity-check example: the inverse is also PosDef. -/
example : ((hierCauchyG 1)⁻¹).PosDef := hierCauchyG_inv_PosDef 1 (by norm_num)

/- ## §8. Abstract Cauchy matrix — Mathlib-PR-shaped

Generalises the entire Round 10 chain to an arbitrary index type and
parameter family `g : n → ℝ` with `g i > 0`. The proof structure is
identical: integral identity → Gram representation → PosSemidef. -/

/-- The abstract Cauchy matrix `C i j := 1 / (g i + g j)` for any
parameter family `g : n → ℝ`. -/
noncomputable def cauchyMatrix {n : Type*} [Fintype n] (g : n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => 1 / (g i + g j)

/-- The hierarchical Cauchy matrix is a special case of `cauchyMatrix`
applied to `hierGrid m`. -/
theorem hierCauchyG_eq_cauchyMatrix (m : ℕ) :
    hierCauchyG m = cauchyMatrix (hierGrid m) := rfl

/-- The abstract Cauchy matrix is symmetric (Hermitian over ℝ) — every
entry `1/(g_i + g_j)` is symmetric in `(i, j)`. -/
theorem cauchyMatrix_isHermitian {n : Type*} [Fintype n] (g : n → ℝ) :
    (cauchyMatrix g).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (cauchyMatrix g j i) = cauchyMatrix g i j
  simp only [cauchyMatrix, Matrix.of_apply]
  rw [show star ((1 : ℝ) / (g j + g i)) = 1 / (g j + g i) from rfl, add_comm]

/-- For positive parameters `g_i > 0`, the abstract Cauchy matrix is
positive semi-definite. Same proof as `hierCauchyG_PosSemidef`,
abstracted to general `g`. -/
theorem cauchyMatrix_PosSemidef {n : Type*} [Fintype n] {g : n → ℝ}
    (hg : ∀ i, 0 < g i) :
    (cauchyMatrix g).PosSemidef := by
  classical
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨cauchyMatrix_isHermitian g, ?_⟩
  intro x
  show 0 ≤ x ⬝ᵥ (cauchyMatrix g) *ᵥ x
  -- Reduce to ∑ i ∑ j, x i * (1/(g i + g j)) * x j.
  have h_quad : x ⬝ᵥ (cauchyMatrix g) *ᵥ x =
      ∑ i, ∑ j, x i * (cauchyMatrix g i j) * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_quad]
  -- Integral representation.
  have h_entry : ∀ i j : n,
      x i * (cauchyMatrix g i j) * x j =
        ∫ t : ℝ in Ioi 0,
          x i * x j * Real.exp (-(g i + g j) * t) := by
    intro i j
    have h_pos : 0 < g i + g j := add_pos (hg i) (hg j)
    simp only [cauchyMatrix, Matrix.of_apply]
    rw [cauchy_inv_eq_integral_exp_neg (hg i) (hg j),
        MeasureTheory.integral_const_mul]
    ring
  -- Pull integrals out via `integral_finset_sum`.
  have h_pair_integrable : ∀ i j : n,
      IntegrableOn (fun t => x i * x j * Real.exp (-(g i + g j) * t)) (Ioi 0) :=
    fun i j => (integrableOn_exp_neg_mul_Ioi_zero
      (add_pos (hg i) (hg j))).const_mul _
  rw [show (∑ i, ∑ j, x i * (cauchyMatrix g i j) * x j) =
      (∫ t : ℝ in Ioi 0,
        ∑ i : n, ∑ j : n,
          x i * x j * Real.exp (-(g i + g j) * t)) from ?_]
  · -- Now apply integral_nonneg to (∑ x_i exp(-g_i t))^2 ≥ 0.
    apply MeasureTheory.integral_nonneg
    intro t
    have h_factor : ∀ i j : n,
        x i * x j * Real.exp (-(g i + g j) * t) =
          (x i * Real.exp (-g i * t)) * (x j * Real.exp (-g j * t)) := by
      intros
      rw [exp_neg_sum_factor]; ring
    simp_rw [h_factor]
    rw [← Finset.sum_mul_sum]
    exact mul_self_nonneg _
  · -- ∑ ∑ ∫ = ∫ ∑ ∑.
    simp_rw [h_entry]
    have step1 : ∀ i : n,
        ∑ j : n, ∫ t : ℝ in Ioi 0,
          x i * x j * Real.exp (-(g i + g j) * t) =
        ∫ t : ℝ in Ioi 0,
          ∑ j : n, x i * x j * Real.exp (-(g i + g j) * t) := by
      intro i
      rw [← integral_finset_sum]
      intros j _; exact h_pair_integrable i j
    simp_rw [step1]
    rw [← integral_finset_sum]
    intros i _
    apply integrable_finset_sum
    intros j _; exact h_pair_integrable i j

/-- For positive parameters `g_i > 0` and a strictly positive determinant
(implied by `g` injective via the classical Cauchy determinant formula —
not formalised here), the abstract Cauchy matrix is positive definite. -/
theorem cauchyMatrix_PosDef {n : Type*} [Fintype n] [DecidableEq n]
    {g : n → ℝ} (hg : ∀ i, 0 < g i)
    (hDet : 0 < (cauchyMatrix g).det) :
    (cauchyMatrix g).PosDef := by
  exact PosDef_of_PosSemidef_of_det_pos (cauchyMatrix_PosSemidef hg) hDet

/-- Sanity-check: the abstract `cauchyMatrix_PosSemidef` recovers
`hierCauchyG_PosSemidef` as a corollary. -/
example (m : ℕ) : (hierCauchyG m).PosSemidef := by
  rw [hierCauchyG_eq_cauchyMatrix]
  exact cauchyMatrix_PosSemidef (hierGrid_pos m)

/-- Sanity-check: 1×1 abstract Cauchy matrix is PSD for any positive
`g₀`. -/
example (g₀ : ℝ) (h : 0 < g₀) :
    (cauchyMatrix (fun _ : Fin 1 => g₀)).PosSemidef :=
  cauchyMatrix_PosSemidef (fun _ => h)

end Erdos524.Helpers
