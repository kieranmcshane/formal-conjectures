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
import FormalConjectures.ErdosProblems.Helpers.StirlingTwoSided

/-!
# Cauchy determinant lower bound on the hierarchical grid (helper for Erdős 524)

Proves `det Σ ≥ exp(-c₀ · m³)` for the m² × m² Cauchy matrix on the hierarchical
grid `δ_{p,q} = 4^(p+m) · (m+q+1)`, where `(p, q) : Fin m × Fin m`. This is used
in the no-Gaussian / no-KMT path to retire `gao_li_wellner_small_ball_upper`.

The proof strategy combines: Cauchy determinant identity (§1), algebraic
decomposition `δ(p,q) = a_p · s_q` (§2), artanh perturbation bound (§3),
Stirling on the shape determinant (§4), and assembly (§5).

The final theorem `cauchy_hierarchical_det_lower_bound` is exposed for
downstream use, in the sharp `det Σ ≥ exp(-c₀ · m³)` form.
The proof uses the algebraic identity that decomposes `log det Σ` via
in-block / cross-block / diagonal pieces, and introduces no new axioms
beyond Mathlib's.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524.Helpers

open Real Finset Matrix BigOperators

-- ## §1. Cauchy determinant identity (Mathlib gap)

/-- Auxiliary: row-reduction step for the Cauchy determinant.

For `δ : Fin (n+1) → ℝ` pairwise distinct with all `δ_i + δ_j > 0`, after
subtracting row 0 from rows `1..n` of the Cauchy matrix and factoring scalars,
the determinant equals `(scalar) · det M'` where `M' i j = 1` for `i = 0` and
`M' i j = 1/(δ i + δ j)` for `i ≥ 1`. -/
private lemma cauchy_det_pos_aux1 {n : ℕ} (δ : Fin (n + 1) → ℝ)
    (hpos : ∀ i j, 0 < δ i + δ j) :
    (Matrix.of fun i j : Fin (n + 1) => 1 / (δ i + δ j)).det =
      (∏ j : Fin (n + 1), 1 / (δ 0 + δ j)) *
      (∏ i : Fin n, (δ 0 - δ i.succ)) *
      (Matrix.of fun i j : Fin (n + 1) =>
        if i = 0 then (1 : ℝ) else 1 / (δ i + δ j)).det := by
  -- Step 1: subtract row 0 from rows i ≥ 1.
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => 1 / (δ i + δ j) with hM_def
  set M1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j =>
      if i = 0 then 1 / (δ 0 + δ j)
      else 1 / (δ i + δ j) - 1 / (δ 0 + δ j) with hM1_def
  -- det M = det M1 by row reductions: row i (i ≠ 0) ↦ row i - row 0.
  have hM_eq_M1 : M.det = M1.det := by
    have := Matrix.det_eq_of_forall_row_eq_smul_add_const
      (A := M) (B := M1)
      (c := fun i => if i = 0 then (0 : ℝ) else 1) 0 (by simp)
      (by
        intro i j
        simp only [M, M1, Matrix.of_apply]
        by_cases hi : i = 0
        · simp [hi]
        · simp [hi])
    exact this
  -- Now factor each entry of M1: row i ≠ 0, column j: (δ 0 - δ i) / ((δ i + δ j)(δ 0 + δ j)).
  set M2 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j =>
      if i = 0 then 1 / (δ 0 + δ j)
      else (δ 0 - δ i) / ((δ i + δ j) * (δ 0 + δ j)) with hM2_def
  have hM1_eq_M2 : M1 = M2 := by
    ext i j
    simp only [M1, M2, Matrix.of_apply]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      have hij : 0 < δ i + δ j := hpos i j
      have h0j : 0 < δ 0 + δ j := hpos 0 j
      field_simp
      ring
  -- Factor 1/(δ 0 + δ j) from each column of M2.
  set M3 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j =>
      if i = 0 then (1 : ℝ)
      else (δ 0 - δ i) / (δ i + δ j) with hM3_def
  have hM2_factor : M2 = Matrix.of fun i j => (1 / (δ 0 + δ j)) * M3 i j := by
    ext i j
    simp only [M2, M3, Matrix.of_apply]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      have h0j : 0 < δ 0 + δ j := hpos 0 j
      field_simp
  have hM2_det : M2.det = (∏ j : Fin (n + 1), 1 / (δ 0 + δ j)) * M3.det := by
    rw [hM2_factor]
    exact Matrix.det_mul_row (fun j => 1 / (δ 0 + δ j)) M3
  -- Factor (δ 0 - δ i) from each row i ≥ 1 of M3.
  set M4 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j =>
      if i = 0 then (1 : ℝ) else 1 / (δ i + δ j) with hM4_def
  have hM3_factor :
      M3 = Matrix.of fun i j =>
        (if i = 0 then (1 : ℝ) else δ 0 - δ i) * M4 i j := by
    ext i j
    simp only [M3, M4, Matrix.of_apply]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      ring
  have hM3_det :
      M3.det = (∏ i : Fin (n + 1), (if i = 0 then (1 : ℝ) else δ 0 - δ i))
        * M4.det := by
    rw [hM3_factor]
    exact Matrix.det_mul_column
      (fun i => if i = 0 then (1 : ℝ) else δ 0 - δ i) M4
  -- Convert ∏ i : Fin (n+1), (if i = 0 then 1 else δ 0 - δ i) = ∏ i : Fin n, (δ 0 - δ i.succ).
  have hprod_eq :
      (∏ i : Fin (n + 1), (if i = 0 then (1 : ℝ) else δ 0 - δ i)) =
      (∏ i : Fin n, (δ 0 - δ i.succ)) := by
    rw [Fin.prod_univ_succ]
    simp
  rw [hM_eq_M1, hM1_eq_M2, hM2_det, hM3_det, hprod_eq]
  ring

/-- Auxiliary: column-reduction step for the Cauchy determinant.

For `M' i j = 1` if `i = 0` and `1/(δ_i + δ_j)` if `i ≥ 1`, after subtracting
column 0 from columns `1..n` and factoring, we get `det M' = scalar · det N`
where `N` is the smaller Cauchy matrix on `δ ∘ Fin.succ`. -/
private lemma cauchy_det_pos_aux2 {n : ℕ} (δ : Fin (n + 1) → ℝ)
    (hpos : ∀ i j, 0 < δ i + δ j) :
    (Matrix.of fun i j : Fin (n + 1) =>
        if i = 0 then (1 : ℝ) else 1 / (δ i + δ j)).det =
      (∏ j : Fin n, (δ 0 - δ j.succ)) *
      (∏ i : Fin n, 1 / (δ i.succ + δ 0)) *
      (Matrix.of fun i j : Fin n =>
        1 / (δ i.succ + δ j.succ)).det := by
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => if i = 0 then (1 : ℝ) else 1 / (δ i + δ j) with hM_def
  -- Subtract column 0 from columns j ≠ 0.
  set M1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j =>
      if j = 0 then (if i = 0 then (1 : ℝ) else 1 / (δ i + δ 0))
      else (if i = 0 then 0
            else 1 / (δ i + δ j) - 1 / (δ i + δ 0)) with hM1_def
  have hM_eq_M1 : M.det = M1.det := by
    have h := Matrix.det_eq_of_forall_row_eq_smul_add_const
      (A := Mᵀ) (B := M1ᵀ)
      (c := fun j => if j = 0 then (0 : ℝ) else 1) 0 (by simp)
      (by
        intro j i
        simp only [Matrix.transpose_apply, M, M1, Matrix.of_apply]
        by_cases hj : j = 0
        · subst hj; simp
        · simp only [hj, if_false]
          by_cases hi : i = 0
          · simp [hi]
          · simp [hi])
    rw [← Matrix.det_transpose M, ← Matrix.det_transpose M1]
    exact h
  -- Replace each (i, j) entry: simplify the i ≥ 1, j ≥ 1 entries.
  set M2 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j =>
      if j = 0 then (if i = 0 then (1 : ℝ) else 1 / (δ i + δ 0))
      else (if i = 0 then 0
            else (δ 0 - δ j) / ((δ i + δ j) * (δ i + δ 0))) with hM2_def
  have hM1_eq_M2 : M1 = M2 := by
    ext i j
    simp only [M1, M2, Matrix.of_apply]
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, if_false]
      by_cases hi : i = 0
      · simp [hi]
      · simp only [hi, if_false]
        have hij : 0 < δ i + δ j := hpos i j
        have hi0 : 0 < δ i + δ 0 := hpos i 0
        field_simp
        ring
  -- Cofactor expansion along row 0 (which is [1, 0, 0, ..., 0]).
  have hrow0_zero : ∀ j : Fin n, M2 0 j.succ = 0 := by
    intro j
    simp [M2, Fin.succ_ne_zero]
  have hM2_00 : M2 0 0 = 1 := by simp [M2]
  have hM2_det_eq :
      M2.det = (M2.submatrix Fin.succ (Fin.succAbove 0)).det := by
    rw [Matrix.det_succ_row_zero]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [hM2_00]
    · intro j _ hj0
      obtain ⟨j', rfl⟩ := j.eq_succ_of_ne_zero hj0
      simp [hrow0_zero j']
    · simp
  -- The submatrix entries: (i', j') ↦ M2 i'.succ j'.succ
  --   = (δ 0 - δ j'.succ) / ((δ i'.succ + δ j'.succ) * (δ i'.succ + δ 0)).
  set N : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i' j' =>
      (δ 0 - δ j'.succ) / ((δ i'.succ + δ j'.succ) * (δ i'.succ + δ 0)) with hN_def
  have hsub_eq : M2.submatrix Fin.succ (Fin.succAbove 0) = N := by
    ext i' j'
    have hsucc_above : (0 : Fin (n + 1)).succAbove j' = j'.succ := by
      simp
    simp only [Matrix.submatrix_apply, hsucc_above, M2, N, Matrix.of_apply,
      Fin.succ_ne_zero, if_false]
  -- Factor N = (col factor) * (row factor) * (smaller Cauchy)
  set N4 : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i' j' => 1 / (δ i'.succ + δ j'.succ) with hN4_def
  set N3 : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i' j' => (1 / (δ i'.succ + δ 0)) * N4 i' j' with hN3_def
  have hN_factor :
      N = Matrix.of fun i' j' => (δ 0 - δ j'.succ) * N3 i' j' := by
    ext i' j'
    simp only [N, N3, N4, Matrix.of_apply]
    have hij : 0 < δ i'.succ + δ j'.succ := hpos i'.succ j'.succ
    have hi0 : 0 < δ i'.succ + δ 0 := hpos i'.succ 0
    field_simp
  have hN_det : N.det = (∏ j' : Fin n, (δ 0 - δ j'.succ)) * N3.det := by
    rw [hN_factor]
    exact Matrix.det_mul_row (fun j' => δ 0 - δ j'.succ) N3
  have hN3_det : N3.det = (∏ i' : Fin n, 1 / (δ i'.succ + δ 0)) * N4.det := by
    exact Matrix.det_mul_column (fun i' => 1 / (δ i'.succ + δ 0)) N4
  rw [hM_eq_M1, hM1_eq_M2, hM2_det_eq, hsub_eq, hN_det, hN3_det]
  ring

/-- Cauchy determinant positivity for `Fin n`-indexed `δ`. -/
private lemma cauchy_det_pos_fin :
    ∀ (n : ℕ) (δ : Fin n → ℝ),
      (∀ i j, 0 < δ i + δ j) → (∀ i j : Fin n, i ≠ j → δ i ≠ δ j) →
      0 < (Matrix.of fun i j : Fin n => 1 / (δ i + δ j)).det := by
  intro n
  induction n with
  | zero =>
    intro δ _ _
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro δ hpos hdiff
    rw [cauchy_det_pos_aux1 δ hpos, cauchy_det_pos_aux2 δ hpos]
    -- Recursively bound via induction hypothesis.
    have hsub_pos : 0 < (Matrix.of fun i j : Fin n =>
        1 / (δ i.succ + δ j.succ)).det := by
      apply ih
      · intro i j; exact hpos i.succ j.succ
      · intro i j hij; apply hdiff; exact fun h => hij (Fin.succ_injective _ h)
    -- All scalar factors are positive (the difference factors appear squared).
    have hf1 : 0 < ∏ j : Fin (n + 1), 1 / (δ 0 + δ j) := by
      apply Finset.prod_pos
      intro j _
      exact one_div_pos.mpr (hpos 0 j)
    have hf4 : 0 < ∏ i : Fin n, 1 / (δ i.succ + δ 0) := by
      apply Finset.prod_pos
      intro i _
      exact one_div_pos.mpr (hpos i.succ 0)
    -- Difference factor squared: ∏ (δ 0 - δ i.succ) appears on both row and col.
    have hf2_ne : (∏ i : Fin n, (δ 0 - δ i.succ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      have : δ 0 ≠ δ i.succ := hdiff 0 i.succ (Fin.succ_ne_zero i).symm
      exact sub_ne_zero.mpr this
    have hf2sq_pos :
        0 < (∏ i : Fin n, (δ 0 - δ i.succ)) * (∏ j : Fin n, (δ 0 - δ j.succ)) :=
      mul_self_pos.mpr hf2_ne
    -- Combine: total = f1 * f2 * (f3 * f4 * det) with f2 = f3.
    -- Reorganize as (f1 * f4 * det) * (f2 * f3) where f2 * f3 > 0 and f1 * f4 * det > 0.
    have hpos_part : 0 <
        (∏ j : Fin (n + 1), 1 / (δ 0 + δ j)) *
        (∏ i : Fin n, 1 / (δ i.succ + δ 0)) *
        (Matrix.of fun i j : Fin n => 1 / (δ i.succ + δ j.succ)).det :=
      mul_pos (mul_pos hf1 hf4) hsub_pos
    have htotal :
        (∏ j : Fin (n + 1), 1 / (δ 0 + δ j)) *
        (∏ i : Fin n, (δ 0 - δ i.succ)) *
        ((∏ j : Fin n, (δ 0 - δ j.succ)) *
         (∏ i : Fin n, 1 / (δ i.succ + δ 0)) *
         (Matrix.of fun i j : Fin n => 1 / (δ i.succ + δ j.succ)).det) =
        ((∏ j : Fin (n + 1), 1 / (δ 0 + δ j)) *
         (∏ i : Fin n, 1 / (δ i.succ + δ 0)) *
         (Matrix.of fun i j : Fin n => 1 / (δ i.succ + δ j.succ)).det) *
        ((∏ i : Fin n, (δ 0 - δ i.succ)) *
         (∏ j : Fin n, (δ 0 - δ j.succ))) := by ring
    rw [htotal]
    exact mul_pos hpos_part hf2sq_pos

/-- **Cauchy determinant positivity.** For pairwise distinct `δ : ι → ℝ` (with `ι`
a finite type with decidable equality) and all `δ_i + δ_j > 0`, the Cauchy
matrix `[1/(δ_i + δ_j)]` has strictly positive determinant.

This is a classical fact (Cauchy 1841). The full identity is
`det = (∏_{i<j} (δ_j - δ_i))² / ∏_{i,j} (δ_i + δ_j) > 0`. We prove positivity
directly by induction via Schur-style row/column reductions; see auxiliary
lemmas `cauchy_det_pos_aux1` and `cauchy_det_pos_aux2`. -/
private theorem cauchy_det_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → ℝ)
    (hpos : ∀ i j, 0 < δ i + δ j)
    (hdiff : ∀ i j : ι, i ≠ j → δ i ≠ δ j) :
    0 < (Matrix.of fun i j : ι => 1 / (δ i + δ j)).det := by
  -- Reduce to the `Fin n` case via `Fintype.equivFin`.
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set δ' : Fin (Fintype.card ι) → ℝ := δ ∘ e.symm with hδ'_def
  have hpos' : ∀ i j, 0 < δ' i + δ' j := fun i j => hpos _ _
  have hdiff' : ∀ i j : Fin (Fintype.card ι), i ≠ j → δ' i ≠ δ' j := by
    intro i j hij heq
    -- δ' i = δ (e.symm i), δ' j = δ (e.symm j); heq : δ (e.symm i) = δ (e.symm j).
    -- Show e.symm i = e.symm j → contradicts hij.
    have hsym_eq : e.symm i = e.symm j := by
      by_contra hne
      exact hdiff _ _ hne heq
    exact hij (e.symm.injective hsym_eq)
  have hfin := cauchy_det_pos_fin (Fintype.card ι) δ' hpos' hdiff'
  -- Transfer back via reindexing.
  have heq : (Matrix.of fun i j : ι => 1 / (δ i + δ j)) =
      (Matrix.of fun i j : Fin (Fintype.card ι) => 1 / (δ' i + δ' j)).submatrix e e := by
    ext i j
    simp [δ', Matrix.submatrix_apply]
  rw [heq, Matrix.det_submatrix_equiv_self]
  exact hfin

/-- **Cauchy 1841 determinant identity (Fin version).**

For `δ : Fin n → ℝ` with `δ_i + δ_j > 0` (all `i, j`) and pairwise distinct,
$$\det \big[1/(\delta_i + \delta_j)\big] = \frac{\big(\prod_{i<j}(\delta_j-\delta_i)\big)^2}{\prod_{i,j}(\delta_i+\delta_j)}.$$

Proved by induction on `n` via Schur-style row/column reductions using
`cauchy_det_pos_aux1` and `cauchy_det_pos_aux2`. -/
private theorem cauchy_det_formula_fin :
    ∀ (n : ℕ) (δ : Fin n → ℝ),
      (∀ i j, 0 < δ i + δ j) → (∀ i j : Fin n, i ≠ j → δ i ≠ δ j) →
      (Matrix.of fun i j : Fin n => 1 / (δ i + δ j)).det =
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j - δ i)) ^ 2 /
          ∏ i : Fin n, ∏ j : Fin n, (δ i + δ j) := by
  intro n
  induction n with
  | zero =>
    intro δ _ _
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro δ hpos hdiff
    -- Apply aux1 and aux2 to expand the LHS recursively.
    rw [cauchy_det_pos_aux1 δ hpos, cauchy_det_pos_aux2 δ hpos]
    -- Apply the inductive hypothesis to the smaller Cauchy determinant.
    have hsub_eq : (Matrix.of fun i j : Fin n =>
        1 / (δ i.succ + δ j.succ)).det =
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j.succ - δ i.succ)) ^ 2 /
          ∏ i : Fin n, ∏ j : Fin n, (δ i.succ + δ j.succ) := by
      have := ih (δ ∘ Fin.succ)
        (fun i j => hpos i.succ j.succ)
        (fun i j hij => hdiff i.succ j.succ
          (fun h => hij (Fin.succ_injective _ h)))
      simpa using this
    rw [hsub_eq]
    -- Decompose the target RHS into the i = 0 and i ≥ 1 contributions.
    -- Numerator decomposition: split the outer product over `Fin (n+1)` at 0.
    have hnum :
        (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (δ j - δ i)) =
          (∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), (δ j - δ 0)) *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j.succ - δ i.succ)) := by
      rw [Fin.prod_univ_succ]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact Fin.prod_Ioi_succ (fun k => δ k - δ i.succ) i
    -- The i=0 term: ∏_{j > 0} (δ j - δ 0) = ∏_{j' : Fin n} (δ j'.succ - δ 0).
    have hIoi0 : (∏ j ∈ Finset.Ioi (0 : Fin (n + 1)), (δ j - δ 0)) =
        ∏ j : Fin n, (δ j.succ - δ 0) := by
      exact Fin.prod_Ioi_zero (fun j => δ j - δ 0)
    -- Denominator decomposition: split row 0 and rows i ≥ 1; for each, split column 0.
    have hden :
        (∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (δ i + δ j)) =
          ((δ 0 + δ 0) * ∏ j : Fin n, (δ 0 + δ j.succ)) *
          (∏ i : Fin n, (δ i.succ + δ 0)) *
          (∏ i : Fin n, ∏ j : Fin n, (δ i.succ + δ j.succ)) := by
      rw [Fin.prod_univ_succ]
      have hrow0 : (∏ j : Fin (n + 1), (δ 0 + δ j)) =
          (δ 0 + δ 0) * ∏ j : Fin n, (δ 0 + δ j.succ) := by
        rw [Fin.prod_univ_succ]
      have hrow_succ : ∀ i : Fin n,
          (∏ j : Fin (n + 1), (δ i.succ + δ j)) =
            (δ i.succ + δ 0) * ∏ j : Fin n, (δ i.succ + δ j.succ) := by
        intro i
        rw [Fin.prod_univ_succ]
      have h2 :
          (∏ i : Fin n, ∏ j : Fin (n + 1), (δ i.succ + δ j)) =
            (∏ i : Fin n, (δ i.succ + δ 0)) *
              (∏ i : Fin n, ∏ j : Fin n, (δ i.succ + δ j.succ)) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        exact hrow_succ i
      rw [hrow0, h2]
      ring
    rw [hden, hnum, hIoi0]
    -- Positivity facts for non-zero/non-vanishing denominators.
    have hd00 : δ 0 + δ 0 ≠ 0 := (hpos 0 0).ne'
    have hd0_succ : ∀ j : Fin n, δ 0 + δ j.succ ≠ 0 := fun j => (hpos 0 j.succ).ne'
    have hd_succ_0 : ∀ i : Fin n, δ i.succ + δ 0 ≠ 0 := fun i => (hpos i.succ 0).ne'
    have hd_succ_succ : ∀ i j : Fin n, δ i.succ + δ j.succ ≠ 0 :=
      fun i j => (hpos i.succ j.succ).ne'
    have hP_d0_succ : (∏ j : Fin n, (δ 0 + δ j.succ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _; exact hd0_succ j
    have hP_d_succ_0 : (∏ i : Fin n, (δ i.succ + δ 0)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _; exact hd_succ_0 i
    have hP_d_succ_succ : (∏ i : Fin n, ∏ j : Fin n, (δ i.succ + δ j.succ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro j _; exact hd_succ_succ i j
    -- Express the prefactor `∏ j : Fin (n+1), 1/(δ 0 + δ j)` explicitly.
    have hprefactor1 : (∏ j : Fin (n + 1), 1 / (δ 0 + δ j)) =
        1 / ((δ 0 + δ 0) * ∏ j : Fin n, (δ 0 + δ j.succ)) := by
      rw [Fin.prod_univ_succ]
      have hfold : (∏ j : Fin n, 1 / (δ 0 + δ j.succ)) =
          1 / ∏ j : Fin n, (δ 0 + δ j.succ) := by
        rw [Finset.prod_div_distrib]
        simp
      rw [hfold]
      field_simp
    have hprefactor2 : (∏ i : Fin n, 1 / (δ i.succ + δ 0)) =
        1 / ∏ i : Fin n, (δ i.succ + δ 0) := by
      rw [Finset.prod_div_distrib]
      simp
    rw [hprefactor1, hprefactor2]
    -- Now both sides are pure rational expressions in the various products.
    -- Set abbreviations to make the algebra readable.
    set A : ℝ := δ 0 + δ 0
    set B : ℝ := ∏ j : Fin n, (δ 0 + δ j.succ)
    set C : ℝ := ∏ i : Fin n, (δ i.succ + δ 0)
    set D : ℝ := ∏ i : Fin n, ∏ j : Fin n, (δ i.succ + δ j.succ)
    set X : ℝ := ∏ j : Fin n, (δ j.succ - δ 0) with hX_def
    set Y : ℝ := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j.succ - δ i.succ)
    -- Use that `(δ 0 - δ x.succ)^2 = (δ x.succ - δ 0)^2` pointwise, so the
    -- products of squares (and hence the squares of the products) coincide.
    have hsq_prod : (∏ x : Fin n, (δ 0 - δ x.succ) ^ 2) =
        ∏ x : Fin n, (δ x.succ - δ 0) ^ 2 := by
      apply Finset.prod_congr rfl
      intro x _; ring
    have hprod_sq_lhs : (∏ x : Fin n, (δ 0 - δ x.succ)) ^ 2 =
        ∏ x : Fin n, (δ 0 - δ x.succ) ^ 2 := by
      rw [← Finset.prod_pow]
    have hprod_sq_rhs : X ^ 2 = ∏ x : Fin n, (δ x.succ - δ 0) ^ 2 := by
      rw [hX_def, ← Finset.prod_pow]
    have hsq : (∏ x : Fin n, (δ 0 - δ x.succ)) ^ 2 = X ^ 2 := by
      rw [hprod_sq_lhs, hsq_prod, ← hprod_sq_rhs]
    -- Rewrite using these:
    -- LHS now reads:
    --   (1 / (A * B)) * X * (X * (1 / C) * (Y^2 / D))
    -- RHS reads:
    --   (X * Y)^2 / ((A * B) * C * D)
    have hA : A ≠ 0 := hd00
    have hB : B ≠ 0 := hP_d0_succ
    have hC : C ≠ 0 := hP_d_succ_0
    have hD : D ≠ 0 := hP_d_succ_succ
    have hAB : A * B ≠ 0 := mul_ne_zero hA hB
    have hABC : A * B * C ≠ 0 := mul_ne_zero hAB hC
    have hABCD : A * B * C * D ≠ 0 := mul_ne_zero hABC hD
    -- Convert the LHS factor `(∏ x, (δ 0 - δ x.succ))` (which equals `(-1)^n * X`)
    -- to `X^2` since it appears squared via the row × column factorization.
    -- We rewrite the LHS algebraically.
    have key :
        1 / (A * B) * (∏ i : Fin n, (δ 0 - δ i.succ)) *
          ((∏ j : Fin n, (δ 0 - δ j.succ)) * (1 / C) * (Y ^ 2 / D)) =
        (1 / (A * B * C * D)) * ((∏ x : Fin n, (δ 0 - δ x.succ)) ^ 2 * Y ^ 2) := by
      field_simp
    rw [key, hsq]
    field_simp

/-- **Cauchy 1841 determinant identity.**

For a finite type `ι` with decidable equality and `δ : ι → ℝ` such that
`δ_i + δ_j > 0` for all `i, j` and `δ` is injective,
$$\det \big[1/(\delta_i + \delta_j)\big] = \frac{\big(\prod_{i<j}(\delta_j-\delta_i)\big)^2}{\prod_{i,j}(\delta_i+\delta_j)}$$
where the index pairs `i < j` are taken with respect to a chosen
linear order; equivalently, after fixing an ordering `e : ι ≃ Fin (card ι)`,
the numerator is the square Vandermonde-style product over `Fin (card ι)`. -/
private theorem cauchy_det_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (δ : ι → ℝ)
    (hpos : ∀ i j, 0 < δ i + δ j)
    (hdiff : ∀ i j : ι, i ≠ j → δ i ≠ δ j) :
    (Matrix.of fun i j : ι => 1 / (δ i + δ j)).det =
      (∏ i : Fin (Fintype.card ι), ∏ j ∈ Finset.Ioi i,
          (δ ((Fintype.equivFin ι).symm j) - δ ((Fintype.equivFin ι).symm i))) ^ 2 /
        ∏ i : ι, ∏ j : ι, (δ i + δ j) := by
  -- Reduce to the `Fin n` case via `Fintype.equivFin`.
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set δ' : Fin (Fintype.card ι) → ℝ := δ ∘ e.symm with hδ'_def
  have hpos' : ∀ i j, 0 < δ' i + δ' j := fun i j => hpos _ _
  have hdiff' : ∀ i j : Fin (Fintype.card ι), i ≠ j → δ' i ≠ δ' j := by
    intro i j hij heq
    have hsym_eq : e.symm i = e.symm j := by
      by_contra hne
      exact hdiff _ _ hne heq
    exact hij (e.symm.injective hsym_eq)
  have hfin := cauchy_det_formula_fin (Fintype.card ι) δ' hpos' hdiff'
  -- Transfer the determinant via reindexing.
  have hmat_eq : (Matrix.of fun i j : ι => 1 / (δ i + δ j)) =
      (Matrix.of fun i j : Fin (Fintype.card ι) => 1 / (δ' i + δ' j)).submatrix e e := by
    ext i j
    simp [δ', Matrix.submatrix_apply]
  rw [hmat_eq, Matrix.det_submatrix_equiv_self, hfin]
  -- Match denominators: ∏ i : Fin n, ∏ j : Fin n, (δ' i + δ' j) = ∏ i : ι, ∏ j : ι, (δ i + δ j).
  congr 1
  -- Reindex the outer and inner products via `e`.
  have hden_eq :
      (∏ i : Fin (Fintype.card ι), ∏ j : Fin (Fintype.card ι), (δ' i + δ' j)) =
        ∏ i : ι, ∏ j : ι, (δ i + δ j) := by
    rw [← Equiv.prod_comp e (fun i : Fin (Fintype.card ι) =>
        ∏ j : Fin (Fintype.card ι), (δ' i + δ' j))]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Equiv.prod_comp e (fun j : Fin (Fintype.card ι) =>
        δ' (e i) + δ' j)]
    apply Finset.prod_congr rfl
    intro j _
    simp [δ']
  exact hden_eq

-- ## §3. Perturbation bound via artanh (fully proven)

/-- For `η ∈ [0, 1)`, `log(1 - η) ≥ -η / (1 - η)`.
This is a standard consequence of `log x ≤ x - 1` applied to `1/(1-η)`. -/
lemma log_one_sub_ge_neg_div {η : ℝ} (_h0 : 0 ≤ η) (h1 : η < 1) :
    -(η / (1 - η)) ≤ Real.log (1 - η) := by
  have h1mη_pos : 0 < 1 - η := by linarith
  -- log(1/(1-η)) ≤ 1/(1-η) - 1 = η/(1-η)
  have hinv_pos : 0 < 1 / (1 - η) := by positivity
  have hkey : Real.log (1 / (1 - η)) ≤ 1 / (1 - η) - 1 :=
    Real.log_le_sub_one_of_pos hinv_pos
  have hsimp : 1 / (1 - η) - 1 = η / (1 - η) := by
    rw [div_sub_one h1mη_pos.ne']
    ring_nf
  rw [hsimp] at hkey
  have hlog_inv : Real.log (1 / (1 - η)) = -Real.log (1 - η) := by
    rw [Real.log_div one_ne_zero h1mη_pos.ne', Real.log_one, zero_sub]
  rw [hlog_inv] at hkey
  linarith

/-- For `η ∈ [0, 1/2]`, `log(1 - η) ≥ -2 η`.
Combines `log(1-η) ≥ -η/(1-η)` with `1/(1-η) ≤ 2`. -/
lemma log_one_sub_ge_neg_two_mul {η : ℝ} (h0 : 0 ≤ η) (h_half : η ≤ 1/2) :
    -(2 * η) ≤ Real.log (1 - η) := by
  have h1 : η < 1 := by linarith
  have h1mη_pos : 0 < 1 - η := by linarith
  have h1mη_ge : 1/2 ≤ 1 - η := by linarith
  have hbase : -(η / (1 - η)) ≤ Real.log (1 - η) :=
    log_one_sub_ge_neg_div h0 h1
  -- η/(1-η) ≤ 2η when η ≥ 0 and 1-η ≥ 1/2
  have hratio : η / (1 - η) ≤ 2 * η := by
    rw [div_le_iff₀ h1mη_pos]
    nlinarith
  linarith

/-- For `η ∈ [0, ∞)`, `log(1 + η) ≤ η`.
This is `Real.log_le_sub_one_of_pos` applied to `1 + η`. -/
lemma log_one_add_le_self {η : ℝ} (h0 : 0 ≤ η) :
    Real.log (1 + η) ≤ η := by
  have hpos : 0 < 1 + η := by linarith
  have := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Perturbation bound.** For `η ∈ [0, 1/2]`,
`log((1 - η) / (1 + η)) ≥ -3 η`. -/
theorem log_artanh_bound {η : ℝ} (h0 : 0 ≤ η) (h_half : η ≤ 1/2) :
    -(3 * η) ≤ Real.log ((1 - η) / (1 + η)) := by
  have h1 : η < 1 := by linarith
  have h1mη_pos : 0 < 1 - η := by linarith
  have h1pη_pos : 0 < 1 + η := by linarith
  rw [Real.log_div h1mη_pos.ne' h1pη_pos.ne']
  have hlow : -(2 * η) ≤ Real.log (1 - η) :=
    log_one_sub_ge_neg_two_mul h0 h_half
  have hupp : Real.log (1 + η) ≤ η := log_one_add_le_self h0
  linarith

-- ## §3'. Geometric series tail bound

/-- `∑_{d=0}^{m-1} (1/4)^d ≤ 4/3`. Geometric sum bound. -/
lemma geom_series_quarter_le {m : ℕ} (_hm : 1 ≤ m) :
    ∑ d ∈ Finset.range m, ((1/4 : ℝ))^d ≤ 4/3 := by
  have hr_lt : (1 : ℝ) / 4 < 1 := by norm_num
  have hr_nn : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hsum_eq : ∑ d ∈ Finset.range m, ((1/4 : ℝ)^d) =
      ((1/4 : ℝ)^m - 1) / (1/4 - 1) := by
    rw [geom_sum_eq (by norm_num : (1/4 : ℝ) ≠ 1) m]
  rw [hsum_eq]
  have hpow_nn : (0 : ℝ) ≤ (1/4 : ℝ)^m := pow_nonneg hr_nn _
  have hpow_le : (1/4 : ℝ)^m ≤ 1 := pow_le_one₀ hr_nn (le_of_lt hr_lt)
  -- (1/4^m - 1)/(1/4 - 1) = (1 - 1/4^m) / (3/4) ≤ 1/(3/4) = 4/3
  have : ((1/4 : ℝ)^m - 1) / (1/4 - 1) = (1 - (1/4 : ℝ)^m) / (3/4) := by
    rw [show ((1/4 : ℝ) - 1) = -(3/4) by ring,
        show ((1/4 : ℝ)^m - 1) = -(1 - (1/4 : ℝ)^m) by ring]
    rw [neg_div_neg_eq]
  rw [this]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3/4)]
  linarith

/-- The combined artanh + nonnegativity bound: `0 ≤ η ≤ 1/2` implies
`-(3 η) ≤ log((1-η)/(1+η)) ≤ 0`. -/
lemma log_artanh_two_sided {η : ℝ} (h0 : 0 ≤ η) (h_half : η ≤ 1/2) :
    -(3 * η) ≤ Real.log ((1 - η) / (1 + η)) ∧
      Real.log ((1 - η) / (1 + η)) ≤ 0 := by
  refine ⟨log_artanh_bound h0 h_half, ?_⟩
  have h1mη_pos : 0 < 1 - η := by linarith
  have h1pη_pos : 0 < 1 + η := by linarith
  have hle : (1 - η) / (1 + η) ≤ 1 := by
    rw [div_le_iff₀ h1pη_pos]; linarith
  have hpos : 0 < (1 - η) / (1 + η) := div_pos h1mη_pos h1pη_pos
  exact Real.log_nonpos hpos.le hle

/-- Symmetry of `cauchy_det_pos`'s output formula — the product over `p.1 < p.2`
is symmetric to the product over `p.1 > p.2` since both factors squared are
symmetric. We don't use this directly but it justifies the formulation. -/
lemma sq_diff_symm {a b : ℝ} : (a - b)^2 = (b - a)^2 := by ring

/-- Placeholder lemma: the real cross-block eta sum bound is
`cross_block_eta_sum_bound_real`, stated after §2 (which defines `crossEta`,
`scaleA`, `shapeS`). Kept as `True := trivial` for compatibility. -/
lemma cross_block_eta_sum_bound {m : ℕ} (_hm : 1 ≤ m) :
    True := trivial

-- ## §2. Algebraic decomposition of the hierarchical grid

/-- The hierarchical grid `δ : Fin m × Fin m → ℝ` defined by
`δ(p,q) = 4^(p+m) · (m + q + 1)`. -/
noncomputable def hierGrid (m : ℕ) : Fin m × Fin m → ℝ :=
  fun pq => (4 : ℝ)^(pq.1.val + m) * ((m : ℝ) + pq.2.val + 1)

/-- The grid is positive. -/
lemma hierGrid_pos (m : ℕ) (pq : Fin m × Fin m) : 0 < hierGrid m pq := by
  unfold hierGrid
  apply mul_pos
  · exact pow_pos (by norm_num : (0 : ℝ) < 4) _
  · have : (0 : ℝ) ≤ pq.2.val := Nat.cast_nonneg _
    linarith [Nat.cast_nonneg (α := ℝ) m]

/-- Pairwise sums on the grid are positive. -/
lemma hierGrid_sum_pos (m : ℕ) (i j : Fin m × Fin m) :
    0 < hierGrid m i + hierGrid m j :=
  add_pos (hierGrid_pos m i) (hierGrid_pos m j)

/-- The "scale" coefficient `a_p = 4^(p+m)`. -/
noncomputable def scaleA (m : ℕ) (p : Fin m) : ℝ := (4 : ℝ)^(p.val + m)

/-- The "shape" coefficient `s_q = m + q + 1`. -/
noncomputable def shapeS (m : ℕ) (q : Fin m) : ℝ := (m : ℝ) + q.val + 1

lemma scaleA_pos (m : ℕ) (p : Fin m) : 0 < scaleA m p := by
  unfold scaleA; exact pow_pos (by norm_num : (0 : ℝ) < 4) _

lemma shapeS_pos (m : ℕ) (q : Fin m) : 0 < shapeS m q := by
  unfold shapeS
  have h1 : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  linarith

/-- `s_q ≤ 2m` for all `q : Fin m` (when `m ≥ 1`). -/
lemma shapeS_le_two_mul {m : ℕ} (hm : 1 ≤ m) (q : Fin m) :
    shapeS m q ≤ 2 * (m : ℝ) := by
  unfold shapeS
  have hq : (q.val : ℝ) ≤ (m : ℝ) - 1 := by
    have hq_lt : q.val < m := q.isLt
    have : (q.val : ℝ) ≤ (m - 1 : ℕ) := by
      exact_mod_cast Nat.le_sub_one_of_lt hq_lt
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : 1 ≤ m := hm
      push_cast [Nat.cast_sub this]
      ring
    linarith
  linarith

/-- `s_q ≥ m + 1`. -/
lemma shapeS_ge {m : ℕ} (q : Fin m) : (m : ℝ) + 1 ≤ shapeS m q := by
  unfold shapeS
  have : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
  linarith

/-- Decomposition: `δ(p,q) = a_p · s_q`. -/
lemma hierGrid_factor (m : ℕ) (pq : Fin m × Fin m) :
    hierGrid m pq = scaleA m pq.1 * shapeS m pq.2 := rfl

/-- Log of the scale: `log a_p = (p + m) log 4`. -/
lemma log_scaleA (m : ℕ) (p : Fin m) :
    Real.log (scaleA m p) = (p.val + m : ℕ) * Real.log 4 := by
  unfold scaleA
  rw [Real.log_pow]

/-- The total `log scale` aggregated over the in-block index `q`:
`∑_q log a_p = m · log a_p`. -/
lemma sum_log_scaleA_inblock (m : ℕ) (p : Fin m) :
    ∑ _q : Fin m, Real.log (scaleA m p) = m * Real.log (scaleA m p) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- Same with both `q, q'` running independently:
`∑_{q, q'} log a_p = m² · log a_p`. -/
lemma sum_log_scaleA_inblock_sq (m : ℕ) (p : Fin m) :
    ∑ _q : Fin m, ∑ _q' : Fin m, Real.log (scaleA m p) =
      m^2 * Real.log (scaleA m p) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- In-block sum: `δ(p,q) + δ(p,q') = a_p · (s_q + s_{q'})`. -/
lemma hierGrid_inblock_sum (m : ℕ) (p : Fin m) (q q' : Fin m) :
    hierGrid m (p, q) + hierGrid m (p, q') =
      scaleA m p * (shapeS m q + shapeS m q') := by
  show scaleA m p * shapeS m q + scaleA m p * shapeS m q' =
    scaleA m p * (shapeS m q + shapeS m q')
  ring

/-- In-block log of sum: `log(δ(p,q) + δ(p,q')) = log a_p + log(s_q + s_{q'})`. -/
lemma log_hierGrid_inblock_sum (m : ℕ) (p : Fin m) (q q' : Fin m) :
    Real.log (hierGrid m (p, q) + hierGrid m (p, q')) =
      Real.log (scaleA m p) + Real.log (shapeS m q + shapeS m q') := by
  rw [hierGrid_inblock_sum]
  exact Real.log_mul (ne_of_gt (scaleA_pos m p))
    (ne_of_gt (add_pos (shapeS_pos m q) (shapeS_pos m q')))

/-- In-block difference: `δ(p,q) - δ(p,q') = a_p · (s_q - s_{q'})`. -/
lemma hierGrid_inblock_diff (m : ℕ) (p : Fin m) (q q' : Fin m) :
    hierGrid m (p, q) - hierGrid m (p, q') =
      scaleA m p * (shapeS m q - shapeS m q') := by
  show scaleA m p * shapeS m q - scaleA m p * shapeS m q' =
    scaleA m p * (shapeS m q - shapeS m q')
  ring

/-- Cross-block factorization for the sum:
`δ(p,q) + δ(r,s) = a_r · s_s · (1 + (a_p / a_r) · (s_q / s_s))`,
needed for the artanh-type bound. -/
lemma hierGrid_crossblock_sum_factor (m : ℕ) (p r : Fin m) (q s : Fin m) :
    hierGrid m (p, q) + hierGrid m (r, s) =
      scaleA m r * shapeS m s *
        (1 + (scaleA m p / scaleA m r) * (shapeS m q / shapeS m s)) := by
  have hr_ne : scaleA m r ≠ 0 := ne_of_gt (scaleA_pos m r)
  have hs_ne : shapeS m s ≠ 0 := ne_of_gt (shapeS_pos m s)
  show scaleA m p * shapeS m q + scaleA m r * shapeS m s =
    scaleA m r * shapeS m s *
      (1 + (scaleA m p / scaleA m r) * (shapeS m q / shapeS m s))
  field_simp
  ring

/-- Cross-block factorization for the difference:
`δ(p,q) - δ(r,s) = a_r · s_s · ((a_p / a_r) · (s_q / s_s) - 1)`. -/
lemma hierGrid_crossblock_diff_factor (m : ℕ) (p r : Fin m) (q s : Fin m) :
    hierGrid m (p, q) - hierGrid m (r, s) =
      scaleA m r * shapeS m s *
        ((scaleA m p / scaleA m r) * (shapeS m q / shapeS m s) - 1) := by
  have hr_ne : scaleA m r ≠ 0 := ne_of_gt (scaleA_pos m r)
  have hs_ne : shapeS m s ≠ 0 := ne_of_gt (shapeS_pos m s)
  show scaleA m p * shapeS m q - scaleA m r * shapeS m s =
    scaleA m r * shapeS m s *
      ((scaleA m p / scaleA m r) * (shapeS m q / shapeS m s) - 1)
  field_simp

/-- The "perturbation parameter" `η_{p,r,q,s} = (a_p / a_r) · (s_q / s_s)`,
used in the cross-block log expansion. For `p < r`, `η ≤ 1/2` (so the artanh
bound applies). -/
noncomputable def crossEta (m : ℕ) (p r : Fin m) (q s : Fin m) : ℝ :=
  (scaleA m p / scaleA m r) * (shapeS m q / shapeS m s)

lemma crossEta_pos (m : ℕ) (p r : Fin m) (q s : Fin m) :
    0 < crossEta m p r q s := by
  unfold crossEta
  exact mul_pos (div_pos (scaleA_pos m p) (scaleA_pos m r))
    (div_pos (shapeS_pos m q) (shapeS_pos m s))

/-- For `p.val < r.val`, the scale ratio `a_p / a_r ≤ 1/4`. -/
lemma scaleA_ratio_le {m : ℕ} {p r : Fin m} (hpr : p.val < r.val) :
    scaleA m p / scaleA m r ≤ 1 / 4 := by
  unfold scaleA
  have h4_pos : (0 : ℝ) < (4 : ℝ)^(r.val + m) := pow_pos (by norm_num) _
  rw [div_le_iff₀ h4_pos]
  have hpw : (4 : ℝ)^(p.val + m) * 4 ≤ (4 : ℝ)^(r.val + m) := by
    have h : (4 : ℝ)^(p.val + m) * (4 : ℝ)^1 ≤ (4 : ℝ)^(r.val + m) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)
    simpa using h
  have h1 : (1 / 4 : ℝ) * (4 : ℝ)^(r.val + m) =
      (4 : ℝ)^(r.val + m) / 4 := by ring
  rw [h1]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- For any `q s : Fin m` with `m ≥ 1`, `s_q / s_s ≤ 2`. -/
lemma shapeS_ratio_le {m : ℕ} (hm : 1 ≤ m) (q s : Fin m) :
    shapeS m q / shapeS m s ≤ 2 := by
  have hs_pos : 0 < shapeS m s := shapeS_pos m s
  rw [div_le_iff₀ hs_pos]
  have hq_le : shapeS m q ≤ 2 * (m : ℝ) := shapeS_le_two_mul hm q
  have hs_ge : (m : ℝ) + 1 ≤ shapeS m s := shapeS_ge s
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  -- 2 m ≤ 2 (m+1) ≤ 2 s_s
  have : shapeS m q ≤ 2 * shapeS m s := by linarith
  linarith

/-- For `p.val < r.val` and any `q s : Fin m`, the perturbation `η ≤ 1/2`. -/
lemma crossEta_le_half {m : ℕ} (hm : 1 ≤ m) {p r : Fin m} (hpr : p.val < r.val)
    (q s : Fin m) : crossEta m p r q s ≤ 1/2 := by
  unfold crossEta
  have hsr : scaleA m p / scaleA m r ≤ 1/4 := scaleA_ratio_le hpr
  have hss : shapeS m q / shapeS m s ≤ 2 := shapeS_ratio_le hm q s
  have hsr_nn : 0 ≤ scaleA m p / scaleA m r :=
    le_of_lt (div_pos (scaleA_pos m p) (scaleA_pos m r))
  have hss_nn : 0 ≤ shapeS m q / shapeS m s :=
    le_of_lt (div_pos (shapeS_pos m q) (shapeS_pos m s))
  calc (scaleA m p / scaleA m r) * (shapeS m q / shapeS m s)
      ≤ (1/4) * 2 := by
        apply mul_le_mul hsr hss hss_nn
        norm_num
    _ = 1/2 := by norm_num

/-- The artanh bound applied at the cross-block perturbation:
`log((1 - η_{p,r,q,s}) / (1 + η_{p,r,q,s})) ≥ -3 η`. -/
lemma log_crossEta_artanh {m : ℕ} (hm : 1 ≤ m) {p r : Fin m}
    (hpr : p.val < r.val) (q s : Fin m) :
    -(3 * crossEta m p r q s) ≤
      Real.log ((1 - crossEta m p r q s) / (1 + crossEta m p r q s)) := by
  apply log_artanh_bound
  · exact le_of_lt (crossEta_pos m p r q s)
  · exact crossEta_le_half hm hpr q s

/-- Cross-block factor of the difference dominates: when `p < r`, the term
`δ(r,s) - δ(p,q)` is positive (since `a_r > a_p` after multiplication by
the `s` factors). -/
lemma hierGrid_cross_diff_pos {m : ℕ} (hm : 1 ≤ m) {p r : Fin m}
    (hpr : p.val < r.val) (q s : Fin m) :
    0 < hierGrid m (r, s) - hierGrid m (p, q) := by
  rw [show hierGrid m (r, s) - hierGrid m (p, q) =
        scaleA m r * shapeS m s - scaleA m p * shapeS m q from rfl]
  -- a_p · s_q ≤ a_p · 2m ≤ a_r/2 · 2m = a_r · m < a_r · (m+1) ≤ a_r · s_s
  have h_ap_pos : 0 < scaleA m p := scaleA_pos m p
  have h_ar_pos : 0 < scaleA m r := scaleA_pos m r
  have h_sq_pos : 0 < shapeS m q := shapeS_pos m q
  have h_ss_pos : 0 < shapeS m s := shapeS_pos m s
  have h_apar : scaleA m p * 4 ≤ scaleA m r := by
    unfold scaleA
    have : (4 : ℝ)^(p.val + m) * (4 : ℝ)^1 ≤ (4 : ℝ)^(r.val + m) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)
    simpa using this
  have h_sq_le : shapeS m q ≤ 2 * (m : ℝ) := shapeS_le_two_mul hm q
  have h_ss_ge : (m : ℝ) + 1 ≤ shapeS m s := shapeS_ge s
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  -- a_p · s_q ≤ a_p · 2m
  have h1 : scaleA m p * shapeS m q ≤ scaleA m p * (2 * (m : ℝ)) := by
    exact mul_le_mul_of_nonneg_left h_sq_le h_ap_pos.le
  -- 2 a_p · m ≤ (a_r / 2) · m ... wait, we need: a_p · 2m < a_r · (m+1).
  -- 4 a_p · 2m / 2 = 4 a_p · m. We have 4 a_p ≤ a_r so 4 a_p · m ≤ a_r · m
  -- Hmm: a_p · 2m vs a_r · (m+1). 2m vs 2(m+1)? Need a_p · 2m < a_r · (m+1).
  -- Use 4 a_p · 2m = 8 a_p · m and a_r · (m+1) ≥ a_r · m. So 8 a_p · m vs 4 a_r · m.
  -- 8 a_p ≤ ?: we have 4 a_p ≤ a_r so 8 a_p ≤ 2 a_r, but we need 8 a_p ≤ 4 a_r,
  -- which is the same (8 a_p ≤ 2 a_r ≤ 4 a_r iff a_r ≥ 0, true).
  -- So a_p · 2m ≤ (a_r / 4) · 2m = a_r · m / 2 ≤ a_r · m < a_r · (m+1) ≤ a_r · s_s.
  have h2 : scaleA m p * (2 * (m : ℝ)) ≤ scaleA m r * (m : ℝ) / 2 := by
    have : 4 * (scaleA m p * (2 * (m : ℝ))) ≤ 4 * (scaleA m r * (m : ℝ) / 2) := by
      have hcalc : 4 * (scaleA m p * (2 * (m : ℝ))) = 8 * scaleA m p * (m : ℝ) := by ring
      have hcalc2 : 4 * (scaleA m r * (m : ℝ) / 2) = 2 * scaleA m r * (m : ℝ) := by ring
      rw [hcalc, hcalc2]
      have : 8 * scaleA m p ≤ 2 * scaleA m r := by linarith
      have hmm : (0 : ℝ) ≤ m := hm_pos.le
      nlinarith
    linarith
  have h3 : scaleA m r * (m : ℝ) / 2 < scaleA m r * shapeS m s := by
    have : scaleA m r * (m : ℝ) / 2 < scaleA m r * ((m : ℝ) + 1) := by
      have hpos2 : 0 < scaleA m r := h_ar_pos
      have : (m : ℝ) / 2 < (m : ℝ) + 1 := by linarith
      have := mul_lt_mul_of_pos_left this h_ar_pos
      linarith
    have h_sub : scaleA m r * ((m : ℝ) + 1) ≤ scaleA m r * shapeS m s :=
      mul_le_mul_of_nonneg_left h_ss_ge h_ar_pos.le
    linarith
  linarith

-- ## §4. The in-block shape determinant `det M`

/-- The shape matrix `M : Fin m → Fin m → ℝ` defined by
`M_{q, q'} = 1 / (s_q + s_{q'})`. This is a Cauchy matrix on the positive
points `s_0, ..., s_{m-1}` and is positive definite. -/
noncomputable def shapeM (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun q q' => 1 / (shapeS m q + shapeS m q')

/-- `s_q + s_{q'} > 0`. -/
lemma shapeM_sum_pos (m : ℕ) (q q' : Fin m) :
    0 < shapeS m q + shapeS m q' :=
  add_pos (shapeS_pos m q) (shapeS_pos m q')

/-- `s_q ≠ s_{q'}` when `q ≠ q'`. -/
lemma shapeS_inj {m : ℕ} {q q' : Fin m} (h : q ≠ q') : shapeS m q ≠ shapeS m q' := by
  unfold shapeS
  intro heq
  have : (q.val : ℝ) = (q'.val : ℝ) := by linarith
  have hqq' : q.val = q'.val := by exact_mod_cast this
  exact h (Fin.ext hqq')

/-- Strict positivity of `det shapeM` (consequence of Cauchy determinant
formula). -/
lemma shapeM_det_pos (m : ℕ) : 0 < (shapeM m).det := by
  unfold shapeM
  exact cauchy_det_pos (shapeS m) (shapeM_sum_pos m) (fun i j hij => shapeS_inj hij)

/-- Lower bound on `log m!` via Stirling: `m log m - m ≤ log m!` for `m ≥ 1`.
This is a coarse but simple consequence of `Stirling.le_log_factorial_stirling`;
we drop the `log(2π)/2` term and the `log m / 2` term as `≥ 0`. -/
lemma log_factorial_lower {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) * Real.log m - m ≤ Real.log m.factorial := by
  have h := Stirling.le_log_factorial_stirling (n := m) (by omega : m ≠ 0)
  have hm_pos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog_m_nn : 0 ≤ Real.log m := Real.log_nonneg hm_pos
  have h2pi_nn : (0 : ℝ) ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 * Real.pi := by
      have hpi : (3 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      linarith
    exact this
  -- `m log m - m ≤ m log m - m + log m / 2 + log (2π) / 2`
  linarith

/-- Upper bound on `log m!` via Stirling: `log m! ≤ m log m - m + (log m)/2 + 2`
for `m ≥ 1`. Drops the small constant, using `factorial_le_stirling` from
StirlingTwoSided. -/
lemma log_factorial_upper {m : ℕ} (hm : 1 ≤ m) :
    Real.log m.factorial ≤
      (m : ℝ) * Real.log m - m + Real.log m / 2 + 2 := by
  have h := Erdos524.Helpers.factorial_le_stirling (n := m) hm
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * m) := Real.sqrt_pos.mpr (by positivity)
  have hpow_pos : 0 < ((m : ℝ) / Real.exp 1)^m :=
    pow_pos (by positivity) _
  have hRHS_pos : 0 < (Real.exp 1 / Real.sqrt (2 * Real.pi)) *
      (Real.sqrt (2 * Real.pi * m) * (m / Real.exp 1) ^ m) := by
    apply mul_pos
    · exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr h2pi)
    · exact mul_pos hsqrt_pos hpow_pos
  -- log of the upper bound expression equals `1 + (1/2)(log m - log(2π)) + ...`
  -- after simplification. We coarse-bound the constants.
  have hfact_pos : (0 : ℝ) < m.factorial := by
    exact_mod_cast Nat.factorial_pos m
  have hlog_le : Real.log m.factorial ≤
      Real.log ((Real.exp 1 / Real.sqrt (2 * Real.pi)) *
        (Real.sqrt (2 * Real.pi * m) * (m / Real.exp 1) ^ m)) := by
    apply Real.log_le_log hfact_pos h
  -- Use the StirlingTwoSided helper directly: log m! / stirling ≤ log(e/√(2π))
  have hbound :
      Real.log m.factorial - Real.log
        (Real.sqrt (2 * Real.pi * m) * (m / Real.exp 1) ^ m) ≤
        Real.log (Real.exp 1 / Real.sqrt (2 * Real.pi)) := by
    have hstir_pos : 0 < Real.sqrt (2 * Real.pi * m) * (m / Real.exp 1) ^ m :=
      mul_pos hsqrt_pos hpow_pos
    rw [← Real.log_div hfact_pos.ne' hstir_pos.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hstir_pos]
    linarith [h]
  -- Now expand `log(√(2πm) · (m/e)^m) = (log(2π) + log m)/2 + m(log m - 1)`.
  have hexp_log : Real.log (Real.sqrt (2 * Real.pi * m) * (m / Real.exp 1) ^ m) =
      (Real.log (2 * Real.pi) + Real.log m) / 2 + m * (Real.log m - 1) := by
    have h1 : Real.log (Real.sqrt (2 * Real.pi * m) * (m / Real.exp 1) ^ m) =
        Real.log (Real.sqrt (2 * Real.pi * m)) + m * Real.log (m / Real.exp 1) := by
      rw [Real.log_mul (Real.sqrt_pos.mpr (by positivity)).ne'
            (pow_pos (by positivity : (0 : ℝ) < m / Real.exp 1) m).ne']
      rw [Real.log_pow]
    rw [h1, Real.log_sqrt (by positivity),
        Real.log_mul h2pi.ne' hm_pos.ne',
        Real.log_div hm_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  -- And `log(e/√(2π)) = 1 - (1/2) log(2π)`.
  have hk_log : Real.log (Real.exp 1 / Real.sqrt (2 * Real.pi)) =
      1 - Real.log (2 * Real.pi) / 2 := by
    rw [Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr h2pi).ne',
        Real.log_exp, Real.log_sqrt h2pi.le]
  rw [hexp_log, hk_log] at hbound
  -- hbound: log m! - [(log(2π) + log m)/2 + m(log m - 1)] ≤ 1 - log(2π)/2
  -- ↔ log m! ≤ 1 - log(2π)/2 + (log(2π)+log m)/2 + m(log m - 1)
  --        = 1 + log m / 2 + m(log m - 1)
  --        = m log m - m + log m / 2 + 1
  -- ≤ m log m - m + log m / 2 + 2.
  linarith

/-- The numerator product in the Cauchy formula for `shapeM m`:
`N_m := ∏_i ∏_{j > i} (s_j - s_i) = ∏_i ((m-1-i.val)!)`.
Each inner product over `j ∈ Ioi i` simplifies because `s_j - s_i = j.val - i.val`
takes values `1, 2, ..., (m-1-i.val)`. -/
private lemma shapeM_inner_diff_prod (m : ℕ) (i : Fin m) :
    ∏ j ∈ Finset.Ioi i, (shapeS m j - shapeS m i) =
      ((m - 1 - i.val).factorial : ℝ) := by
  -- Show the product equals (m - 1 - i.val)!.
  -- The set `Ioi i` consists of `j : Fin m` with `j > i`; for each such `j`,
  -- `s_j - s_i = j.val - i.val`. As `j.val` ranges over `i.val+1, ..., m-1`,
  -- the differences take values `1, 2, ..., m-1-i.val`, whose product is
  -- the factorial.
  have hkey : ∀ j ∈ Finset.Ioi i, shapeS m j - shapeS m i =
      ((j.val - i.val : ℕ) : ℝ) := by
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hij_val : i.val < j.val := hij
    unfold shapeS
    have hsub : ((j.val - i.val : ℕ) : ℝ) = (j.val : ℝ) - (i.val : ℝ) := by
      have : i.val ≤ j.val := le_of_lt hij_val
      push_cast [Nat.cast_sub this]
      ring
    rw [hsub]; ring
  rw [Finset.prod_congr rfl hkey]
  -- Now compute `∏_{j ∈ Ioi i, j : Fin m} (j.val - i.val) = (m-1-i.val)!`.
  -- Use the bijection: `Ioi i` in `Fin m` corresponds to `Finset.Ioo i.val m`
  -- in `ℕ`, and via `k ↦ k - i.val - 1` to `Finset.range (m - 1 - i.val)`.
  -- We use `Finset.prod_Ioi_eq_prod_range` or direct manipulation.
  -- Direct path: rewrite as a product over `k : Fin (m - 1 - i.val)`.
  have hbij : (∏ j ∈ Finset.Ioi i, ((j.val - i.val : ℕ) : ℝ)) =
      ∏ k ∈ Finset.range (m - 1 - i.val), ((k + 1 : ℕ) : ℝ) := by
    -- Use `Finset.prod_bij'` with explicit forward (j ↦ j.val - i.val - 1)
    -- and backward (k ↦ ⟨i.val + 1 + k, _⟩) maps.
    refine Finset.prod_bij'
      (fun (j : Fin m) (_ : j ∈ Finset.Ioi i) => j.val - i.val - 1)
      (fun (k : ℕ) (hk : k ∈ Finset.range (m - 1 - i.val)) =>
        (⟨i.val + 1 + k, by
          simp only [Finset.mem_range] at hk
          have him : i.val < m := i.isLt
          omega⟩ : Fin m))
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hij_val : i.val < j.val := hij
      simp only [Finset.mem_range]
      have hjm : j.val < m := j.isLt
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ioi]
      exact Fin.lt_def.mpr (by simp; omega)
    · intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hij_val : i.val < j.val := hij
      apply Fin.ext
      simp
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      show i.val + 1 + k - i.val - 1 = k
      omega
    · intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hij_val : i.val < j.val := hij
      have heq : j.val - i.val = (j.val - i.val - 1) + 1 := by omega
      norm_cast
  rw [hbij]
  -- `∏_{k=0}^{N-1} (k+1) = N!` using `Finset.prod_range_factorial` or direct.
  have : ∀ N : ℕ, ∏ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) = (N.factorial : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      rw [Nat.factorial_succ]
      push_cast
      ring
  exact this _

/-- The total numerator log: `log N_m = ∑_{n=0}^{m-1} log(n!)`. -/
private lemma shapeM_numerator_log_eq (m : ℕ) :
    Real.log (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (shapeS m j - shapeS m i)) =
      ∑ n ∈ Finset.range m, Real.log ((n.factorial : ℝ)) := by
  -- Use `shapeM_inner_diff_prod` pointwise and `Real.log_prod` over the outer.
  have hpos : ∀ i : Fin m, 0 < ∏ j ∈ Finset.Ioi i, (shapeS m j - shapeS m i) := by
    intro i
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hij_val : i.val < j.val := hij
    unfold shapeS
    have : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij_val
    linarith
  have hpos_prod : 0 < ∏ i : Fin m,
      ∏ j ∈ Finset.Ioi i, (shapeS m j - shapeS m i) :=
    Finset.prod_pos (fun i _ => hpos i)
  rw [Real.log_prod (fun i _ => (hpos i).ne')]
  -- Now reindex the outer sum from `Fin m` to `Finset.range m` (via `i ↦ m-1-i.val`).
  have hpoint : ∀ i : Fin m, Real.log (∏ j ∈ Finset.Ioi i, (shapeS m j - shapeS m i)) =
      Real.log (((m - 1 - i.val).factorial : ℝ)) := by
    intro i
    rw [shapeM_inner_diff_prod m i]
  rw [Finset.sum_congr rfl (fun i _ => hpoint i)]
  -- Reindex `i : Fin m ↦ m - 1 - i.val : Finset.range m`. Use `sum_bij'`.
  refine Finset.sum_bij'
    (fun (i : Fin m) (_ : i ∈ (Finset.univ : Finset (Fin m))) => m - 1 - i.val)
    (fun (k : ℕ) (hk : k ∈ Finset.range m) =>
      (⟨m - 1 - k, by
        simp only [Finset.mem_range] at hk
        omega⟩ : Fin m))
    ?_ ?_ ?_ ?_ ?_
  · intro i _; simp only [Finset.mem_range]; have := i.isLt; omega
  · intro k hk; exact Finset.mem_univ _
  · intro i _
    apply Fin.ext
    show m - 1 - (m - 1 - i.val) = i.val
    have := i.isLt
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    show m - 1 - (m - 1 - k) = k
    omega
  · intro i _
    rfl

/-- The denominator log: each pairwise sum `s_q + s_{q'}` is at most `4m`,
so `log(s_q + s_{q'}) ≤ log(4m) ≤ log m + 3` for `m ≥ 1`. -/
private lemma shapeM_denominator_log_le {m : ℕ} (hm : 1 ≤ m)
    (i j : Fin m) :
    Real.log (shapeS m i + shapeS m j) ≤ Real.log m + 3 := by
  have hsi := shapeS_le_two_mul hm i
  have hsj := shapeS_le_two_mul hm j
  have hsum_le : shapeS m i + shapeS m j ≤ 4 * (m : ℝ) := by linarith
  have hsum_pos : 0 < shapeS m i + shapeS m j := shapeM_sum_pos m i j
  have hlog_le : Real.log (shapeS m i + shapeS m j) ≤ Real.log (4 * (m : ℝ)) :=
    Real.log_le_log hsum_pos hsum_le
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog_4m : Real.log (4 * (m : ℝ)) = Real.log 4 + Real.log m := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hm_pos.ne']
  rw [hlog_4m] at hlog_le
  have hlog_4 : Real.log 4 ≤ 3 := by
    have h : Real.log 4 ≤ 4 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  linarith

/-- Bound on the numerator log: `log N_m ≥ (m(m-1)/2) log m - m²` for `m ≥ 1`.

Uses Stirling lower `log(n!) ≥ n log n - n` and the elementary
`n log n ≥ n log m - (m - n)` (from `log(m/n) ≤ m/n - 1`). -/
private lemma shapeM_numerator_log_ge {m : ℕ} (hm : 1 ≤ m) :
    Real.log (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (shapeS m j - shapeS m i)) ≥
      ((m : ℝ) * (m - 1) / 2) * Real.log m - (m : ℝ)^2 := by
  rw [shapeM_numerator_log_eq]
  -- Goal: ∑ n ∈ range m, log(n!) ≥ m(m-1)/2 · log m - m²
  -- For each n ≥ 1: log(n!) ≥ n log n - n ≥ n log m - (m - n) - n = n log m - m
  -- Sum over n = 1, ..., m-1: ≥ (m(m-1)/2) log m - m(m-1) ≥ (m(m-1)/2) log m - m²
  have hkey : ∀ n ∈ Finset.range m, Real.log ((n.factorial : ℝ)) ≥
      (n : ℝ) * Real.log m - (m : ℝ) := by
    intro n hn
    simp at hn
    by_cases h0 : n = 0
    · subst h0
      simp only [Nat.cast_zero, zero_mul, zero_sub, Nat.factorial_zero, Nat.cast_one,
        Real.log_one, ge_iff_le]
      have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
      have hStir : (n : ℝ) * Real.log n - n ≤ Real.log n.factorial :=
        log_factorial_lower hn1
      -- Show n log n ≥ n log m - (m - n).
      -- n log n - n log m = n log(n/m) ≥ n · (1 - m/n) = n - m  (since log x ≥ 1 - 1/x)
      -- Use Real.log_le_sub_one_of_pos applied to m/n: log(m/n) ≤ m/n - 1.
      -- So n log n ≥ n log m - n(m/n - 1) = n log m - m + n ≥ n log m - m.
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
      have hmn_pos : (0 : ℝ) < (m : ℝ) / n := div_pos hm_pos hn_pos
      have hlog_div : Real.log ((m : ℝ) / n) ≤ (m : ℝ) / n - 1 :=
        Real.log_le_sub_one_of_pos hmn_pos
      have hlog_split : Real.log ((m : ℝ) / n) = Real.log m - Real.log n :=
        Real.log_div hm_pos.ne' hn_pos.ne'
      rw [hlog_split] at hlog_div
      -- log m - log n ≤ m/n - 1
      -- Multiply by n: n log m - n log n ≤ m - n.
      have hmul : (n : ℝ) * (Real.log m - Real.log n) ≤ (n : ℝ) * ((m : ℝ) / n - 1) := by
        apply mul_le_mul_of_nonneg_left hlog_div hn_pos.le
      have hmn_simp : (n : ℝ) * ((m : ℝ) / n - 1) = (m : ℝ) - n := by
        field_simp
      rw [hmn_simp] at hmul
      have hexp : (n : ℝ) * (Real.log m - Real.log n) = n * Real.log m - n * Real.log n := by
        ring
      rw [hexp] at hmul
      -- So n log n ≥ n log m - (m - n).
      have hnlogn_ge : (n : ℝ) * Real.log n ≥ n * Real.log m - (m - n) := by linarith
      -- Combine: log(n!) ≥ n log n - n ≥ n log m - (m - n) - n = n log m - m.
      linarith
  -- Sum the inequality.
  have hsum : ∑ n ∈ Finset.range m, ((n : ℝ) * Real.log m - (m : ℝ)) ≤
      ∑ n ∈ Finset.range m, Real.log ((n.factorial : ℝ)) :=
    Finset.sum_le_sum hkey
  have hsum_eval : ∑ n ∈ Finset.range m, ((n : ℝ) * Real.log m - (m : ℝ)) =
      ((m : ℝ) * (m - 1) / 2) * Real.log m - (m : ℝ)^2 := by
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    rw [Finset.sum_const, Finset.card_range]
    have hsumcast : ∑ n ∈ Finset.range m, (n : ℝ) = (m * (m - 1) / 2 : ℝ) := by
      -- Use Gauss sum: ∑_{n=0}^{m-1} n = m(m-1)/2.
      clear hkey hsum hm
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    rw [hsumcast]
    have h_msq : (m : ℝ)^2 = m * m := by ring
    rw [h_msq]
    ring
  linarith

/-- **Stirling lower bound on `log det M` (explicit form).**
For all `m ≥ 1`, `log det M ≥ -100 · m²`. The witness `C₁ = 100` is
comfortably loose to absorb the `m log m ≤ m²` slack.

The proof combines:
- Cauchy formula: `det M = (∏_{q<q'} (s_{q'} - s_q))² / ∏_{q,q'} (s_q + s_{q'})`
- Stirling for the numerator log: each `log(n!) ≥ n log n - n`
- Coarse upper bound on the denominator log: `∑_{q,q'} log(s_q + s_{q'}) ≤ m²(log m + 2)`

The leading `m² log m` terms cancel exactly, leaving residual `≤ 5 m²`. -/
theorem shapeM_log_det_ge_explicit :
    ∀ m : ℕ, 1 ≤ m →
      -((100 : ℝ) * (m : ℝ) ^ 2) ≤ Real.log (shapeM m).det := by
  intro m hm
  -- Apply Cauchy formula: det shapeM = N²/D.
  have hcauchy := cauchy_det_formula_fin m (shapeS m) (shapeM_sum_pos m)
    (fun i j hij => shapeS_inj hij)
  set N : ℝ := ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
    (shapeS m j - shapeS m i) with hN_def
  set D : ℝ := ∏ i : Fin m, ∏ j : Fin m, (shapeS m i + shapeS m j) with hD_def
  -- shapeM = ... = N² / D
  have hshapeM_eq : (shapeM m).det = N^2 / D := by
    unfold shapeM
    exact hcauchy
  -- Positivity of N and D.
  have hN_pos : 0 < N := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hij_val : i.val < j.val := hij
    unfold shapeS
    have : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij_val
    linarith
  have hD_pos : 0 < D := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j _
    exact shapeM_sum_pos m i j
  have hNsq_pos : 0 < N^2 := by positivity
  have hdiv_pos : 0 < N^2 / D := div_pos hNsq_pos hD_pos
  -- Take log: log det = 2 log N - log D.
  have hlog_det_eq : Real.log (shapeM m).det = 2 * Real.log N - Real.log D := by
    rw [hshapeM_eq, Real.log_div hNsq_pos.ne' hD_pos.ne', Real.log_pow]
    push_cast; ring
  rw [hlog_det_eq]
  -- Lower bound on log N.
  have hlogN_ge : Real.log N ≥
      ((m : ℝ) * (m - 1) / 2) * Real.log m - (m : ℝ)^2 := by
    exact shapeM_numerator_log_ge hm
  -- Upper bound on log D.
  have hlogD_le : Real.log D ≤ (m : ℝ)^2 * (Real.log m + 3) := by
    -- log D = ∑_i ∑_j log(s_i + s_j) ≤ m² · (log m + 3).
    have hprod_pos : ∀ i : Fin m,
        0 < ∏ j : Fin m, (shapeS m i + shapeS m j) := fun i =>
      Finset.prod_pos (fun j _ => shapeM_sum_pos m i j)
    rw [hD_def, Real.log_prod (fun i _ => (hprod_pos i).ne')]
    have hsum_outer : ∀ i : Fin m,
        Real.log (∏ j : Fin m, (shapeS m i + shapeS m j)) ≤
        (m : ℝ) * (Real.log m + 3) := by
      intro i
      rw [Real.log_prod (fun j _ => (shapeM_sum_pos m i j).ne')]
      have h_each : ∀ j : Fin m, Real.log (shapeS m i + shapeS m j) ≤
          Real.log m + 3 := fun j => shapeM_denominator_log_le hm i j
      have hbnd : ∑ j : Fin m, Real.log (shapeS m i + shapeS m j) ≤
          ∑ _j : Fin m, (Real.log m + 3) :=
        Finset.sum_le_sum (fun j _ => h_each j)
      have hconst : ∑ _j : Fin m, ((Real.log m + 3 : ℝ)) =
          (m : ℝ) * (Real.log m + 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
      linarith
    have h_outer_bound : ∑ i : Fin m,
        Real.log (∏ j : Fin m, (shapeS m i + shapeS m j)) ≤
        (m : ℝ) * ((m : ℝ) * (Real.log m + 3)) := by
      have hbnd := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsum_outer i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hbnd
      convert hbnd using 1
      ring
    have h_sq : (m : ℝ)^2 * (Real.log m + 3) =
        (m : ℝ) * ((m : ℝ) * (Real.log m + 3)) := by ring
    linarith [h_sq]
  -- Combine: 2 log N - log D ≥ m(m-1) log m - 2m² - m²(log m + 2)
  --        = m(m-1) log m - 2m² - m² log m - 2m²
  --        = (m² - m - m²) log m - 4m² = -m log m - 4m²
  -- And m log m ≤ m·m = m² (since log m ≤ m), so ≥ -m² - 4m² = -5m².
  have hlog_m_le : Real.log m ≤ (m : ℝ) := by
    rcases Nat.lt_or_ge 1 m with h2 | h2
    · have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
      have h := Real.log_le_sub_one_of_pos hm_pos
      linarith
    · interval_cases m
      simp [Real.log_one]
  have hlog_m_nn : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  -- Combine the bounds. Use that:
  --   2 log N ≥ m(m-1) log m - 2m²
  --   log D ≤ m²(log m + 2) = m² log m + 2m²
  -- So 2 log N - log D ≥ m(m-1) log m - 2m² - m² log m - 2m²
  --                    = (m² - m - m²) log m - 4m² = -m log m - 4m²
  --                    ≥ -m·m - 4m² = -5m².
  have hcombined : 2 * Real.log N - Real.log D ≥
      ((m : ℝ) * (m - 1)) * Real.log m - 2 * (m : ℝ)^2 -
      ((m : ℝ)^2 * (Real.log m + 3)) := by
    have h1 : 2 * Real.log N ≥ ((m : ℝ) * (m - 1)) * Real.log m - 2 * (m : ℝ)^2 := by
      have := hlogN_ge
      linarith
    linarith
  have hsimp : ((m : ℝ) * (m - 1)) * Real.log m - 2 * (m : ℝ)^2 -
      ((m : ℝ)^2 * (Real.log m + 3)) =
      -((m : ℝ) * Real.log m) - 5 * (m : ℝ)^2 := by ring
  rw [hsimp] at hcombined
  -- Now -m log m - 5m² ≥ -m² - 5m² = -6m² ≥ -100m².
  have h_mlogm : (m : ℝ) * Real.log m ≤ (m : ℝ)^2 := by
    have : (m : ℝ) * Real.log m ≤ (m : ℝ) * m := by
      exact mul_le_mul_of_nonneg_left hlog_m_le hm_nn
    have h_msq : (m : ℝ)^2 = m * m := by ring
    linarith
  have hbound : -((m : ℝ) * Real.log m) - 5 * (m : ℝ)^2 ≥ -(100 * (m : ℝ)^2) := by
    have hmsq_nn : 0 ≤ (m : ℝ)^2 := by positivity
    linarith
  linarith

/-- **Stirling lower bound on `log det M` (existential form).**
There exists an absolute constant `C₁ > 0` such that for all `m ≥ 1`,
`log det M ≥ -C₁ · m²`. Thin wrapper around `shapeM_log_det_ge_explicit`
with `C₁ = 100`. -/
theorem shapeM_log_det_ge :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ m : ℕ, 1 ≤ m →
      -(C₁ * (m : ℝ) ^ 2) ≤ Real.log (shapeM m).det :=
  ⟨100, by norm_num, shapeM_log_det_ge_explicit⟩

-- ## §5. Final assembly

/-- The Cauchy matrix on the hierarchical grid. -/
noncomputable def hierCauchy (m : ℕ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  Matrix.of fun i j => 1 / (hierGrid m i + hierGrid m j)

/-- Pairwise distinctness of `hierGrid` values: `δ(p,q) ≠ δ(p',q')` whenever
`(p, q) ≠ (p', q')`. Uses that `4^k` dominates `2m` so different `p` values
force different scales. -/
lemma hierGrid_inj {m : ℕ} (hm : 1 ≤ m) :
    ∀ i j : Fin m × Fin m, i ≠ j → hierGrid m i ≠ hierGrid m j := by
  intro ⟨p, q⟩ ⟨p', q'⟩ hne
  unfold hierGrid
  intro heq
  by_cases hp : p = p'
  · subst hp
    have hq : q ≠ q' := by
      intro hq
      apply hne
      rw [hq]
    have h4_pos : (0 : ℝ) < (4 : ℝ)^(p.val + m) :=
      pow_pos (by norm_num) _
    have hfac : (m : ℝ) + q.val + 1 = (m : ℝ) + q'.val + 1 := by
      have := mul_left_cancel₀ (ne_of_gt h4_pos) heq
      exact this
    have : (q.val : ℝ) = (q'.val : ℝ) := by linarith
    have hqq' : q.val = q'.val := by exact_mod_cast this
    exact hq (Fin.ext hqq')
  · -- p ≠ p': WLOG p.val < p'.val. Then 4^(p'+m) (m+q'+1) > 4^(p+m) (2m)
    --        ≥ 4^(p+m) (m+q+1).
    -- Concretely show LHS ≠ RHS.
    have hp_ne : p.val ≠ p'.val := fun h => hp (Fin.ext h)
    rcases lt_or_gt_of_ne hp_ne with hpp' | hpp'
    · -- p.val < p'.val
      -- 4^(p+m) · (m+q+1) ≤ 4^(p+m) · 2m < 4^(p'+m) · (m+1) ≤ 4^(p'+m) · (m+q'+1)
      exfalso
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
      have hLHS_le : (4 : ℝ)^(p.val + m) * ((m : ℝ) + q.val + 1) ≤
          (4 : ℝ)^(p.val + m) * (2 * (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hq : (q.val : ℝ) ≤ (m : ℝ) - 1 := by
          have hq_lt : q.val < m := q.isLt
          have : (q.val : ℝ) ≤ (m - 1 : ℕ) := by
            exact_mod_cast Nat.le_sub_one_of_lt hq_lt
          have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            push_cast [Nat.cast_sub hm]
            ring
          linarith
        linarith
      have hRHS_ge : (4 : ℝ)^(p.val + m) * (2 * (m : ℝ)) <
          (4 : ℝ)^(p'.val + m) * ((m : ℝ) + q'.val + 1) := by
        have hq' : (1 : ℝ) ≤ (q'.val : ℝ) + 1 := by
          have : (0 : ℝ) ≤ q'.val := Nat.cast_nonneg _
          linarith
        -- 4^(p+m) · 2m < 4^(p'+m) · (m+1) ≤ 4^(p'+m) · (m+q'+1)
        have h_step1 : (4 : ℝ)^(p.val + m) * (2 * (m : ℝ)) <
            (4 : ℝ)^(p'.val + m) * ((m : ℝ) + 1) := by
          have hpw : (4 : ℝ)^(p.val + m) * 4 ≤ (4 : ℝ)^(p'.val + m) := by
            have : (4 : ℝ)^(p.val + m) * (4 : ℝ)^1 ≤ (4 : ℝ)^(p'.val + m) := by
              rw [← pow_add]
              apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
              omega
            simpa using this
          have h4pos : (0 : ℝ) < (4 : ℝ)^(p.val + m) := pow_pos (by norm_num) _
          have h2m_lt : 2 * (m : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
          calc (4 : ℝ)^(p.val + m) * (2 * (m : ℝ))
              < (4 : ℝ)^(p.val + m) * (4 * ((m : ℝ) + 1)) := by
                exact mul_lt_mul_of_pos_left h2m_lt h4pos
            _ = ((4 : ℝ)^(p.val + m) * 4) * ((m : ℝ) + 1) := by ring
            _ ≤ (4 : ℝ)^(p'.val + m) * ((m : ℝ) + 1) := by
                apply mul_le_mul_of_nonneg_right hpw
                linarith
        have h_step2 : (4 : ℝ)^(p'.val + m) * ((m : ℝ) + 1) ≤
            (4 : ℝ)^(p'.val + m) * ((m : ℝ) + q'.val + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (0 : ℝ) ≤ q'.val := Nat.cast_nonneg _
          linarith
        linarith
      linarith
    · -- p'.val < p.val: symmetric
      exfalso
      have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
      have hRHS_le : (4 : ℝ)^(p'.val + m) * ((m : ℝ) + q'.val + 1) ≤
          (4 : ℝ)^(p'.val + m) * (2 * (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hq : (q'.val : ℝ) ≤ (m : ℝ) - 1 := by
          have hq_lt : q'.val < m := q'.isLt
          have : (q'.val : ℝ) ≤ (m - 1 : ℕ) := by
            exact_mod_cast Nat.le_sub_one_of_lt hq_lt
          have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            push_cast [Nat.cast_sub hm]
            ring
          linarith
        linarith
      have hLHS_ge : (4 : ℝ)^(p'.val + m) * (2 * (m : ℝ)) <
          (4 : ℝ)^(p.val + m) * ((m : ℝ) + q.val + 1) := by
        have hq : (1 : ℝ) ≤ (q.val : ℝ) + 1 := by
          have : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
          linarith
        have h_step1 : (4 : ℝ)^(p'.val + m) * (2 * (m : ℝ)) <
            (4 : ℝ)^(p.val + m) * ((m : ℝ) + 1) := by
          have hpw : (4 : ℝ)^(p'.val + m) * 4 ≤ (4 : ℝ)^(p.val + m) := by
            have : (4 : ℝ)^(p'.val + m) * (4 : ℝ)^1 ≤ (4 : ℝ)^(p.val + m) := by
              rw [← pow_add]
              apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
              omega
            simpa using this
          have h4pos : (0 : ℝ) < (4 : ℝ)^(p'.val + m) := pow_pos (by norm_num) _
          have h2m_lt : 2 * (m : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
          calc (4 : ℝ)^(p'.val + m) * (2 * (m : ℝ))
              < (4 : ℝ)^(p'.val + m) * (4 * ((m : ℝ) + 1)) := by
                exact mul_lt_mul_of_pos_left h2m_lt h4pos
            _ = ((4 : ℝ)^(p'.val + m) * 4) * ((m : ℝ) + 1) := by ring
            _ ≤ (4 : ℝ)^(p.val + m) * ((m : ℝ) + 1) := by
                apply mul_le_mul_of_nonneg_right hpw
                linarith
        have h_step2 : (4 : ℝ)^(p.val + m) * ((m : ℝ) + 1) ≤
            (4 : ℝ)^(p.val + m) * ((m : ℝ) + q.val + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
          linarith
        linarith
      linarith

/-- Strict positivity of the hierarchical Cauchy determinant (any `m ≥ 1`). -/
lemma hierCauchy_det_pos {m : ℕ} (hm : 1 ≤ m) : 0 < (hierCauchy m).det := by
  unfold hierCauchy
  have hpos : ∀ i j : Fin m × Fin m, 0 < hierGrid m i + hierGrid m j :=
    hierGrid_sum_pos m
  have hdiff : ∀ i j : Fin m × Fin m, i ≠ j → hierGrid m i ≠ hierGrid m j :=
    hierGrid_inj hm
  exact cauchy_det_pos (hierGrid m) hpos hdiff

/- ### §5.1 Helper bounds for the assembly -/

/-- Sum of `log a_p` is bounded by `2 m^2 log 4`. We have
`∑_p log a_p = log 4 · ∑_p (p + m) = log 4 · (m(m-1)/2 + m²) ≤ (3/2) m² log 4`. -/
private lemma sum_log_scaleA_le {m : ℕ} (_hm : 1 ≤ m) :
    ∑ p : Fin m, Real.log (scaleA m p) ≤ 2 * (m : ℝ)^2 * Real.log 4 := by
  -- log scaleA m p = (p+m) log 4. Sum: log 4 * sum (p+m).
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have heach : ∀ p : Fin m, Real.log (scaleA m p) =
      ((p.val + m : ℕ) : ℝ) * Real.log 4 := log_scaleA m
  calc ∑ p : Fin m, Real.log (scaleA m p)
      = ∑ p : Fin m, ((p.val + m : ℕ) : ℝ) * Real.log 4 := by
        apply Finset.sum_congr rfl
        intros p _; exact heach p
    _ = (∑ p : Fin m, ((p.val + m : ℕ) : ℝ)) * Real.log 4 := by
        rw [← Finset.sum_mul]
    _ ≤ (∑ _p : Fin m, (2 * m : ℝ)) * Real.log 4 := by
        apply mul_le_mul_of_nonneg_right _ hlog4_pos.le
        apply Finset.sum_le_sum
        intros p _
        push_cast
        have : (p.val : ℝ) ≤ (m : ℝ) := by
          have : p.val < m := p.isLt
          exact_mod_cast this.le
        linarith
    _ = (m : ℝ) * (2 * m) * Real.log 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = 2 * (m : ℝ)^2 * Real.log 4 := by ring

/-- Each `log a_p` is nonnegative since `a_p = 4^(p+m) ≥ 1`. -/
private lemma log_scaleA_nonneg (m : ℕ) (p : Fin m) : 0 ≤ Real.log (scaleA m p) := by
  rw [log_scaleA]
  apply mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))

/-- Total cross-block sum of `crossEta` summed over `p<r, q, s`, bounded by
`(8/3) m^3` via the factorization `crossEta = (a_p/a_r)(s_q/s_s)` and the
geometric series bound on the scale ratios. -/
private lemma cross_block_eta_sum_bound_real {m : ℕ} (hm : 1 ≤ m) :
    ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
        (if p.val < r.val then crossEta m p r q s else 0) ≤
      (8/3 : ℝ) * (m : ℝ)^3 := by
  -- Use the factorization crossEta = (a_p/a_r) * (s_q/s_s) and split the sum.
  -- Step 1: rewrite as ∑_{p,r} (if p<r then a_p/a_r else 0) * ∑_{q,s} s_q/s_s.
  have hfac :
      ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
          (if p.val < r.val then crossEta m p r q s else 0) =
        (∑ p : Fin m, ∑ r : Fin m,
            (if p.val < r.val then scaleA m p / scaleA m r else 0)) *
        (∑ q : Fin m, ∑ s : Fin m, shapeS m q / shapeS m s) := by
    -- Pull the (q,s) factor out of the (p,r) sum.
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intros p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intros r _
    by_cases hpr : p.val < r.val
    · simp only [hpr, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros s _
      unfold crossEta
      ring
    · simp only [hpr, if_false]
      rw [zero_mul]
      symm; rw [Finset.sum_eq_zero]; intros q _
      rw [Finset.sum_eq_zero]; intros s _
      simp
  rw [hfac]
  -- Step 2: bound the (q,s)-sum by 2 m².
  have hqs_bnd : (∑ q : Fin m, ∑ s : Fin m, shapeS m q / shapeS m s) ≤ 2 * (m : ℝ)^2 := by
    have heach : ∀ q s : Fin m, shapeS m q / shapeS m s ≤ 2 :=
      fun q s => shapeS_ratio_le hm q s
    calc ∑ q : Fin m, ∑ s : Fin m, shapeS m q / shapeS m s
        ≤ ∑ _q : Fin m, ∑ _s : Fin m, (2 : ℝ) := by
          apply Finset.sum_le_sum; intros q _
          apply Finset.sum_le_sum; intros s _
          exact heach q s
      _ = 2 * (m : ℝ)^2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  -- Step 3: bound the (p,r)-sum by (4/3) m via geometric series.
  have hpr_bnd : (∑ p : Fin m, ∑ r : Fin m,
      (if p.val < r.val then scaleA m p / scaleA m r else 0)) ≤ (4/3 : ℝ) * m := by
    -- Per fixed r, the sum over p<r is bounded by 4/3 (geom series).
    -- Sum over r in Fin m: bounded by m · 4/3 = (4/3) m.
    -- Step 1: swap sums to put `r` outside.
    rw [Finset.sum_comm]
    -- Now goal: ∑_r ∑_p (if p<r then ...) ≤ (4/3) m.
    have hper_r : ∀ r : Fin m,
        ∑ p : Fin m, (if p.val < r.val then scaleA m p / scaleA m r else 0) ≤
          (4/3 : ℝ) := by
      intro r
      -- For each p<r, scaleA m p / scaleA m r = (1/4)^(r.val - p.val).
      -- Bound by ∑_{k=0}^{m-1} (1/4)^k ≤ 4/3.
      -- We use: each term ≤ (1/4)^(r.val - p.val) when p<r.
      -- Strategy: reindex by k = r.val - p.val; for p < r, k ranges over {1, ..., r.val}.
      -- The LHS sum equals ∑_{p < r} (1/4)^(r.val - p.val) = ∑_{k=1}^{r.val} (1/4)^k.
      -- This is bounded by ∑_{d=0}^{m-1} (1/4)^d ≤ 4/3 since {1,...,r.val} ⊂ {0,...,m-1}.
      -- We use: ∑_{p : Fin m} (if p<r then (1/4)^(r-p) else 0) = ∑_{k=1}^r (1/4)^k.
      -- We bound each summand directly.
      -- Even simpler: each NON-ZERO term equals (1/4)^k for some k ∈ {1, ..., r.val}.
      -- And each (1/4)^k ≤ ∑_{d=0}^{m-1} (1/4)^d when k < m. Not directly useful as a per-term bound.
      -- Use the explicit formula: bound by the geometric sum directly via injection.
      -- Map each p < r to k = r.val - p.val ∈ Finset.range m. Show sum-LHS ≤ sum over k via map.
      -- This requires Finset.sum_image or similar.
      -- SIMPLER: use ∑_{p : Fin m} (if p.val < r.val then scaleA m p / scaleA m r else 0) =
      --        ∑_{p : Fin m, p.val < r.val} scaleA m p / scaleA m r  (using sum_filter or sum_ite).
      -- Then via reindexing p ↔ r.val - p.val, identify with ∑_{k=1}^{r.val} (1/4)^k.
      -- That's tedious. Let's use a direct upper bound: each term ≤ (1/4)^1 = 1/4
      -- and the number of terms with p<r is at most r.val ≤ m. This gives LHS ≤ m/4.
      -- Then per-r bound: m/4. Sum over r: m²/4. Total ≤ m²/4 = (m/3) · (3m/4)... hmm.
      -- Wait we need ≤ 4/3 PER R. m/4 ≤ 4/3 iff m ≤ 16/3. So this doesn't work for m ≥ 6.
      -- We MUST use geometric sum.
      -- Use: (1/4)^(r-p) ≤ (1/4)^(r-p) (trivially), and bound the sum by
      -- ∑_{p : Fin m, p.val < r.val} (1/4)^(r.val - p.val).
      -- Reindex via the bijection p ↦ r.val - p.val from {p : p < r} to {1, ..., r}.
      -- This last sum ≤ ∑_{d ∈ range m, d ≥ 1} (1/4)^d ≤ ∑_{d ∈ range m} (1/4)^d ≤ 4/3.
      -- The reindexing is the painful part. Use Finset.sum_bij.
      have hsum_eq : ∑ p : Fin m, (if p.val < r.val then scaleA m p / scaleA m r else 0) =
          ∑ p ∈ (Finset.univ : Finset (Fin m)).filter (fun p => p.val < r.val),
            scaleA m p / scaleA m r := by
        rw [Finset.sum_filter]
      rw [hsum_eq]
      -- Now the sum is over filtered set. Reindex p ↦ r.val - p.val.
      -- Map the filtered set to a Finset of natural numbers (range r.val + 1) \ {0}.
      -- Use Finset.sum_nbij to reindex.
      -- For p with p.val < r.val, r.val - p.val ∈ {1, 2, ..., r.val}.
      -- Define: φ : {p : Fin m // p.val < r.val} → Finset.Ioc 0 r.val by p ↦ r.val - p.val.
      -- This is a bijection.
      have hsum_eq2 : ∑ p ∈ (Finset.univ : Finset (Fin m)).filter (fun p => p.val < r.val),
            scaleA m p / scaleA m r =
          ∑ k ∈ Finset.Ioc 0 r.val, (1/4 : ℝ)^k := by
        -- Reindex via p ↔ k = r.val - p.val using sum_nbij'.
        refine Finset.sum_nbij' (fun p => r.val - p.val) (fun k => ⟨r.val - k, ?_⟩)
          ?_ ?_ ?_ ?_ ?_
        · -- r.val - k < m: needs k ∈ Ioc 0 r.val so k ≥ 1, hence r.val - k ≤ r.val - 1 < r.val < m.
          -- Actually: k ≥ 0 anyway, r.val - k ≤ r.val < m.
          exact lt_of_le_of_lt (Nat.sub_le _ _) r.isLt
        · -- forward: p ∈ filter ↦ k ∈ Ioc 0 r.val.
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          simp only [Finset.mem_Ioc]
          omega
        · -- backward: k ∈ Ioc 0 r.val ↦ p ∈ filter (i.e., p.val < r.val).
          intro k hk
          simp only [Finset.mem_Ioc] at hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · -- left_inv: ⟨r.val - (r.val - p.val), _⟩ = p.
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          ext
          show r.val - (r.val - p.val) = p.val
          omega
        · -- right_inv: r.val - (r.val - k).val = k.
          intro k hk
          simp only [Finset.mem_Ioc] at hk
          show r.val - (r.val - k) = k
          omega
        · -- values match: scaleA m p / scaleA m r = (1/4)^(r.val - p.val).
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          show scaleA m p / scaleA m r = (1/4)^(r.val - p.val)
          unfold scaleA
          have h4pos_p : (0 : ℝ) < (4 : ℝ)^(p.val + m) := pow_pos (by norm_num) _
          have h4pos_r : (0 : ℝ) < (4 : ℝ)^(r.val + m) := pow_pos (by norm_num) _
          have hkey : (4 : ℝ)^(p.val + m) * (4 : ℝ)^(r.val - p.val) =
              (4 : ℝ)^(r.val + m) := by
            rw [← pow_add]; congr 1; omega
          rw [show ((1:ℝ)/4) = (4:ℝ)⁻¹ by norm_num, inv_pow]
          field_simp
          linarith
      rw [hsum_eq2]
      -- Now bound ∑_{k ∈ Ioc 0 r.val} (1/4)^k ≤ ∑_{d ∈ range m} (1/4)^d ≤ 4/3.
      have hr_le_m : r.val ≤ m := le_of_lt r.isLt
      have hsubset : Finset.Ioc 0 r.val ⊆ Finset.range m := by
        intro k hk
        simp only [Finset.mem_Ioc] at hk
        simp only [Finset.mem_range]
        omega
      have hnonneg : ∀ d ∈ Finset.range m \ Finset.Ioc 0 r.val, (0 : ℝ) ≤ (1/4 : ℝ)^d := by
        intros d _; exact pow_nonneg (by norm_num) _
      have hbnd : ∑ k ∈ Finset.Ioc 0 r.val, (1/4 : ℝ)^k ≤
          ∑ d ∈ Finset.range m, (1/4 : ℝ)^d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intros d _ _
        exact pow_nonneg (by norm_num) _
      linarith [geom_series_quarter_le hm]
    calc ∑ r : Fin m, ∑ p : Fin m,
            (if p.val < r.val then scaleA m p / scaleA m r else 0)
        ≤ ∑ _r : Fin m, (4/3 : ℝ) := Finset.sum_le_sum (fun r _ => hper_r r)
      _ = (m : ℝ) * (4/3) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
      _ = (4/3 : ℝ) * m := by ring
  -- Combine.
  have hqs_nn : 0 ≤ ∑ q : Fin m, ∑ s : Fin m, shapeS m q / shapeS m s := by
    apply Finset.sum_nonneg; intros q _
    apply Finset.sum_nonneg; intros s _
    exact (div_pos (shapeS_pos m q) (shapeS_pos m s)).le
  have hpr_nn : 0 ≤ ∑ p : Fin m, ∑ r : Fin m,
      (if p.val < r.val then scaleA m p / scaleA m r else 0) := by
    apply Finset.sum_nonneg; intros p _
    apply Finset.sum_nonneg; intros r _
    by_cases hpr : p.val < r.val
    · simp only [hpr, if_true]
      exact (div_pos (scaleA_pos m p) (scaleA_pos m r)).le
    · simp only [hpr, if_false]; exact le_refl 0
  have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  -- (4/3 m) * (2 m²) = (8/3) m³.
  have : (∑ p : Fin m, ∑ r : Fin m,
      (if p.val < r.val then scaleA m p / scaleA m r else 0)) *
      (∑ q : Fin m, ∑ s : Fin m, shapeS m q / shapeS m s) ≤
      ((4/3 : ℝ) * m) * (2 * (m : ℝ)^2) := by
    apply mul_le_mul hpr_bnd hqs_bnd hqs_nn
    nlinarith [hm_nn]
  have heq : ((4/3 : ℝ) * m) * (2 * (m : ℝ)^2) = (8/3) * (m : ℝ)^3 := by ring
  linarith

/- ### §5.1.5 Helpers for the algebraic identity -/

/-- Logged form of the in-block grid difference factorization. -/
private lemma log_hierGrid_inblock_diff_abs (m : ℕ) (p : Fin m) {q q' : Fin m}
    (hqq' : q ≠ q') :
    Real.log |hierGrid m (p, q) - hierGrid m (p, q')| =
      Real.log (scaleA m p) + Real.log |shapeS m q - shapeS m q'| := by
  rw [hierGrid_inblock_diff, abs_mul, abs_of_pos (scaleA_pos m p)]
  rw [Real.log_mul (ne_of_gt (scaleA_pos m p))]
  rw [abs_ne_zero]
  exact sub_ne_zero.mpr (shapeS_inj hqq')

/-- Diagonal contribution: `∑_i log(δᵢ + δᵢ) = m² log 2 + m·∑_p log a_p + m·∑_q log s_q`. -/
private lemma diagonal_log_contribution (m : ℕ) :
    ∑ i : Fin m × Fin m, Real.log (hierGrid m i + hierGrid m i) =
      (m : ℝ)^2 * Real.log 2 +
      (m : ℝ) * ∑ p : Fin m, Real.log (scaleA m p) +
      (m : ℝ) * ∑ q : Fin m, Real.log (shapeS m q) := by
  -- δᵢ + δᵢ = 2 · a_p · s_q. log = log 2 + log a_p + log s_q.
  have hpw : ∀ i : Fin m × Fin m,
      Real.log (hierGrid m i + hierGrid m i) =
        Real.log 2 + Real.log (scaleA m i.1) + Real.log (shapeS m i.2) := by
    rintro ⟨p, q⟩
    have hδ : hierGrid m (p, q) = scaleA m p * shapeS m q := rfl
    have h2 : hierGrid m (p, q) + hierGrid m (p, q) = 2 * (scaleA m p * shapeS m q) := by
      rw [hδ]; ring
    rw [h2]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (mul_ne_zero (ne_of_gt (scaleA_pos m p)) (ne_of_gt (shapeS_pos m q)))]
    rw [Real.log_mul (ne_of_gt (scaleA_pos m p)) (ne_of_gt (shapeS_pos m q))]
    ring
  simp_rw [hpw]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have h_a : ∑ i : Fin m × Fin m, Real.log (scaleA m i.1) =
      (m : ℝ) * ∑ p : Fin m, Real.log (scaleA m p) := by
    rw [show (Finset.univ : Finset (Fin m × Fin m)) = Finset.univ ×ˢ Finset.univ from rfl,
        Finset.sum_product]
    rw [Finset.sum_comm]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h_s : ∑ i : Fin m × Fin m, Real.log (shapeS m i.2) =
      (m : ℝ) * ∑ q : Fin m, Real.log (shapeS m q) := by
    rw [show (Finset.univ : Finset (Fin m × Fin m)) = Finset.univ ×ˢ Finset.univ from rfl,
        Finset.sum_product]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [h_a, h_s]
  ring

/-- Decomposition of `offDiag(Fin m × Fin m)` into in-block (same first coord, different
second coord) and cross-block (different first coord) pieces. -/
private lemma offDiag_block_decomp {m : ℕ}
    (f : (Fin m × Fin m) × (Fin m × Fin m) → ℝ) :
    ∑ pq ∈ (Finset.univ : Finset (Fin m × Fin m)).offDiag, f pq =
      (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
          f ((p, qq'.1), (p, qq'.2)))
      + (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag,
          ∑ q : Fin m, ∑ s : Fin m, f ((pr.1, q), (pr.2, s))) := by
  -- Split offDiag by predicate `pq.1.1 = pq.2.1`.
  set S := (Finset.univ : Finset (Fin m × Fin m)).offDiag
  have hsplit : ∑ pq ∈ S, f pq =
      (∑ pq ∈ S.filter (fun pq => pq.1.1 = pq.2.1), f pq) +
      (∑ pq ∈ S.filter (fun pq => ¬ pq.1.1 = pq.2.1), f pq) := by
    rw [Finset.sum_filter_add_sum_filter_not S (fun pq => pq.1.1 = pq.2.1) f]
  rw [hsplit]
  congr 1
  · -- In-block: pq.1.1 = pq.2.1 and pq.1 ≠ pq.2 means pq.1.2 ≠ pq.2.2.
    rw [show (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
          f ((p, qq'.1), (p, qq'.2))) =
        ∑ x ∈ (Finset.univ : Finset (Fin m)) ×ˢ
              ((Finset.univ : Finset (Fin m)).offDiag),
          f ((x.1, x.2.1), (x.1, x.2.2)) by
        rw [Finset.sum_product]]
    -- Bijection: ((p, q), (p, q')) ↔ (p, (q, q')).
    refine Finset.sum_nbij'
      (i := fun pq => (pq.1.1, (pq.1.2, pq.2.2)))
      (j := fun x => ((x.1, x.2.1), (x.1, x.2.2)))
      ?_ ?_ ?_ ?_ ?_
    · intro pq hpq
      have hpq' := hpq
      simp only [Finset.mem_filter, S, Finset.mem_offDiag, Finset.mem_univ,
        true_and] at hpq'
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_offDiag, true_and]
      obtain ⟨hne, heq⟩ := hpq'
      intro h
      apply hne
      exact Prod.ext heq h
    · intro x hx
      have hx' := hx
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_offDiag, true_and] at hx'
      simp only [Finset.mem_filter, S, Finset.mem_offDiag, Finset.mem_univ, true_and,
        and_true]
      intro h
      apply hx'
      exact congrArg Prod.snd h
    · intro pq hpq
      have hpq' := hpq
      simp only [Finset.mem_filter, S, Finset.mem_offDiag, Finset.mem_univ,
        true_and] at hpq'
      obtain ⟨_, heq⟩ := hpq'
      have h21_11 : pq.2.1 = pq.1.1 := heq.symm
      ext <;> simp [h21_11]
    · intro x _; rfl
    · intro pq hpq
      have hpq' := hpq
      simp only [Finset.mem_filter, S, Finset.mem_offDiag, Finset.mem_univ,
        true_and] at hpq'
      obtain ⟨_, heq⟩ := hpq'
      have h21_11 : pq.2.1 = pq.1.1 := heq.symm
      simp only []
      congr 1
      ext <;> simp [h21_11]
  · -- Cross-block: pq.1.1 ≠ pq.2.1.
    rw [show (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag,
          ∑ q : Fin m, ∑ s : Fin m, f ((pr.1, q), (pr.2, s))) =
        ∑ y ∈ (Finset.univ : Finset (Fin m)).offDiag ×ˢ
              ((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))),
          f ((y.1.1, y.2.1), (y.1.2, y.2.2)) by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl; intros pr _
        rw [Finset.sum_product]]
    -- Bijection: ((p, q), (r, s)) with p ≠ r ↔ ((p, r), (q, s)).
    refine Finset.sum_nbij'
      (i := fun pq => ((pq.1.1, pq.2.1), (pq.1.2, pq.2.2)))
      (j := fun y => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      ?_ ?_ ?_ ?_ ?_
    · intro pq hpq
      have hpq' := hpq
      simp only [Finset.mem_filter, S, Finset.mem_offDiag, Finset.mem_univ,
        true_and] at hpq'
      simp only [Finset.mem_product, Finset.mem_offDiag, Finset.mem_univ, true_and,
        and_true]
      exact hpq'.2
    · intro y hy
      have hy' := hy
      simp only [Finset.mem_product, Finset.mem_offDiag, Finset.mem_univ, true_and,
        and_true] at hy'
      simp only [Finset.mem_filter, S, Finset.mem_offDiag, Finset.mem_univ, true_and]
      refine ⟨?_, hy'⟩
      intro h
      apply hy'
      exact congrArg Prod.fst h
    · intro pq _
      rfl
    · intro y _
      rfl
    · intro pq _
      rfl

/-- In-block log contribution: per-block, the sum over pairs `(q, q')` with `q ≠ q'` of
`log|δ(p,q) - δ(p,q')| - log(δ(p,q) + δ(p,q'))` simplifies to a `p`-independent
sum involving only `shapeS` (since `log a_p` cancels between `|...|` and `+`). -/
private lemma inblock_log_pair_diff (m : ℕ) (p : Fin m) {q q' : Fin m} (hqq' : q ≠ q') :
    Real.log |hierGrid m (p, q) - hierGrid m (p, q')| -
      Real.log (hierGrid m (p, q) + hierGrid m (p, q')) =
    Real.log |shapeS m q - shapeS m q'| - Real.log (shapeS m q + shapeS m q') := by
  rw [log_hierGrid_inblock_diff_abs m p hqq', log_hierGrid_inblock_sum]
  ring

/-- The double product `∏_i ∏_j (δ_i + δ_j)` decomposes log-wise into a diagonal
contribution and an offDiag contribution. -/
private lemma log_denom_double_prod {n : ℕ} (δ : Fin n → ℝ)
    (hpos : ∀ i j, 0 < δ i + δ j) :
    Real.log (∏ i : Fin n, ∏ j : Fin n, (δ i + δ j)) =
      (∑ i : Fin n, Real.log (δ i + δ i)) +
      (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, Real.log (δ p.1 + δ p.2)) := by
  -- Step 1: log of double product = sum of sum of logs.
  have hlog_outer : Real.log (∏ i : Fin n, ∏ j : Fin n, (δ i + δ j)) =
      ∑ i : Fin n, ∑ j : Fin n, Real.log (δ i + δ j) := by
    rw [Real.log_prod (fun i _ =>
      Finset.prod_ne_zero_iff.mpr (fun j _ => ne_of_gt (hpos i j)))]
    apply Finset.sum_congr rfl; intros i _
    exact Real.log_prod (fun j _ => ne_of_gt (hpos i j))
  rw [hlog_outer]
  -- Step 2: ∑_i ∑_j = ∑_{(i,j) ∈ univ ×ˢ univ}.
  rw [show ∑ i : Fin n, ∑ j : Fin n, Real.log (δ i + δ j) =
      ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)),
        Real.log (δ p.1 + δ p.2) by
    rw [Finset.sum_product]]
  -- Step 3: split univ ×ˢ univ = diag ∪ offDiag.
  -- diag = {(i,i) | i ∈ univ}; offDiag = {(i,j) | i ≠ j}.
  -- Use Finset.sum_filter_add_sum_filter_not with predicate `p.1 = p.2`.
  rw [← Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)))
      (fun p => p.1 = p.2)]
  congr 1
  · -- Diagonal: filter by p.1 = p.2 gives ∑_i log(δ_i + δ_i).
    -- Bijection: (i, i) ↔ i.
    apply Finset.sum_nbij' (i := fun p => p.1) (j := fun i => (i, i))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hp
      exact Finset.mem_univ _
    · intro i _
      simp [Finset.mem_filter]
    · intro p hp
      have hp' := hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hp'
      show (p.1, p.1) = p
      ext
      · rfl
      · exact congrArg (fun (x : Fin n) => x.val) hp'
    · intro i _; rfl
    · intro p hp
      have hp' := hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hp'
      rw [hp']
  · -- offDiag piece: filter by ¬ (p.1 = p.2).
    apply Finset.sum_nbij' (i := fun p => p) (j := fun p => p)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hp
      simp [Finset.mem_offDiag, hp]
    · intro p hp
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
      simp [Finset.mem_filter, hp]
    · intros _ _; rfl
    · intros _ _; rfl
    · intros _ _; rfl

/-- The hierarchical grid value is a natural number cast to ℝ:
`hierGrid m (p, q) = (4^(p+m) * (m + q + 1) : ℕ)`. -/
private lemma hierGrid_eq_natCast (m : ℕ) (pq : Fin m × Fin m) :
    hierGrid m pq = ((4 ^ (pq.1.val + m) * (m + pq.2.val + 1) : ℕ) : ℝ) := by
  unfold hierGrid
  push_cast
  ring

/-- The hierarchical grid takes positive natural-number values, so distinct
entries differ by at least `1` in absolute value. -/
private lemma hierGrid_diff_abs_ge_one {m : ℕ} (hm : 1 ≤ m) {i j : Fin m × Fin m}
    (hne : i ≠ j) : 1 ≤ |hierGrid m i - hierGrid m j| := by
  set ai : ℕ := 4 ^ (i.1.val + m) * (m + i.2.val + 1) with hai_def
  set aj : ℕ := 4 ^ (j.1.val + m) * (m + j.2.val + 1) with haj_def
  have hi : hierGrid m i = (ai : ℝ) := hierGrid_eq_natCast m i
  have hj : hierGrid m j = (aj : ℝ) := hierGrid_eq_natCast m j
  have hne_real : hierGrid m i ≠ hierGrid m j := hierGrid_inj hm i j hne
  rw [hi, hj] at hne_real ⊢
  have hne_nat : ai ≠ aj := fun h => hne_real (by rw [h])
  rcases lt_or_gt_of_ne hne_nat with h | h
  · have h1 : ai + 1 ≤ aj := h
    have h1r : (1 : ℝ) ≤ (aj : ℝ) - (ai : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at this
      linarith
    have hneg : (ai : ℝ) - (aj : ℝ) < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · have h1 : aj + 1 ≤ ai := h
    have h1r : (1 : ℝ) ≤ (ai : ℝ) - (aj : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at this
      linarith
    have hpos : (0 : ℝ) < (ai : ℝ) - (aj : ℝ) := by linarith
    rw [abs_of_pos hpos]
    linarith

/-- Upper bound on each hierarchical grid entry: `δ(p, q) ≤ 4^(2m) · 2m`. -/
private lemma hierGrid_le_bound {m : ℕ} (hm : 1 ≤ m) (pq : Fin m × Fin m) :
    hierGrid m pq ≤ (4 : ℝ) ^ (2 * m) * (2 * (m : ℝ)) := by
  rw [hierGrid_factor]
  have hp_lt : pq.1.val < m := pq.1.isLt
  have h_aple : scaleA m pq.1 ≤ (4 : ℝ) ^ (2 * m) := by
    unfold scaleA
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
    omega
  have h_sple : shapeS m pq.2 ≤ 2 * (m : ℝ) := shapeS_le_two_mul hm pq.2
  have h_ap_pos : 0 < scaleA m pq.1 := scaleA_pos m pq.1
  have h_pow_pos : (0 : ℝ) < (4 : ℝ) ^ (2 * m) := pow_pos (by norm_num) _
  have h_sp_nn : 0 ≤ shapeS m pq.2 := (shapeS_pos m pq.2).le
  have h_2m_nn : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
  calc scaleA m pq.1 * shapeS m pq.2
      ≤ (4 : ℝ) ^ (2 * m) * shapeS m pq.2 :=
        mul_le_mul_of_nonneg_right h_aple h_sp_nn
    _ ≤ (4 : ℝ) ^ (2 * m) * (2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left h_sple h_pow_pos.le

/-- Upper bound on the log of a pairwise sum on the hierarchical grid. -/
private lemma log_hierGrid_sum_le {m : ℕ} (hm : 1 ≤ m) (i j : Fin m × Fin m) :
    Real.log (hierGrid m i + hierGrid m j) ≤
      2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ)) := by
  have hi := hierGrid_le_bound hm i
  have hj := hierGrid_le_bound hm j
  have hbnd : hierGrid m i + hierGrid m j ≤ 2 * ((4 : ℝ) ^ (2 * m) * (2 * (m : ℝ))) := by
    linarith
  have hsum_pos : 0 < hierGrid m i + hierGrid m j := hierGrid_sum_pos m i j
  have hbnd_pos : (0 : ℝ) < 2 * ((4 : ℝ) ^ (2 * m) * (2 * (m : ℝ))) := by
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hlog_le : Real.log (hierGrid m i + hierGrid m j) ≤
      Real.log (2 * ((4 : ℝ) ^ (2 * m) * (2 * (m : ℝ)))) :=
    Real.log_le_log hsum_pos hbnd
  -- Simplify the RHS log.
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow_pos : (0 : ℝ) < (4 : ℝ) ^ (2 * m) := pow_pos (by norm_num) _
  have h4m_pos : (0 : ℝ) < 4 * (m : ℝ) := by positivity
  have hrearr : (2 : ℝ) * ((4 : ℝ) ^ (2 * m) * (2 * (m : ℝ))) =
      (4 : ℝ) ^ (2 * m) * (4 * (m : ℝ)) := by ring
  rw [hrearr] at hlog_le
  rw [Real.log_mul hpow_pos.ne' h4m_pos.ne', Real.log_pow] at hlog_le
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [h2m] at hlog_le
  linarith

/- ### §5.2 The main assembly -/

/-- Packaged log-form of the lower bound (relaxed to `m⁵`, used as a stepping
stone for the sharper `m³` bound below).
Direct application of `cauchy_det_formula_fin` + naive estimates: the Cauchy
numerator factors `|δⱼ - δᵢ|` are positive integers (so `2 log|N| ≥ 0`), and
each `log(δᵢ + δⱼ) ≤ 2m log 4 + log(4m)`. Summing over `m⁴` denominator pairs
gives `-O(m⁵)`. -/
private theorem hierarchical_log_det_lower_bound_m5 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℕ, 1 ≤ m →
      -(c₀ * (m : ℝ) ^ 5) ≤ Real.log (Matrix.of fun i j : Fin m × Fin m =>
        1 / (hierGrid m i + hierGrid m j)).det := by
  -- Pick c₀ = 5 + log 16 (slack for log m ≤ m).
  refine ⟨5 + Real.log 16, ?_, ?_⟩
  · have hlog16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
    linarith
  intro m hm
  -- Setup: e is the equivalence Fin m × Fin m ≃ Fin (m²).
  set e : Fin m × Fin m ≃ Fin (Fintype.card (Fin m × Fin m)) :=
    Fintype.equivFin (Fin m × Fin m) with he_def
  set N : ℕ := Fintype.card (Fin m × Fin m) with hN_def
  have hN_eq : N = m * m := by
    show Fintype.card (Fin m × Fin m) = m * m
    rw [Fintype.card_prod, Fintype.card_fin]
  set δ : Fin m × Fin m → ℝ := hierGrid m with hδ_def
  set δ' : Fin N → ℝ := δ ∘ e.symm with hδ'_def
  have hpos : ∀ i j : Fin m × Fin m, 0 < δ i + δ j := hierGrid_sum_pos m
  have hdiff : ∀ i j : Fin m × Fin m, i ≠ j → δ i ≠ δ j := hierGrid_inj hm
  have hpos' : ∀ i j : Fin N, 0 < δ' i + δ' j := fun i j => hpos _ _
  have hdiff' : ∀ i j : Fin N, i ≠ j → δ' i ≠ δ' j := by
    intro i j hij heq
    have hsym_eq : e.symm i = e.symm j := by
      by_contra hne
      exact hdiff _ _ hne heq
    exact hij (e.symm.injective hsym_eq)
  have hcauchy_fin := cauchy_det_formula_fin N δ' hpos' hdiff'
  have hmat_eq : (Matrix.of fun i j : Fin m × Fin m => 1 / (δ i + δ j)) =
      (Matrix.of fun i j : Fin N => 1 / (δ' i + δ' j)).submatrix e e := by
    ext i j
    simp [δ', Matrix.submatrix_apply]
  set Num : ℝ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (δ' j - δ' i) with hNum_def
  set Den : ℝ := ∏ i : Fin N, ∏ j : Fin N, (δ' i + δ' j) with hDen_def
  have hdet_eq :
      (Matrix.of fun i j : Fin m × Fin m => 1 / (δ i + δ j)).det = Num ^ 2 / Den := by
    rw [hmat_eq, Matrix.det_submatrix_equiv_self]
    exact hcauchy_fin
  have hDen_pos : 0 < Den := by
    apply Finset.prod_pos; intro i _
    apply Finset.prod_pos; intro j _; exact hpos' i j
  have hNum_ne : Num ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hij_ne : i ≠ j := ne_of_lt hij
    exact sub_ne_zero.mpr (hdiff' j i (Ne.symm hij_ne))
  have hNumSq_pos : 0 < Num ^ 2 := by positivity
  rw [hdet_eq, Real.log_div hNumSq_pos.ne' hDen_pos.ne']
  -- Step 1: log(Num²) ≥ 0 since each |δ' j - δ' i| ≥ 1.
  have hlogNumSq_nn : 0 ≤ Real.log (Num ^ 2) := by
    have hNumSq_eq : Num ^ 2 = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (δ' j - δ' i) ^ 2 := by
      rw [hNum_def]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl; intro i _
      rw [← Finset.prod_pow]
    rw [hNumSq_eq]
    have hfac_ge_one : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, 1 ≤ (δ' j - δ' i) ^ 2 := by
      intro i j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hne : i ≠ j := ne_of_lt hij
      have habs : 1 ≤ |δ' j - δ' i| := by
        show 1 ≤ |hierGrid m (e.symm j) - hierGrid m (e.symm i)|
        have hsym_ne : e.symm j ≠ e.symm i := fun h => hne.symm (e.symm.injective h)
        exact hierGrid_diff_abs_ge_one hm hsym_ne
      have habs_sq : (1 : ℝ) ≤ |δ' j - δ' i| ^ 2 := by
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ |δ' j - δ' i| ^ 2 := by
              apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) habs
      rw [sq_abs] at habs_sq
      exact habs_sq
    have hprod_pos : ∀ i : Fin N,
        0 < ∏ j ∈ Finset.Ioi i, (δ' j - δ' i) ^ 2 := by
      intro i
      apply Finset.prod_pos
      intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hne_ij : i ≠ j := ne_of_lt hij
      have : δ' j - δ' i ≠ 0 := sub_ne_zero.mpr (hdiff' j i (Ne.symm hne_ij))
      positivity
    rw [Real.log_prod (fun i _ => (hprod_pos i).ne')]
    apply Finset.sum_nonneg; intro i _
    rw [Real.log_prod]
    · apply Finset.sum_nonneg; intro j hj
      exact Real.log_nonneg (hfac_ge_one i j hj)
    · intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hne_ij : i ≠ j := ne_of_lt hij
      have : δ' j - δ' i ≠ 0 := sub_ne_zero.mpr (hdiff' j i (Ne.symm hne_ij))
      exact pow_ne_zero _ this
  -- Step 2: log Den ≤ N² · (2m log 4 + log(4m)) where N = m². So m^4 · O(m + log m).
  have hDen_log_le : Real.log Den ≤
      (N : ℝ) * ((N : ℝ) * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ)))) := by
    have hprod_pos_inner : ∀ i : Fin N,
        0 < ∏ j : Fin N, (δ' i + δ' j) := fun i =>
      Finset.prod_pos (fun j _ => hpos' i j)
    rw [hDen_def, Real.log_prod (fun i _ => (hprod_pos_inner i).ne')]
    have hper_i : ∀ i : Fin N,
        Real.log (∏ j : Fin N, (δ' i + δ' j)) ≤
          (N : ℝ) * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ))) := by
      intro i
      rw [Real.log_prod (fun j _ => (hpos' i j).ne')]
      have hper_j : ∀ j : Fin N, Real.log (δ' i + δ' j) ≤
          2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ)) := by
        intro j
        show Real.log (hierGrid m (e.symm i) + hierGrid m (e.symm j)) ≤
          2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ))
        exact log_hierGrid_sum_le hm (e.symm i) (e.symm j)
      have hsum_le : ∑ j : Fin N, Real.log (δ' i + δ' j) ≤
          ∑ _j : Fin N, (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ))) :=
        Finset.sum_le_sum (fun j _ => hper_j j)
      have hconst_eq : ∑ _j : Fin N, ((2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ)))) =
          (N : ℝ) * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      linarith
    have hsum_outer : ∑ i : Fin N, Real.log (∏ j : Fin N, (δ' i + δ' j)) ≤
        ∑ _i : Fin N, ((N : ℝ) * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ)))) :=
      Finset.sum_le_sum (fun i _ => hper_i i)
    have hconst_outer_eq : ∑ _i : Fin N, ((N : ℝ) * (2 * (m : ℝ) * Real.log 4 +
            Real.log (4 * (m : ℝ)))) =
        (N : ℝ) * ((N : ℝ) * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ)))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    linarith
  -- Now: log det = log Num² - log Den ≥ 0 - log Den ≥ -K where K is the bound above.
  -- We need K ≤ (5 + log 16) m⁵.
  -- K = N² · (2m log 4 + log(4m)) where N = m².
  -- (N : ℝ) = m², so N² = m⁴.
  -- K = m⁴ · (2m log 4 + log(4m)) = 2m⁵ log 4 + m⁴ log(4m).
  -- log(4m) = log 4 + log m ≤ log 4 + m, so m⁴ log(4m) ≤ m⁴ log 4 + m⁵.
  -- m⁴ log 4 ≤ m⁵ log 4 since m ≥ 1.
  -- So K ≤ 2 m⁵ log 4 + m⁵ log 4 + m⁵ = 3 m⁵ log 4 + m⁵ = (3 log 4 + 1) m⁵.
  -- And 3 log 4 + 1 ≤ 5 + log 16 = 5 + 2 log 4? Need log 4 ≤ 4. ✓.
  -- (3 log 4 + 1 ≈ 5.16, 5 + 2 log 4 ≈ 7.77. So 5.16 < 7.77. ✓.)
  have hN_real : (N : ℝ) = (m : ℝ) * (m : ℝ) := by
    have : (N : ℕ) = m * m := hN_eq
    exact_mod_cast this
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm_ge_one : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4m_split : Real.log (4 * (m : ℝ)) = Real.log 4 + Real.log m := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hm_pos.ne']
  have hlog_m_le : Real.log m ≤ (m : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hm_pos
    linarith
  have hlog_m_nn : 0 ≤ Real.log m := Real.log_nonneg hm_ge_one
  -- Bound K = (N : ℝ)² · (2m log 4 + log(4m)) = m⁴ · (2m log 4 + log(4m)).
  have hK_eq :
      (N : ℝ) * ((N : ℝ) * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ)))) =
      (m : ℝ)^4 * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ))) := by
    rw [hN_real]; ring
  rw [hK_eq] at hDen_log_le
  -- Bound K ≤ (5 + log 16) m⁵.
  have hm_pow_nn : ∀ k : ℕ, 0 ≤ (m : ℝ)^k := fun k => by positivity
  have hm5_nn : 0 ≤ (m : ℝ)^5 := hm_pow_nn 5
  have hm4_nn : 0 ≤ (m : ℝ)^4 := hm_pow_nn 4
  have hm4_le_m5 : (m : ℝ)^4 ≤ (m : ℝ)^5 := by
    have h : (m : ℝ)^5 = (m : ℝ)^4 * m := by ring
    rw [h]
    nlinarith [hm4_nn, hm_ge_one]
  -- K = m⁴ · (2m log 4 + log 4 + log m).
  have hK_split : (m : ℝ)^4 * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ))) =
      2 * (m : ℝ)^5 * Real.log 4 + (m : ℝ)^4 * Real.log 4 + (m : ℝ)^4 * Real.log m := by
    rw [hlog4m_split]; ring
  -- Bound (m^4 log 4) ≤ m^5 log 4.
  have hbnd1 : (m : ℝ)^4 * Real.log 4 ≤ (m : ℝ)^5 * Real.log 4 := by
    have : (m : ℝ)^4 * Real.log 4 ≤ (m : ℝ)^5 * Real.log 4 :=
      mul_le_mul_of_nonneg_right hm4_le_m5 hlog4_pos.le
    exact this
  -- Bound (m^4 log m) ≤ m^4 · m = m^5.
  have hbnd2 : (m : ℝ)^4 * Real.log m ≤ (m : ℝ)^5 := by
    have : (m : ℝ)^4 * Real.log m ≤ (m : ℝ)^4 * m :=
      mul_le_mul_of_nonneg_left hlog_m_le hm4_nn
    have heq : (m : ℝ)^4 * m = (m : ℝ)^5 := by ring
    linarith
  have hK_bnd : (m : ℝ)^4 * (2 * (m : ℝ) * Real.log 4 + Real.log (4 * (m : ℝ))) ≤
      3 * (m : ℝ)^5 * Real.log 4 + (m : ℝ)^5 := by
    rw [hK_split]
    linarith
  -- And 3 log 4 + 1 ≤ 5 + log 16. Need log 16 = 2 log 4.
  have hlog16_eq : Real.log 16 = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = 4 * 4 by norm_num,
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  have hlog4_le : Real.log 4 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  -- log Den ≤ K ≤ 3 m⁵ log 4 + m⁵ ≤ (5 + log 16) m⁵.
  -- We need 3 log 4 + 1 ≤ 5 + log 16 = 5 + 2 log 4, i.e., log 4 ≤ 4. ✓.
  have hfinal_bnd :
      3 * (m : ℝ)^5 * Real.log 4 + (m : ℝ)^5 ≤ (5 + Real.log 16) * (m : ℝ)^5 := by
    rw [hlog16_eq]
    have hineq : 3 * Real.log 4 + 1 ≤ 5 + 2 * Real.log 4 := by linarith
    nlinarith [hineq, hm5_nn]
  -- Combine.
  linarith

/- ### §5.3 The sharper m³ bound via the algebraic identity -/

/-- For a Cauchy matrix on `Fin n` with pairwise distinct positive-sum entries,
`2 log Num = ∑_{(i,j) ∈ offDiag} log|δ_j - δ_i|`. The factor of 2 absorbs the
fact that each unordered pair appears once in the product over `i < j` but
twice in the sum over `i ≠ j`. -/
private lemma cauchy_log_num_sq_eq_offDiag {n : ℕ} (δ : Fin n → ℝ)
    (hdiff : ∀ i j : Fin n, i ≠ j → δ i ≠ δ j) :
    Real.log ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j - δ i)) ^ 2) =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, Real.log |δ p.1 - δ p.2| := by
  -- Step 1: log(Num²) = ∑_{i, j ∈ Ioi i} 2 log|δ j - δ i|.
  set Num : ℝ := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j - δ i) with hNum_def
  have hNum_ne : Num ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hij_ne : i ≠ j := ne_of_lt hij
    exact sub_ne_zero.mpr (hdiff j i hij_ne.symm)
  -- Num² = ∏_i ∏_{j ∈ Ioi i} (δ_j - δ_i)² = ∏_i ∏_{j ∈ Ioi i} |δ_j - δ_i|²
  have hNumSq_eq : Num ^ 2 =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j - δ i) ^ 2 := by
    rw [hNum_def, ← Finset.prod_pow]
    apply Finset.prod_congr rfl; intro i _
    rw [← Finset.prod_pow]
  rw [hNumSq_eq]
  -- log of nested product = nested sum of logs.
  have hpos_inner : ∀ i : Fin n, 0 < ∏ j ∈ Finset.Ioi i, (δ j - δ i) ^ 2 := by
    intro i
    apply Finset.prod_pos; intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have : δ j - δ i ≠ 0 := sub_ne_zero.mpr (hdiff j i (ne_of_lt hij).symm)
    positivity
  rw [Real.log_prod (fun i _ => (hpos_inner i).ne')]
  have hreindex : ∀ i : Fin n,
      Real.log (∏ j ∈ Finset.Ioi i, (δ j - δ i) ^ 2) =
        ∑ j ∈ Finset.Ioi i, 2 * Real.log |δ j - δ i| := by
    intro i
    have hne : ∀ j ∈ Finset.Ioi i, (δ j - δ i) ^ 2 ≠ 0 := by
      intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have : δ j - δ i ≠ 0 := sub_ne_zero.mpr (hdiff j i (ne_of_lt hij).symm)
      positivity
    rw [Real.log_prod (fun j hj => hne j hj)]
    apply Finset.sum_congr rfl; intro j _
    rw [show ((δ j - δ i) ^ 2 : ℝ) = |δ j - δ i| ^ 2 by rw [sq_abs],
        Real.log_pow]
    push_cast; ring
  simp_rw [hreindex]
  -- Now: ∑_i ∑_{j ∈ Ioi i} 2 log|δ j - δ i| = ∑_{(i,j) ∈ offDiag} log|δ p.1 - δ p.2|
  -- using the bijection between {(i,j) : j > i} ⊔ {(i,j) : j > i, swap} and offDiag.
  -- Step: ∑_i ∑_{j ∈ Ioi i} 2 X = ∑_{i, j ∈ Ioi i} (X + X) = ∑_{(i,j) ∈ Ioi pair} (X + X_swap)
  -- where X_swap = log|δ i - δ j| = log|δ j - δ i|. Each contributes once for each ordering.
  -- Easiest: rewrite 2 log|·| = log|·| + log|·|, then split into i<j part and i>j part.
  have h2split : ∀ (i : Fin n) (j : Fin n),
      2 * Real.log |δ j - δ i| = Real.log |δ j - δ i| + Real.log |δ i - δ j| := by
    intro i j
    rw [abs_sub_comm]
    ring
  -- Rewrite using h2split.
  have hexpand : (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, 2 * Real.log |δ j - δ i|) =
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log |δ j - δ i|) +
      (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log |δ i - δ j|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    exact h2split i j
  rw [hexpand]
  -- Now goal: (sum over i<j) + (sum over i<j with swapped form)
  -- = ∑_{(i,j) ∈ offDiag} log|δ p.1 - δ p.2|
  -- Strategy: split offDiag into {(i,j) : i < j} and {(i,j) : j < i}.
  rw [show ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, Real.log |δ p.1 - δ p.2| =
      (∑ p ∈ ((Finset.univ : Finset (Fin n)).offDiag).filter (fun p => p.1 < p.2),
          Real.log |δ p.1 - δ p.2|) +
      (∑ p ∈ ((Finset.univ : Finset (Fin n)).offDiag).filter (fun p => ¬ p.1 < p.2),
          Real.log |δ p.1 - δ p.2|) by
    rw [Finset.sum_filter_add_sum_filter_not]]
  congr 1
  · -- First piece: ∑_i ∑_{j ∈ Ioi i} log|δ i - δ j| equals
    --             ∑_{(p,q), p < q} log|δ p - δ q|.
    -- Bijection: (i, j) with j > i ↔ (i, j) ∈ offDiag with i < j.
    rw [show (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log |δ j - δ i|) =
        ∑ ij ∈ (Finset.univ : Finset (Fin n)).sigma
          (fun i : Fin n => Finset.Ioi i), Real.log |δ ij.2 - δ ij.1| by
      rw [Finset.sum_sigma]]
    refine Finset.sum_nbij'
      (i := fun (ij : Σ _ : Fin n, Fin n) => (ij.1, ij.2))
      (j := fun (p : Fin n × Fin n) => ⟨p.1, p.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro ij hij
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hij
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
      refine ⟨ne_of_lt hij, hij⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and]
      exact hp.2
    · intro ij _; rfl
    · intro p _; rfl
    · intro ij hij
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hij
      rw [abs_sub_comm]
  · -- Second piece: ∑_i ∑_{j ∈ Ioi i} log|δ i - δ j| equals
    --             ∑_{(p,q), p > q} log|δ p - δ q|.
    -- Bijection: (i, j) with j > i ↔ (j, i) ∈ offDiag with j > i (i.e., not p.1 < p.2).
    rw [show (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log |δ i - δ j|) =
        ∑ ij ∈ (Finset.univ : Finset (Fin n)).sigma
          (fun i : Fin n => Finset.Ioi i), Real.log |δ ij.1 - δ ij.2| by
      rw [Finset.sum_sigma]]
    refine Finset.sum_nbij'
      (i := fun (ij : Σ _ : Fin n, Fin n) => (ij.2, ij.1))
      (j := fun (p : Fin n × Fin n) => ⟨p.2, p.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro ij hij
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hij
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        not_lt]
      refine ⟨(ne_of_lt hij).symm, hij.le⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        not_lt] at hp
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and]
      have hne : p.1 ≠ p.2 := hp.1
      have hle : p.2 ≤ p.1 := hp.2
      exact lt_of_le_of_ne hle hne.symm
    · intro ij _; rfl
    · intro p _; rfl
    · intro ij _
      show Real.log |δ ij.1 - δ ij.2| = Real.log |δ ij.2 - δ ij.1|
      rw [abs_sub_comm]

/-- **Cauchy log-det offDiag form.** For pairwise distinct `δ : Fin n → ℝ`
with positive sums, the log of the Cauchy determinant decomposes as:
```
log det = ∑_{(i,j) ∈ offDiag} log|δ_i - δ_j| - ∑_i log(δ_i + δ_i)
        - ∑_{(i,j) ∈ offDiag} log(δ_i + δ_j)
```
This is the logged form of Cauchy's identity, with the denominator split
into diagonal and off-diagonal pieces. -/
private lemma cauchy_log_det_offDiag_form {n : ℕ} (δ : Fin n → ℝ)
    (hpos : ∀ i j, 0 < δ i + δ j) (hdiff : ∀ i j : Fin n, i ≠ j → δ i ≠ δ j) :
    Real.log (Matrix.of fun i j : Fin n => 1 / (δ i + δ j)).det =
      (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
          Real.log |δ p.1 - δ p.2|) -
      (∑ i : Fin n, Real.log (δ i + δ i)) -
      (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
          Real.log (δ p.1 + δ p.2)) := by
  have hcauchy := cauchy_det_formula_fin n δ hpos hdiff
  set Num : ℝ := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (δ j - δ i) with hNum_def
  set Den : ℝ := ∏ i : Fin n, ∏ j : Fin n, (δ i + δ j) with hDen_def
  have hDen_pos : 0 < Den := by
    apply Finset.prod_pos; intro i _
    apply Finset.prod_pos; intro j _; exact hpos i j
  have hNum_ne : Num ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    exact sub_ne_zero.mpr (hdiff j i (ne_of_lt hij).symm)
  have hNumSq_pos : 0 < Num ^ 2 := by positivity
  have hdet_eq : (Matrix.of fun i j : Fin n => 1 / (δ i + δ j)).det = Num ^ 2 / Den := hcauchy
  rw [hdet_eq, Real.log_div hNumSq_pos.ne' hDen_pos.ne']
  -- log(Num²) = ∑_{(i,j) ∈ offDiag} log|δ_i - δ_j|.
  have hlogNumSq := cauchy_log_num_sq_eq_offDiag δ hdiff
  rw [hlogNumSq]
  -- log Den = (diagonal) + (offDiag).
  have hlogDen := log_denom_double_prod δ hpos
  rw [hlogDen]
  ring

/-- The hierGrid Cauchy log-det in the form needed for the m³ bound:
```
log det Σ = ∑_{(i,j) ∈ offDiag(Fin m × Fin m)} log|δ_i - δ_j|
          - ∑_i log(δ_i + δ_i)
          - ∑_{(i,j) ∈ offDiag} log(δ_i + δ_j)
```
This is `cauchy_log_det_offDiag_form` transferred via the `Fin m × Fin m ≃ Fin (m²)` equivalence. -/
private lemma hierCauchy_log_det_offDiag {m : ℕ} (hm : 1 ≤ m) :
    Real.log (Matrix.of fun i j : Fin m × Fin m => 1 / (hierGrid m i + hierGrid m j)).det =
      (∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).offDiag,
          Real.log |hierGrid m p.1 - hierGrid m p.2|) -
      (∑ i : Fin m × Fin m, Real.log (hierGrid m i + hierGrid m i)) -
      (∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).offDiag,
          Real.log (hierGrid m p.1 + hierGrid m p.2)) := by
  -- Reindex via Fin m × Fin m ≃ Fin (m²).
  set e : Fin m × Fin m ≃ Fin (Fintype.card (Fin m × Fin m)) :=
    Fintype.equivFin (Fin m × Fin m) with he_def
  set N : ℕ := Fintype.card (Fin m × Fin m) with hN_def
  set δ : Fin m × Fin m → ℝ := hierGrid m with hδ_def
  set δ' : Fin N → ℝ := δ ∘ e.symm with hδ'_def
  have hpos : ∀ i j : Fin m × Fin m, 0 < δ i + δ j := hierGrid_sum_pos m
  have hdiff : ∀ i j : Fin m × Fin m, i ≠ j → δ i ≠ δ j := hierGrid_inj hm
  have hpos' : ∀ i j : Fin N, 0 < δ' i + δ' j := fun i j => hpos _ _
  have hdiff' : ∀ i j : Fin N, i ≠ j → δ' i ≠ δ' j := by
    intro i j hij heq
    have hsym_eq : e.symm i = e.symm j := by
      by_contra hne
      exact hdiff _ _ hne heq
    exact hij (e.symm.injective hsym_eq)
  have hmat_eq : (Matrix.of fun i j : Fin m × Fin m => 1 / (δ i + δ j)) =
      (Matrix.of fun i j : Fin N => 1 / (δ' i + δ' j)).submatrix e e := by
    ext i j; simp [δ', Matrix.submatrix_apply]
  have hdet_eq : (Matrix.of fun i j : Fin m × Fin m => 1 / (δ i + δ j)).det =
      (Matrix.of fun i j : Fin N => 1 / (δ' i + δ' j)).det := by
    rw [hmat_eq, Matrix.det_submatrix_equiv_self]
  -- Apply the Fin N version.
  have hfinN := cauchy_log_det_offDiag_form δ' hpos' hdiff'
  rw [hdet_eq, hfinN]
  -- Transfer the three sums on the RHS via e.
  -- 1) Off-diagonal numerator.
  have h1 : ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        Real.log |δ' p.1 - δ' p.2| =
      ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).offDiag,
        Real.log |δ p.1 - δ p.2| := by
    -- Use the product equivalence (e × e) restricted to offDiag.
    refine Finset.sum_nbij'
      (i := fun (p : Fin N × Fin N) => (e.symm p.1, e.symm p.2))
      (j := fun (q : (Fin m × Fin m) × (Fin m × Fin m)) => (e q.1, e q.2))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      intro h
      apply hp
      apply e.symm.injective
      exact h
    · intro q hq
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hq
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      intro h
      apply hq
      apply e.injective
      exact h
    · intro p _; ext <;> simp
    · intro q _; ext <;> simp
    · intro p _
      show Real.log |δ' p.1 - δ' p.2| =
        Real.log |δ (e.symm p.1) - δ (e.symm p.2)|
      simp [δ']
  -- 2) Diagonal denominator.
  have h2 : ∑ i : Fin N, Real.log (δ' i + δ' i) =
      ∑ i : Fin m × Fin m, Real.log (δ i + δ i) := by
    rw [← Equiv.sum_comp e (fun i => Real.log (δ' i + δ' i))]
    apply Finset.sum_congr rfl; intro i _
    simp [δ']
  -- 3) Off-diagonal denominator.
  have h3 : ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,
        Real.log (δ' p.1 + δ' p.2) =
      ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).offDiag,
        Real.log (δ p.1 + δ p.2) := by
    refine Finset.sum_nbij'
      (i := fun (p : Fin N × Fin N) => (e.symm p.1, e.symm p.2))
      (j := fun (q : (Fin m × Fin m) × (Fin m × Fin m)) => (e q.1, e q.2))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      intro h
      apply hp
      apply e.symm.injective
      exact h
    · intro q hq
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hq
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      intro h
      apply hq
      apply e.injective
      exact h
    · intro p _; ext <;> simp
    · intro q _; ext <;> simp
    · intro p _
      show Real.log (δ' p.1 + δ' p.2) =
        Real.log (δ (e.symm p.1) + δ (e.symm p.2))
      simp [δ']
  rw [h1, h2, h3]

/-- Form of `log det shapeM` matching the offDiag Cauchy decomposition.
This is `cauchy_log_det_offDiag_form` specialised to `shapeS`. -/
private lemma shapeM_log_det_offDiag {m : ℕ} :
    Real.log (shapeM m).det =
      (∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag,
          Real.log |shapeS m p.1 - shapeS m p.2|) -
      (∑ q : Fin m, Real.log (shapeS m q + shapeS m q)) -
      (∑ p ∈ (Finset.univ : Finset (Fin m)).offDiag,
          Real.log (shapeS m p.1 + shapeS m p.2)) := by
  unfold shapeM
  exact cauchy_log_det_offDiag_form (shapeS m) (shapeM_sum_pos m)
    (fun i j hij => shapeS_inj hij)

/-- The in-block contribution simplifies via `inblock_log_pair_diff`. -/
private lemma hierCauchy_inblock_offDiag_eq {m : ℕ} :
    (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
        (Real.log |hierGrid m (p, qq'.1) - hierGrid m (p, qq'.2)| -
          Real.log (hierGrid m (p, qq'.1) + hierGrid m (p, qq'.2)))) =
      (m : ℝ) * (∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
        (Real.log |shapeS m qq'.1 - shapeS m qq'.2| -
          Real.log (shapeS m qq'.1 + shapeS m qq'.2))) := by
  have hkey : ∀ (p : Fin m) (qq' : Fin m × Fin m),
      qq' ∈ (Finset.univ : Finset (Fin m)).offDiag →
      Real.log |hierGrid m (p, qq'.1) - hierGrid m (p, qq'.2)| -
        Real.log (hierGrid m (p, qq'.1) + hierGrid m (p, qq'.2)) =
      Real.log |shapeS m qq'.1 - shapeS m qq'.2| -
        Real.log (shapeS m qq'.1 + shapeS m qq'.2) := by
    intro p qq' hqq'
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hqq'
    exact inblock_log_pair_diff m p hqq'
  -- Each inner sum is the same.
  have hsum_eq : ∀ p : Fin m,
      (∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
        (Real.log |hierGrid m (p, qq'.1) - hierGrid m (p, qq'.2)| -
          Real.log (hierGrid m (p, qq'.1) + hierGrid m (p, qq'.2)))) =
      (∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
        (Real.log |shapeS m qq'.1 - shapeS m qq'.2| -
          Real.log (shapeS m qq'.1 + shapeS m qq'.2))) := by
    intro p
    apply Finset.sum_congr rfl
    intro qq' hqq'
    exact hkey p qq' hqq'
  rw [Finset.sum_congr rfl (fun p _ => hsum_eq p)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- For p ≠ r, the cross-block log pair satisfies a lower bound via the
artanh inequality. The bound is `≥ -3 · ηswap` where `ηswap` is `(min/max)·(s ratio)`. -/
private lemma cross_log_pair_lb {m : ℕ} (hm : 1 ≤ m) {p r : Fin m} (hpr : p ≠ r)
    (q s : Fin m) :
    Real.log |hierGrid m (p, q) - hierGrid m (r, s)| -
      Real.log (hierGrid m (p, q) + hierGrid m (r, s)) ≥
    -(3 * (if p.val < r.val then crossEta m p r q s else crossEta m r p s q)) := by
  -- Case split p.val < r.val vs p.val > r.val.
  rcases lt_or_gt_of_ne (fun h : p.val = r.val => hpr (Fin.ext h)) with hpr_lt | hpr_gt
  · -- p.val < r.val. Use η = (a_p/a_r)(s_q/s_s).
    simp only [hpr_lt, if_true]
    -- |δ(p,q) - δ(r,s)| = δ(r,s) - δ(p,q) since η < 1.
    have hdiff_pos : 0 < hierGrid m (r, s) - hierGrid m (p, q) :=
      hierGrid_cross_diff_pos hm hpr_lt q s
    have habs : |hierGrid m (p, q) - hierGrid m (r, s)| =
        hierGrid m (r, s) - hierGrid m (p, q) := by
      rw [abs_sub_comm]; exact abs_of_pos hdiff_pos
    rw [habs]
    -- δ(r,s) - δ(p,q) = a_r s_s (1 - η).
    have hdiff_factor : hierGrid m (r, s) - hierGrid m (p, q) =
        scaleA m r * shapeS m s * (1 - crossEta m p r q s) := by
      have hd := hierGrid_crossblock_diff_factor m p r q s
      unfold crossEta
      have heq : hierGrid m (p, q) - hierGrid m (r, s) =
          scaleA m r * shapeS m s *
            ((scaleA m p / scaleA m r) * (shapeS m q / shapeS m s) - 1) := hd
      have : hierGrid m (r, s) - hierGrid m (p, q) =
          -(hierGrid m (p, q) - hierGrid m (r, s)) := by ring
      rw [this, heq]
      ring
    -- δ(p,q) + δ(r,s) = a_r s_s (1 + η).
    have hsum_factor : hierGrid m (p, q) + hierGrid m (r, s) =
        scaleA m r * shapeS m s * (1 + crossEta m p r q s) := by
      have hs := hierGrid_crossblock_sum_factor m p r q s
      unfold crossEta
      exact hs
    rw [hdiff_factor, hsum_factor]
    have h_ar_pos : 0 < scaleA m r := scaleA_pos m r
    have h_ss_pos : 0 < shapeS m s := shapeS_pos m s
    have h_ars_pos : 0 < scaleA m r * shapeS m s := mul_pos h_ar_pos h_ss_pos
    have h_eta_pos : 0 < crossEta m p r q s := crossEta_pos m p r q s
    have h_eta_le : crossEta m p r q s ≤ 1/2 := crossEta_le_half hm hpr_lt q s
    have h_one_sub_pos : 0 < 1 - crossEta m p r q s := by linarith
    have h_one_add_pos : 0 < 1 + crossEta m p r q s := by linarith
    rw [Real.log_mul h_ars_pos.ne' h_one_sub_pos.ne']
    rw [Real.log_mul h_ars_pos.ne' h_one_add_pos.ne']
    -- The (a_r s_s) terms cancel.
    have hgoal_eq :
        Real.log (scaleA m r * shapeS m s) + Real.log (1 - crossEta m p r q s) -
          (Real.log (scaleA m r * shapeS m s) + Real.log (1 + crossEta m p r q s)) =
        Real.log ((1 - crossEta m p r q s) / (1 + crossEta m p r q s)) := by
      rw [Real.log_div h_one_sub_pos.ne' h_one_add_pos.ne']
      ring
    rw [hgoal_eq]
    exact log_crossEta_artanh hm hpr_lt q s
  · -- p.val > r.val: symmetric. Swap roles.
    simp only [show ¬ p.val < r.val from not_lt.mpr (le_of_lt hpr_gt), if_false]
    -- |δ(p,q) - δ(r,s)| = δ(p,q) - δ(r,s) since now p > r (so a_p s_q > a_r s_s).
    have hdiff_pos : 0 < hierGrid m (p, q) - hierGrid m (r, s) :=
      hierGrid_cross_diff_pos hm hpr_gt s q
    have habs : |hierGrid m (p, q) - hierGrid m (r, s)| =
        hierGrid m (p, q) - hierGrid m (r, s) := abs_of_pos hdiff_pos
    rw [habs]
    -- δ(p,q) - δ(r,s) = a_p s_q (1 - η_swap) where η_swap = (a_r/a_p)(s_s/s_q).
    have hdiff_factor : hierGrid m (p, q) - hierGrid m (r, s) =
        scaleA m p * shapeS m q * (1 - crossEta m r p s q) := by
      have hd := hierGrid_crossblock_diff_factor m r p s q
      unfold crossEta
      -- hd: δ(r,s) - δ(p,q) = a_p s_q ((a_r/a_p)(s_s/s_q) - 1)
      have heq : hierGrid m (r, s) - hierGrid m (p, q) =
          scaleA m p * shapeS m q *
            ((scaleA m r / scaleA m p) * (shapeS m s / shapeS m q) - 1) := hd
      have : hierGrid m (p, q) - hierGrid m (r, s) =
          -(hierGrid m (r, s) - hierGrid m (p, q)) := by ring
      rw [this, heq]
      ring
    have hsum_factor : hierGrid m (p, q) + hierGrid m (r, s) =
        scaleA m p * shapeS m q * (1 + crossEta m r p s q) := by
      have hs := hierGrid_crossblock_sum_factor m r p s q
      unfold crossEta
      -- hs: δ(r,s) + δ(p,q) = a_p s_q (1 + (a_r/a_p)(s_s/s_q))
      have heq : hierGrid m (r, s) + hierGrid m (p, q) =
          scaleA m p * shapeS m q *
            (1 + (scaleA m r / scaleA m p) * (shapeS m s / shapeS m q)) := hs
      have hcomm : hierGrid m (p, q) + hierGrid m (r, s) =
          hierGrid m (r, s) + hierGrid m (p, q) := by ring
      rw [hcomm, heq]
    rw [hdiff_factor, hsum_factor]
    have h_ap_pos : 0 < scaleA m p := scaleA_pos m p
    have h_sq_pos : 0 < shapeS m q := shapeS_pos m q
    have h_apq_pos : 0 < scaleA m p * shapeS m q := mul_pos h_ap_pos h_sq_pos
    have h_eta_pos : 0 < crossEta m r p s q := crossEta_pos m r p s q
    have h_eta_le : crossEta m r p s q ≤ 1/2 := crossEta_le_half hm hpr_gt s q
    have h_one_sub_pos : 0 < 1 - crossEta m r p s q := by linarith
    have h_one_add_pos : 0 < 1 + crossEta m r p s q := by linarith
    rw [Real.log_mul h_apq_pos.ne' h_one_sub_pos.ne']
    rw [Real.log_mul h_apq_pos.ne' h_one_add_pos.ne']
    have hgoal_eq :
        Real.log (scaleA m p * shapeS m q) + Real.log (1 - crossEta m r p s q) -
          (Real.log (scaleA m p * shapeS m q) + Real.log (1 + crossEta m r p s q)) =
        Real.log ((1 - crossEta m r p s q) / (1 + crossEta m r p s q)) := by
      rw [Real.log_div h_one_sub_pos.ne' h_one_add_pos.ne']
      ring
    rw [hgoal_eq]
    exact log_crossEta_artanh hm hpr_gt s q

/-- Lower bound on the total cross-block log contribution. -/
private lemma crossblock_log_lb {m : ℕ} (hm : 1 ≤ m) :
    (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
        (Real.log |hierGrid m (pr.1, q) - hierGrid m (pr.2, s)| -
          Real.log (hierGrid m (pr.1, q) + hierGrid m (pr.2, s)))) ≥
    -(16 : ℝ) * (m : ℝ)^3 := by
  -- For each (p, r) ∈ offDiag, q, s: lower bound by -3 · η_relevant.
  -- Sum over offDiag × q × s = sum over (p<r, q, s) doubled (by symmetry).
  -- Bound by `cross_block_eta_sum_bound_real` (≤ (8/3) m³).
  -- Total: -3 · 2 · (8/3) m³ = -16 m³.
  -- Step 1: Per-term lower bound.
  have hterm : ∀ (pr : Fin m × Fin m) (q s : Fin m),
      pr ∈ (Finset.univ : Finset (Fin m)).offDiag →
      Real.log |hierGrid m (pr.1, q) - hierGrid m (pr.2, s)| -
        Real.log (hierGrid m (pr.1, q) + hierGrid m (pr.2, s)) ≥
      -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
              else crossEta m pr.2 pr.1 s q)) := by
    intro pr q s hpr
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hpr
    exact cross_log_pair_lb hm hpr q s
  -- Step 2: Sum the lower bound.
  have hsum_lb : (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag,
                  ∑ q : Fin m, ∑ s : Fin m,
                    (Real.log |hierGrid m (pr.1, q) - hierGrid m (pr.2, s)| -
                      Real.log (hierGrid m (pr.1, q) + hierGrid m (pr.2, s)))) ≥
      ∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag,
        ∑ q : Fin m, ∑ s : Fin m,
          -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                  else crossEta m pr.2 pr.1 s q)) := by
    apply Finset.sum_le_sum; intro pr hpr
    apply Finset.sum_le_sum; intro q _
    apply Finset.sum_le_sum; intro s _
    exact hterm pr q s hpr
  -- Step 3: rewrite the bound as -3 · (sum of η over ordered pairs and swapped pairs).
  -- Specifically: ∑_{pr ∈ offDiag} ∑_{q,s} η_{relevant} = 2 · ∑_{p<r, q, s} η_{p,r,q,s}.
  have hsum_eq : ∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag,
      ∑ q : Fin m, ∑ s : Fin m,
        -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                else crossEta m pr.2 pr.1 s q)) =
      -(3 * (2 * ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
        (if p.val < r.val then crossEta m p r q s else 0))) := by
    -- Split offDiag by p<r vs r<p.
    rw [show ∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag,
            ∑ q : Fin m, ∑ s : Fin m,
              -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                      else crossEta m pr.2 pr.1 s q)) =
        ∑ pr ∈ ((Finset.univ : Finset (Fin m)).offDiag).filter (fun pr => pr.1.val < pr.2.val),
            ∑ q : Fin m, ∑ s : Fin m,
              -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                      else crossEta m pr.2 pr.1 s q)) +
        ∑ pr ∈ ((Finset.univ : Finset (Fin m)).offDiag).filter (fun pr => ¬ pr.1.val < pr.2.val),
            ∑ q : Fin m, ∑ s : Fin m,
              -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                      else crossEta m pr.2 pr.1 s q)) by
      rw [Finset.sum_filter_add_sum_filter_not]]
    -- The two pieces equal each other (after reindexing in the second).
    -- Piece 1 (p<r): ∑_{p<r, q, s} -(3 · crossEta m p r q s).
    -- Piece 2 (p>r, swap to p<r form via (p,r,q,s) ↔ (r,p,s,q)).
    have hpiece1 :
        ∑ pr ∈ ((Finset.univ : Finset (Fin m)).offDiag).filter (fun pr => pr.1.val < pr.2.val),
            ∑ q : Fin m, ∑ s : Fin m,
              -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                      else crossEta m pr.2 pr.1 s q)) =
        ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
          (if p.val < r.val then -(3 * crossEta m p r q s) else 0) := by
      rw [show ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
              (if p.val < r.val then -(3 * crossEta m p r q s) else 0) =
            ∑ p : Fin m, ∑ r : Fin m,
              (if p.val < r.val then ∑ q : Fin m, ∑ s : Fin m, -(3 * crossEta m p r q s) else 0)
            by
        apply Finset.sum_congr rfl; intro p _
        apply Finset.sum_congr rfl; intro r _
        by_cases hpr : p.val < r.val
        · simp only [hpr, if_true]
        · simp only [hpr, if_false]
          rw [Finset.sum_eq_zero]; intro q _
          rw [Finset.sum_eq_zero]; intro s _
          rfl]
      rw [show ∑ p : Fin m, ∑ r : Fin m,
              (if p.val < r.val then ∑ q : Fin m, ∑ s : Fin m, -(3 * crossEta m p r q s) else 0) =
          ∑ pr ∈ ((Finset.univ : Finset (Fin m × Fin m))).filter (fun pr => pr.1.val < pr.2.val),
            ∑ q : Fin m, ∑ s : Fin m, -(3 * crossEta m pr.1 pr.2 q s) by
        rw [Finset.sum_filter]
        rw [show (Finset.univ : Finset (Fin m × Fin m)) = Finset.univ ×ˢ Finset.univ from rfl,
            Finset.sum_product]]
      -- Match the filter sets.
      apply Finset.sum_nbij' (i := fun (pr : Fin m × Fin m) => pr) (j := fun (pr : Fin m × Fin m) => pr)
      · intro pr hpr
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hpr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hpr.2
      · intro pr hpr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpr
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
        refine ⟨?_, hpr⟩
        intro h
        exact (lt_irrefl _ (h ▸ hpr))
      · intros _ _; rfl
      · intros _ _; rfl
      · intro pr hpr
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at hpr
        simp only [hpr.2, if_true]
    have hpiece2 :
        ∑ pr ∈ ((Finset.univ : Finset (Fin m)).offDiag).filter (fun pr => ¬ pr.1.val < pr.2.val),
            ∑ q : Fin m, ∑ s : Fin m,
              -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                      else crossEta m pr.2 pr.1 s q)) =
        ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
          (if p.val < r.val then -(3 * crossEta m p r q s) else 0) := by
      -- Reindex: in the filter (p>r), use (r,p,s,q) instead of (p,r,q,s).
      -- The sum becomes ∑_{r<p, q, s} -3 · crossEta m r p s q (since for p>r, the "if" picks else branch with crossEta m pr.2 pr.1 s q = crossEta m r p s q).
      -- After renaming p↔r and q↔s, this is ∑_{p<r, q, s} -3 · crossEta m p r q s.
      have h_rewrite : ∀ pr ∈ ((Finset.univ : Finset (Fin m)).offDiag).filter (fun pr => ¬ pr.1.val < pr.2.val),
          ∑ q : Fin m, ∑ s : Fin m,
            -(3 * (if pr.1.val < pr.2.val then crossEta m pr.1 pr.2 q s
                    else crossEta m pr.2 pr.1 s q)) =
          ∑ q : Fin m, ∑ s : Fin m, -(3 * crossEta m pr.2 pr.1 s q) := by
        intro pr hpr
        simp only [Finset.mem_filter] at hpr
        apply Finset.sum_congr rfl; intro q _
        apply Finset.sum_congr rfl; intro s _
        simp [hpr.2]
      rw [Finset.sum_congr rfl h_rewrite]
      -- Now: ∑_{(p,r) : p>r} ∑_{q,s} -3 crossEta m r p s q
      -- = ∑_{(p',r') : r'<p'} ∑_{q,s} -3 crossEta m p' r' s q     [rename (p,r)↔(r',p')]
      -- = ∑_{p<r} ∑_{q,s} -3 crossEta m p r s q
      -- = ∑_{p<r} ∑_{s,q} -3 crossEta m p r s q   [swap inner sums]
      -- After q↔s relabel: = ∑_{p<r, q, s} -3 crossEta m p r q s.
      -- Bijection: (pr, q, s) ↔ ((pr.2, pr.1), s, q). Change set.
      rw [show ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
              (if p.val < r.val then -(3 * crossEta m p r q s) else 0) =
            ∑ p : Fin m, ∑ r : Fin m,
              (if p.val < r.val then ∑ q : Fin m, ∑ s : Fin m, -(3 * crossEta m p r q s) else 0)
            by
        apply Finset.sum_congr rfl; intro p _
        apply Finset.sum_congr rfl; intro r _
        by_cases hpr : p.val < r.val
        · simp only [hpr, if_true]
        · simp only [hpr, if_false]
          rw [Finset.sum_eq_zero]; intro q _
          rw [Finset.sum_eq_zero]; intro s _
          rfl]
      rw [show ∑ p : Fin m, ∑ r : Fin m,
              (if p.val < r.val then ∑ q : Fin m, ∑ s : Fin m, -(3 * crossEta m p r q s) else 0) =
          ∑ pr ∈ ((Finset.univ : Finset (Fin m × Fin m))).filter (fun pr => pr.1.val < pr.2.val),
            ∑ q : Fin m, ∑ s : Fin m, -(3 * crossEta m pr.1 pr.2 q s) by
        rw [Finset.sum_filter]
        rw [show (Finset.univ : Finset (Fin m × Fin m)) = Finset.univ ×ˢ Finset.univ from rfl,
            Finset.sum_product]]
      -- Bijection: pr ↦ (pr.2, pr.1), then swap inner q ↔ s.
      refine Finset.sum_nbij'
        (i := fun (pr : Fin m × Fin m) => (pr.2, pr.1))
        (j := fun (pr : Fin m × Fin m) => (pr.2, pr.1))
        ?_ ?_ ?_ ?_ ?_
      · intro pr hpr
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, not_lt] at hpr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hne : pr.1 ≠ pr.2 := hpr.1
        have hne_val : pr.2.val ≠ pr.1.val := fun h => hne (Fin.ext h.symm)
        have hle : pr.2.val ≤ pr.1.val := hpr.2
        exact lt_of_le_of_ne hle hne_val
      · intro pr hpr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpr
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, not_lt]
        have hne : pr.2 ≠ pr.1 := fun h => (lt_irrefl _ (h ▸ hpr))
        refine ⟨hne, ?_⟩
        exact le_of_lt hpr
      · intros pr _; ext <;> rfl
      · intros pr _; ext <;> rfl
      · intro pr hpr
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and, not_lt] at hpr
        -- Need: ∑_{q,s} -3 · crossEta m pr.2 pr.1 s q = ∑_{q,s} -3 · crossEta m (pr.2, pr.1).1 (pr.2, pr.1).2 q s
        -- Wait the j-inner sum is over (q, s); the swap is built-in.
        -- After (pr ↦ (pr.2, pr.1)), the new pr' has pr'.1 = old pr.2, pr'.2 = old pr.1.
        -- So we need: ∑_q ∑_s -3 crossEta m pr.2 pr.1 s q = ∑_q ∑_s -3 crossEta m pr'.1 pr'.2 q s
        -- i.e., ∑_q ∑_s crossEta m pr.2 pr.1 s q = ∑_q ∑_s crossEta m pr.2 pr.1 q s.
        -- This is just swapping q ↔ s in the inner double sum.
        rw [Finset.sum_comm]
    rw [hpiece1, hpiece2]
    -- Now goal: (∑_{p<r..} -(3*η)) + (∑_{p<r..} -(3*η)) = -(3 * (2 * ∑_{p<r..} η)).
    -- First aggregate: ∑ ite (-(3*η)) 0 = -3 * ∑ ite η 0.
    have hagg : ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
            (if p.val < r.val then -(3 * crossEta m p r q s) else 0) =
        -3 * ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
          (if p.val < r.val then crossEta m p r q s else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro q _
      apply Finset.sum_congr rfl; intro s _
      by_cases hpr : p.val < r.val
      · simp only [hpr, if_true]; ring
      · simp only [hpr, if_false]; ring
    rw [hagg]
    ring
  -- Step 4: combine.
  have hbnd_eta := cross_block_eta_sum_bound_real hm
  rw [hsum_eq] at hsum_lb
  have h_bnd : -(3 * (2 * ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
        (if p.val < r.val then crossEta m p r q s else 0))) ≥
      -(16 * (m : ℝ)^3) := by
    have h_eta_nn : 0 ≤ ∑ p : Fin m, ∑ r : Fin m, ∑ q : Fin m, ∑ s : Fin m,
        (if p.val < r.val then crossEta m p r q s else 0) := by
      apply Finset.sum_nonneg; intro p _
      apply Finset.sum_nonneg; intro r _
      apply Finset.sum_nonneg; intro q _
      apply Finset.sum_nonneg; intro s _
      by_cases hpr : p.val < r.val
      · simp only [hpr, if_true]; exact (crossEta_pos m p r q s).le
      · simp only [hpr, if_false]; exact le_refl _
    -- 3 · 2 · (8/3) m³ = 16 m³.
    nlinarith [hbnd_eta]
  linarith

/-- **The m³ form (explicit)**: for all `m ≥ 1`, the witness is
`c₀ = 116 + 2 · log 4`, derived from `shapeM_log_det_ge_explicit`'s
`C₁ = 100` plus the cross-block `16 m³` and the geometric scale-ratio
`2 m³ log 4` contributions. -/
private theorem hierarchical_log_det_lower_bound_explicit :
    ∀ m : ℕ, 1 ≤ m →
      -((116 + 2 * Real.log 4) * (m : ℝ) ^ 3) ≤
        Real.log (Matrix.of fun i j : Fin m × Fin m =>
          1 / (hierGrid m i + hierGrid m j)).det := by
  -- C₁ = 100 from shapeM_log_det_ge_explicit; the witness is C₁ + 16 + 2 log 4.
  intro m hm
  have hC₁ : -((100 : ℝ) * (m : ℝ) ^ 2) ≤ Real.log (shapeM m).det :=
    shapeM_log_det_ge_explicit m hm
  -- Step 1: Apply the offDiag form of log det.
  rw [hierCauchy_log_det_offDiag hm]
  -- Step 2: Decompose offDiag of |δ_i - δ_j| into in-block + cross-block via
  --        offDiag_block_decomp. Same for log(δ_i + δ_j).
  set δ : Fin m × Fin m → ℝ := hierGrid m with hδ_def
  -- Apply offDiag_block_decomp to the |·| sum and the (·+·) sum.
  rw [offDiag_block_decomp (fun pq => Real.log |δ pq.1 - δ pq.2|)]
  rw [offDiag_block_decomp (fun pq => Real.log (δ pq.1 + δ pq.2))]
  -- Now goal has:
  --   (in-block_diff + cross-block_diff) - diag - (in-block_sum + cross-block_sum)
  -- = (in-block_diff - in-block_sum) - diag + (cross-block_diff - cross-block_sum)
  -- Step 3: Simplify. Group terms and combine in-block and cross-block.
  -- in-block_diff - in-block_sum = ∑_p ∑_{(q,q') ∈ offDiag} (log|δ_diff| - log(δ_sum))
  -- which equals m · (∑_{(q,q') ∈ offDiag} (log|s_q-s_{q'}| - log(s_q+s_{q'})))
  -- by hierCauchy_inblock_offDiag_eq.
  -- cross-block_diff - cross-block_sum is bounded below by -16 m³ via crossblock_log_lb.
  -- diag = m² log 2 + m · ∑_p log a_p + m · ∑_q log s_q via diagonal_log_contribution.
  -- Step 4: Use shapeM_log_det_offDiag to express the in-block sum in terms of log det shapeM.
  -- ∑_{(q,q') ∈ offDiag} (log|s_q-s_{q'}| - log(s_q+s_{q'})) = log det shapeM + ∑_q log(s_q + s_q)
  -- = log det shapeM + ∑_q log(2 s_q).
  -- And ∑_q log(2 s_q) = m log 2 + ∑_q log s_q.
  -- So in-block contribution = m · log det shapeM + m² log 2 + m · ∑_q log s_q.
  -- This cancels exactly with diag's m² log 2 + m · ∑_q log s_q, leaving:
  --   m · log det shapeM + m · ∑_p log a_p (with a sign).
  -- Final form:
  --   log det Σ = m · log det shapeM - m · ∑_p log a_p + (cross-block_diff - cross-block_sum)
  --
  -- Lower bounds:
  --   m · log det shapeM ≥ -100 m³ (from shapeM_log_det_ge using -100 m² · m).
  --   -m · ∑_p log a_p ≥ -m · 2 m² log 4 = -2 m³ log 4 (from sum_log_scaleA_le).
  --   (cross-block_diff - cross-block_sum) ≥ -16 m³ (from crossblock_log_lb).
  -- Sum: -100 m³ - 2 m³ log 4 - 16 m³ = -(116 + 2 log 4) m³ ≥ -(120 + 2 log 4) m³. ✓

  -- Step 4a: Compute the combined in-block sum.
  -- The in-block diff and in-block sum (from offDiag_block_decomp) combine to
  -- m · ∑_{(q,q') ∈ offDiag} (log|s_q - s_{q'}| - log(s_q + s_{q'})).
  have h_inblock_diff :
      (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
          Real.log |δ (p, qq'.1) - δ (p, qq'.2)|) -
      (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
          Real.log (δ (p, qq'.1) + δ (p, qq'.2))) =
      (m : ℝ) * (∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
        (Real.log |shapeS m qq'.1 - shapeS m qq'.2| -
          Real.log (shapeS m qq'.1 + shapeS m qq'.2))) := by
    rw [show (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
              Real.log |δ (p, qq'.1) - δ (p, qq'.2)|) -
            (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
              Real.log (δ (p, qq'.1) + δ (p, qq'.2))) =
        ∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
            (Real.log |δ (p, qq'.1) - δ (p, qq'.2)| -
              Real.log (δ (p, qq'.1) + δ (p, qq'.2))) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← Finset.sum_sub_distrib]]
    show (∑ p : Fin m, ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
          (Real.log |hierGrid m (p, qq'.1) - hierGrid m (p, qq'.2)| -
            Real.log (hierGrid m (p, qq'.1) + hierGrid m (p, qq'.2)))) =
      (m : ℝ) * _
    exact hierCauchy_inblock_offDiag_eq

  -- Step 4b: Express the shapeS offDiag sum via shapeM_log_det.
  -- ∑_{(q,q') ∈ offDiag} (log|s_q-s_{q'}| - log(s_q+s_{q'})) = log det shapeM + ∑_q log(2 s_q)
  have h_shapeM_offdiag :
      ∑ qq' ∈ (Finset.univ : Finset (Fin m)).offDiag,
        (Real.log |shapeS m qq'.1 - shapeS m qq'.2| -
          Real.log (shapeS m qq'.1 + shapeS m qq'.2)) =
      Real.log (shapeM m).det + ∑ q : Fin m, Real.log (shapeS m q + shapeS m q) := by
    rw [shapeM_log_det_offDiag]
    rw [Finset.sum_sub_distrib]
    ring

  -- Step 4c: Diagonal contribution.
  have h_diag := diagonal_log_contribution m

  -- Step 5: Cross-block lower bound.
  have h_cross := crossblock_log_lb hm

  -- Build the combined cross-block diff.
  have h_cross_combined :
      (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
          Real.log |δ (pr.1, q) - δ (pr.2, s)|) -
      (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
          Real.log (δ (pr.1, q) + δ (pr.2, s))) ≥ -(16 * (m : ℝ)^3) := by
    have hexpand :
        (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
            Real.log |δ (pr.1, q) - δ (pr.2, s)|) -
        (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
            Real.log (δ (pr.1, q) + δ (pr.2, s))) =
        ∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
            (Real.log |δ (pr.1, q) - δ (pr.2, s)| -
              Real.log (δ (pr.1, q) + δ (pr.2, s))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro pr _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro q _
      rw [← Finset.sum_sub_distrib]
    rw [hexpand]
    show (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
          (Real.log |hierGrid m (pr.1, q) - hierGrid m (pr.2, s)| -
            Real.log (hierGrid m (pr.1, q) + hierGrid m (pr.2, s)))) ≥
      -(16 * (m : ℝ)^3)
    have := h_cross
    linarith

  -- Step 6: Combine.
  -- log det Σ = (in-block_diff + cross-block_diff) - diag - (in-block_sum + cross-block_sum)
  --          = h_inblock_diff_lhs + (cross-block_diff - cross-block_sum) - diag
  -- Apply h_inblock_diff to rewrite first part.
  rw [show ∀ (A B C D E : ℝ), A + B - C - (D + E) = (A - D) + (B - E) - C
      from fun A B C D E => by ring]
  rw [h_inblock_diff, h_shapeM_offdiag, h_diag]

  -- Use ∑_q log(s_q + s_q) = ∑_q log(2 s_q) = m log 2 + ∑_q log s_q.
  have h_sum_2sq : ∑ q : Fin m, Real.log (shapeS m q + shapeS m q) =
      (m : ℝ) * Real.log 2 + ∑ q : Fin m, Real.log (shapeS m q) := by
    have hpw : ∀ q : Fin m, Real.log (shapeS m q + shapeS m q) =
        Real.log 2 + Real.log (shapeS m q) := by
      intro q
      have h2sq : shapeS m q + shapeS m q = 2 * shapeS m q := by ring
      rw [h2sq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (shapeS_pos m q))]
    rw [Finset.sum_congr rfl (fun q _ => hpw q)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]

  rw [h_sum_2sq]

  -- Now goal:
  --   ↑m * (log det shapeM + (↑m * log 2 + ∑ q, log (shapeS m q))) +
  --   (... cross-diff - cross-sum ...) -
  --   (↑m^2 * log 2 + ↑m * ∑ p, log (scaleA m p) + ↑m * ∑ q, log (shapeS m q))
  -- ≥ -((120 + 2 * log 4) * ↑m^3)
  -- The m² log 2 + m · ∑_q log s_q cancels.
  -- Goal simplifies to:
  --   m · log det shapeM + (cross-diff - cross-sum) - m · ∑_p log a_p ≥ -(120 + 2 log 4) m³
  -- Lower bound:
  --   m · log det shapeM ≥ m · (-100 m²) = -100 m³
  --   cross-diff - cross-sum ≥ -16 m³
  --   -m · ∑_p log a_p ≥ -m · 2 m² log 4 = -2 m³ log 4
  -- Total ≥ -118 m³ - 2 m³ log 4 ≥ -(120 + 2 log 4) m³. ✓.
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm_nn : (0 : ℝ) ≤ m := hm_pos.le
  have hm3_nn : (0 : ℝ) ≤ (m : ℝ)^3 := by positivity
  have hm2_nn : (0 : ℝ) ≤ (m : ℝ)^2 := by positivity
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

  have hC₁_use : -((100 : ℝ) * (m : ℝ)^2) ≤ Real.log (shapeM m).det := hC₁
  -- m · log det shapeM ≥ -m · 100 · m² = -100 · m³.
  have h_shapeM_lb : (m : ℝ) * Real.log (shapeM m).det ≥ -((100 : ℝ) * (m : ℝ)^3) := by
    have h_m_C1 : (m : ℝ) * (-((100 : ℝ) * (m : ℝ)^2)) = -(100 * (m : ℝ)^3) := by ring
    have hmul := mul_le_mul_of_nonneg_left hC₁_use hm_nn
    linarith [hmul]

  -- ∑_p log a_p ≤ 2 m² log 4 (from sum_log_scaleA_le).
  have h_logA_le := sum_log_scaleA_le hm
  -- m · ∑_p log a_p ≤ 2 m³ log 4.
  have h_m_logA_le : (m : ℝ) * ∑ p : Fin m, Real.log (scaleA m p) ≤
      2 * (m : ℝ)^3 * Real.log 4 := by
    have := mul_le_mul_of_nonneg_left h_logA_le hm_nn
    have heq : (m : ℝ) * (2 * (m : ℝ)^2 * Real.log 4) = 2 * (m : ℝ)^3 * Real.log 4 := by ring
    linarith

  -- All pieces combined.
  -- In Lean, the goal currently is:
  --   m * (log det shapeM + (m * log 2 + ∑ log s_q)) + crossDiff -
  --     (m² log 2 + m * ∑ log a_p + m * ∑ log s_q) ≥ -((120 + 2 log 4) * m³)
  -- Collect crossDiff name and bound it.
  set crossDiff : ℝ :=
    (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
        Real.log |δ (pr.1, q) - δ (pr.2, s)|) -
    (∑ pr ∈ (Finset.univ : Finset (Fin m)).offDiag, ∑ q : Fin m, ∑ s : Fin m,
        Real.log (δ (pr.1, q) + δ (pr.2, s))) with hcrossDiff_def

  -- Rewrite goal in terms of crossDiff.
  have hgoal_simp :
      (m : ℝ) * (Real.log (shapeM m).det + ((m : ℝ) * Real.log 2 + ∑ q : Fin m, Real.log (shapeS m q))) +
      crossDiff -
      ((m : ℝ)^2 * Real.log 2 + (m : ℝ) * ∑ p : Fin m, Real.log (scaleA m p) +
        (m : ℝ) * ∑ q : Fin m, Real.log (shapeS m q)) =
      (m : ℝ) * Real.log (shapeM m).det + crossDiff -
        (m : ℝ) * ∑ p : Fin m, Real.log (scaleA m p) := by
    have hmsq : (m : ℝ) * ((m : ℝ) * Real.log 2) = (m : ℝ)^2 * Real.log 2 := by ring
    ring

  show (m : ℝ) * (Real.log (shapeM m).det + ((m : ℝ) * Real.log 2 + ∑ q : Fin m, Real.log (shapeS m q))) +
      crossDiff -
      ((m : ℝ)^2 * Real.log 2 + (m : ℝ) * ∑ p : Fin m, Real.log (scaleA m p) +
        (m : ℝ) * ∑ q : Fin m, Real.log (shapeS m q)) ≥ -((116 + 2 * Real.log 4) * (m : ℝ)^3)
  rw [hgoal_simp]

  -- Final inequality: m · log det shapeM + crossDiff - m · ∑ log a_p ≥ -(116 + 2 log 4) m³.
  -- Use the three lower bounds:
  --   m · log det shapeM ≥ -100 m³.
  --   crossDiff ≥ -16 m³.
  --   -m · ∑ log a_p ≥ -2 m³ log 4.
  have hCross_use : crossDiff ≥ -(16 * (m : ℝ)^3) := h_cross_combined
  linarith [h_shapeM_lb, hCross_use, h_m_logA_le, hm3_nn, hlog4_pos]

/-- **The m³ form (existential)**: there exists `c₀ > 0` such that
`-c₀ · m³ ≤ log det Σ` for all `m ≥ 1`. Thin wrapper around
`hierarchical_log_det_lower_bound_explicit` with `c₀ = 116 + 2 · log 4`. -/
private theorem hierarchical_log_det_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℕ, 1 ≤ m →
      -(c₀ * (m : ℝ) ^ 3) ≤ Real.log (Matrix.of fun i j : Fin m × Fin m =>
        1 / (hierGrid m i + hierGrid m j)).det := by
  refine ⟨116 + 2 * Real.log 4, ?_, hierarchical_log_det_lower_bound_explicit⟩
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  linarith

/-- **Main theorem.** There exists an absolute constant `c₀ > 0` such that
for the `m² × m²` Cauchy matrix `Σ` on the hierarchical grid
`δ_{p,q} = 4^(p+m) · (m + q + 1)`, we have
`det Σ ≥ exp(-c₀ · m³)` for all `m ≥ 1`.

The proof goes through the algebraic identity that decomposes
`log det Σ = m · log det shapeM + 2 · ∑_{p<r,q,s} log((1-η)/(1+η)) - m · ∑_p log a_p`,
combining `shapeM_log_det_ge` (via Stirling), the artanh perturbation bound,
and the geometric scale-ratio sum. -/
theorem cauchy_hierarchical_det_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℕ, 1 ≤ m →
      Real.exp (-(c₀ * (m : ℝ) ^ 3)) ≤
        (Matrix.of fun i j : Fin m × Fin m =>
          1 / (hierGrid m i + hierGrid m j)).det := by
  obtain ⟨c₀, hc₀_pos, hc₀⟩ := hierarchical_log_det_lower_bound
  refine ⟨c₀, hc₀_pos, ?_⟩
  intro m hm
  have hdet_pos : 0 < (Matrix.of fun i j : Fin m × Fin m =>
      1 / (hierGrid m i + hierGrid m j)).det := by
    have := hierCauchy_det_pos hm
    unfold hierCauchy at this
    exact this
  -- Reduce to log form: exp(-c₀ m³) ≤ det Σ ↔ -c₀ m³ ≤ log det Σ.
  have hlog_lb : -(c₀ * (m : ℝ) ^ 3) ≤
      Real.log (Matrix.of fun i j : Fin m × Fin m =>
        1 / (hierGrid m i + hierGrid m j)).det :=
    hc₀ m hm
  have := Real.exp_le_exp.mpr hlog_lb
  rwa [Real.exp_log hdet_pos] at this

/-- **Sister lemma with explicit constant.** For all `m ≥ 1`,
the Cauchy determinant satisfies `det Σ ≥ exp(-120 · m³)`.
The constant `120` is comfortably above the actual witness
`116 + 2 · log 4 ≈ 118.77` from `hierarchical_log_det_lower_bound_explicit`,
giving callers a clean numerical bound to chain against. -/
theorem cauchy_hierarchical_det_lower_bound_explicit :
    ∀ m : ℕ, 1 ≤ m →
      Real.exp (-(120 : ℝ) * (m : ℝ) ^ 3) ≤
        (Matrix.of fun i j : Fin m × Fin m =>
          1 / (hierGrid m i + hierGrid m j)).det := by
  intro m hm
  -- Step 1: 116 + 2 · log 4 ≤ 120 since log 2 < 0.6932 ⟹ log 4 = 2·log 2 < 1.3864.
  have h_log2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h_log4_eq : Real.log 4 = 2 * Real.log 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]; push_cast; ring
  have h_const : 116 + 2 * Real.log 4 ≤ 120 := by
    rw [h_log4_eq]; linarith
  -- Step 2: m³ ≥ 0, so (116 + 2 log 4) · m³ ≤ 120 · m³.
  have hm3_nn : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
  have h_chain : (116 + 2 * Real.log 4) * (m : ℝ) ^ 3 ≤ 120 * (m : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right h_const hm3_nn
  -- Step 3: Apply explicit log bound and exp.
  have h_log_explicit := hierarchical_log_det_lower_bound_explicit m hm
  have h_log_lb : -((120 : ℝ) * (m : ℝ) ^ 3) ≤
      Real.log (Matrix.of fun i j : Fin m × Fin m =>
        1 / (hierGrid m i + hierGrid m j)).det := by linarith
  have hdet_pos : 0 < (Matrix.of fun i j : Fin m × Fin m =>
      1 / (hierGrid m i + hierGrid m j)).det := by
    have := hierCauchy_det_pos hm
    unfold hierCauchy at this
    exact this
  have h_exp_chain := Real.exp_le_exp.mpr h_log_lb
  rw [Real.exp_log hdet_pos] at h_exp_chain
  have h_neg_eq : -(120 : ℝ) * (m : ℝ) ^ 3 = -((120 : ℝ) * (m : ℝ) ^ 3) := by ring
  rw [h_neg_eq]
  exact h_exp_chain

end Erdos524.Helpers
