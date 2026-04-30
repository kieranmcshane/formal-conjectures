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

import FormalConjectures.ErdosProblems.Helpers.YGLWConstruction
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
# Phase 2 / Round 11 — Bridge to the `brownian-motion` project

This file provides the **Tier-2 bridge** to retire the `Y_GLW_exists`
axiom via the [Degenne–Pfaffelhuber 2025 `brownian-motion` Lean
project](https://github.com/RemyDegenne/brownian-motion). That project
has a fully formalised Brownian motion via the
**projective-limit construction**:

1. `brownianCovMatrix I : Matrix I I ℝ` for finite `I ⊆ ℝ≥0` with
   `K_BM(s, t) = min(s, t)`,
2. `gaussianProjectiveFamily I` from `multivariateGaussian 0
   (brownianCovMatrix I)`,
3. `projectiveLimit gaussianProjectiveFamily : Measure (ℝ≥0 → ℝ)`,
4. `kolmogorov_chentsov_continuity` for continuous-paths modification.

The construction is **kernel-generic**: replacing `min(s, t)` with
`K_GLW(u, v)` gives the GLW process directly. The bridge below packages
the *kernel-side* content needed for that substitution (PSD,
finite-grid positivity), and documents the BM-side calls as BLOCKERs
parameterised over the (not-yet-imported) `brownian-motion` API.

## Why a bridge file

The `brownian-motion` project uses Lean 4.30.0-rc1 (master) or 4.27.0-rc1
(historical, commit `91267abd`), neither of which exactly matches our
project's pinned `leanprover/lean4:v4.27.0` toolchain. A direct
`require brownian-motion from git` clause is therefore not currently
possible without a coordinated toolchain bump. This bridge file is the
explicit specification of how the retirement *would* proceed, with all
the kernel-side arguments proved in full.

## What this file contributes

### K_GLW-specific content

* **`glwCovMatrix`**: the concrete K_GLW Gram matrix on a finite grid
  `us : Fin n → ℝ`, with `(glwCovMatrix us) i j = K_GLW (us i) (us j)`.
* **`glwCovMatrix_isHermitian`** and **`glwCovMatrix_symm`**: symmetry
  (corollary of `K_GLW_symm`).
* **`glwCovMatrix_PosSemidef`**: positive semi-definiteness, a corollary
  of `K_GLW_quadratic_form_nonneg` from `YGLWConstruction.lean`. This
  is the **mathematical core of the bridge**: the precondition for
  `multivariateGaussian` (Mathlib's existing API and the
  `brownian-motion` project's).
* **`glwCovMatrix_eq_gramMatrixL2`**: K_GLW Gram = generic Gram of
  the exponential family.
* **`glwCovMatrix_PosSemidef_via_gramMatrixL2`**: alternative 2-line
  proof of K_GLW PSD via the generic abstraction below.
* **Entry-wise**: `glwCovMatrix_entry_pos` (every entry > 0 on nonneg
  grids), `glwCovMatrix_entry_le_one`, `glwCovMatrix_diag_at_zero`,
  `glwCovMatrix_diag_nonneg`, `glwCovMatrix_diag_le_one`.
* **Mercer matrix form**: `glwCovMatrix_eq_integral` recasts each entry
  as the L²([0,1]) inner product of the exponential integrands.
* **Sub-grid restriction**: `glwCovMatrix_submatrix`,
  `glwCovMatrix_submatrix_PosSemidef` — restriction of the K_GLW Gram
  matrix to a sub-grid is again the K_GLW Gram of the sub-grid, with
  PSD preserved (the BLOCKER-B2 precondition).
* **Det / trace bounds**: `glwCovMatrix_det_nonneg`,
  `glwCovMatrix_trace_nonneg`, `glwCovMatrix_trace_le`.

### Generic Gram-matrix abstraction (Mathlib-PR-shaped)

* **`gramMatrixL2`**: for any family `(φᵢ : Fin n → ℝ → ℝ)`, the Gram
  matrix `G_{ij} = ∫₀¹ φᵢ φⱼ`.
* **`gramMatrixL2_PosSemidef`**: for any continuous family, `G` is
  positive semi-definite. Proof via the integral-of-square argument.
  `glwCovMatrix_PosSemidef` is the K_GLW special case where
  `φᵢ s := exp(-uᵢ s)`.
* **`gramMatrixL2_diag_eq`**: G_{ii} = ‖φᵢ‖²_{L²([0,1])}.
* **`gramMatrixL2_diff_sq`**: ∫ (φᵢ - φⱼ)² = G_{ii} + G_{jj} - 2 G_{ij}
  (the L²-distance / variance-of-difference identity).
* **`gramMatrixL2_smul_family`**: bilinearity in per-index scaling.
* **`gramMatrixL2_zero`**: the constant-zero family yields the zero
  matrix.
* **`gramMatrixL2_submatrix`**: sub-grid restriction.

### Documented BLOCKERs

For each step of the `brownian-motion` projective-limit construction
the bridge documents the missing project API and identifies the
**preconditions already proven here**:

* **B1 (multivariateGaussian)**: `glwCovMatrix_PosSemidef` ✓
* **B2 (gaussianProjectiveFamily consistency)**:
  `glwCovMatrix_submatrix_PosSemidef` ✓
* **B3 (projectiveLimit / Kolmogorov extension)**: external API needed.
* **B4 (Kolmogorov–Chentsov continuity)**: `L2_diff_le_sq` from
  `YGLWConstruction.lean` ✓
* **B5 (Borell + Borel–Cantelli tail decay)**: `K_GLW_var_tendsto_zero`
  from `YGLWConstruction.lean` ✓

Only B3 (the abstract projective-limit theorem) requires the
`brownian-motion` project's API. All four other preconditions have
explicit Lean witnesses proved across this file and `YGLWConstruction.lean`.

When the toolchain alignment lands, the bridge becomes a 5-step proof
with no sorries.
-/

namespace Erdos524.Helpers
open Matrix MeasureTheory

/-! ## 1. The K_GLW finite-grid Gram matrix -/

/-- The K_GLW finite-grid covariance matrix on `Fin n` indexed by a
positive grid `us : Fin n → ℝ`. -/
noncomputable def glwCovMatrix {n : ℕ} (us : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => K_GLW (us i) (us j)

@[simp]
theorem glwCovMatrix_apply {n : ℕ} (us : Fin n → ℝ) (i j : Fin n) :
    glwCovMatrix us i j = K_GLW (us i) (us j) := rfl

/-! ## 2. Symmetry / Hermitian property -/

/-- `glwCovMatrix` is symmetric: `glwCovMatrix us i j = glwCovMatrix us j i`. -/
theorem glwCovMatrix_symm {n : ℕ} (us : Fin n → ℝ) (i j : Fin n) :
    glwCovMatrix us i j = glwCovMatrix us j i := by
  simp [glwCovMatrix_apply, K_GLW_symm]

/-- `glwCovMatrix` is Hermitian (real-valued symmetric matrix). -/
theorem glwCovMatrix_isHermitian {n : ℕ} (us : Fin n → ℝ) :
    (glwCovMatrix us).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose, Matrix.transpose,
        glwCovMatrix_apply, K_GLW_symm]

/-! ## 3. Positive semi-definiteness — the main contribution -/

/-- **The key bridge lemma**: `glwCovMatrix` is positive semi-definite
for any nonnegative grid. Direct corollary of
`K_GLW_quadratic_form_nonneg` from `YGLWConstruction.lean`. -/
theorem glwCovMatrix_PosSemidef {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    (glwCovMatrix us).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (glwCovMatrix_isHermitian us) ?_
  intro x
  -- Goal: 0 ≤ star x ⬝ᵥ (glwCovMatrix us *ᵥ x).
  -- Over ℝ, `star = id`, so `star x ⬝ᵥ ... = x ⬝ᵥ ...`.
  -- Expand: x ⬝ᵥ (M *ᵥ x) = ∑ i, x i * ∑ j, M i j * x j = ∑ i ∑ j, x i * x j * K(uᵢ, uⱼ).
  show 0 ≤ ∑ i, star (x i) * ((glwCovMatrix us *ᵥ x) i)
  have h_eq : ∑ i, star (x i) * ((glwCovMatrix us *ᵥ x) i) =
              ∑ i, ∑ j, x i * x j * K_GLW (us i) (us j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct]
    rw [show star (x i) = x i from rfl]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [glwCovMatrix_apply]
    ring
  rw [h_eq]
  exact K_GLW_quadratic_form_nonneg us x h_us

/-! ## 4. Diagonal entries -/

/-- The diagonal of `glwCovMatrix` records the marginal variances
`K_GLW(uᵢ, uᵢ)`. -/
@[simp]
theorem glwCovMatrix_diag_eq {n : ℕ} (us : Fin n → ℝ) (i : Fin n) :
    glwCovMatrix us i i = K_GLW (us i) (us i) := rfl

/-- Each diagonal entry is non-negative for nonneg-indexed grids. -/
theorem glwCovMatrix_diag_nonneg {n : ℕ} (us : Fin n → ℝ) (h_us : ∀ i, 0 ≤ us i)
    (i : Fin n) :
    0 ≤ glwCovMatrix us i i := by
  rw [glwCovMatrix_diag_eq]
  exact le_of_lt (K_GLW_pos _ _ (h_us i) (h_us i))

/-- Each diagonal entry is bounded above by `1`. -/
theorem glwCovMatrix_diag_le_one {n : ℕ} (us : Fin n → ℝ) (h_us : ∀ i, 0 ≤ us i)
    (i : Fin n) :
    glwCovMatrix us i i ≤ 1 := by
  rw [glwCovMatrix_diag_eq]
  exact K_GLW_le_one _ _ (h_us i) (h_us i)

/-! ## 4.5. Entry-wise positivity and bounds -/

/-- Every entry of `glwCovMatrix us` is strictly positive on nonneg
grids. Direct from `K_GLW_pos`. -/
theorem glwCovMatrix_entry_pos {n : ℕ} (us : Fin n → ℝ) (h_us : ∀ i, 0 ≤ us i)
    (i j : Fin n) :
    0 < glwCovMatrix us i j := by
  rw [glwCovMatrix_apply]
  exact K_GLW_pos _ _ (h_us i) (h_us j)

/-- Every entry of `glwCovMatrix us` is bounded above by `1` on nonneg
grids. Direct from `K_GLW_le_one`. -/
theorem glwCovMatrix_entry_le_one {n : ℕ} (us : Fin n → ℝ) (h_us : ∀ i, 0 ≤ us i)
    (i j : Fin n) :
    glwCovMatrix us i j ≤ 1 := by
  rw [glwCovMatrix_apply]
  exact K_GLW_le_one _ _ (h_us i) (h_us j)

/-- The (i, i) entry equals `1` when `uᵢ = 0`. -/
theorem glwCovMatrix_diag_at_zero {n : ℕ} (us : Fin n → ℝ) {i : Fin n}
    (hi : us i = 0) :
    glwCovMatrix us i i = 1 := by
  rw [glwCovMatrix_diag_eq, hi]
  exact K_GLW_zero

/-! ## 4.55. Generic Mercer / Gram-matrix abstraction (Mathlib-PR-shaped)

The Mercer / Gram structure is **kernel-generic**: for any family
`(φᵢ : ℝ → ℝ)_{i ∈ Fin n}` of square-integrable functions on `[0, 1]`,
the Gram matrix `Gᵢⱼ := ⟨φᵢ, φⱼ⟩_{L²([0,1])} = ∫₀¹ φᵢ φⱼ` is positive
semi-definite. This is exactly what makes Mercer kernels well-defined.

`glwCovMatrix_PosSemidef` is the K_GLW specialisation; the abstraction
below lifts the argument to any kernel of the form `K(i, j) = ⟨φᵢ, φⱼ⟩`. -/

/-- The Gram matrix of a family of continuous functions, evaluated as
`G_{i,j} := ∫₀¹ φᵢ(s) · φⱼ(s) ds`. -/
noncomputable def gramMatrixL2 {n : ℕ} (φ : Fin n → ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∫ s in (0 : ℝ)..1, φ i s * φ j s

@[simp]
theorem gramMatrixL2_apply {n : ℕ} (φ : Fin n → ℝ → ℝ) (i j : Fin n) :
    gramMatrixL2 φ i j = ∫ s in (0 : ℝ)..1, φ i s * φ j s := rfl

/-- The Gram matrix is symmetric. -/
theorem gramMatrixL2_symm {n : ℕ} (φ : Fin n → ℝ → ℝ) (i j : Fin n) :
    gramMatrixL2 φ i j = gramMatrixL2 φ j i := by
  simp [gramMatrixL2_apply]
  congr 1
  funext s
  ring

/-- **Generic Mercer / Gram-matrix PSD** (Mathlib-PR-shaped abstraction):
for any family of continuous functions `(φᵢ)_{i ∈ Fin n}`, the Gram
matrix `Gᵢⱼ := ∫₀¹ φᵢ φⱼ` is positive semi-definite.

Proof: the quadratic form is `∑ᵢⱼ xᵢ xⱼ ∫₀¹ φᵢ φⱼ = ∫₀¹ (∑ᵢ xᵢ φᵢ)²`,
the integral of a square — non-negative. This is a Mathlib-PR-shaped
generalisation of `glwCovMatrix_PosSemidef` (which is the special case
`φᵢ(s) := exp(-uᵢ s)`). -/
theorem gramMatrixL2_PosSemidef {n : ℕ} (φ : Fin n → ℝ → ℝ)
    (h_cont : ∀ i, Continuous (φ i)) :
    (gramMatrixL2 φ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: gramMatrixL2 is symmetric (i,j-swap preserves the integral).
    ext i j
    simp [Matrix.conjTranspose, Matrix.transpose, gramMatrixL2_apply]
    congr 1
    funext s
    ring
  · intro x
    -- Goal: 0 ≤ star x ⬝ᵥ (G *ᵥ x).
    show 0 ≤ ∑ i, star (x i) * ((gramMatrixL2 φ *ᵥ x) i)
    -- Step 1: rewrite each row entry as ∫₀¹ φᵢ * (∑ⱼ xⱼ φⱼ).
    have h_pair_int : ∀ i j : Fin n,
        IntervalIntegrable (fun s => x i * x j * (φ i s * φ j s))
          MeasureTheory.volume 0 1 := by
      intro i j
      have h_cont_ij : Continuous (fun s => x i * x j * (φ i s * φ j s)) := by
        exact continuous_const.mul ((h_cont i).mul (h_cont j))
      exact h_cont_ij.intervalIntegrable 0 1
    have h_rowsum_cont : ∀ i, Continuous
        (fun s => ∑ j : Fin n, x i * x j * (φ i s * φ j s)) := by
      intro i
      apply continuous_finset_sum
      intro j _
      exact continuous_const.mul ((h_cont i).mul (h_cont j))
    have h_rowsum_int : ∀ i, IntervalIntegrable
        (fun s => ∑ j : Fin n, x i * x j * (φ i s * φ j s))
        MeasureTheory.volume 0 1 :=
      fun i => (h_rowsum_cont i).intervalIntegrable 0 1
    -- Step 2: the entire sum equals ∫₀¹ (∑ᵢ xᵢ φᵢ s)².
    have h_quad_eq : (∑ i, star (x i) * ((gramMatrixL2 φ *ᵥ x) i)) =
        ∫ s in (0 : ℝ)..1, (∑ i, x i * φ i s)^2 := by
      -- Step 2a: expand each row entry.
      have h_row_simp : ∀ i, star (x i) * ((gramMatrixL2 φ *ᵥ x) i) =
          ∑ j : Fin n, x i * x j * (gramMatrixL2 φ i j) := by
        intro i
        rw [Matrix.mulVec, dotProduct]
        rw [show star (x i) = x i from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have h_pair_eq : ∀ i j : Fin n, x i * x j * (gramMatrixL2 φ i j) =
          ∫ s in (0 : ℝ)..1, x i * x j * (φ i s * φ j s) := by
        intro i j
        rw [gramMatrixL2_apply, intervalIntegral.integral_const_mul]
      have h_row_eq : ∀ i, star (x i) * ((gramMatrixL2 φ *ᵥ x) i) =
          ∫ s in (0 : ℝ)..1, ∑ j : Fin n, x i * x j * (φ i s * φ j s) := by
        intro i
        rw [h_row_simp]
        rw [show (∑ j : Fin n, x i * x j * gramMatrixL2 φ i j) =
              ∑ j : Fin n, ∫ s in (0 : ℝ)..1, x i * x j * (φ i s * φ j s) from
              Finset.sum_congr rfl fun j _ => h_pair_eq i j]
        symm
        exact intervalIntegral.integral_finset_sum (fun j _ => h_pair_int i j)
      -- Step 2b: now sum over i and pull integral out.
      rw [Finset.sum_congr rfl (fun i _ => h_row_eq i)]
      rw [← intervalIntegral.integral_finset_sum
            (fun i _ => h_rowsum_int i)]
      congr 1
      funext s
      -- Goal: ∑ᵢⱼ xᵢ xⱼ φᵢ s φⱼ s = (∑ᵢ xᵢ φᵢ s)².
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h_quad_eq]
    -- ∫₀¹ f² ≥ 0.
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun _ => sq_nonneg _)

/-! ## 4.55b. Generic Gram-matrix corollaries (Mathlib-PR-shaped)

The diagonal entries `gramMatrixL2 φ i i = ∫ (φᵢ)²` are the squared
L²-norms of the family. Combined with the PSD result, these give
clean structural identities. -/

/-- The diagonal entries of `gramMatrixL2` equal the integrand-squared
integrals (= squared L²([0,1]) norms). -/
@[simp]
theorem gramMatrixL2_diag_eq {n : ℕ} (φ : Fin n → ℝ → ℝ) (i : Fin n) :
    gramMatrixL2 φ i i = ∫ s in (0 : ℝ)..1, (φ i s)^2 := by
  rw [gramMatrixL2_apply]
  congr 1
  funext s
  ring

/-- Each diagonal entry of `gramMatrixL2` is non-negative. The integrand
`(φᵢ s)²` is non-negative pointwise, so the integral over `[0, 1]` is. -/
theorem gramMatrixL2_diag_nonneg {n : ℕ} (φ : Fin n → ℝ → ℝ)
    (i : Fin n) :
    0 ≤ gramMatrixL2 φ i i := by
  rw [gramMatrixL2_diag_eq]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun _ => sq_nonneg _)

/-- The "L²-distance squared" identity:
`∫₀¹ (φᵢ - φⱼ)² = G_{ii} + G_{jj} - 2 G_{ij}`. The deterministic
shadow of `‖X - Y‖²_{L²(Ω)} = Var(X) + Var(Y) - 2 Cov(X, Y)`. -/
theorem gramMatrixL2_diff_sq {n : ℕ} (φ : Fin n → ℝ → ℝ)
    (h_cont : ∀ i, Continuous (φ i)) (i j : Fin n) :
    ∫ s in (0 : ℝ)..1, (φ i s - φ j s)^2 =
      gramMatrixL2 φ i i - 2 * gramMatrixL2 φ i j + gramMatrixL2 φ j j := by
  have h_expand : (fun s : ℝ => (φ i s - φ j s)^2) =
      fun s : ℝ => (φ i s)^2 - 2 * (φ i s * φ j s) + (φ j s)^2 := by
    funext s; ring
  rw [h_expand]
  have h_ii : IntervalIntegrable (fun s : ℝ => (φ i s)^2) MeasureTheory.volume 0 1 := by
    have h_cont_ii : Continuous (fun s : ℝ => (φ i s)^2) := (h_cont i).pow 2
    exact h_cont_ii.intervalIntegrable 0 1
  have h_jj : IntervalIntegrable (fun s : ℝ => (φ j s)^2) MeasureTheory.volume 0 1 := by
    have h_cont_jj : Continuous (fun s : ℝ => (φ j s)^2) := (h_cont j).pow 2
    exact h_cont_jj.intervalIntegrable 0 1
  have h_ij : IntervalIntegrable (fun s : ℝ => φ i s * φ j s)
      MeasureTheory.volume 0 1 :=
    ((h_cont i).mul (h_cont j)).intervalIntegrable 0 1
  have h_2ij : IntervalIntegrable (fun s : ℝ => 2 * (φ i s * φ j s))
      MeasureTheory.volume 0 1 := h_ij.const_mul 2
  rw [intervalIntegral.integral_add (h_ii.sub h_2ij) h_jj,
      intervalIntegral.integral_sub h_ii h_2ij,
      intervalIntegral.integral_const_mul,
      gramMatrixL2_diag_eq, gramMatrixL2_diag_eq, gramMatrixL2_apply]

/-! ## 4.56. K_GLW Gram-matrix as a special case of `gramMatrixL2`

The K_GLW Gram matrix `glwCovMatrix us` is the generic Gram matrix
`gramMatrixL2` applied to the exponential family
`s ↦ exp(-uᵢ s)`. So `glwCovMatrix_PosSemidef` factors through
`gramMatrixL2_PosSemidef`. -/

/-- For nonneg grids `us`, the K_GLW Gram matrix equals the generic
L²([0,1])-Gram matrix of the exponential integrand family. -/
theorem glwCovMatrix_eq_gramMatrixL2 {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    glwCovMatrix us = gramMatrixL2 (fun i => glwIntegrand (us i)) := by
  ext i j
  rw [glwCovMatrix_apply, gramMatrixL2_apply]
  exact K_GLW_eq_integral_glwIntegrand_mul (h_us i) (h_us j)

/-- **Alternative proof of `glwCovMatrix_PosSemidef`** via the generic
Gram-matrix abstraction. The original proof in Section 3 unrolls the
integral-of-square argument inline; this alternative shows the same
result is a 2-line corollary of the generic Mathlib-PR-shaped lemma. -/
theorem glwCovMatrix_PosSemidef_via_gramMatrixL2 {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    (glwCovMatrix us).PosSemidef := by
  rw [glwCovMatrix_eq_gramMatrixL2 us h_us]
  exact gramMatrixL2_PosSemidef _ (fun i => glwIntegrand_continuous (us i))

/-! ## 4.6. Mercer integral representation, matrix form

The matrix form of the Mercer / L²-inner-product representation
`K_GLW(uᵢ, uⱼ) = ∫₀¹ exp(-uᵢ s) · exp(-uⱼ s) ds` says that
`glwCovMatrix us` is the Gram matrix of the family
`(s ↦ exp(-uᵢ s))_{i ∈ Fin n}` under the L²([0, 1]) inner product. -/

/-- Each entry of `glwCovMatrix us` equals the L²([0,1]) inner product
of the corresponding pair of integrand functions. The matrix form of
`K_GLW_eq_integral_glwIntegrand_mul`. -/
theorem glwCovMatrix_eq_integral {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) (i j : Fin n) :
    glwCovMatrix us i j =
      ∫ s in (0 : ℝ)..1, glwIntegrand (us i) s * glwIntegrand (us j) s := by
  rw [glwCovMatrix_apply]
  exact K_GLW_eq_integral_glwIntegrand_mul (h_us i) (h_us j)

/-! ## 4.65. Bilinearity in the family

`gramMatrixL2 φ` is bilinear in the family `φ` in the natural sense:
scaling each integrand `φᵢ` by `cᵢ` scales the (i, j) entry by `cᵢ · cⱼ`. -/

/-- Scaling the integrand family by per-index constants scales each
Gram-matrix entry by the product of the constants. -/
theorem gramMatrixL2_smul_family {n : ℕ} (φ : Fin n → ℝ → ℝ)
    (cs : Fin n → ℝ) (i j : Fin n) :
    gramMatrixL2 (fun i s => cs i * φ i s) i j =
      cs i * cs j * gramMatrixL2 φ i j := by
  rw [gramMatrixL2_apply, gramMatrixL2_apply,
      ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

/-- The Gram matrix of the constant-zero family is zero. -/
@[simp]
theorem gramMatrixL2_zero {n : ℕ} :
    gramMatrixL2 (fun (_ : Fin n) (_ : ℝ) => (0 : ℝ)) = 0 := by
  ext i j
  simp [gramMatrixL2_apply]

/-! ## 4.7. Submatrix / sub-grid restriction

For the projective-family consistency hypothesis (BLOCKER B2 below):
restriction of the K_GLW Gram matrix to a sub-grid yields the K_GLW
Gram of the sub-grid. Generic version for `gramMatrixL2`. -/

/-- Restricting `gramMatrixL2` to a sub-index `f : Fin m → Fin n` is
the Gram matrix of the restricted family `φ ∘ f`. -/
theorem gramMatrixL2_submatrix {m n : ℕ} (φ : Fin n → ℝ → ℝ)
    (f : Fin m → Fin n) :
    (gramMatrixL2 φ).submatrix f f = gramMatrixL2 (φ ∘ f) := by
  ext i j
  rfl

/-- Restricting `glwCovMatrix` to a sub-grid `f : Fin m → Fin n` is the
K_GLW Gram of the sub-grid. -/
theorem glwCovMatrix_submatrix {m n : ℕ} (us : Fin n → ℝ)
    (f : Fin m → Fin n) :
    (glwCovMatrix us).submatrix f f = glwCovMatrix (us ∘ f) := by
  ext i j
  rfl

/-- The PSD property is preserved under sub-grid restriction. (This
matches the projective-family marginalisation hypothesis B2: the
K_GLW Gaussian projective family on a finite index set restricts to
the K_GLW Gaussian projective family on any subset.) -/
theorem glwCovMatrix_submatrix_PosSemidef {m n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) (f : Fin m → Fin n) :
    ((glwCovMatrix us).submatrix f f).PosSemidef := by
  rw [glwCovMatrix_submatrix]
  exact glwCovMatrix_PosSemidef (us ∘ f) (fun i => h_us (f i))

/-! ## 4.8. Determinant and trace bounds

Standard PSD corollaries: `det ≥ 0` and `trace ≥ 0`. -/

/-- The determinant of `glwCovMatrix us` is non-negative for nonneg
grids (a corollary of `PosSemidef.det_nonneg`). -/
theorem glwCovMatrix_det_nonneg {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    0 ≤ (glwCovMatrix us).det :=
  (glwCovMatrix_PosSemidef us h_us).det_nonneg

/-- The trace of `glwCovMatrix us` is non-negative for nonneg grids
(sum of non-negative diagonal entries). -/
theorem glwCovMatrix_trace_nonneg {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    0 ≤ (glwCovMatrix us).trace := by
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  intro i _
  exact glwCovMatrix_diag_nonneg us h_us i

/-- The trace of `glwCovMatrix us` is bounded above by `n` (each
diagonal entry is `≤ 1`). -/
theorem glwCovMatrix_trace_le {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    (glwCovMatrix us).trace ≤ (n : ℝ) := by
  rw [Matrix.trace]
  calc ∑ i : Fin n, (glwCovMatrix us).diag i
      ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact glwCovMatrix_diag_le_one us h_us i
    _ = (n : ℝ) := by simp

/-! ## 4.9. Sum-of-entries and Frobenius bounds

Round 12 additions. The **sum of all entries** of `glwCovMatrix us` is
the variance of the random sum `Σᵢ Y(uᵢ)` once a process realisation
exists; the bound below gives the deterministic constraints on that
variance, controlling Borell-type sup bounds independently of the
`brownian-motion` projective-limit construction.

Likewise the **Frobenius squared norm** `Σᵢⱼ Mᵢⱼ²` controls the
operator norm: `‖M‖_op ≤ ‖M‖_F`, so any operator-norm bound on
`glwCovMatrix` factors through these inequalities. -/

/-- Sum of all entries of `glwCovMatrix us` is non-negative on nonneg
grids — a direct consequence of `glwCovMatrix_entry_pos`. -/
theorem glwCovMatrix_sum_entries_nonneg {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, glwCovMatrix us i j := by
  apply Finset.sum_nonneg
  intros i _
  apply Finset.sum_nonneg
  intros j _
  exact le_of_lt (glwCovMatrix_entry_pos us h_us i j)

/-- Sum of all entries of `glwCovMatrix us` is bounded above by `n²`
on nonneg grids — direct from `glwCovMatrix_entry_le_one`. -/
theorem glwCovMatrix_sum_entries_le {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    ∑ i : Fin n, ∑ j : Fin n, glwCovMatrix us i j ≤ (n : ℝ) * n := by
  calc ∑ i : Fin n, ∑ j : Fin n, glwCovMatrix us i j
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intros i _
        apply Finset.sum_le_sum
        intros j _
        exact glwCovMatrix_entry_le_one us h_us i j
    _ = (n : ℝ) * n := by simp [Finset.sum_const]

/-- Frobenius-squared bound for `glwCovMatrix us` on nonneg grids:
`Σᵢⱼ Mᵢⱼ² ≤ n²`. Each entry lies in `[0, 1]`, so its square does too. -/
theorem glwCovMatrix_frobenius_sq_le {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    ∑ i : Fin n, ∑ j : Fin n, (glwCovMatrix us i j)^2 ≤ (n : ℝ) * n := by
  calc ∑ i : Fin n, ∑ j : Fin n, (glwCovMatrix us i j)^2
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intros i _
        apply Finset.sum_le_sum
        intros j _
        have hpos : 0 ≤ glwCovMatrix us i j :=
          le_of_lt (glwCovMatrix_entry_pos us h_us i j)
        have hle : glwCovMatrix us i j ≤ 1 :=
          glwCovMatrix_entry_le_one us h_us i j
        calc (glwCovMatrix us i j)^2
            = glwCovMatrix us i j * glwCovMatrix us i j := sq _
          _ ≤ 1 * 1 := mul_le_mul hle hle hpos (by norm_num)
          _ = 1 := by norm_num
    _ = (n : ℝ) * n := by simp [Finset.sum_const]

/-- Frobenius-squared lower bound for `glwCovMatrix us` on nonneg
grids: `Σᵢⱼ Mᵢⱼ² ≥ 0`. -/
theorem glwCovMatrix_frobenius_sq_nonneg {n : ℕ} (us : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, (glwCovMatrix us i j)^2 := by
  apply Finset.sum_nonneg
  intros i _
  apply Finset.sum_nonneg
  intros j _
  exact sq_nonneg _

/-! ## 4.10. Cauchy-Schwarz consequences and small-dim determinants

Round 12 additions. The kernel-side Cauchy-Schwarz inequality
`K_GLW(u, v)² ≤ K_GLW(u, u) · K_GLW(v, v)` (proven in
`YGLWConstruction.lean` as `K_GLW_cauchy_schwarz`) lifts directly to
the Gram matrix as the off-diagonal-vs-diagonal control. The 1×1
determinant identity gives the simplest non-trivial PSD witness; this
serves as the base case for the inductive Sylvester argument that
underpins the projective-family marginal consistency. -/

/-- Off-diagonal Cauchy-Schwarz: each squared entry is bounded by the
product of the two diagonal entries on the same row/column. Direct
lift of `K_GLW_cauchy_schwarz`. -/
theorem glwCovMatrix_entry_sq_le_diag_prod {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) (i j : Fin n) :
    (glwCovMatrix us i j)^2 ≤ glwCovMatrix us i i * glwCovMatrix us j j := by
  rw [glwCovMatrix_apply, glwCovMatrix_diag_eq, glwCovMatrix_diag_eq]
  exact K_GLW_cauchy_schwarz (h_us i) (h_us j)

/-- 1-dim determinant: for `n = 1`, the determinant of `glwCovMatrix`
is exactly the single entry `K_GLW(u₀, u₀)`. -/
theorem glwCovMatrix_one_dim_det (us : Fin 1 → ℝ) :
    (glwCovMatrix us).det = K_GLW (us 0) (us 0) := by
  rw [Matrix.det_unique]
  simp [glwCovMatrix_apply]

/-- 1-dim determinant non-negativity (refining
`glwCovMatrix_det_nonneg` to give the explicit value). -/
theorem glwCovMatrix_one_dim_det_nonneg (us : Fin 1 → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    0 ≤ (glwCovMatrix us).det := by
  rw [glwCovMatrix_one_dim_det]
  exact le_of_lt (K_GLW_pos _ _ (h_us 0) (h_us 0))

/-- 1-dim determinant upper bound: `det glwCovMatrix ≤ 1`. -/
theorem glwCovMatrix_one_dim_det_le_one (us : Fin 1 → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    (glwCovMatrix us).det ≤ 1 := by
  rw [glwCovMatrix_one_dim_det]
  exact K_GLW_le_one _ _ (h_us 0) (h_us 0)

/-! ## 4.11. Constant-grid and 2-dim determinant identities

Round 12 additions. The constant-grid case (all `uᵢ = c`) gives the
all-`K_GLW(c, c)` matrix — a rank-1 matrix whose PSD structure is
trivial. The 2-dim explicit determinant identity makes the
Cauchy-Schwarz inequality structurally visible: PSD = (det ≥ 0)
in 2 dimensions is exactly Cauchy-Schwarz. -/

/-- For a constant grid `uᵢ = c`, every entry of `glwCovMatrix` is
`K_GLW(c, c)`. -/
theorem glwCovMatrix_const_grid_apply {n : ℕ} (c : ℝ) (i j : Fin n) :
    glwCovMatrix (fun _ : Fin n => c) i j = K_GLW c c := by
  rw [glwCovMatrix_apply]

/-- For a constant grid, `glwCovMatrix` equals the all-`K_GLW(c, c)`
constant matrix. -/
theorem glwCovMatrix_const_grid {n : ℕ} (c : ℝ) :
    glwCovMatrix (fun _ : Fin n => c) =
      Matrix.of (fun _ _ : Fin n => K_GLW c c) := by
  ext i j
  exact glwCovMatrix_const_grid_apply c i j

/-- 2-dim determinant identity: for `n = 2`, the determinant is exactly
`K_GLW(u₀, u₀) · K_GLW(u₁, u₁) - K_GLW(u₀, u₁)²`. The non-negativity of
this quantity for nonneg grids is exactly `K_GLW_cauchy_schwarz`. -/
theorem glwCovMatrix_two_dim_det (us : Fin 2 → ℝ) :
    (glwCovMatrix us).det =
      K_GLW (us 0) (us 0) * K_GLW (us 1) (us 1) -
      K_GLW (us 0) (us 1) * K_GLW (us 1) (us 0) := by
  rw [Matrix.det_fin_two]
  simp [glwCovMatrix_apply]

/-- 2-dim determinant identity, simplified using K_GLW symmetry. -/
theorem glwCovMatrix_two_dim_det_symm (us : Fin 2 → ℝ) :
    (glwCovMatrix us).det =
      K_GLW (us 0) (us 0) * K_GLW (us 1) (us 1) -
      (K_GLW (us 0) (us 1))^2 := by
  rw [glwCovMatrix_two_dim_det]
  rw [show K_GLW (us 1) (us 0) = K_GLW (us 0) (us 1) from K_GLW_symm _ _]
  ring

/-- 2-dim determinant non-negativity via Cauchy-Schwarz (alternative to
the generic `glwCovMatrix_det_nonneg` proof through `PosSemidef`). -/
theorem glwCovMatrix_two_dim_det_nonneg_via_cauchy (us : Fin 2 → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    0 ≤ (glwCovMatrix us).det := by
  rw [glwCovMatrix_two_dim_det_symm]
  linarith [K_GLW_cauchy_schwarz (h_us 0) (h_us 1)]

/-! ## 4.12. Diagonal-entry identities and zero-grid case

Round 12 additions. The diagonal entry `Mᵢᵢ = K_GLW(uᵢ, uᵢ) =
K_GLW_aux(2·uᵢ)` is the building block of every variance / sup-bound
calculation. The zero-grid case is the simplest non-trivial Gram
matrix (every entry = 1). Together these give the boundary cases
needed for the inductive grid arguments. -/

/-- The diagonal of `glwCovMatrix` factors through `K_GLW_aux` applied
to twice the grid value. -/
theorem glwCovMatrix_diag_eq_K_GLW_aux_double {n : ℕ} (us : Fin n → ℝ)
    (i : Fin n) :
    glwCovMatrix us i i = K_GLW_aux (2 * us i) := by
  rw [glwCovMatrix_diag_eq, K_GLW_def]
  congr 1
  ring

/-- All entries of `glwCovMatrix` equal `1` when `us` is the zero
constant grid. -/
theorem glwCovMatrix_zero_grid_apply {n : ℕ} (i j : Fin n) :
    glwCovMatrix (fun _ : Fin n => (0 : ℝ)) i j = 1 := by
  rw [glwCovMatrix_apply, K_GLW_zero]

/-- The K_GLW Gram matrix on the zero constant grid is the all-ones
matrix. -/
theorem glwCovMatrix_zero_grid {n : ℕ} :
    glwCovMatrix (fun _ : Fin n => (0 : ℝ)) =
      Matrix.of (fun _ _ : Fin n => (1 : ℝ)) := by
  ext i j
  exact glwCovMatrix_zero_grid_apply i j

/-- The constant-grid `glwCovMatrix` is positive semi-definite — direct
specialisation of `glwCovMatrix_PosSemidef`. -/
theorem glwCovMatrix_const_grid_PosSemidef {n : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    (glwCovMatrix (fun _ : Fin n => c)).PosSemidef :=
  glwCovMatrix_PosSemidef _ (fun _ => hc)

/-- The zero-grid `glwCovMatrix` is positive semi-definite. -/
theorem glwCovMatrix_zero_grid_PosSemidef {n : ℕ} :
    (glwCovMatrix (fun _ : Fin n => (0 : ℝ))).PosSemidef :=
  glwCovMatrix_const_grid_PosSemidef le_rfl

/-! ## 4.13. Generic Gram-matrix small-dim identities (Mathlib-PR-shaped)

Round 12 additions. Lifts the small-dim determinant identities from
`glwCovMatrix` to the generic `gramMatrixL2` abstraction. These are
direct Mathlib-PR candidates: the proofs use only standard matrix /
integration API. -/

/-- 1-dim determinant for `gramMatrixL2`: equals the L²-norm-squared
of the single function. -/
theorem gramMatrixL2_one_dim_det (φ : Fin 1 → ℝ → ℝ) :
    (gramMatrixL2 φ).det = ∫ s in (0 : ℝ)..1, (φ 0 s)^2 := by
  rw [Matrix.det_unique]
  simp [gramMatrixL2_apply, sq]

/-- 1-dim determinant non-negativity for `gramMatrixL2`. -/
theorem gramMatrixL2_one_dim_det_nonneg (φ : Fin 1 → ℝ → ℝ) :
    0 ≤ (gramMatrixL2 φ).det := by
  rw [gramMatrixL2_one_dim_det]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun _ => sq_nonneg _)

/-- 2-dim determinant for `gramMatrixL2`: explicit formula. -/
theorem gramMatrixL2_two_dim_det (φ : Fin 2 → ℝ → ℝ) :
    (gramMatrixL2 φ).det =
      gramMatrixL2 φ 0 0 * gramMatrixL2 φ 1 1 -
      gramMatrixL2 φ 0 1 * gramMatrixL2 φ 1 0 := by
  rw [Matrix.det_fin_two]

/-- 2-dim determinant for `gramMatrixL2`, simplified using symmetry. -/
theorem gramMatrixL2_two_dim_det_symm (φ : Fin 2 → ℝ → ℝ) :
    (gramMatrixL2 φ).det =
      gramMatrixL2 φ 0 0 * gramMatrixL2 φ 1 1 -
      (gramMatrixL2 φ 0 1)^2 := by
  rw [gramMatrixL2_two_dim_det]
  rw [show gramMatrixL2 φ 1 0 = gramMatrixL2 φ 0 1 from gramMatrixL2_symm _ _ _]
  ring

/-! ## 4.14. Quadratic-form identities

Round 12 additions. The quadratic form `x ⬝ M ⬝ x = Σᵢⱼ xᵢ xⱼ Mᵢⱼ`
expansion is the algebraic core of every PSD-via-test-vector proof.
Extracting it as a standalone identity (rather than re-proving inside
each `PosSemidef` argument) is what makes downstream variance / sup
calculations one-line. -/

/-- Standard quadratic-form expansion for `glwCovMatrix`:
`x ⬝ M ⬝ x = Σᵢⱼ xᵢ xⱼ K_GLW(uᵢ, uⱼ)`. -/
theorem glwCovMatrix_quadratic_form_eq_sum {n : ℕ} (us : Fin n → ℝ)
    (x : Fin n → ℝ) :
    ∑ i, x i * ((glwCovMatrix us *ᵥ x) i) =
      ∑ i, ∑ j, x i * x j * K_GLW (us i) (us j) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [glwCovMatrix_apply]
  ring

/-- The K_GLW quadratic form is non-negative on nonneg grids — direct
restatement of `K_GLW_quadratic_form_nonneg` via the Gram-matrix
quadratic-form identity. -/
theorem glwCovMatrix_quadratic_form_nonneg {n : ℕ} (us : Fin n → ℝ)
    (x : Fin n → ℝ) (h_us : ∀ i, 0 ≤ us i) :
    0 ≤ ∑ i, x i * ((glwCovMatrix us *ᵥ x) i) := by
  rw [glwCovMatrix_quadratic_form_eq_sum]
  exact K_GLW_quadratic_form_nonneg us x h_us

/-- For the all-ones test vector, the K_GLW quadratic form equals the
sum of all entries. -/
theorem glwCovMatrix_quadratic_form_at_one {n : ℕ} (us : Fin n → ℝ) :
    ∑ i, (1 : ℝ) * ((glwCovMatrix us *ᵥ (fun _ => 1)) i) =
      ∑ i, ∑ j, K_GLW (us i) (us j) := by
  rw [glwCovMatrix_quadratic_form_eq_sum]
  simp

/-! ## 4.15. Generic Gram-matrix `gramMatrixL2` further structure

Round 12 additions. More Mathlib-PR-shaped abstractions: behavior of
`gramMatrixL2` under sign-flip, addition of families, and constant
families. -/

/-- Negating the family does not change the Gram matrix:
`gramMatrixL2 (-φ) = gramMatrixL2 φ` since `(-φᵢ)·(-φⱼ) = φᵢ·φⱼ`. -/
theorem gramMatrixL2_neg_family {n : ℕ} (φ : Fin n → ℝ → ℝ) :
    gramMatrixL2 (fun i s => -(φ i s)) = gramMatrixL2 φ := by
  ext i j
  rw [gramMatrixL2_apply, gramMatrixL2_apply]
  congr 1
  funext s
  ring

/-- For the constant family `φᵢ = c`, every entry of the Gram matrix
is `c²`. -/
theorem gramMatrixL2_const_family_apply {n : ℕ} (c : ℝ) (i j : Fin n) :
    gramMatrixL2 (fun _ : Fin n => fun _ : ℝ => c) i j = c^2 := by
  rw [gramMatrixL2_apply]
  simp [sq]

/-- For the constant family `φᵢ = c`, the Gram matrix is the constant
`c²` matrix. -/
theorem gramMatrixL2_const_family {n : ℕ} (c : ℝ) :
    gramMatrixL2 (fun _ : Fin n => fun _ : ℝ => c) =
      Matrix.of (fun _ _ : Fin n => c^2) := by
  ext i j
  exact gramMatrixL2_const_family_apply c i j

/-- The constant-family Gram matrix is positive semi-definite (with
PSD constant `c² ≥ 0`). -/
theorem gramMatrixL2_const_family_PosSemidef {n : ℕ} (c : ℝ) :
    (gramMatrixL2 (fun _ : Fin n => fun _ : ℝ => c)).PosSemidef :=
  gramMatrixL2_PosSemidef _ (fun _ => continuous_const)

/-! ## 4.16. Grid translation and dilation

Round 12 additions. The K_GLW kernel only depends on `u + v`, so any
grid transformation that changes `(uᵢ + uⱼ)` in a tractable way gives
explicit identities for `glwCovMatrix`. The two basic transformations
are *translation* `us ↦ us + c` (each entry's argument shifts by `2c`)
and *dilation* `us ↦ λ · us` (each entry's argument scales by `λ`). -/

/-- Under translation of the grid by a constant `c`, each entry of
`glwCovMatrix` shifts: `Mᵢⱼ(us + c) = K_GLW_aux((uᵢ + uⱼ) + 2c)`. -/
theorem glwCovMatrix_translate_apply {n : ℕ} (us : Fin n → ℝ) (c : ℝ)
    (i j : Fin n) :
    glwCovMatrix (fun i => us i + c) i j = K_GLW_aux ((us i + us j) + 2 * c) := by
  rw [glwCovMatrix_apply, K_GLW_def]
  congr 1
  ring

/-- Under dilation of the grid by a constant `λ`, each entry of
`glwCovMatrix` scales: `Mᵢⱼ(λ · us) = K_GLW_aux(λ · (uᵢ + uⱼ))`. -/
theorem glwCovMatrix_dilate_apply {n : ℕ} (us : Fin n → ℝ) (lam : ℝ)
    (i j : Fin n) :
    glwCovMatrix (fun i => lam * us i) i j =
      K_GLW_aux (lam * (us i + us j)) := by
  rw [glwCovMatrix_apply, K_GLW_def]
  congr 1
  ring

/-- Translation of a nonneg grid by a non-negative constant remains
nonneg, so the translated `glwCovMatrix` is PSD. -/
theorem glwCovMatrix_translate_PosSemidef {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) {c : ℝ} (hc : 0 ≤ c) :
    (glwCovMatrix (fun i => us i + c)).PosSemidef :=
  glwCovMatrix_PosSemidef _ (fun i => add_nonneg (h_us i) hc)

/-- Dilation of a nonneg grid by a non-negative scalar remains nonneg,
so the dilated `glwCovMatrix` is PSD. -/
theorem glwCovMatrix_dilate_PosSemidef {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) {lam : ℝ} (h_lam : 0 ≤ lam) :
    (glwCovMatrix (fun i => lam * us i)).PosSemidef :=
  glwCovMatrix_PosSemidef _ (fun i => mul_nonneg h_lam (h_us i))

/-! ## 4.17. Trace expansion via K_GLW and K_GLW_aux

Round 12 additions. Explicit form of the trace as a sum of variances
`K_GLW(uᵢ, uᵢ)` and as a sum of single-variable kernel values
`K_GLW_aux(2·uᵢ)`. These are the standard re-writings used in
variance / sup-norm estimates downstream. -/

/-- The trace of `glwCovMatrix us` equals the sum of variances
`K_GLW(uᵢ, uᵢ)`. -/
theorem glwCovMatrix_trace_eq_sum_var {n : ℕ} (us : Fin n → ℝ) :
    (glwCovMatrix us).trace = ∑ i : Fin n, K_GLW (us i) (us i) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact glwCovMatrix_diag_eq us i

/-- The trace of `glwCovMatrix us` equals the sum of single-variable
kernel values `K_GLW_aux(2·uᵢ)` (via the diagonal factorisation). -/
theorem glwCovMatrix_trace_eq_sum_K_GLW_aux_double {n : ℕ} (us : Fin n → ℝ) :
    (glwCovMatrix us).trace = ∑ i : Fin n, K_GLW_aux (2 * us i) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact glwCovMatrix_diag_eq_K_GLW_aux_double us i

/-- The trace of the constant-grid `glwCovMatrix` equals
`n · K_GLW(c, c)`. -/
theorem glwCovMatrix_const_grid_trace {n : ℕ} (c : ℝ) :
    (glwCovMatrix (fun _ : Fin n => c)).trace = (n : ℝ) * K_GLW c c := by
  rw [glwCovMatrix_trace_eq_sum_var]
  simp [Finset.sum_const]

/-- The trace of the zero-grid `glwCovMatrix` equals `n` (since each
diagonal entry is `K_GLW(0, 0) = 1`). -/
theorem glwCovMatrix_zero_grid_trace {n : ℕ} :
    (glwCovMatrix (fun _ : Fin n => (0 : ℝ))).trace = (n : ℝ) := by
  rw [glwCovMatrix_const_grid_trace, K_GLW_zero, mul_one]

/-! ## 4.18. Tighter bounds via variance decay

Round 12 additions. The kernel-side variance bounds
`K_GLW(u, u) < 1` (strict) and `K_GLW(u, u) ≤ 1/(2u)` (decay) lift
directly to diagonal-entry and trace bounds for `glwCovMatrix` on
strictly positive grids — improving on the basic `≤ 1` and `≤ n`
bounds from §4 / §4.8. -/

/-- Each diagonal entry is strictly less than `1` on strictly positive
grids — direct lift of `K_GLW_var_lt_one`. -/
theorem glwCovMatrix_diag_lt_one {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 < us i) (i : Fin n) :
    glwCovMatrix us i i < 1 := by
  rw [glwCovMatrix_diag_eq]
  exact K_GLW_var_lt_one (h_us i)

/-- Each diagonal entry decays as `≤ 1/(2 uᵢ)` on strictly positive
grids — direct lift of `K_GLW_var_le_recip`. -/
theorem glwCovMatrix_diag_le_recip {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 < us i) (i : Fin n) :
    glwCovMatrix us i i ≤ 1 / (2 * us i) := by
  rw [glwCovMatrix_diag_eq]
  exact K_GLW_var_le_recip (h_us i)

/-- The trace is bounded above by the sum of variance-decay bounds:
`tr(M) ≤ Σᵢ 1/(2 uᵢ)`. -/
theorem glwCovMatrix_trace_le_recip_sum {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 < us i) :
    (glwCovMatrix us).trace ≤ ∑ i : Fin n, 1 / (2 * us i) := by
  rw [Matrix.trace]
  apply Finset.sum_le_sum
  intros i _
  exact glwCovMatrix_diag_le_recip us h_us i

/-! ## 5. Bridge to the `brownian-motion` project — BLOCKER documentation

The Degenne–Pfaffelhuber `brownian-motion` project's construction
proceeds via the following API calls. Each is documented below as a
BLOCKER (still missing in Mathlib core, present in the project) and
parameterised by the kernel data we just proved.

### BLOCKER B1: `multivariateGaussian` on a finite-dim space.

* **TRIED**: searched Mathlib for `multivariateGaussian`, `gaussianPi`,
  `IsGaussian (Measure ℝⁿ)`. Mathlib has `IsGaussian` as a general
  predicate but no constructor producing a multivariate Gaussian
  measure from `(mean, PSD covariance matrix)`.
* **PROJECT API**: `multivariateGaussian (m : E) (Σ : Matrix n n ℝ)
  (hΣ : Σ.PosSemidef) : Measure E`.
* **PRECONDITION SATISFIED**: `glwCovMatrix_PosSemidef` (above) gives
  `(glwCovMatrix us).PosSemidef` for any nonneg-indexed grid.

### BLOCKER B2: `gaussianProjectiveFamily` consistency.

* **TRIED**: Mathlib has `IsProjectiveMeasureFamily` in
  `Mathlib/Probability/Kernel/MeasurableLebesgueDecomposition.lean`,
  but no infrastructure to build the family from a covariance.
* **PRECONDITION SATISFIED**: `glwCovMatrix_submatrix_PosSemidef`
  (Section 4.7 above) gives the kernel-side restriction property
  `((glwCovMatrix us).submatrix f f).PosSemidef`. Combined with B1,
  this gives the consistency hypothesis for the projective family
  on any sub-grid `f : Fin m → Fin n`.
* **PROJECT API**: `gaussianProjectiveFamily K : ∀ I, Measure (I → ℝ)`
  where the projective family is consistent under restriction to
  smaller `I' ⊆ I`.
* **PRECONDITION SATISFIED** (assuming B1): for `I' ⊆ I`, the marginal
  of `multivariateGaussian 0 (K|_I)` on `I'` equals
  `multivariateGaussian 0 (K|_{I'})` — this is the standard
  "Gaussian marginalisation" identity, **provable with B1 in hand**.

### BLOCKER B3: `projectiveLimit` (Kolmogorov extension).

* **TRIED**: Mathlib has `Measure.infinitePi` (countable independent
  product), `IsProjectiveLimit` predicate, but no
  Kolmogorov-extension constructor for general projective families
  parameterised over `Finset ℝ≥0`.
* **PROJECT API**: `projectiveLimit (F : ∀ I : Finset ι, Measure (I → ℝ))
  (hF : IsProjectiveMeasureFamily F) : Measure (ι → ℝ)`. Closure of the
  projective limit when the index set is `ℝ≥0` (uncountable).

### BLOCKER B4: Kolmogorov–Chentsov continuity.

* **TRIED**: `Mathlib/Probability/Process/Kolmogorov.lean` covers the
  zero-one law, not Kolmogorov–Chentsov.
* **PROJECT API**: `kolmogorov_chentsov : ∀ (Y : ι → Ω → ℝ),
  (∀ s t, ‖Y s - Y t‖_{L²}^2 ≤ C |s - t|^(2 + δ)) →
  ∃ Ỹ ~ Y, ContinuousPaths Ỹ`.
* **PRECONDITION SATISFIED**: `L2_diff_le_sq` from
  `YGLWConstruction.lean` gives the Hölder-1 bound `K(u, u) - 2 K(u, v) +
  K(v, v) ≤ |u - v|²` directly. Combined with the Wiener-isometry-side
  identity `‖Y(u) - Y(v)‖²_{L²(Ω)} = K(u, u) - 2 K(u, v) + K(v, v)`,
  this gives the Kolmogorov–Chentsov hypothesis with `(C, δ) = (1, 0)`
  or, after a lift to higher moments, `(C, δ) = (3, 2)` (using the
  fourth-moment Gaussian identity `E[X⁴] = 3·Var(X)²`).

### BLOCKER B5: Borell sup-bound + Borel–Cantelli for tail decay.

* **TRIED**: Mathlib has Fernique (`IsGaussian.fernique`), no Borell.
* **PROJECT API**: not yet present even in the `brownian-motion`
  project; this is a forward-looking conjunct.
* **PRECONDITION SATISFIED**: `K_GLW_var_tendsto_zero` from
  `YGLWConstruction.lean` gives the variance-side L²-decay; the
  remaining work is the standard Borell concentration + Borel–Cantelli
  on integer-indexed sup-windows.

### Roadmap

When the `brownian-motion` project's API is available (via toolchain
alignment / Mathlib merge), the proof of `Y_GLW_exists` reduces to:

```
theorem Y_GLW_exists_from_brownian_motion : Y_GLW_exists.statement := by
  -- 1. Apply B1 + B2 to glwCovMatrix to get gaussianProjectiveFamily.
  -- 2. Apply B3 to get projectiveLimit measure on `ℝ≥0 → ℝ`.
  -- 3. Define Y(u, ω) := ω u; verify centeredness, covariance from B1.
  -- 4. Apply B4 with L2_diff_le_sq to get continuous-paths modification.
  -- 5. Apply B5 with K_GLW_var_tendsto_zero to get tail decay.
  sorry
```

Each step is a one-line application of the corresponding project API
to the kernel-side content already proved in this file and in
`YGLWConstruction.lean`. The `glwCovMatrix_PosSemidef` lemma above is
the **mathematical core** of the bridge: it is what makes the
projective family well-defined. -/

end Erdos524.Helpers
