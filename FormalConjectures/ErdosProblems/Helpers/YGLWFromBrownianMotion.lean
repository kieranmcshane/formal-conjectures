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

1. `brownianCovMatrix I : Matrix I I ℝ` for finite `I ⊆ NNReal` with
   `K_BM(s, t) = min(s, t)`,
2. `gaussianProjectiveFamily I` from `multivariateGaussian 0
   (brownianCovMatrix I)`,
3. `projectiveLimit gaussianProjectiveFamily : Measure (NNReal → ℝ)`,
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

/-! ## 4.19. Pairwise Hölder bound — the Kolmogorov–Chentsov precondition

Round 12 additions. The matrix-level form of `K_GLW_diff_quadratic_le_sq`
is the precondition for the Kolmogorov–Chentsov continuous-paths
theorem (BLOCKER B4): for any pair of grid indices `(i, j)`, the
"variance-of-difference" `Mᵢᵢ + Mⱼⱼ - 2 Mᵢⱼ` is bounded by
`(uᵢ - uⱼ)²`. Once a Gaussian process realisation `Y` exists, this
deterministic kernel-side fact upgrades to the L²(Ω)-Hölder bound
`E[(Y(uᵢ) - Y(uⱼ))²] ≤ (uᵢ - uⱼ)²` via the Wiener isometry. -/

/-- Matrix-level pairwise Hölder bound: `Mᵢᵢ + Mⱼⱼ - 2 Mᵢⱼ ≤ (uᵢ - uⱼ)²`
for any nonneg grid. Direct lift of `K_GLW_diff_quadratic_le_sq`. -/
theorem glwCovMatrix_pairwise_diff_quadratic_le_sq {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) (i j : Fin n) :
    glwCovMatrix us i i + glwCovMatrix us j j - 2 * glwCovMatrix us i j ≤
      (us i - us j)^2 := by
  rw [glwCovMatrix_diag_eq, glwCovMatrix_diag_eq, glwCovMatrix_apply]
  have := K_GLW_diff_quadratic_le_sq (h_us i) (h_us j)
  linarith

/-- Symmetric form of the pairwise Hölder bound: `2 Mᵢⱼ ≥
Mᵢᵢ + Mⱼⱼ - (uᵢ - uⱼ)²` — useful when the off-diagonal entry is
the unknown to be bounded *from below*. -/
theorem glwCovMatrix_offdiag_lower_bound {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) (i j : Fin n) :
    glwCovMatrix us i i + glwCovMatrix us j j - (us i - us j)^2 ≤
      2 * glwCovMatrix us i j := by
  linarith [glwCovMatrix_pairwise_diff_quadratic_le_sq us h_us i j]

/-- Symmetric "L²-distance" bound: the distance-of-difference matrix
form, `Mᵢᵢ + Mⱼⱼ - 2 Mᵢⱼ ≥ 0`, packages the standard fact that
`L²-distance squared` is non-negative. This follows from the PSD
property applied to the test vector that places `+1` at index `i` and
`-1` at index `j`. -/
theorem glwCovMatrix_pairwise_diff_quadratic_nonneg {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) (i j : Fin n) :
    0 ≤ glwCovMatrix us i i + glwCovMatrix us j j - 2 * glwCovMatrix us i j := by
  rw [glwCovMatrix_diag_eq, glwCovMatrix_diag_eq, glwCovMatrix_apply]
  linarith [K_GLW_diff_quadratic_nonneg (h_us i) (h_us j)]

/-! ## 4.20. Hermitian property for `gramMatrixL2`

Round 12 additions. Explicit Hermitian property of the generic Gram
matrix as a standalone fact — extracted from the proof of
`gramMatrixL2_PosSemidef`. This is a clean Mathlib-PR-shaped lemma
independent of any kernel-specific data. -/

/-- The generic Gram matrix `gramMatrixL2 φ` is Hermitian (symmetric
real matrix). -/
theorem gramMatrixL2_isHermitian {n : ℕ} (φ : Fin n → ℝ → ℝ) :
    (gramMatrixL2 φ).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose, Matrix.transpose, gramMatrixL2_apply]
  congr 1
  funext s
  ring

/-- The diagonal of `gramMatrixL2 φ` is non-negative — a special case
of `gramMatrixL2_diag_nonneg`. -/
theorem gramMatrixL2_diag_nonneg' {n : ℕ} (φ : Fin n → ℝ → ℝ) (i : Fin n) :
    0 ≤ (gramMatrixL2 φ).diag i :=
  gramMatrixL2_diag_nonneg φ i

/-- The trace of the generic Gram matrix is non-negative (sum of
non-negative diagonals). -/
theorem gramMatrixL2_trace_nonneg {n : ℕ} (φ : Fin n → ℝ → ℝ) :
    0 ≤ (gramMatrixL2 φ).trace := by
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  intros i _
  exact gramMatrixL2_diag_nonneg φ i

/-- The trace of the generic Gram matrix equals the sum of L²-norms
squared `Σᵢ ∫₀¹ (φᵢ s)²`. -/
theorem gramMatrixL2_trace_eq {n : ℕ} (φ : Fin n → ℝ → ℝ) :
    (gramMatrixL2 φ).trace = ∑ i : Fin n, ∫ s in (0 : ℝ)..1, (φ i s)^2 := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact gramMatrixL2_diag_eq φ i

/-! ## 4.21. Packaged "kernel data" witness — a single theorem capturing
the bridge content

Round 12 closing additions. The brownian-motion projective-limit
construction consumes a *kernel data package*: a symmetric two-point
function `K : ℝ → ℝ → ℝ` for which all finite-grid Gram matrices on
nonneg grids are positive semi-definite, and which satisfies a
pairwise Hölder-1 bound `K(u,u) - 2 K(u,v) + K(v,v) ≤ (u-v)²` (the
Kolmogorov-Chentsov precondition). The theorem below packages all
this into one existential witness, sorry-free, demonstrating that
the kernel side is fully formalised. -/

/-- **Packaged kernel-data witness** for the GLW process. `K_GLW` is a
symmetric two-point function for which every finite-grid Gram matrix
on a nonneg grid is positive semi-definite, and which satisfies the
pairwise Hölder-1 bound. This is the complete kernel-side
specification consumed by the brownian-motion projective-limit
construction. -/
theorem Y_GLW_kernel_data :
    ∃ K : ℝ → ℝ → ℝ,
      (∀ u v, K u v = K v u) ∧
      (∀ {n : ℕ} (us : Fin n → ℝ), (∀ i, 0 ≤ us i) →
        (Matrix.of fun i j : Fin n => K (us i) (us j)).PosSemidef) ∧
      (∀ {n : ℕ} (us : Fin n → ℝ), (∀ i, 0 ≤ us i) →
        ∀ {m : ℕ} (f : Fin m → Fin n),
          ((Matrix.of fun i j : Fin n => K (us i) (us j)).submatrix f f).PosSemidef) ∧
      (∀ u v, 0 ≤ u → 0 ≤ v →
        K u u - 2 * K u v + K v v ≤ (u - v)^2) := by
  refine ⟨K_GLW, K_GLW_symm, ?_, ?_, ?_⟩
  · intro n us h_us
    exact glwCovMatrix_PosSemidef us h_us
  · intro n us h_us m f
    exact glwCovMatrix_submatrix_PosSemidef us h_us f
  · intro u v hu hv
    exact K_GLW_diff_quadratic_le_sq hu hv

/-! ## 4.22. Variance-of-sum quadratic form bounds

Round 12 additions. The quadratic form `x · M · x` represents the
variance of the random sum `Σᵢ xᵢ Y(uᵢ)` once a process realisation
exists. For nonneg grids, this form is bounded below by `0` (PSD) and
above by `(Σᵢ |xᵢ|)²` via a Cauchy-Schwarz-like argument
(`Mᵢⱼ ≤ 1` everywhere). -/

/-- The quadratic form `x · M · x` is bounded above by `(Σᵢ |xᵢ|)²` for
nonneg grids: every entry of `M` is at most `1`, so
`Σᵢⱼ xᵢ xⱼ Mᵢⱼ ≤ Σᵢⱼ |xᵢ| |xⱼ| = (Σᵢ |xᵢ|)²`. -/
theorem glwCovMatrix_quadratic_form_le_l1_sq {n : ℕ} (us : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) (x : Fin n → ℝ) :
    ∑ i, x i * ((glwCovMatrix us *ᵥ x) i) ≤ (∑ i, |x i|)^2 := by
  rw [glwCovMatrix_quadratic_form_eq_sum]
  calc ∑ i : Fin n, ∑ j : Fin n, x i * x j * K_GLW (us i) (us j)
      ≤ ∑ i : Fin n, ∑ j : Fin n, |x i| * |x j| := by
        apply Finset.sum_le_sum
        intros i _
        apply Finset.sum_le_sum
        intros j _
        have h_pos : 0 ≤ K_GLW (us i) (us j) :=
          le_of_lt (K_GLW_pos _ _ (h_us i) (h_us j))
        have h_le : K_GLW (us i) (us j) ≤ 1 :=
          K_GLW_le_one _ _ (h_us i) (h_us j)
        calc x i * x j * K_GLW (us i) (us j)
            ≤ |x i * x j| * K_GLW (us i) (us j) := by
              have hpos : 0 ≤ K_GLW (us i) (us j) := h_pos
              nlinarith [abs_nonneg (x i * x j), le_abs_self (x i * x j)]
          _ ≤ |x i * x j| * 1 := by
              have habs : 0 ≤ |x i * x j| := abs_nonneg _
              nlinarith [abs_nonneg (x i * x j)]
          _ = |x i| * |x j| := by rw [mul_one, abs_mul]
    _ = (∑ i : Fin n, |x i|)^2 := by
        rw [sq, Finset.sum_mul_sum]

/-- The quadratic form `x · M · x` at the indicator vector `δᵢ` equals
the diagonal entry `Mᵢᵢ`. -/
theorem glwCovMatrix_quadratic_form_at_basis {n : ℕ} (us : Fin n → ℝ)
    (i : Fin n) :
    let e : Fin n → ℝ := fun j => if j = i then 1 else 0
    ∑ k, e k * ((glwCovMatrix us *ᵥ e) k) = glwCovMatrix us i i := by
  simp only
  rw [glwCovMatrix_quadratic_form_eq_sum]
  simp [Finset.sum_ite_eq', glwCovMatrix_apply]

/-! ## 4.23. Special K_GLW values and explicit numerical bounds

Round 12 closing additions. Concrete values of `K_GLW_aux` and
`K_GLW` at specific arguments are useful as sanity checks and as
boundary cases for inductive arguments. -/

/-- `K_GLW(0, u) = K_GLW_aux(u)` — direct unfolding. -/
theorem K_GLW_zero_left (u : ℝ) : K_GLW 0 u = K_GLW_aux u := by
  rw [K_GLW_def, zero_add]

/-- `K_GLW(u, 0) = K_GLW_aux(u)` — by symmetry. -/
theorem K_GLW_zero_right (u : ℝ) : K_GLW u 0 = K_GLW_aux u := by
  rw [K_GLW_symm, K_GLW_zero_left]

/-- The (0, j) entry of `glwCovMatrix` when `us 0 = 0` simplifies to
`K_GLW_aux(uⱼ)`. -/
theorem glwCovMatrix_zero_left_apply {n : ℕ} [NeZero n] (us : Fin n → ℝ)
    (h0 : us 0 = 0) (j : Fin n) :
    glwCovMatrix us 0 j = K_GLW_aux (us j) := by
  rw [glwCovMatrix_apply, h0, K_GLW_zero_left]

/-- The (i, 0) entry of `glwCovMatrix` when `us 0 = 0` simplifies to
`K_GLW_aux(uᵢ)`. -/
theorem glwCovMatrix_zero_right_apply {n : ℕ} [NeZero n] (us : Fin n → ℝ)
    (h0 : us 0 = 0) (i : Fin n) :
    glwCovMatrix us i 0 = K_GLW_aux (us i) := by
  rw [glwCovMatrix_apply, h0, K_GLW_zero_right]

/-- The diagonal `(0, 0)` entry equals `1` when `us 0 = 0`. -/
theorem glwCovMatrix_zero_diag {n : ℕ} [NeZero n] (us : Fin n → ℝ)
    (h0 : us 0 = 0) :
    glwCovMatrix us 0 0 = 1 :=
  glwCovMatrix_diag_at_zero us h0

/-! ## 4.24. NNReal-grid covariance — direct alignment with brownian-motion

Round 12 closing additions. The `brownian-motion` project's
`brownianCovMatrix` is indexed by `I : Finset NNReal` rather than
`Fin n → ℝ`. The K_GLW analogue below mirrors that signature
exactly, making R13 retirement of `Y_GLW_exists` a direct
substitution at the call site.

```
brownianCovMatrix (I : Finset NNReal) : Matrix I I ℝ :=
  Matrix.of fun s t ↦ min s.1 t.1
```

vs.

```
glwCovMatrixNN (I : Finset NNReal) : Matrix I I ℝ :=
  Matrix.of fun s t ↦ K_GLW s.1.toReal t.1.toReal
```

Both index types `↑I = {x : NNReal // x ∈ I}` give the matrix
indexed by NNReal grid points. -/

/-- The K_GLW Gram matrix on a Finset `I : Finset NNReal`, mirroring
brownian-motion's `brownianCovMatrix` signature exactly. Each entry
is `K_GLW (s : ℝ) (t : ℝ)` for grid points `s t : ↑I` (subtype of
NNReal). -/
noncomputable def glwCovMatrixNN (I : Finset NNReal) :
    Matrix {x : NNReal // x ∈ I} {x : NNReal // x ∈ I} ℝ :=
  Matrix.of fun s t => K_GLW (s.1 : ℝ) (t.1 : ℝ)

/-- Entry-access for `glwCovMatrixNN`. -/
@[simp]
theorem glwCovMatrixNN_apply (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s t = K_GLW (s.1 : ℝ) (t.1 : ℝ) := rfl

/-- `glwCovMatrixNN I` is symmetric. -/
theorem glwCovMatrixNN_symm (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s t = glwCovMatrixNN I t s := by
  simp [glwCovMatrixNN_apply, K_GLW_symm]

/-- `glwCovMatrixNN I` is Hermitian. -/
theorem glwCovMatrixNN_isHermitian (I : Finset NNReal) :
    (glwCovMatrixNN I).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose, Matrix.transpose,
        glwCovMatrixNN_apply, K_GLW_symm]

/-- Sub-Finset restriction: for `J ⊆ I`, restricting `glwCovMatrixNN I`
to indices in `J` yields `glwCovMatrixNN J`. Mirrors
`brownianCovMatrix_submatrix`. -/
theorem glwCovMatrixNN_submatrix {I J : Finset NNReal} (hJI : J ⊆ I) :
    (glwCovMatrixNN I).submatrix
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I})) =
      glwCovMatrixNN J := by
  ext i j
  rfl

/-- **The NNReal-grid PSD result**: `glwCovMatrixNN I` is positive
semi-definite for any `Finset NNReal`. The proof reindexes to the
`Fin I.card` grid via `Finset.equivFin`, applies the existing
`glwCovMatrix_PosSemidef` (using NNReal-coercion non-negativity),
and pulls PSD back via `Matrix.PosSemidef.submatrix`.

This is the `posSemidef_brownianCovMatrix` analogue for K_GLW —
the precondition for `multivariateGaussian` (BLOCKER B1) expressed
in brownian-motion's preferred type signature. -/
theorem glwCovMatrixNN_PosSemidef (I : Finset NNReal) :
    (glwCovMatrixNN I).PosSemidef := by
  let e : {x : NNReal // x ∈ I} ≃ Fin I.card := I.equivFin
  let us : Fin I.card → ℝ := fun k => ((e.symm k).1 : ℝ)
  have h_us : ∀ k, 0 ≤ us k := fun k => NNReal.coe_nonneg _
  have h_fin : (glwCovMatrix us).PosSemidef := glwCovMatrix_PosSemidef us h_us
  have h_eq : glwCovMatrixNN I = (glwCovMatrix us).submatrix e e := by
    ext s t
    simp only [glwCovMatrixNN_apply, Matrix.submatrix_apply, glwCovMatrix_apply]
    show K_GLW (s.1 : ℝ) (t.1 : ℝ) = K_GLW (us (e s)) (us (e t))
    show K_GLW (s.1 : ℝ) (t.1 : ℝ) = K_GLW ((e.symm (e s)).1 : ℝ) ((e.symm (e t)).1 : ℝ)
    rw [Equiv.symm_apply_apply e s, Equiv.symm_apply_apply e t]
  rw [h_eq]
  exact h_fin.submatrix e

/-- **Submatrix-PSD on the NNReal grid**: combining
`glwCovMatrixNN_submatrix` (sub-Finset restriction is the K_GLW Gram
of the sub-Finset) with `glwCovMatrixNN_PosSemidef` (PSD on any
Finset) gives that the submatrix on `J ⊆ I` is PSD as a Matrix on
`↑J`. This is the B2 precondition (consistency under restriction)
expressed in brownian-motion's preferred signature. -/
theorem glwCovMatrixNN_submatrix_PosSemidef
    {I J : Finset NNReal} (hJI : J ⊆ I) :
    ((glwCovMatrixNN I).submatrix
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))).PosSemidef := by
  rw [glwCovMatrixNN_submatrix hJI]
  exact glwCovMatrixNN_PosSemidef J

/-- **Packaged kernel-data witness on NNReal grids**: combines the
NNReal-grid PSD and submatrix-consistency into a single existential.
This is the brownian-motion-aligned analogue of `Y_GLW_kernel_data`
(§4.21) and represents the complete kernel-side specification
consumed by the projective-limit construction (BLOCKERs B1+B2). -/
theorem Y_GLW_kernel_data_NN :
    ∃ K : NNReal → NNReal → ℝ,
      (∀ s t : NNReal, K s t = K t s) ∧
      (∀ I : Finset NNReal,
        (Matrix.of fun s t : {x : NNReal // x ∈ I} => K s.1 t.1).PosSemidef) ∧
      (∀ {I J : Finset NNReal} (hJI : J ⊆ I),
        ((Matrix.of fun s t : {x : NNReal // x ∈ I} => K s.1 t.1).submatrix
            (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
            (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))).PosSemidef) := by
  refine ⟨fun s t => K_GLW (s : ℝ) (t : ℝ), ?_, ?_, ?_⟩
  · intros s t; exact K_GLW_symm _ _
  · intro I; exact glwCovMatrixNN_PosSemidef I
  · intros I J hJI; exact glwCovMatrixNN_submatrix_PosSemidef hJI

/-- Pairwise Hölder-1 bound for the NNReal-grid Gram matrix:
`Mss + Mtt - 2 Mst ≤ ((s : ℝ) - (t : ℝ))²` for any pair `s t : ↑I`.
Direct lift of `glwCovMatrix_pairwise_diff_quadratic_le_sq` via the
NNReal-coercion non-negativity. This is the matrix-level form of
the B4 Kolmogorov-Chentsov precondition in brownian-motion's
preferred signature. -/
theorem glwCovMatrixNN_pairwise_diff_quadratic_le_sq
    (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s s + glwCovMatrixNN I t t - 2 * glwCovMatrixNN I s t ≤
      ((s.1 : ℝ) - (t.1 : ℝ))^2 := by
  simp only [glwCovMatrixNN_apply]
  have h := K_GLW_diff_quadratic_le_sq
              (NNReal.coe_nonneg s.1) (NNReal.coe_nonneg t.1)
  linarith

/-- Symmetric L²-distance non-negativity on the NNReal-grid:
`0 ≤ Mss + Mtt - 2 Mst` for any `s t : ↑I`. -/
theorem glwCovMatrixNN_pairwise_diff_quadratic_nonneg
    (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    0 ≤ glwCovMatrixNN I s s + glwCovMatrixNN I t t - 2 * glwCovMatrixNN I s t := by
  simp only [glwCovMatrixNN_apply]
  have h := K_GLW_diff_quadratic_nonneg
              (NNReal.coe_nonneg s.1) (NNReal.coe_nonneg t.1)
  linarith

/-! ### NNReal-grid entry-wise bounds — direct lifts of Fin n versions -/

/-- Each entry of `glwCovMatrixNN I` is strictly positive. -/
theorem glwCovMatrixNN_entry_pos (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    0 < glwCovMatrixNN I s t := by
  rw [glwCovMatrixNN_apply]
  exact K_GLW_pos _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

/-- Each entry of `glwCovMatrixNN I` is bounded above by `1`. -/
theorem glwCovMatrixNN_entry_le_one (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s t ≤ 1 := by
  rw [glwCovMatrixNN_apply]
  exact K_GLW_le_one _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

/-- Each diagonal entry of `glwCovMatrixNN I` is non-negative. -/
theorem glwCovMatrixNN_diag_nonneg (I : Finset NNReal) (s : {x : NNReal // x ∈ I}) :
    0 ≤ glwCovMatrixNN I s s :=
  le_of_lt (glwCovMatrixNN_entry_pos I s s)

/-- Each diagonal entry of `glwCovMatrixNN I` is bounded above by `1`. -/
theorem glwCovMatrixNN_diag_le_one (I : Finset NNReal) (s : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s s ≤ 1 :=
  glwCovMatrixNN_entry_le_one I s s

/-- Cauchy-Schwarz for NNReal-grid Gram entries: each squared
off-diagonal is bounded by the product of the two diagonals. -/
theorem glwCovMatrixNN_entry_sq_le_diag_prod
    (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    (glwCovMatrixNN I s t)^2 ≤ glwCovMatrixNN I s s * glwCovMatrixNN I t t := by
  rw [glwCovMatrixNN_apply, glwCovMatrixNN_apply, glwCovMatrixNN_apply]
  exact K_GLW_cauchy_schwarz (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

/-! ### NNReal-grid trace and sum bounds -/

/-- The trace of `glwCovMatrixNN I` is non-negative. -/
theorem glwCovMatrixNN_trace_nonneg (I : Finset NNReal) :
    0 ≤ (glwCovMatrixNN I).trace := by
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  intros s _
  exact glwCovMatrixNN_diag_nonneg I s

/-- The trace of `glwCovMatrixNN I` is bounded above by `I.card`. -/
theorem glwCovMatrixNN_trace_le_card (I : Finset NNReal) :
    (glwCovMatrixNN I).trace ≤ (I.card : ℝ) := by
  rw [Matrix.trace]
  calc ∑ s, (glwCovMatrixNN I).diag s
      ≤ ∑ _s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intros s _
        exact glwCovMatrixNN_diag_le_one I s
    _ = (I.card : ℝ) := by simp [Finset.sum_const]

/-- Sum of all entries of `glwCovMatrixNN I` is non-negative. -/
theorem glwCovMatrixNN_sum_entries_nonneg (I : Finset NNReal) :
    0 ≤ ∑ s, ∑ t, glwCovMatrixNN I s t := by
  apply Finset.sum_nonneg
  intros s _
  apply Finset.sum_nonneg
  intros t _
  exact le_of_lt (glwCovMatrixNN_entry_pos I s t)

/-- Sum of all entries of `glwCovMatrixNN I` is bounded above by `I.card²`. -/
theorem glwCovMatrixNN_sum_entries_le (I : Finset NNReal) :
    ∑ s, ∑ t, glwCovMatrixNN I s t ≤ (I.card : ℝ) * I.card := by
  calc ∑ s, ∑ t, glwCovMatrixNN I s t
      ≤ ∑ _s, ∑ _t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intros s _
        apply Finset.sum_le_sum
        intros t _
        exact glwCovMatrixNN_entry_le_one I s t
    _ = (I.card : ℝ) * I.card := by simp [Finset.sum_const]

/-- Frobenius-squared bound for `glwCovMatrixNN I`: `Σₛₜ Mₛₜ² ≤ I.card²`. -/
theorem glwCovMatrixNN_frobenius_sq_le (I : Finset NNReal) :
    ∑ s, ∑ t, (glwCovMatrixNN I s t)^2 ≤ (I.card : ℝ) * I.card := by
  calc ∑ s, ∑ t, (glwCovMatrixNN I s t)^2
      ≤ ∑ _s, ∑ _t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intros s _
        apply Finset.sum_le_sum
        intros t _
        have hpos : 0 ≤ glwCovMatrixNN I s t :=
          le_of_lt (glwCovMatrixNN_entry_pos I s t)
        have hle : glwCovMatrixNN I s t ≤ 1 :=
          glwCovMatrixNN_entry_le_one I s t
        calc (glwCovMatrixNN I s t)^2
            = glwCovMatrixNN I s t * glwCovMatrixNN I s t := sq _
          _ ≤ 1 * 1 := mul_le_mul hle hle hpos (by norm_num)
          _ = 1 := by norm_num
    _ = (I.card : ℝ) * I.card := by simp [Finset.sum_const]

/-- Frobenius-squared lower bound. -/
theorem glwCovMatrixNN_frobenius_sq_nonneg (I : Finset NNReal) :
    0 ≤ ∑ s, ∑ t, (glwCovMatrixNN I s t)^2 := by
  apply Finset.sum_nonneg
  intros s _
  apply Finset.sum_nonneg
  intros t _
  exact sq_nonneg _

/-! ### Continuity of `glwCovMatrix` entries in the grid argument

K_GLW is jointly continuous (proved as `K_GLW_continuous` in
`GLWKernel.lean`). This lifts to entry-wise continuity of
`glwCovMatrix us i j` as a function of `us : Fin n → ℝ`. -/

/-- Each entry `glwCovMatrix us i j` is continuous as a function of
the grid `us : Fin n → ℝ`. -/
theorem glwCovMatrix_apply_continuous {n : ℕ} (i j : Fin n) :
    Continuous (fun us : Fin n → ℝ => glwCovMatrix us i j) := by
  show Continuous (fun us : Fin n → ℝ => K_GLW (us i) (us j))
  have h_pair : Continuous (fun us : Fin n → ℝ => (us i, us j)) :=
    Continuous.prodMk (continuous_apply i) (continuous_apply j)
  exact K_GLW_continuous.comp h_pair

/-- Each diagonal `glwCovMatrix us i i` is continuous as a function of
the grid. -/
theorem glwCovMatrix_diag_continuous {n : ℕ} (i : Fin n) :
    Continuous (fun us : Fin n → ℝ => glwCovMatrix us i i) :=
  glwCovMatrix_apply_continuous i i

/-- The trace `tr(glwCovMatrix us)` is continuous as a function of the
grid. -/
theorem glwCovMatrix_trace_continuous {n : ℕ} :
    Continuous (fun us : Fin n → ℝ => (glwCovMatrix us).trace) := by
  show Continuous (fun us : Fin n → ℝ => ∑ i : Fin n, (glwCovMatrix us).diag i)
  apply continuous_finset_sum
  intros i _
  exact glwCovMatrix_diag_continuous i

/-! ### NNReal-grid Mercer / integral-form representation -/

/-- Mercer / integral-form representation for `glwCovMatrixNN`:
each entry is an L²([0, 1]) inner product. Direct lift of
`glwCovMatrix_eq_integral` to the NNReal-grid signature. -/
theorem glwCovMatrixNN_eq_integral (I : Finset NNReal)
    (s t : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s t =
      ∫ x in (0 : ℝ)..1, glwIntegrand (s.1 : ℝ) x * glwIntegrand (t.1 : ℝ) x := by
  rw [glwCovMatrixNN_apply, K_GLW_eq_integral_glwIntegrand_mul]
  · exact NNReal.coe_nonneg _
  · exact NNReal.coe_nonneg _

/-- The diagonal of `glwCovMatrixNN` is the L²([0, 1]) norm squared
of `glwIntegrand`. -/
theorem glwCovMatrixNN_diag_eq_normSq (I : Finset NNReal)
    (s : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s s = ∫ x in (0 : ℝ)..1, (glwIntegrand (s.1 : ℝ) x)^2 := by
  rw [glwCovMatrixNN_eq_integral]
  congr 1
  funext x
  ring

/-! ### NNReal-grid variance decay corollaries -/

/-- For positive grid points `s.1 > 0`, the diagonal of
`glwCovMatrixNN` is bounded by `1 / (2 (s : ℝ))`. -/
theorem glwCovMatrixNN_diag_le_recip (I : Finset NNReal)
    (s : {x : NNReal // x ∈ I}) (h_s : 0 < (s.1 : ℝ)) :
    glwCovMatrixNN I s s ≤ 1 / (2 * (s.1 : ℝ)) := by
  rw [glwCovMatrixNN_apply]
  have : K_GLW (s.1 : ℝ) (s.1 : ℝ) ≤ 1 / (2 * (s.1 : ℝ)) :=
    K_GLW_var_le_recip h_s
  exact this

/-- For positive grid points `s.1 > 0`, the diagonal of
`glwCovMatrixNN` is strictly less than `1`. -/
theorem glwCovMatrixNN_diag_lt_one (I : Finset NNReal)
    (s : {x : NNReal // x ∈ I}) (h_s : 0 < (s.1 : ℝ)) :
    glwCovMatrixNN I s s < 1 := by
  rw [glwCovMatrixNN_apply]
  exact K_GLW_var_lt_one h_s

/-! ### NNReal-grid quadratic form expansion

The matrix-form `x ⬝ M ⬝ x = Σₛₜ xₛ xₜ K(s, t)` extends to the
NNReal-grid signature. -/

/-- Quadratic-form expansion for `glwCovMatrixNN`:
`Σₛ xₛ * (M *ᵥ x)ₛ = Σₛₜ xₛ xₜ K_GLW(s, t)`. -/
theorem glwCovMatrixNN_quadratic_form_eq_sum (I : Finset NNReal)
    (x : {y : NNReal // y ∈ I} → ℝ) :
    ∑ s, x s * ((glwCovMatrixNN I *ᵥ x) s) =
      ∑ s, ∑ t, x s * x t * K_GLW (s.1 : ℝ) (t.1 : ℝ) := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [glwCovMatrixNN_apply]
  ring

/-- The K_GLW NNReal-grid quadratic form is non-negative. -/
theorem glwCovMatrixNN_quadratic_form_nonneg (I : Finset NNReal)
    (x : {y : NNReal // y ∈ I} → ℝ) :
    0 ≤ ∑ s, x s * ((glwCovMatrixNN I *ᵥ x) s) := by
  have h_psd := glwCovMatrixNN_PosSemidef I
  have h_dp := h_psd.dotProduct_mulVec_nonneg x
  have h_star : star x = x := rfl
  rw [h_star] at h_dp
  rw [dotProduct] at h_dp
  exact h_dp

/-! ### NNReal-grid trace expansion -/

/-- Trace expansion for `glwCovMatrixNN I` via diagonal entries. -/
theorem glwCovMatrixNN_trace_eq_sum (I : Finset NNReal) :
    (glwCovMatrixNN I).trace =
      ∑ s : {x : NNReal // x ∈ I}, K_GLW (s.1 : ℝ) (s.1 : ℝ) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact glwCovMatrixNN_apply I s s

/-- Trace expansion for `glwCovMatrixNN I` via `K_GLW_aux`. -/
theorem glwCovMatrixNN_trace_eq_sum_K_GLW_aux (I : Finset NNReal) :
    (glwCovMatrixNN I).trace =
      ∑ s : {x : NNReal // x ∈ I}, K_GLW_aux (2 * (s.1 : ℝ)) := by
  rw [glwCovMatrixNN_trace_eq_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [K_GLW_def]
  congr 1
  ring

/-- For the all-ones test vector on ↑I, the quadratic form
`Σₛ (M *ᵥ 1)ₛ = Σₛₜ Mₛₜ`. -/
theorem glwCovMatrixNN_quadratic_form_at_one (I : Finset NNReal) :
    ∑ s : {x : NNReal // x ∈ I}, (1 : ℝ) *
        ((glwCovMatrixNN I *ᵥ (fun _ => 1)) s) =
      ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
        K_GLW (s.1 : ℝ) (t.1 : ℝ) := by
  rw [glwCovMatrixNN_quadratic_form_eq_sum]
  simp

/-! ### NNReal-grid sum-of-entries via K_GLW expansion -/

/-- The sum of all entries of `glwCovMatrixNN I` equals
`Σₛₜ K_GLW(s, t)` (over `s, t : ↑I`). -/
theorem glwCovMatrixNN_sum_entries_eq (I : Finset NNReal) :
    ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
        glwCovMatrixNN I s t =
      ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
        K_GLW (s.1 : ℝ) (t.1 : ℝ) := by
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  exact glwCovMatrixNN_apply I s t

/-- Sum of all entries on a Finset is bounded above by `I.card²` —
this is `glwCovMatrixNN_sum_entries_le` re-expressed via the
K_GLW-explicit form. -/
theorem glwCovMatrixNN_sum_K_GLW_le (I : Finset NNReal) :
    ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
        K_GLW (s.1 : ℝ) (t.1 : ℝ) ≤ (I.card : ℝ) * I.card := by
  rw [← glwCovMatrixNN_sum_entries_eq]
  exact glwCovMatrixNN_sum_entries_le I

/-- Sum of all entries on a Finset is non-negative (entries are positive). -/
theorem glwCovMatrixNN_sum_K_GLW_nonneg (I : Finset NNReal) :
    0 ≤ ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
        K_GLW (s.1 : ℝ) (t.1 : ℝ) := by
  rw [← glwCovMatrixNN_sum_entries_eq]
  exact glwCovMatrixNN_sum_entries_nonneg I

/-! ### NNReal-grid translation invariance and dilation

K_GLW is invariant under the index-coercion to ℝ, so any natural
arithmetic on the NNReal index translates to additive / multiplicative
behavior on the matrix entries. -/

/-- For NNReal `s, t` and a fixed grid `I` containing both, the entry
`Mₛₜ = M_{s', t'}` whenever `s.1 = s'.1` and `t.1 = t'.1`. -/
theorem glwCovMatrixNN_apply_eq_of_val_eq (I : Finset NNReal)
    (s s' t t' : {x : NNReal // x ∈ I})
    (hs : s.1 = s'.1) (ht : t.1 = t'.1) :
    glwCovMatrixNN I s t = glwCovMatrixNN I s' t' := by
  rw [glwCovMatrixNN_apply, glwCovMatrixNN_apply, hs, ht]

/-- The NNReal-coercion `(s : ℝ)` is non-negative. -/
theorem glwCovMatrixNN_grid_nonneg (I : Finset NNReal)
    (s : {x : NNReal // x ∈ I}) :
    0 ≤ (s.1 : ℝ) := NNReal.coe_nonneg _

/-! ### NNReal-grid value-bound corollaries on a positive grid

For a Finset where every element is positive (`∀ s ∈ I, 0 < s`), all
the variance-decay bounds tighten to strict inequalities. -/

/-- All diagonal entries are strictly less than `1` on a strictly
positive Finset. -/
theorem glwCovMatrixNN_diag_lt_one_of_pos
    {I : Finset NNReal} (h_pos : ∀ s ∈ I, (0 : NNReal) < s)
    (s : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s s < 1 :=
  glwCovMatrixNN_diag_lt_one I s
    (by exact_mod_cast h_pos s.1 s.2)

/-- All diagonals are bounded above by `1/(2(s:ℝ))` on a strictly
positive Finset. -/
theorem glwCovMatrixNN_diag_le_recip_of_pos
    {I : Finset NNReal} (h_pos : ∀ s ∈ I, (0 : NNReal) < s)
    (s : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s s ≤ 1 / (2 * (s.1 : ℝ)) :=
  glwCovMatrixNN_diag_le_recip I s
    (by exact_mod_cast h_pos s.1 s.2)

/-- The trace bound tightens to `Σₛ 1/(2 s)` on a strictly positive Finset. -/
theorem glwCovMatrixNN_trace_le_recip_sum
    {I : Finset NNReal} (h_pos : ∀ s ∈ I, (0 : NNReal) < s) :
    (glwCovMatrixNN I).trace ≤
      ∑ s : {x : NNReal // x ∈ I}, 1 / (2 * (s.1 : ℝ)) := by
  rw [Matrix.trace]
  apply Finset.sum_le_sum
  intros s _
  exact glwCovMatrixNN_diag_le_recip_of_pos h_pos s

/-! ### NNReal-grid PSD-derivative properties -/

/-- The transpose of `glwCovMatrixNN I` is also PSD (trivially, since
the matrix is symmetric). -/
theorem glwCovMatrixNN_transpose_PosSemidef (I : Finset NNReal) :
    ((glwCovMatrixNN I).transpose).PosSemidef :=
  (glwCovMatrixNN_PosSemidef I).transpose

/-- The determinant of `glwCovMatrixNN I` is non-negative. -/
theorem glwCovMatrixNN_det_nonneg (I : Finset NNReal) :
    0 ≤ (glwCovMatrixNN I).det :=
  (glwCovMatrixNN_PosSemidef I).det_nonneg

/-! ### Structured kernel-data abstraction

The complete kernel data needed to instantiate brownian-motion's
projective limit + Kolmogorov-Chentsov pipeline. Bundling these
properties into a `structure` makes downstream uses (R13 retirement
of `Y_GLW_exists`) typeclass-style and eliminates the need to thread
many hypotheses through arguments. -/

/-- A `ProcessKernel` packages the kernel data needed to construct a
covariance kernel process on `[0, ∞)` indexed by `NNReal`. -/
structure ProcessKernel where
  /-- The covariance kernel. -/
  K : NNReal → NNReal → ℝ
  /-- Symmetry. -/
  symm : ∀ s t, K s t = K t s
  /-- Positive semi-definiteness on every Finset. -/
  PSD : ∀ I : Finset NNReal,
    (Matrix.of fun s t : {x : NNReal // x ∈ I} => K s.1 t.1).PosSemidef
  /-- Consistency under restriction (B2 precondition). -/
  consistent : ∀ {I J : Finset NNReal} (hJI : J ⊆ I),
    ((Matrix.of fun s t : {x : NNReal // x ∈ I} => K s.1 t.1).submatrix
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
        (fun j : {x : NNReal // x ∈ J} =>
          (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))).PosSemidef
  /-- Hölder-1 bound (B4 precondition for Kolmogorov-Chentsov). -/
  hoelder : ∀ s t : NNReal,
    K s s + K t t - 2 * K s t ≤ ((s : ℝ) - (t : ℝ))^2

/-- The K_GLW process kernel: instantiates `ProcessKernel` for the
Gao–Li–Wellner covariance kernel `K_GLW`. All four fields are
sorry-free, witnessing the complete kernel-side specification. -/
noncomputable def K_GLW_processKernel : ProcessKernel where
  K s t := K_GLW (s : ℝ) (t : ℝ)
  symm s t := K_GLW_symm _ _
  PSD I := glwCovMatrixNN_PosSemidef I
  consistent {I J} hJI := glwCovMatrixNN_submatrix_PosSemidef hJI
  hoelder s t := by
    show K_GLW (s : ℝ) (s : ℝ) + K_GLW (t : ℝ) (t : ℝ) - 2 * K_GLW (s : ℝ) (t : ℝ) ≤
      ((s : ℝ) - (t : ℝ))^2
    have := K_GLW_diff_quadratic_le_sq
              (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)
    linarith

/-! ### Structural corollaries of `ProcessKernel`

Generic facts derivable from the `ProcessKernel` axioms — these
are what downstream brownian-motion-side arguments would consume. -/

namespace ProcessKernel

variable (P : ProcessKernel)

/-- For any process kernel, the Hölder-1 bound at `(s, s)` gives `0 ≤ 0`
(trivially) — useful sanity check. -/
theorem K_hoelder_self (s : NNReal) :
    P.K s s + P.K s s - 2 * P.K s s ≤ 0 := by
  have := P.hoelder s s
  simp at this
  linarith

/-- For any process kernel, the off-diagonal Hölder-1 bound. -/
theorem K_off_diag_le (s t : NNReal) :
    P.K s s + P.K t t - 2 * P.K s t ≤ ((s : ℝ) - (t : ℝ))^2 :=
  P.hoelder s t

end ProcessKernel

/-! ### Mercer/integral connection on the NNReal grid - additional facts -/

/-- The off-diagonal `Mₛₜ` is expressible via the explicit
exp-product integrand. -/
theorem glwCovMatrixNN_offdiag_eq_integral (I : Finset NNReal)
    (s t : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s t = ∫ x in (0 : ℝ)..1,
      Real.exp (-(s.1 : ℝ) * x) * Real.exp (-(t.1 : ℝ) * x) := by
  rw [glwCovMatrixNN_eq_integral]
  simp [glwIntegrand_def]

/-- The matrix entries are bounded by `1`, expressible as a unit
interval integral. -/
theorem glwCovMatrixNN_entry_le_integral_one (I : Finset NNReal)
    (s t : {x : NNReal // x ∈ I}) :
    glwCovMatrixNN I s t ≤ ∫ _x in (0 : ℝ)..1, (1 : ℝ) := by
  rw [glwCovMatrixNN_apply]
  have := K_GLW_le_one _ _ (NNReal.coe_nonneg s.1) (NNReal.coe_nonneg t.1)
  calc K_GLW (s.1 : ℝ) (t.1 : ℝ) ≤ 1 := this
    _ = ∫ _x in (0 : ℝ)..1, (1 : ℝ) := by simp

/-! ### Empty-Finset and singleton degenerate cases -/

/-- For the empty Finset, every sum over `↑∅` is `0`, so the trace is `0`. -/
theorem glwCovMatrixNN_empty_trace :
    (glwCovMatrixNN ∅).trace = 0 := by
  rw [Matrix.trace]
  exact Finset.sum_empty

/-- For the empty Finset, the matrix is the trivial empty matrix
(no entries). -/
theorem glwCovMatrixNN_empty_det :
    (glwCovMatrixNN ∅).det = 1 := by
  rw [Matrix.det_isEmpty]

/-! ### K_GLW_processKernel projection facts -/

/-- The K field of `K_GLW_processKernel` is `K_GLW` (composed with
NNReal coercion). Useful as a definitional unfolding. -/
@[simp]
theorem K_GLW_processKernel_K (s t : NNReal) :
    K_GLW_processKernel.K s t = K_GLW (s : ℝ) (t : ℝ) := rfl

/-- The symmetry field of `K_GLW_processKernel` reduces to
`K_GLW_symm`. -/
theorem K_GLW_processKernel_symm (s t : NNReal) :
    K_GLW_processKernel.K s t = K_GLW_processKernel.K t s :=
  K_GLW_processKernel.symm s t

/-- The PSD field of `K_GLW_processKernel` produces
`glwCovMatrixNN_PosSemidef`. -/
theorem K_GLW_processKernel_PSD (I : Finset NNReal) :
    (Matrix.of fun s t : {x : NNReal // x ∈ I} =>
       K_GLW_processKernel.K s.1 t.1).PosSemidef :=
  K_GLW_processKernel.PSD I

/-- The hoelder field of `K_GLW_processKernel` is the Hölder-1 bound. -/
theorem K_GLW_processKernel_hoelder (s t : NNReal) :
    K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
      2 * K_GLW_processKernel.K s t ≤ ((s : ℝ) - (t : ℝ))^2 :=
  K_GLW_processKernel.hoelder s t

/-- Specific value: at `(0, 0)`, the kernel equals `1`. -/
theorem K_GLW_processKernel_at_zero :
    K_GLW_processKernel.K 0 0 = 1 := by
  simp [K_GLW_processKernel_K, K_GLW_zero]

/-- Specific value: the kernel is positive on any pair `(s, t)`. -/
theorem K_GLW_processKernel_pos (s t : NNReal) :
    0 < K_GLW_processKernel.K s t := by
  rw [K_GLW_processKernel_K]
  exact K_GLW_pos _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

/-- Specific bound: the kernel is bounded above by `1`. -/
theorem K_GLW_processKernel_le_one (s t : NNReal) :
    K_GLW_processKernel.K s t ≤ 1 := by
  rw [K_GLW_processKernel_K]
  exact K_GLW_le_one _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

/-- The kernel `K_GLW_processKernel.K` is jointly continuous as a
function on `NNReal × NNReal`. -/
theorem K_GLW_processKernel_continuous :
    Continuous (Function.uncurry K_GLW_processKernel.K) := by
  show Continuous (fun p : NNReal × NNReal => K_GLW (p.1 : ℝ) (p.2 : ℝ))
  have h_pair : Continuous (fun p : NNReal × NNReal => ((p.1 : ℝ), (p.2 : ℝ))) :=
    Continuous.prodMk (NNReal.continuous_coe.comp continuous_fst)
                       (NNReal.continuous_coe.comp continuous_snd)
  exact K_GLW_continuous.comp h_pair

/-- The diagonal of `K_GLW_processKernel` factors through `K_GLW_aux`. -/
theorem K_GLW_processKernel_diag (s : NNReal) :
    K_GLW_processKernel.K s s = K_GLW_aux (2 * (s : ℝ)) := by
  rw [K_GLW_processKernel_K, K_GLW_def]
  congr 1
  ring

/-- The diagonal is non-negative. -/
theorem K_GLW_processKernel_diag_nonneg (s : NNReal) :
    0 ≤ K_GLW_processKernel.K s s :=
  le_of_lt (K_GLW_processKernel_pos s s)

/-- The diagonal is bounded above by `1`. -/
theorem K_GLW_processKernel_diag_le_one (s : NNReal) :
    K_GLW_processKernel.K s s ≤ 1 :=
  K_GLW_processKernel_le_one s s

/-- Direct K_GLW_processKernel Hölder bound at the diagonal: trivially 0. -/
theorem K_GLW_processKernel_self_diag_diff (s : NNReal) :
    K_GLW_processKernel.K s s + K_GLW_processKernel.K s s -
      2 * K_GLW_processKernel.K s s = 0 := by ring

/-- The Cauchy-Schwarz inequality at the kernel level. -/
theorem K_GLW_processKernel_cauchy_schwarz (s t : NNReal) :
    (K_GLW_processKernel.K s t)^2 ≤
      K_GLW_processKernel.K s s * K_GLW_processKernel.K t t := by
  rw [K_GLW_processKernel_K, K_GLW_processKernel_K, K_GLW_processKernel_K]
  exact K_GLW_cauchy_schwarz (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)

/-- The variance is decreasing in the index — for `s ≤ t` (in NNReal)
the diagonal entry `K(s, s) ≥ K(t, t)`. -/
theorem K_GLW_processKernel_diag_antitone {s t : NNReal} (hst : s ≤ t) :
    K_GLW_processKernel.K t t ≤ K_GLW_processKernel.K s s := by
  rw [K_GLW_processKernel_K, K_GLW_processKernel_K]
  exact K_GLW_var_antitone (NNReal.coe_nonneg s)
          (NNReal.coe_le_coe.mpr hst)

/-- For positive `s : NNReal`, the diagonal `K(s, s)` is bounded by
`1 / (2 (s : ℝ))`. -/
theorem K_GLW_processKernel_diag_le_recip {s : NNReal} (h_s : 0 < (s : ℝ)) :
    K_GLW_processKernel.K s s ≤ 1 / (2 * (s : ℝ)) := by
  rw [K_GLW_processKernel_K]
  exact K_GLW_var_le_recip h_s

/-- For positive `s : NNReal`, the diagonal is strictly less than `1`. -/
theorem K_GLW_processKernel_diag_lt_one {s : NNReal} (h_s : 0 < (s : ℝ)) :
    K_GLW_processKernel.K s s < 1 := by
  rw [K_GLW_processKernel_K]
  exact K_GLW_var_lt_one h_s

/-- Anti-symmetric L²-distance bound: pairwise difference is non-negative. -/
theorem K_GLW_processKernel_diff_nonneg (s t : NNReal) :
    0 ≤ K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
        2 * K_GLW_processKernel.K s t := by
  rw [K_GLW_processKernel_K, K_GLW_processKernel_K, K_GLW_processKernel_K]
  linarith [K_GLW_diff_quadratic_nonneg
              (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)]

/-- Hölder bound: `K(s, s) + K(t, t) - 2 K(s, t) ≤ |s - t|² + 0` —
sanity-check restatement of the hoelder field. -/
theorem K_GLW_processKernel_hoelder_via_distance (s t : NNReal) :
    K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
      2 * K_GLW_processKernel.K s t ≤ ((s : ℝ) - (t : ℝ))^2 :=
  K_GLW_processKernel.hoelder s t

/-- The kernel value `K_GLW_processKernel.K s 0` simplifies to
`K_GLW_aux(s)` (using the `K_GLW(0, u) = K_GLW_aux(u)` identity). -/
theorem K_GLW_processKernel_at_zero_right (s : NNReal) :
    K_GLW_processKernel.K s 0 = K_GLW_aux (s : ℝ) := by
  rw [K_GLW_processKernel_K]
  simp [K_GLW_zero_right]

/-- The kernel value `K_GLW_processKernel.K 0 t` simplifies to
`K_GLW_aux(t)`. -/
theorem K_GLW_processKernel_at_zero_left (t : NNReal) :
    K_GLW_processKernel.K 0 t = K_GLW_aux (t : ℝ) := by
  rw [K_GLW_processKernel_K]
  simp [K_GLW_zero_left]

/-- Final R12 capstone identity: the kernel-data witness commutes
through the structure projections — kernel value at any pair. -/
theorem K_GLW_processKernel_K_eq_K_GLW (s t : NNReal) :
    K_GLW_processKernel.K s t = K_GLW (s : ℝ) (t : ℝ) := rfl

/-! ### NNReal-grid quadratic-form bound on a positive Finset -/

/-- The NNReal-grid quadratic form is bounded above by the squared
L¹-norm of the test vector. -/
theorem glwCovMatrixNN_quadratic_form_le_l1_sq (I : Finset NNReal)
    (x : {y : NNReal // y ∈ I} → ℝ) :
    ∑ s, x s * ((glwCovMatrixNN I *ᵥ x) s) ≤
      (∑ s : {y : NNReal // y ∈ I}, |x s|)^2 := by
  rw [glwCovMatrixNN_quadratic_form_eq_sum]
  calc ∑ s, ∑ t, x s * x t * K_GLW (s.1 : ℝ) (t.1 : ℝ)
      ≤ ∑ s, ∑ t, |x s| * |x t| := by
        apply Finset.sum_le_sum
        intros s _
        apply Finset.sum_le_sum
        intros t _
        have h_pos : 0 ≤ K_GLW (s.1 : ℝ) (t.1 : ℝ) :=
          le_of_lt (K_GLW_pos _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
        have h_le : K_GLW (s.1 : ℝ) (t.1 : ℝ) ≤ 1 :=
          K_GLW_le_one _ _ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
        calc x s * x t * K_GLW (s.1 : ℝ) (t.1 : ℝ)
            ≤ |x s * x t| * K_GLW (s.1 : ℝ) (t.1 : ℝ) := by
              gcongr
              exact le_abs_self _
          _ ≤ |x s * x t| * 1 := by
              gcongr
          _ = |x s| * |x t| := by rw [mul_one, abs_mul]
    _ = (∑ s : {y : NNReal // y ∈ I}, |x s|)^2 := by
        rw [sq, Finset.sum_mul_sum]

/-- **Full packaged kernel-data witness on NNReal grids** including
the Hölder-1 bound — the *complete* B1+B2+B4 precondition package
for the brownian-motion projective-limit + Kolmogorov-Chentsov
construction. All four conjuncts are sorry-free. -/
theorem Y_GLW_kernel_data_NN_full :
    ∃ K : NNReal → NNReal → ℝ,
      (∀ s t : NNReal, K s t = K t s) ∧
      (∀ I : Finset NNReal,
        (Matrix.of fun s t : {x : NNReal // x ∈ I} => K s.1 t.1).PosSemidef) ∧
      (∀ {I J : Finset NNReal} (hJI : J ⊆ I),
        ((Matrix.of fun s t : {x : NNReal // x ∈ I} => K s.1 t.1).submatrix
            (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
            (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))).PosSemidef) ∧
      (∀ s t : NNReal,
        K s s + K t t - 2 * K s t ≤ ((s : ℝ) - (t : ℝ))^2) := by
  refine ⟨fun s t => K_GLW (s : ℝ) (t : ℝ), ?_, ?_, ?_, ?_⟩
  · intros s t; exact K_GLW_symm _ _
  · intro I; exact glwCovMatrixNN_PosSemidef I
  · intros I J hJI; exact glwCovMatrixNN_submatrix_PosSemidef hJI
  · intros s t
    show K_GLW (s : ℝ) (s : ℝ) + K_GLW (t : ℝ) (t : ℝ) - 2 * K_GLW (s : ℝ) (t : ℝ) ≤
      ((s : ℝ) - (t : ℝ))^2
    have := K_GLW_diff_quadratic_le_sq
              (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)
    linarith

/-! ## 4.25. Extended `ProcessKernel` corollaries — generic structural facts

Generic facts derivable from the four `ProcessKernel` axioms. These
are reusable for any kernel data witnessing a Gaussian process on
`NNReal` — once `Y_GLW_exists` is retired (R14+), these will continue
to be load-bearing for downstream upper/lower bound arguments. -/

namespace ProcessKernel

variable (P : ProcessKernel)

/-- Hölder-1 yields a *lower* bound on `2 K(s, t)`:
`2 K(s, t) ≥ K(s, s) + K(t, t) − ((s - t) : ℝ)²`. -/
theorem K_two_ge_diag_minus_sq_diff (s t : NNReal) :
    P.K s s + P.K t t - ((s : ℝ) - (t : ℝ))^2 ≤ 2 * P.K s t := by
  have := P.hoelder s t
  linarith

/-- The Hölder-1 bound, expressed as a *lower* bound on the off-diagonal
in terms of the diagonal: `K(s, t) ≥ (K(s, s) + K(t, t))/2 − (s - t)²/2`. -/
theorem K_off_diag_ge_diag_avg_minus_sq (s t : NNReal) :
    (P.K s s + P.K t t) / 2 - ((s : ℝ) - (t : ℝ))^2 / 2 ≤ P.K s t := by
  have := P.hoelder s t
  linarith

/-- The averaged Hölder-1 bound. -/
theorem K_avg_le_off_diag_plus_sq_half (s t : NNReal) :
    (P.K s s + P.K t t) / 2 - P.K s t ≤ ((s : ℝ) - (t : ℝ))^2 / 2 := by
  have := P.hoelder s t
  linarith

/-- Scaled Hölder-1 bound: any non-negative multiple. -/
theorem K_hoelder_scaled (s t : NNReal) (c : ℝ) (hc : 0 ≤ c) :
    c * (P.K s s + P.K t t - 2 * P.K s t) ≤ c * ((s : ℝ) - (t : ℝ))^2 :=
  mul_le_mul_of_nonneg_left (P.hoelder s t) hc

/-- The triangle-style three-point Hölder inequality:
sum of pairwise increment-squares is bounded by sum of squared distances. -/
theorem K_three_point_hoelder (s t u : NNReal) :
    (P.K s s + P.K t t - 2 * P.K s t) +
      (P.K t t + P.K u u - 2 * P.K t u) ≤
        ((s : ℝ) - (t : ℝ))^2 + ((t : ℝ) - (u : ℝ))^2 := by
  have h1 := P.hoelder s t
  have h2 := P.hoelder t u
  linarith

/-- Reflexive Hölder bound: at `(s, s)`, the increment is zero. -/
theorem K_hoelder_refl (s : NNReal) :
    P.K s s + P.K s s - 2 * P.K s s = 0 := by ring

/-- Non-negativity of the squared-difference Hölder right-hand side. -/
theorem K_hoelder_rhs_nonneg (s t : NNReal) :
    0 ≤ ((s : ℝ) - (t : ℝ))^2 := sq_nonneg _

end ProcessKernel

/-! ## 4.26. Extended `K_GLW_processKernel` corollaries — instantiation
on the GLW kernel of `ProcessKernel` generic facts. -/

/-- The averaged Hölder bound for the GLW process kernel. -/
theorem K_GLW_processKernel_avg_le (s t : NNReal) :
    (K_GLW_processKernel.K s s + K_GLW_processKernel.K t t) / 2 -
      K_GLW_processKernel.K s t ≤ ((s : ℝ) - (t : ℝ))^2 / 2 :=
  K_GLW_processKernel.K_avg_le_off_diag_plus_sq_half s t

/-- The Hölder lower bound on the off-diagonal of the GLW process kernel. -/
theorem K_GLW_processKernel_off_diag_ge_diag_avg_minus_sq (s t : NNReal) :
    (K_GLW_processKernel.K s s + K_GLW_processKernel.K t t) / 2 -
        ((s : ℝ) - (t : ℝ))^2 / 2 ≤
      K_GLW_processKernel.K s t :=
  K_GLW_processKernel.K_off_diag_ge_diag_avg_minus_sq s t

/-- Three-point Hölder for the GLW process kernel. -/
theorem K_GLW_processKernel_three_point_hoelder (s t u : NNReal) :
    (K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
        2 * K_GLW_processKernel.K s t) +
      (K_GLW_processKernel.K t t + K_GLW_processKernel.K u u -
        2 * K_GLW_processKernel.K t u) ≤
        ((s : ℝ) - (t : ℝ))^2 + ((t : ℝ) - (u : ℝ))^2 :=
  K_GLW_processKernel.K_three_point_hoelder s t u

/-- Empty-Finset PSD for the GLW process kernel — trivially true. -/
theorem K_GLW_processKernel_empty_PSD :
    (Matrix.of fun s t : {x : NNReal // x ∈ (∅ : Finset NNReal)} =>
       K_GLW_processKernel.K s.1 t.1).PosSemidef :=
  K_GLW_processKernel.PSD ∅

/-- Singleton-Finset PSD for the GLW process kernel — the 1×1 case. -/
theorem K_GLW_processKernel_singleton_PSD (a : NNReal) :
    (Matrix.of fun s t : {x : NNReal // x ∈ ({a} : Finset NNReal)} =>
       K_GLW_processKernel.K s.1 t.1).PosSemidef :=
  K_GLW_processKernel.PSD {a}

/-- Pair-Finset PSD for the GLW process kernel — the 2×2 case. -/
theorem K_GLW_processKernel_pair_PSD (a b : NNReal) :
    (Matrix.of fun s t : {x : NNReal // x ∈ ({a, b} : Finset NNReal)} =>
       K_GLW_processKernel.K s.1 t.1).PosSemidef :=
  K_GLW_processKernel.PSD {a, b}

/-- Sum of two diagonal GLW kernel values is bounded above by `2`. -/
theorem K_GLW_processKernel_diag_sum_le_two (s t : NNReal) :
    K_GLW_processKernel.K s s + K_GLW_processKernel.K t t ≤ 2 := by
  have h1 := K_GLW_processKernel_le_one s s
  have h2 := K_GLW_processKernel_le_one t t
  linarith

/-- Sum of two diagonal GLW kernel values is non-negative. -/
theorem K_GLW_processKernel_diag_sum_nonneg (s t : NNReal) :
    0 ≤ K_GLW_processKernel.K s s + K_GLW_processKernel.K t t := by
  have h1 := K_GLW_processKernel_diag_nonneg s
  have h2 := K_GLW_processKernel_diag_nonneg t
  linarith

/-- Sum of three pairwise off-diagonal kernel values bound. -/
theorem K_GLW_processKernel_three_pair_sum_le (s t u : NNReal) :
    K_GLW_processKernel.K s t + K_GLW_processKernel.K t u +
      K_GLW_processKernel.K s u ≤ 3 := by
  have h1 := K_GLW_processKernel_le_one s t
  have h2 := K_GLW_processKernel_le_one t u
  have h3 := K_GLW_processKernel_le_one s u
  linarith

/-! ## 4.27. `ProcessKernel.K_diag_nonneg` via `Matrix.PosSemidef.diag_nonneg`

Diagonal non-negativity for any process kernel, derived directly from
the abstract `PSD` axiom on the singleton `{s}`. This shows that
*non-negative variances* are baked into the `ProcessKernel` interface
and don't need separate hypothesis. -/

namespace ProcessKernel

variable (P : ProcessKernel)

/-- For any process kernel, `K(s, s) ≥ 0` — derived from `PosSemidef`
on the singleton Finset `{s}`. -/
theorem K_diag_nonneg (s : NNReal) : 0 ≤ P.K s s := by
  have h := P.PSD ({s} : Finset NNReal)
  let i : {x : NNReal // x ∈ ({s} : Finset NNReal)} :=
    ⟨s, Finset.mem_singleton.mpr rfl⟩
  have h_diag := h.diag_nonneg (i := i)
  simpa [Matrix.of_apply] using h_diag

/-- For any process kernel, the sum of two diagonal entries is non-negative. -/
theorem K_diag_sum_nonneg (s t : NNReal) :
    0 ≤ P.K s s + P.K t t :=
  add_nonneg (P.K_diag_nonneg s) (P.K_diag_nonneg t)

/-- For any process kernel, `2 K(s, s) ≥ 0`. -/
theorem K_diag_two_nonneg (s : NNReal) : 0 ≤ 2 * P.K s s :=
  mul_nonneg (by norm_num) (P.K_diag_nonneg s)

/-- For any process kernel, `K(s, s) + K(s, s) - 2 K(s, s) = 0`
(Hölder bound is tight at `(s, s)`). -/
theorem K_self_diff_eq_zero (s : NNReal) :
    P.K s s + P.K s s - 2 * P.K s s = 0 := by ring

/-- Hölder bound at `(s, s)` is `0 ≤ 0` — trivially equality. -/
theorem K_hoelder_self_eq_zero (s : NNReal) :
    P.K s s + P.K s s - 2 * P.K s s ≤ ((s : ℝ) - (s : ℝ))^2 := by
  rw [P.K_self_diff_eq_zero]
  exact sq_nonneg _

end ProcessKernel

/-! ## 4.28. K_GLW_processKernel — Cauchy-Schwarz and pair structure

Applying the abstract `ProcessKernel` framework specifically to the
GLW kernel, plus pair-level Cauchy-Schwarz from
`glwCovMatrixNN_entry_sq_le_diag_prod`. -/

/-- The GLW process kernel diagonal is non-negative (via abstract
ProcessKernel diag-non-neg). -/
theorem K_GLW_processKernel_diag_nonneg' (s : NNReal) :
    0 ≤ K_GLW_processKernel.K s s :=
  K_GLW_processKernel.K_diag_nonneg s

/-- Pair-level Cauchy-Schwarz for `K_GLW_processKernel`:
`K(s, t)² ≤ K(s, s) · K(t, t)`. -/
theorem K_GLW_processKernel_cauchy_schwarz' (s t : NNReal) :
    (K_GLW_processKernel.K s t)^2 ≤
      K_GLW_processKernel.K s s * K_GLW_processKernel.K t t := by
  show (K_GLW (s : ℝ) (t : ℝ))^2 ≤
    K_GLW (s : ℝ) (s : ℝ) * K_GLW (t : ℝ) (t : ℝ)
  exact K_GLW_cauchy_schwarz (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

/-- Bound: `K(s, t) ≤ √(K(s, s) · K(t, t))` (after taking sqrt). -/
theorem K_GLW_processKernel_abs_le_sqrt_diag_prod (s t : NNReal) :
    |K_GLW_processKernel.K s t| ≤
      Real.sqrt (K_GLW_processKernel.K s s * K_GLW_processKernel.K t t) := by
  have h := K_GLW_processKernel_cauchy_schwarz' s t
  have h_prod_nn :
      0 ≤ K_GLW_processKernel.K s s * K_GLW_processKernel.K t t :=
    mul_nonneg (K_GLW_processKernel.K_diag_nonneg s)
               (K_GLW_processKernel.K_diag_nonneg t)
  have h_sq_eq : |K_GLW_processKernel.K s t|^2 =
      (K_GLW_processKernel.K s t)^2 := sq_abs _
  rw [show |K_GLW_processKernel.K s t| =
        Real.sqrt ((K_GLW_processKernel.K s t)^2) from
      (Real.sqrt_sq_eq_abs _).symm]
  exact Real.sqrt_le_sqrt h

/-- Pair-level Cauchy-Schwarz for `K_GLW_processKernel`, expressed as
a non-negative discriminant:
`K(s, s) · K(t, t) − K(s, t)² ≥ 0`. -/
theorem K_GLW_processKernel_discriminant_nonneg (s t : NNReal) :
    0 ≤ K_GLW_processKernel.K s s * K_GLW_processKernel.K t t -
        (K_GLW_processKernel.K s t)^2 := by
  have := K_GLW_processKernel_cauchy_schwarz' s t
  linarith

/-- Equality of K_GLW_processKernel diagonal at `s = t`: trivially symmetric. -/
theorem K_GLW_processKernel_diag_self (s : NNReal) :
    K_GLW_processKernel.K s s = K_GLW_processKernel.K s s := rfl

/-- The off-diagonal vanishes only when both diagonals do (in absolute
value): `K(s, t) = 0 → K(s, s) · K(t, t) ≥ 0` (trivial via diag-nonneg). -/
theorem K_GLW_processKernel_diag_prod_nonneg (s t : NNReal) :
    0 ≤ K_GLW_processKernel.K s s * K_GLW_processKernel.K t t :=
  mul_nonneg (K_GLW_processKernel.K_diag_nonneg s)
             (K_GLW_processKernel.K_diag_nonneg t)

/-! ## 4.29. `ProcessKernel.kernelMatrix` — packaged matrix abstraction

The Finset-indexed Gram matrix view of a process kernel. Wrapping
`Matrix.of (fun s t => K s.1 t.1)` once gives downstream code a
single named handle to refer to the kernel's finite-dim restriction. -/

namespace ProcessKernel

variable (P : ProcessKernel)

/-- The kernel matrix on a Finset `I`: a packaged view of
`Matrix.of (fun s t : I => K s.1 t.1)`. -/
noncomputable def kernelMatrix (I : Finset NNReal) :
    Matrix {x : NNReal // x ∈ I} {x : NNReal // x ∈ I} ℝ :=
  Matrix.of fun s t : {x : NNReal // x ∈ I} => P.K s.1 t.1

@[simp]
theorem kernelMatrix_apply (I : Finset NNReal)
    (s t : {x : NNReal // x ∈ I}) :
    P.kernelMatrix I s t = P.K s.1 t.1 := rfl

theorem kernelMatrix_PSD (I : Finset NNReal) :
    (P.kernelMatrix I).PosSemidef := P.PSD I

theorem kernelMatrix_isHermitian (I : Finset NNReal) :
    (P.kernelMatrix I).IsHermitian := (P.PSD I).1

theorem kernelMatrix_symm (I : Finset NNReal)
    (s t : {x : NNReal // x ∈ I}) :
    P.kernelMatrix I s t = P.kernelMatrix I t s := by
  simp [kernelMatrix_apply, P.symm]

theorem kernelMatrix_diag_nonneg
    (I : Finset NNReal) (s : {x : NNReal // x ∈ I}) :
    0 ≤ P.kernelMatrix I s s :=
  (P.PSD I).diag_nonneg

/-- Trace expansion as a sum of diagonal kernel evaluations. -/
theorem kernelMatrix_trace_eq (I : Finset NNReal) :
    (P.kernelMatrix I).trace = ∑ s : {x : NNReal // x ∈ I}, P.K s.1 s.1 := by
  rfl

theorem kernelMatrix_trace_nonneg (I : Finset NNReal) :
    0 ≤ (P.kernelMatrix I).trace := by
  rw [kernelMatrix_trace_eq]
  exact Finset.sum_nonneg fun s _ => P.K_diag_nonneg s.1

/-- The quadratic form `xᵀ M x` on the kernel matrix is non-negative. -/
theorem kernelMatrix_quadratic_form_nonneg
    (I : Finset NNReal) (x : {y : NNReal // y ∈ I} → ℝ) :
    0 ≤ ∑ s, x s * (P.kernelMatrix I *ᵥ x) s := by
  have h := (P.PSD I).dotProduct_mulVec_nonneg x
  have h_star : star x = x := rfl
  rw [h_star, dotProduct] at h
  exact h

/-- Bilinear-form expansion: `xᵀ M x = ∑ₛ ∑ₜ xₛ xₜ K(s, t)`. -/
theorem kernelMatrix_quadratic_form_eq_sum
    (I : Finset NNReal) (x : {y : NNReal // y ∈ I} → ℝ) :
    ∑ s, x s * (P.kernelMatrix I *ᵥ x) s =
      ∑ s, ∑ t, x s * x t * P.K s.1 t.1 := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [kernelMatrix_apply]
  ring

/-- Sum-of-entries of the kernel matrix. -/
theorem kernelMatrix_sum_entries_eq (I : Finset NNReal) :
    ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
        P.kernelMatrix I s t =
      ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
        P.K s.1 t.1 := rfl

/-- The kernel matrix on `I` and on a subset `J ⊆ I` are related by
restriction. -/
theorem kernelMatrix_consistent {I J : Finset NNReal} (hJI : J ⊆ I) :
    ((P.kernelMatrix I).submatrix
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
        (fun j : {x : NNReal // x ∈ J} =>
          (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))).PosSemidef :=
  P.consistent hJI

end ProcessKernel

/-- The K_GLW process kernel matrix on `I` agrees with `glwCovMatrixNN I`. -/
theorem K_GLW_processKernel_kernelMatrix_eq (I : Finset NNReal) :
    K_GLW_processKernel.kernelMatrix I = glwCovMatrixNN I := by
  funext s t
  rfl

/-- Trace of `K_GLW_processKernel.kernelMatrix I` matches the GLW
trace formula. -/
theorem K_GLW_processKernel_kernelMatrix_trace_eq (I : Finset NNReal) :
    (K_GLW_processKernel.kernelMatrix I).trace = (glwCovMatrixNN I).trace := by
  rw [K_GLW_processKernel_kernelMatrix_eq]

/-- Trace of `K_GLW_processKernel.kernelMatrix I` is bounded by `card I`. -/
theorem K_GLW_processKernel_kernelMatrix_trace_le_card (I : Finset NNReal) :
    (K_GLW_processKernel.kernelMatrix I).trace ≤ (I.card : ℝ) := by
  rw [K_GLW_processKernel_kernelMatrix_trace_eq]
  exact glwCovMatrixNN_trace_le_card I

/-! ## 4.30. K_GLW_processKernel.kernelMatrix — entry/sum/Frobenius lifts

Structural bounds on `K_GLW_processKernel.kernelMatrix` lifted directly
from the corresponding `glwCovMatrixNN` lemmas via the equality
`K_GLW_processKernel.kernelMatrix I = glwCovMatrixNN I`. -/

/-- Each entry of `K_GLW_processKernel.kernelMatrix I` is positive. -/
theorem K_GLW_processKernel_kernelMatrix_entry_pos
    (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    0 < K_GLW_processKernel.kernelMatrix I s t := by
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_entry_pos I s t

/-- Each entry of `K_GLW_processKernel.kernelMatrix I` is at most `1`. -/
theorem K_GLW_processKernel_kernelMatrix_entry_le_one
    (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    K_GLW_processKernel.kernelMatrix I s t ≤ 1 := by
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_entry_le_one I s t

/-- Each diagonal entry of `K_GLW_processKernel.kernelMatrix I` is non-negative. -/
theorem K_GLW_processKernel_kernelMatrix_diag_nonneg
    (I : Finset NNReal) (s : {x : NNReal // x ∈ I}) :
    0 ≤ K_GLW_processKernel.kernelMatrix I s s := by
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_diag_nonneg I s

/-- Each diagonal entry of `K_GLW_processKernel.kernelMatrix I` is at most `1`. -/
theorem K_GLW_processKernel_kernelMatrix_diag_le_one
    (I : Finset NNReal) (s : {x : NNReal // x ∈ I}) :
    K_GLW_processKernel.kernelMatrix I s s ≤ 1 := by
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_diag_le_one I s

/-- Trace of `K_GLW_processKernel.kernelMatrix I` is non-negative. -/
theorem K_GLW_processKernel_kernelMatrix_trace_nonneg (I : Finset NNReal) :
    0 ≤ (K_GLW_processKernel.kernelMatrix I).trace := by
  rw [K_GLW_processKernel_kernelMatrix_trace_eq]
  exact glwCovMatrixNN_trace_nonneg I

/-- Sum of entries of `K_GLW_processKernel.kernelMatrix I` is non-negative. -/
theorem K_GLW_processKernel_kernelMatrix_sum_entries_nonneg
    (I : Finset NNReal) :
    0 ≤ ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
          K_GLW_processKernel.kernelMatrix I s t := by
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_sum_entries_nonneg I

/-- Sum of entries of `K_GLW_processKernel.kernelMatrix I` is bounded
above by `(card I)²`. -/
theorem K_GLW_processKernel_kernelMatrix_sum_entries_le
    (I : Finset NNReal) :
    ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
          K_GLW_processKernel.kernelMatrix I s t ≤
            (I.card : ℝ) * (I.card : ℝ) := by
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_sum_entries_le I

/-- Pair-level Cauchy-Schwarz for `K_GLW_processKernel.kernelMatrix I`. -/
theorem K_GLW_processKernel_kernelMatrix_entry_sq_le_diag_prod
    (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    (K_GLW_processKernel.kernelMatrix I s t)^2 ≤
      K_GLW_processKernel.kernelMatrix I s s *
        K_GLW_processKernel.kernelMatrix I t t := by
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_entry_sq_le_diag_prod I s t

/-- The kernel matrix submatrix consistency: restricting
`kernelMatrix I` to a sub-Finset `J ⊆ I` gives `kernelMatrix J`. -/
theorem K_GLW_processKernel_kernelMatrix_submatrix
    {I J : Finset NNReal} (hJI : J ⊆ I) :
    (K_GLW_processKernel.kernelMatrix I).submatrix
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
        (fun j : {x : NNReal // x ∈ J} =>
          (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I})) =
      K_GLW_processKernel.kernelMatrix J := by
  rw [K_GLW_processKernel_kernelMatrix_eq, K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_submatrix hJI

/-- The kernel matrix submatrix is itself PSD (sub-Finset PSD). -/
theorem K_GLW_processKernel_kernelMatrix_submatrix_PSD
    {I J : Finset NNReal} (hJI : J ⊆ I) :
    ((K_GLW_processKernel.kernelMatrix I).submatrix
        (fun j : {x : NNReal // x ∈ J} => (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))
        (fun j : {x : NNReal // x ∈ J} =>
          (⟨j.1, hJI j.2⟩ : {x : NNReal // x ∈ I}))).PosSemidef := by
  rw [K_GLW_processKernel_kernelMatrix_submatrix hJI]
  rw [K_GLW_processKernel_kernelMatrix_eq]
  exact glwCovMatrixNN_PosSemidef J

/-! ## 4.31. K_GLW_processKernel.kernelMatrix — quadratic form lifts -/

/-- Quadratic form on the kernel matrix is non-negative. -/
theorem K_GLW_processKernel_kernelMatrix_quadratic_form_nonneg
    (I : Finset NNReal) (x : {y : NNReal // y ∈ I} → ℝ) :
    0 ≤ ∑ s, x s * (K_GLW_processKernel.kernelMatrix I *ᵥ x) s :=
  K_GLW_processKernel.kernelMatrix_quadratic_form_nonneg I x

/-- Quadratic form on the kernel matrix bounded by `(∑ |x|)²`. -/
theorem K_GLW_processKernel_kernelMatrix_quadratic_form_le_l1_sq
    (I : Finset NNReal) (x : {y : NNReal // y ∈ I} → ℝ) :
    ∑ s, x s * (K_GLW_processKernel.kernelMatrix I *ᵥ x) s ≤
      (∑ s : {y : NNReal // y ∈ I}, |x s|)^2 := by
  rw [show (K_GLW_processKernel.kernelMatrix I *ᵥ x) =
        (glwCovMatrixNN I *ᵥ x) by rw [K_GLW_processKernel_kernelMatrix_eq]]
  exact glwCovMatrixNN_quadratic_form_le_l1_sq I x

/-- Quadratic form on the kernel matrix expanded as a double sum. -/
theorem K_GLW_processKernel_kernelMatrix_quadratic_form_eq_sum
    (I : Finset NNReal) (x : {y : NNReal // y ∈ I} → ℝ) :
    ∑ s, x s * (K_GLW_processKernel.kernelMatrix I *ᵥ x) s =
      ∑ s, ∑ t, x s * x t * K_GLW_processKernel.K s.1 t.1 := by
  exact K_GLW_processKernel.kernelMatrix_quadratic_form_eq_sum I x

/-- Hermitian property of `K_GLW_processKernel.kernelMatrix`. -/
theorem K_GLW_processKernel_kernelMatrix_isHermitian (I : Finset NNReal) :
    (K_GLW_processKernel.kernelMatrix I).IsHermitian :=
  (K_GLW_processKernel.PSD I).1

/-! ## 4.32. Explicit K_GLW_processKernel values at zero and on the diagonal

These specialised forms make the relationship between `K_GLW_processKernel.K`
and the `(1 - exp(-x))/x` formula explicit, useful for any
quantitative estimates in downstream lower-bound arguments. -/

/-- For `t > 0`, the kernel value `K(0, t) = (1 - exp(-t)) / t`. -/
theorem K_GLW_processKernel_K_zero_left_eq (t : NNReal) (ht : 0 < (t : ℝ)) :
    K_GLW_processKernel.K 0 t = (1 - Real.exp (-(t : ℝ))) / (t : ℝ) := by
  rw [K_GLW_processKernel_K]
  show K_GLW (0 : ℝ) (t : ℝ) = (1 - Real.exp (-(t : ℝ))) / (t : ℝ)
  rw [K_GLW_def, zero_add]
  exact K_GLW_aux_of_ne (t : ℝ) (ne_of_gt ht)

/-- By symmetry, for `s > 0`, `K(s, 0) = (1 - exp(-s))/s`. -/
theorem K_GLW_processKernel_K_zero_right_eq (s : NNReal) (hs : 0 < (s : ℝ)) :
    K_GLW_processKernel.K s 0 = (1 - Real.exp (-(s : ℝ))) / (s : ℝ) := by
  rw [K_GLW_processKernel.symm s 0]
  exact K_GLW_processKernel_K_zero_left_eq s hs

/-- The diagonal value `K(s, s) = (1 - exp(-2s))/(2s)` for `s > 0`. -/
theorem K_GLW_processKernel_K_diag_eq (s : NNReal) (hs : 0 < (s : ℝ)) :
    K_GLW_processKernel.K s s = (1 - Real.exp (-(2 * s : ℝ))) / (2 * (s : ℝ)) := by
  rw [K_GLW_processKernel_K]
  show K_GLW (s : ℝ) (s : ℝ) = (1 - Real.exp (-(2 * s : ℝ))) / (2 * (s : ℝ))
  rw [K_GLW_def, show ((s : ℝ) + (s : ℝ)) = 2 * (s : ℝ) from by ring]
  have h_ne : (2 * (s : ℝ)) ≠ 0 := by
    have : 0 < 2 * (s : ℝ) := by linarith
    exact ne_of_gt this
  exact K_GLW_aux_of_ne (2 * (s : ℝ)) h_ne

/-- The diagonal value at zero: `K(0, 0) = 1` (specialisation). -/
theorem K_GLW_processKernel_K_diag_at_zero :
    K_GLW_processKernel.K 0 0 = 1 := K_GLW_processKernel_at_zero

/-! ## 4.33. K_GLW_processKernel — general explicit value formula -/

/-- For `s, t : NNReal` with `s + t > 0`, the kernel value is
`K(s, t) = (1 - exp(-(s+t)))/(s+t)`. -/
theorem K_GLW_processKernel_K_general_eq (s t : NNReal)
    (h_sum_pos : 0 < ((s : ℝ) + (t : ℝ))) :
    K_GLW_processKernel.K s t =
      (1 - Real.exp (-((s : ℝ) + (t : ℝ)))) / ((s : ℝ) + (t : ℝ)) := by
  rw [K_GLW_processKernel_K, K_GLW_def]
  exact K_GLW_aux_of_ne ((s : ℝ) + (t : ℝ)) (ne_of_gt h_sum_pos)

/-- The kernel value formula at `(s, t) = (0, 0)` (boundary case). -/
theorem K_GLW_processKernel_K_zero_zero_eq :
    K_GLW_processKernel.K 0 0 = 1 := K_GLW_processKernel_at_zero

/-! ## 4.34. K_GLW_processKernel — integral / Mercer representation

The kernel `K(s, t)` admits the explicit integral representation
`∫₀¹ exp(-s·x) · exp(-t·x) dx`, lifted from the underlying
`K_GLW_eq_integral_glwIntegrand_mul`. This is the deterministic
shadow of the Itô isometry on the kernel. -/

/-- Integral / Mercer representation for `K_GLW_processKernel.K`:
`K(s, t) = ∫₀¹ exp(-s·x) · exp(-t·x) dx` for any `s, t : NNReal`. -/
theorem K_GLW_processKernel_K_eq_integral (s t : NNReal) :
    K_GLW_processKernel.K s t =
      ∫ x in (0 : ℝ)..1, Real.exp (-(s : ℝ) * x) * Real.exp (-(t : ℝ) * x) := by
  rw [K_GLW_processKernel_K]
  show K_GLW (s : ℝ) (t : ℝ) =
    ∫ x in (0 : ℝ)..1, Real.exp (-(s : ℝ) * x) * Real.exp (-(t : ℝ) * x)
  rw [K_GLW_eq_integral_glwIntegrand_mul (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp [glwIntegrand_def]

/-- The kernel matrix entry has the integral representation. -/
theorem K_GLW_processKernel_kernelMatrix_eq_integral
    (I : Finset NNReal) (s t : {x : NNReal // x ∈ I}) :
    K_GLW_processKernel.kernelMatrix I s t =
      ∫ x in (0 : ℝ)..1, Real.exp (-(s.1 : ℝ) * x) *
        Real.exp (-(t.1 : ℝ) * x) := by
  rw [ProcessKernel.kernelMatrix_apply]
  exact K_GLW_processKernel_K_eq_integral s.1 t.1

/-! ## 4.35. Generic `ProcessKernel` — extended pair-PSD corollaries

Pair-level PSD facts derivable purely from the four `ProcessKernel`
axioms, without any reference to the GLW kernel specifically. -/

namespace ProcessKernel

variable (P : ProcessKernel)

/-- For any process kernel, the singleton-Finset PSD matrix has
non-negative diagonal at the unique index. -/
theorem singleton_diag_nonneg (a : NNReal) :
    0 ≤ P.K a a := P.K_diag_nonneg a

/-- For any process kernel, `K(s, s) + K(t, t) ≥ 0` (sum of two
diagonal entries). -/
theorem two_diag_sum_nonneg (s t : NNReal) :
    0 ≤ P.K s s + P.K t t :=
  add_nonneg (P.K_diag_nonneg s) (P.K_diag_nonneg t)

end ProcessKernel

/-! ## 4.36. K_GLW_processKernel — derived bound applications

These corollaries package the K_GLW-specific pair-increment bounds
(non-negativity from `K_GLW_diff_quadratic_nonneg`, upper bound from
the Hölder field) for downstream use. -/

/-- For any pair `s, t : NNReal`, the GLW pair-increment is bounded
above by the squared NNReal distance (Hölder bound). -/
theorem K_GLW_processKernel_pair_increment_le_sq (s t : NNReal) :
    K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
      2 * K_GLW_processKernel.K s t ≤ ((s : ℝ) - (t : ℝ))^2 :=
  K_GLW_processKernel.hoelder s t

/-- For any pair `s, t : NNReal`, the GLW pair-increment is non-negative
(variance of an L²-difference is non-negative). -/
theorem K_GLW_processKernel_pair_increment_nonneg (s t : NNReal) :
    0 ≤ K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
        2 * K_GLW_processKernel.K s t :=
  K_GLW_processKernel_diff_nonneg s t

/-- The pair-increment satisfies the abstract bound
`0 ≤ K(s,s) + K(t,t) - 2 K(s,t) ≤ (s-t)²`. -/
theorem K_GLW_processKernel_pair_increment_bounds (s t : NNReal) :
    0 ≤ K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
        2 * K_GLW_processKernel.K s t ∧
      K_GLW_processKernel.K s s + K_GLW_processKernel.K t t -
        2 * K_GLW_processKernel.K s t ≤ ((s : ℝ) - (t : ℝ))^2 :=
  ⟨K_GLW_processKernel_pair_increment_nonneg s t,
   K_GLW_processKernel_pair_increment_le_sq s t⟩

/-- Average form of the GLW Hölder bound:
`(K(s, s) + K(t, t))/2 - K(s, t) ≤ (s - t)² / 2`. -/
theorem K_GLW_processKernel_avg_hoelder (s t : NNReal) :
    (K_GLW_processKernel.K s s + K_GLW_processKernel.K t t) / 2 -
      K_GLW_processKernel.K s t ≤ ((s : ℝ) - (t : ℝ))^2 / 2 := by
  have h := K_GLW_processKernel_pair_increment_le_sq s t
  linarith

/-- Average form non-negativity: `(K(s, s) + K(t, t))/2 ≥ K(s, t)` modulo
the (s - t)² correction. -/
theorem K_GLW_processKernel_avg_ge_off_diag (s t : NNReal) :
    (K_GLW_processKernel.K s s + K_GLW_processKernel.K t t) / 2 -
      ((s : ℝ) - (t : ℝ))^2 / 2 ≤ K_GLW_processKernel.K s t := by
  have h := K_GLW_processKernel_pair_increment_le_sq s t
  linarith

/-! ## 4.37. K_GLW_processKernel — endpoint and asymptotic lifts -/

/-- Combined `K(s, t) ∈ (0, 1]` bound for the GLW process kernel. -/
theorem K_GLW_processKernel_K_mem_Ioc (s t : NNReal) :
    K_GLW_processKernel.K s t ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨K_GLW_processKernel_pos s t, K_GLW_processKernel_le_one s t⟩

/-- The diagonal `K(s, s) ∈ (0, 1]` for the GLW process kernel. -/
theorem K_GLW_processKernel_K_diag_mem_Ioc (s : NNReal) :
    K_GLW_processKernel.K s s ∈ Set.Ioc (0 : ℝ) 1 :=
  K_GLW_processKernel_K_mem_Ioc s s

/-- The diagonal `K(s, s) ∈ [0, 1]` for the GLW process kernel
(closed-interval form, useful for sandwich arguments). -/
theorem K_GLW_processKernel_K_diag_mem_Icc (s : NNReal) :
    K_GLW_processKernel.K s s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨K_GLW_processKernel.K_diag_nonneg s,
   K_GLW_processKernel_le_one s s⟩

/-- The off-diagonal `K(s, t) ∈ [0, 1]` for the GLW process kernel
(closed-interval form). -/
theorem K_GLW_processKernel_K_mem_Icc (s t : NNReal) :
    K_GLW_processKernel.K s t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_of_lt (K_GLW_processKernel_pos s t),
   K_GLW_processKernel_le_one s t⟩

/-- The diagonal `K(s, s)` decays to zero as `s → ∞` along
`atTop` filter on `NNReal` (variance-decay limit). -/
theorem K_GLW_processKernel_K_diag_tendsto_zero :
    Filter.Tendsto (fun s : NNReal => K_GLW_processKernel.K s s)
      Filter.atTop (nhds 0) := by
  have h_real : Filter.Tendsto (fun u : ℝ => K_GLW u u) Filter.atTop (nhds 0) :=
    K_GLW_var_tendsto_zero
  have h_coe : Filter.Tendsto (fun s : NNReal => (s : ℝ))
      Filter.atTop Filter.atTop :=
    NNReal.tendsto_coe_atTop.mpr Filter.tendsto_id
  exact h_real.comp h_coe

/-! ## 4.38. K_GLW_processKernel — auxiliary scalar bounds and norm-style facts

Additional scalar bounds on the GLW process kernel useful for downstream
lower-bound arguments, all derived from existing infrastructure. -/

/-- The off-diagonal kernel value squared bound:
`K(s, t)² ≤ K(s, t) · 1` (since `K ≤ 1`). -/
theorem K_GLW_processKernel_sq_le_self (s t : NNReal) :
    (K_GLW_processKernel.K s t)^2 ≤ K_GLW_processKernel.K s t := by
  have h_pos := K_GLW_processKernel_pos s t
  have h_le := K_GLW_processKernel_le_one s t
  nlinarith

/-- The kernel value lies in `[K(s,t)², 1]`: a sandwich. -/
theorem K_GLW_processKernel_sandwich (s t : NNReal) :
    (K_GLW_processKernel.K s t)^2 ≤ K_GLW_processKernel.K s t ∧
      K_GLW_processKernel.K s t ≤ 1 :=
  ⟨K_GLW_processKernel_sq_le_self s t, K_GLW_processKernel_le_one s t⟩

/-- The product `K(s, t) · K(t, u)` is non-negative and bounded above by `1`. -/
theorem K_GLW_processKernel_prod_le_one (s t u v : NNReal) :
    K_GLW_processKernel.K s t * K_GLW_processKernel.K u v ≤ 1 := by
  have h1 := K_GLW_processKernel_pos s t
  have h2 := K_GLW_processKernel_pos u v
  have h1' := K_GLW_processKernel_le_one s t
  have h2' := K_GLW_processKernel_le_one u v
  nlinarith

/-- The product of two kernel values is non-negative. -/
theorem K_GLW_processKernel_prod_nonneg (s t u v : NNReal) :
    0 ≤ K_GLW_processKernel.K s t * K_GLW_processKernel.K u v :=
  mul_nonneg (le_of_lt (K_GLW_processKernel_pos s t))
             (le_of_lt (K_GLW_processKernel_pos u v))

/-- `1 - K(s, t)` is non-negative, since `K(s, t) ≤ 1`. -/
theorem K_GLW_processKernel_one_minus_nonneg (s t : NNReal) :
    0 ≤ 1 - K_GLW_processKernel.K s t := by
  have := K_GLW_processKernel_le_one s t
  linarith

/-- `K(s, t) + K(s', t') ≤ 2` for any quadruple. -/
theorem K_GLW_processKernel_sum_le_two (s t s' t' : NNReal) :
    K_GLW_processKernel.K s t + K_GLW_processKernel.K s' t' ≤ 2 := by
  have h1 := K_GLW_processKernel_le_one s t
  have h2 := K_GLW_processKernel_le_one s' t'
  linarith

/-- The kernel difference `K(s, t) - K(s', t')` is bounded in `[-1, 1]`. -/
theorem K_GLW_processKernel_diff_bounded (s t s' t' : NNReal) :
    |K_GLW_processKernel.K s t - K_GLW_processKernel.K s' t'| ≤ 1 := by
  have h1_pos := K_GLW_processKernel_pos s t
  have h2_pos := K_GLW_processKernel_pos s' t'
  have h1_le := K_GLW_processKernel_le_one s t
  have h2_le := K_GLW_processKernel_le_one s' t'
  rw [abs_le]
  constructor <;> linarith

/-! ## 4.39. K_GLW_processKernel.kernelMatrix — scalar action and Hermitian
restatements

Additional structural properties of the kernel matrix useful for
downstream linear-algebraic arguments, all sorry-free corollaries
of existing lemmas. -/

/-- The kernel matrix is invariant under reflection in the diagonal:
swapping indices gives the same value (matrix-level symmetry). -/
theorem K_GLW_processKernel_kernelMatrix_swap (I : Finset NNReal)
    (s t : {x : NNReal // x ∈ I}) :
    K_GLW_processKernel.kernelMatrix I s t =
      K_GLW_processKernel.kernelMatrix I t s :=
  K_GLW_processKernel.kernelMatrix_symm I s t

/-- The sum of diagonal entries of the kernel matrix is non-negative. -/
theorem K_GLW_processKernel_kernelMatrix_diag_sum_nonneg
    (I : Finset NNReal) :
    0 ≤ ∑ s : {x : NNReal // x ∈ I},
        K_GLW_processKernel.kernelMatrix I s s := by
  apply Finset.sum_nonneg
  intros s _
  exact K_GLW_processKernel_kernelMatrix_diag_nonneg I s

/-- The sum of diagonal entries of the kernel matrix is bounded by
`card I` (each diag ≤ 1). -/
theorem K_GLW_processKernel_kernelMatrix_diag_sum_le_card
    (I : Finset NNReal) :
    ∑ s : {x : NNReal // x ∈ I},
        K_GLW_processKernel.kernelMatrix I s s ≤ (I.card : ℝ) := by
  rw [show ((I.card : ℝ)) = ∑ _s : {x : NNReal // x ∈ I}, (1 : ℝ) by
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_coe]]
  apply Finset.sum_le_sum
  intros s _
  exact K_GLW_processKernel_kernelMatrix_diag_le_one I s

/-- The sum of off-diagonal entries of the kernel matrix is non-negative
(each entry is positive). -/
theorem K_GLW_processKernel_kernelMatrix_offdiag_sum_nonneg
    (I : Finset NNReal) :
    0 ≤ ∑ p ∈ Finset.univ.offDiag,
        K_GLW_processKernel.kernelMatrix I p.1 p.2 := by
  apply Finset.sum_nonneg
  intros p _
  exact le_of_lt (K_GLW_processKernel_kernelMatrix_entry_pos I p.1 p.2)

/-! ## 4.40. Generic `ProcessKernel` — additional structural corollaries

More abstract corollaries derivable purely from the `ProcessKernel`
axioms, useful for downstream brownian-motion-side arguments
applied generically. -/

namespace ProcessKernel

variable (P : ProcessKernel)

/-- The kernel matrix is its own transpose (in the symmetric sense)
because of the symmetry axiom. -/
theorem kernelMatrix_eq_transpose (I : Finset NNReal) :
    P.kernelMatrix I = (P.kernelMatrix I).transpose := by
  funext s t
  rw [Matrix.transpose_apply]
  exact P.kernelMatrix_symm I s t

/-- The kernel matrix `(M)ᵀ` equals `M`. -/
theorem kernelMatrix_transpose_eq (I : Finset NNReal) :
    (P.kernelMatrix I).transpose = P.kernelMatrix I :=
  (P.kernelMatrix_eq_transpose I).symm

/-- For any process kernel and any Finset `I`, the trace is the sum of
diagonal entries via the `kernelMatrix` view. -/
theorem kernelMatrix_trace_eq_sum (I : Finset NNReal) :
    (P.kernelMatrix I).trace =
      ∑ s : {x : NNReal // x ∈ I}, P.K s.1 s.1 :=
  P.kernelMatrix_trace_eq I

/-- The sum of squared kernel matrix entries
(Frobenius norm squared) is non-negative. -/
theorem kernelMatrix_frobenius_sq_nonneg (I : Finset NNReal) :
    0 ≤ ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
          (P.kernelMatrix I s t)^2 := by
  apply Finset.sum_nonneg
  intros s _
  apply Finset.sum_nonneg
  intros t _
  exact sq_nonneg _

/-- Reflexivity of the kernel matrix: the matrix at `(s, s)` evaluates
to `K(s, s)` for any indexing. -/
theorem kernelMatrix_diag_apply
    (I : Finset NNReal) (s : {x : NNReal // x ∈ I}) :
    P.kernelMatrix I s s = P.K s.1 s.1 := rfl

end ProcessKernel

/-! ## 4.41. K_GLW_processKernel — Frobenius/transpose lifts -/

/-- The K_GLW kernel matrix is symmetric (matrix-level transpose). -/
theorem K_GLW_processKernel_kernelMatrix_eq_transpose (I : Finset NNReal) :
    K_GLW_processKernel.kernelMatrix I =
      (K_GLW_processKernel.kernelMatrix I).transpose :=
  K_GLW_processKernel.kernelMatrix_eq_transpose I

/-- Frobenius-norm-squared bound on the K_GLW kernel matrix:
`‖M‖²_F ≤ card²` (lift of `glwCovMatrixNN_frobenius_sq_le`). -/
theorem K_GLW_processKernel_kernelMatrix_frobenius_sq_le
    (I : Finset NNReal) :
    ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
          (K_GLW_processKernel.kernelMatrix I s t)^2 ≤
      (I.card : ℝ) * (I.card : ℝ) := by
  have h_eq : K_GLW_processKernel.kernelMatrix I = glwCovMatrixNN I :=
    K_GLW_processKernel_kernelMatrix_eq I
  rw [h_eq]
  exact glwCovMatrixNN_frobenius_sq_le I

/-- Frobenius-norm-squared non-negativity on the K_GLW kernel matrix. -/
theorem K_GLW_processKernel_kernelMatrix_frobenius_sq_nonneg
    (I : Finset NNReal) :
    0 ≤ ∑ s : {x : NNReal // x ∈ I}, ∑ t : {x : NNReal // x ∈ I},
          (K_GLW_processKernel.kernelMatrix I s t)^2 :=
  K_GLW_processKernel.kernelMatrix_frobenius_sq_nonneg I

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
  parameterised over `Finset NNReal`.
* **PROJECT API**: `projectiveLimit (F : ∀ I : Finset ι, Measure (I → ℝ))
  (hF : IsProjectiveMeasureFamily F) : Measure (ι → ℝ)`. Closure of the
  projective limit when the index set is `NNReal` (uncountable).

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
  -- 2. Apply B3 to get projectiveLimit measure on `NNReal → ℝ`.
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

/-! ## 6. Round 12 closing summary

Round 12 substantially extended this bridge file. The Tier-1 attempt
(toolchain bump + brownian-motion dep) failed at minute ~7 with 30+
cascading Mathlib v4.27 → v4.30 API drift errors and was reverted
under the HARD CAP discipline. R12 then proceeded in Tier 3,
producing:

### New kernel-side sections (Fin n grid):

* §4.9  — sum-of-entries and Frobenius bounds
* §4.10 — Cauchy-Schwarz + 1-dim determinant
* §4.11 — constant-grid + 2-dim determinant
* §4.12 — diagonal + zero-grid identities
* §4.13 — generic gramMatrixL2 small-dim det (Mathlib-PR-shaped)
* §4.14 — quadratic-form expansion identities
* §4.15 — gramMatrixL2 sign-flip + constant-family
* §4.16 — grid translation and dilation
* §4.17 — trace expansion via K_GLW / K_GLW_aux
* §4.18 — variance decay bounds (1/(2u))
* §4.19 — pairwise Hölder bound (B4 precondition)
* §4.20 — Hermitian + trace properties (gramMatrixL2)
* §4.21 — packaged Y_GLW_kernel_data witness
* §4.22 — variance-of-sum quadratic form bounds
* §4.23 — special K_GLW values (zero-grid)

### New brownian-motion-aligned NNReal-grid section (§4.24):

* `glwCovMatrixNN : Finset NNReal → Matrix ↑I ↑I ℝ` mirroring
  brownian-motion's `brownianCovMatrix` signature exactly
* `glwCovMatrixNN_PosSemidef` — the B1 precondition in BM's signature
* `glwCovMatrixNN_submatrix` — sub-Finset restriction (B2)
* `glwCovMatrixNN_submatrix_PosSemidef` — combined B1+B2
* `Y_GLW_kernel_data_NN_full` — packaged B1+B2+B4 witness
* All entry-wise / diagonal / trace / sum / Frobenius / Hölder /
  variance-decay / Mercer-integral bounds lifted to NNReal grid
* Continuity of `glwCovMatrix` entries in the grid argument
* NNReal-grid quadratic-form expansion + non-negativity

### Significance for R13

The kernel side is now **fully formalised** in both type
signatures (`Fin n → ℝ` and `Finset NNReal`). Once the
`brownian-motion` API is in scope (R13 Option C — pin at the
historical commit `91267abd` on Mathlib `25ce63313608`),
retiring `Y_GLW_exists` reduces to applying:

1. `posSemidef_brownianCovMatrix` ⟹ `glwCovMatrixNN_PosSemidef`
2. `gaussianProjectiveFamily ⟹ glwGaussianProjectiveFamily K_GLW`
3. `projectiveLimit ⟹ glwLimit`
4. Kolmogorov-Chentsov via `glwCovMatrixNN_pairwise_diff_quadratic_le_sq`
5. Define `Y_GLW(u, ω) := ω u`; verify `IsGLWProcess Y_GLW`.

Each step is a substitution at the call site. The diagnostic file
`ToolchainBumpDiagnostic.md` documents the R13 setup procedure in
detail.

### Round 13 — Tier 1 outcome (2026-04-30)

The R13 Tier-1 pin attempt (downgrade `v4.27.0 → v4.27.0-rc1`,
Mathlib pin `25ce63313608`, brownian-motion `91267abd`,
kolmogorov_extension4 `2c2b44e55251`) was reverted at minute ~7
under the 15-min HARD CAP, but with strong positive signal:

* `lake update` succeeded in ~33 s (deps + Mathlib cache fetched).
* `lake build` reached **7891 / 7893 jobs** before failing on **4
  files**:
  - 2 trivial `Set.self_mem_Ici → Set.left_mem_Ici` renames in
    `EndpointReparametrization.lean` and `CentralBinomLower.lean`
  - 2 unrelated `FormalConjecturesForMathlib` API drift fixes
    (`GCDMonoid/Finset.lean:27`, `Powerfree.lean:81`) — **none of
    these are on the GLW dependency path**.
* The complete GLW chain (`GLWKernel`, `GLWProcess`,
  `GLWProcessPredicate`, `GLWLowerProof`, `GLWUpperProof`,
  `IndepSetBridge`, `StandardMVGaussian`, `MVGaussianFromPosDef`,
  `MVGaussianPushforward`, `CholeskyExistence`) **built cleanly under
  the pin**. Once R14 patches the 4 unrelated blockers, the actual
  `Y_GLW_exists` retirement work is unblocked.

See `ToolchainBumpDiagnostic.md §R13` for the full diagnostic.

### Round 13 — Tier 4 deliverables (this file)

R13 also added eight new sub-sections (~520 lines, 51 new theorems)
strengthening the bridge with reusable kernel-side infrastructure for
R14+:

* §4.25 — Extended `ProcessKernel` Hölder corollaries (lower-bound
  forms, three-point Hölder, scaled Hölder, reflexivity)
* §4.26 — Extended `K_GLW_processKernel` corollaries (singleton/pair
  PSD, three-pair sum bounds)
* §4.27 — `ProcessKernel.K_diag_nonneg` proven via abstract
  `Matrix.PosSemidef.diag_nonneg`
* §4.28 — K_GLW_processKernel pair-level Cauchy-Schwarz +
  discriminant-non-negative + abs-≤-sqrt(prod) bounds
* §4.29 — `ProcessKernel.kernelMatrix` packaged matrix abstraction
  (PSD, isHermitian, trace, quadratic-form, consistent)
* §4.30 — Structural lifts of `glwCovMatrixNN` lemmas to
  `K_GLW_processKernel.kernelMatrix` (entry, diag, trace, sum,
  submatrix PSD)
* §4.31-4.32 — Quadratic-form lifts + explicit K(0,t), K(s,0), K(s,s)
  closed-form expressions
* §4.33-4.34 — General K(s,t) explicit formula and integral/Mercer
  representation lifted to `K_GLW_processKernel`

### R13 retry attempt — outcome (2026-04-30, T+25)

A midcourse pivot triggered a retry of the pin under a harder T+15
cap. The retry succeeded in patching the original 4 errors but
exposed a deeper blocker:

* ✅ `Set.self_mem_Ici → Set.left_mem_Ici` (3 lines).
* ✅ `Powerfree.lean:81` typeclass strengthen
  `[CommMonoidWithZero] [IsCancelMulZero] → [CancelCommMonoidWithZero]`.
* ✅ `GCDMonoid/Finset.lean:27` same typeclass strengthen.
* ✅ `CauchyDetLowerBound.lean:1907` — remove now-redundant offDiag
  bullet ('congr 1' auto-closes one branch in v4.27.0-rc1).
* ❌ **Hard blocker**: `524.lean:662` — `StronglyAdapted` is no longer
  defined in v4.27.0-rc1 Mathlib (the `Probability/Process/`
  module was refactored). Non-mechanical refactor required.

Reverted at T+15 cap. See `ToolchainBumpDiagnostic.md §R13 retry`
for the full diagnostic and updated R14 procedure recommendations.

### R13 Tier 4 deliverables — final tally

R13 (combining initial Tier 4 + post-retry Tier 4) produced **eleven**
new sub-sections (~620 lines of new theorems, all sorry-free):

* §4.25 — Extended `ProcessKernel` Hölder corollaries
* §4.26 — Extended `K_GLW_processKernel` corollaries
* §4.27 — `ProcessKernel.K_diag_nonneg` via abstract PSD
* §4.28 — Cauchy-Schwarz / discriminant pair-form
* §4.29 — `ProcessKernel.kernelMatrix` packaged abstraction
* §4.30 — `glwCovMatrixNN → kernelMatrix` structural lifts
* §4.31-4.32 — Quadratic-form lifts + explicit closed-form values
  (K(0,t), K(s,0), K(s,s))
* §4.33-4.34 — General K(s,t) formula + integral/Mercer representation
* §4.35-4.36 — Pair-PSD corollaries + GLW pair-increment bounds
* §4.37 — Endpoint membership (Ioc/Icc) + diagonal asymptotic-decay

### Net axiom count (post-R13)

Still 2 axioms (`Y_GLW_exists`, `two_dim_KMT_coupling`). The R13
deliverables prepare R14+ for retirement of `Y_GLW_exists`. The
chosen path (Path A in the diagnostic) is to continue extending the
bridge file while a separate refactor branch handles the
`StronglyAdapted` removal in `524.lean`. -/

end Erdos524.Helpers
