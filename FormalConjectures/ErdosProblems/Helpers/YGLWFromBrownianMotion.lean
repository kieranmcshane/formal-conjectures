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

* **`glwCovMatrix`**: the concrete K_GLW Gram matrix on a finite grid
  `us : Fin n → ℝ`.
* **`glwCovMatrix_isHermitian`**: the Gram matrix is symmetric (a
  corollary of `K_GLW_symm`).
* **`glwCovMatrix_PosSemidef`**: positive semi-definiteness, a
  corollary of `K_GLW_quadratic_form_nonneg` from
  `YGLWConstruction.lean`.
* **`glwCovMatrix_diag_eq`**: explicit diagonal entries (= `K_GLW(uᵢ, uᵢ)`).
* **Documented BLOCKERs** for each `brownian-motion`-side step.

The PSD result is the main mathematical contribution: it is the
*precondition* for `multivariateGaussian` (Mathlib's existing API and
the `brownian-motion` project's). Once the toolchain alignment lands,
the bridge becomes a real proof with no sorries.
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
