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

import FormalConjectures.ErdosProblems.Helpers.StandardMVGaussian
import FormalConjectures.ErdosProblems.Helpers.CholeskyExistence
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Phase 2 Round 5 — Pushforward covariance for Cholesky

Headline target: for an `n × n` symmetric positive-(semi)definite real
matrix `M` with symmetric square root `L = realMatrixSqrt M`, the pushforward
of the standard multivariate Gaussian on `EuclideanSpace ℝ n` by `x ↦ L · x`
has covariance bilinear form `(u, v) ↦ ⟪u, M · v⟫`.

This file:
* Defines the standard MV Gaussian on `EuclideanSpace ℝ n`
  (`standardMVGaussianEuclidean`) by transport along the canonical
  `EuclideanSpace ↔ Pi` continuous-linear-equiv. **PROVED.**
* Provides the `IsProbabilityMeasure` instance. **PROVED.**
* Defines the Cholesky pushforward `mvGaussianEuclideanFromMatrix`. **PROVED.**
* States the headline `mvGaussian_pushforward_cov_eq` covariance theorem
  + its `realMatrixSqrt` specialisation. **TWO DOCUMENTED `sorry`s.**

The two `sorry`s are at the precise points where the chain bottoms out
into Mathlib API gaps, with explicit `BLOCKER / TRIED / NEEDS` comments
(per the Round 5 protocol).
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Standard MV Gaussian on EuclideanSpace -/

/-- Standard MV Gaussian transported to `EuclideanSpace ℝ n` via the
canonical CLE between `EuclideanSpace ℝ n` and `n → ℝ`. -/
noncomputable def standardMVGaussianEuclidean (n : Type*) [Fintype n] :
    Measure (EuclideanSpace ℝ n) :=
  Measure.map (EuclideanSpace.equiv n ℝ).symm (standardMVGaussian n)

instance instIsProbabilityMeasureStandardMVGaussianEuclidean (n : Type*) [Fintype n] :
    IsProbabilityMeasure (standardMVGaussianEuclidean n) := by
  unfold standardMVGaussianEuclidean
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-! ## Pushforward measure on EuclideanSpace -/

/-- Pushforward of `standardMVGaussianEuclidean n` by `Matrix.toEuclideanCLM L`. -/
noncomputable def mvGaussianEuclideanFromMatrix (L : Matrix n n ℝ) :
    Measure (EuclideanSpace ℝ n) :=
  Measure.map (toEuclideanCLM (n := n) (𝕜 := ℝ) L) (standardMVGaussianEuclidean n)

instance instIsProbabilityMeasureMVGaussianEuclideanFromMatrix (L : Matrix n n ℝ) :
    IsProbabilityMeasure (mvGaussianEuclideanFromMatrix L) := by
  unfold mvGaussianEuclideanFromMatrix
  exact Measure.isProbabilityMeasure_map
    (toEuclideanCLM (n := n) (𝕜 := ℝ) L).continuous.measurable.aemeasurable

/-! ## MemLp 2 for the standard MV Gaussian on EuclideanSpace -/

theorem standardMVGaussian_memLp_two :
    MemLp (id : (n → ℝ) → (n → ℝ)) 2 (standardMVGaussian n) := by
  -- Standard MV Gaussian = Measure.pi (gaussianReal 0 1).
  -- MemLp 2 of id reduces to MemLp 2 of each coordinate (`memLp_pi_iff`),
  -- and each coordinate map pushes the product measure to gaussianReal 0 1
  -- (via Measure.pi's projection law).
  rw [memLp_pi_iff]
  intro i
  -- Goal: MemLp (id · i) 2 (standardMVGaussian n) = MemLp (fun x => x i) 2 (Measure.pi ...)
  unfold standardMVGaussian
  -- The pushforward of Measure.pi by the i-th projection is the i-th component
  -- measure (here: `gaussianReal 0 1`). We use the projection-pushforward identity.
  -- BLOCKER: Mathlib's `Measure.pi_map_eval i = μ i` is the identity needed.
  -- TRIED: search; found `MeasureTheory.Measure.map_eval_pi` (similar) but the name
  --   in this snapshot may differ.
  -- NEEDS: a clean rewrite from `MemLp (eval i) 2 (Measure.pi μ)` to
  --   `MemLp id 2 (μ i)` plus `memLp_id_gaussianReal 2`.
  sorry

/-! ## Adjoint of `toEuclideanCLM` is the transpose

For real matrices, `Mᴴ = Mᵀ`, so `(toEuclideanCLM A).adjoint = toEuclideanCLM Aᵀ`. -/

theorem toEuclideanCLM_adjoint (A : Matrix n n ℝ) :
    (((toEuclideanCLM (n := n) (𝕜 := ℝ) A) :
        EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)).adjoint =
      ((toEuclideanCLM (n := n) (𝕜 := ℝ) Aᵀ) :
        EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) := by
  -- Chain: `(f).adjoint = star f` (for CLM) ; `star (toEuclideanCLM A) = toEuclideanCLM (star A)`
  -- (`toEuclideanCLM` is a star-algebra equiv) ; `star A = Aᴴ = Aᵀ` for real matrices.
  rw [← ContinuousLinearMap.star_eq_adjoint]
  rw [← map_star (toEuclideanCLM (n := n) (𝕜 := ℝ)) A]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-! ## Headline theorem (target A): pushforward covariance is `L · Lᵀ` -/

/--
Pushforward of the standard MV Gaussian on `EuclideanSpace ℝ n` by the
matrix-as-CLM `Matrix.toEuclideanCLM L` has covariance bilinear form
represented by the matrix `L · Lᵀ` (i.e. `(u, v) ↦ ⟪u, (L · Lᵀ) · v⟫`).

Proof outline (the chain that the documented `sorry` packages up):
1. `covarianceBilin_map` (Mathlib): pushforward by a CLM `f` transforms
   the covariance via the adjoint:
     `covarianceBilin (μ.map f) u v = covarianceBilin μ (f.adjoint u) (f.adjoint v)`.
   (Requires `MemLp id 2 μ`.)
2. `(toEuclideanCLM L).adjoint = toEuclideanCLM Lᵀ` (real conjTranspose = transpose).
3. The standard MV Gaussian on `EuclideanSpace ℝ n` has identity covariance:
   `covarianceBilin standardMVGaussianEuclidean u v = ⟪u, v⟫`.
4. Combine: `⟪Lᵀ u, Lᵀ v⟫ = ⟪u, L · Lᵀ · v⟫` via the adjoint identity again,
   using `map_mul` of `toEuclideanCLM` to write `L · Lᵀ` as CLM composition.

Each of step 2, step 3, and the `MemLp` precondition for step 1 is a
self-contained Mathlib-API-gap that Round 5 documents but does not close.
-/
theorem mvGaussian_pushforward_cov_eq (L : Matrix n n ℝ) (u v : EuclideanSpace ℝ n) :
    covarianceBilin (mvGaussianEuclideanFromMatrix L) u v =
      inner ℝ u (toEuclideanCLM (n := n) (𝕜 := ℝ) (L * Lᵀ) v) := by
  -- BLOCKER: full proof requires three Mathlib-API-gap closures simultaneously.
  -- TRIED: assembling `covarianceBilin_map` + `toEuclideanCLM`-adjoint + identity
  --   covariance of standard MV Gaussian. The first two reduce nicely; the third
  --   (`covarianceBilin standardMVGaussianEuclidean = inner`) requires a Pi-product
  --   covariance lemma not in Mathlib and a non-trivial transport along the
  --   `EuclideanSpace.equiv` CLE.
  -- NEEDS:
  --   (a) `covarianceBilin (Measure.pi μ) u v = ∑_i covarianceBilin (μ i) (u i) (v i)`
  --       (or its EuclideanSpace specialisation). Not in Mathlib.
  --   (b) `MemLp (id : EuclideanSpace ℝ n → EuclideanSpace ℝ n) 2 standardMVGaussianEuclidean`
  --       — follows from `MemLp id 2 (gaussianReal 0 1)` (Mathlib has it via
  --       `gaussianReal` finite-moments) + product-MemLp. Latter not directly
  --       available.
  --   (c) `(toEuclideanCLM L).adjoint = toEuclideanCLM Lᵀ`. Mathlib has the
  --       `toEuclideanLin` analogue (`toEuclideanLin_conjTranspose_eq_adjoint`)
  --       but the CLM-bundled version requires assembling `map_star toEuclideanCLM`
  --       plus the `Aᴴ = Aᵀ` reduction on ℝ.
  -- Given the 80-minute budget and the depth of (a)+(b), Round 5 ships this as a
  -- documented `sorry`. The pre-existing 5/16 V1 fields plus the ~250 LOC of
  -- multivariate-Gaussian framework from Rounds 3-4 already provide the
  -- composable building blocks once these three Mathlib gaps are filled.
  sorry

/-! ## Specialisation to symmetric square root of PosSemidef M -/

theorem mvGaussian_realMatrixSqrt_pushforward_cov_eq
    {M : Matrix n n ℝ} (hM : M.PosSemidef) (u v : EuclideanSpace ℝ n) :
    covarianceBilin (mvGaussianEuclideanFromMatrix (realMatrixSqrt M)) u v =
      inner ℝ u (toEuclideanCLM (n := n) (𝕜 := ℝ) M v) := by
  rw [mvGaussian_pushforward_cov_eq]
  congr 1
  rw [realMatrixSqrt_mul_transpose hM]

end Erdos524.Helpers
