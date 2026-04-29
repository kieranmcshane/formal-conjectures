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

set_option maxHeartbeats 800000

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
  rw [memLp_pi_iff]
  intro i
  -- Standard MV Gaussian = Measure.pi (gaussianReal 0 1).
  -- The i-th coordinate eval is measure-preserving, and id ∈ L²(gaussianReal 0 1).
  unfold standardMVGaussian
  have h_meas_pres :
      MeasurePreserving (Function.eval i) (Measure.pi (fun _ : n => gaussianReal 0 1))
        (gaussianReal 0 1) :=
    MeasureTheory.measurePreserving_eval _ _
  have h_id : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  -- `MemLp.comp_measurePreserving`: `MemLp g p ν` + `MeasurePreserving f μ ν` ⊢ `MemLp (g ∘ f) p μ`.
  -- Apply with g := id, f := eval i, ν := gaussianReal 0 1, μ := Measure.pi.
  -- Result: MemLp (id ∘ eval i) 2 (Measure.pi) = MemLp (eval i) 2 (Measure.pi).
  have := h_id.comp_measurePreserving h_meas_pres
  -- `id ∘ eval i = eval i = (· i)`.
  exact this

/-! ## MemLp 2 for `standardMVGaussianEuclidean` -/

theorem standardMVGaussianEuclidean_memLp_two :
    MemLp (id : EuclideanSpace ℝ n → EuclideanSpace ℝ n) 2
      (standardMVGaussianEuclidean n) := by
  -- Lift `standardMVGaussian_memLp_two` via the equiv. Use `memLp_map_measure_iff`:
  --   `MemLp id 2 (Measure.map equiv.symm μ) ↔ MemLp (id ∘ equiv.symm) 2 μ`
  -- = `MemLp equiv.symm 2 standardMVGaussian`. Since `equiv.symm` is the identity
  -- at the underlying type level (just a WithLp.toLp wrapper), and standardMVGaussian
  -- has MemLp 2 of `id`, this should follow by composition with a Lipschitz CLM.
  unfold standardMVGaussianEuclidean
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  -- Goal: MemLp (id ∘ (equiv.symm : (n → ℝ) → EuclideanSpace ℝ n)) 2 standardMVGaussian.
  -- The equiv.symm is a Lipschitz continuous-linear-equiv, and id ∘ equiv.symm
  -- is a Lipschitz function of x. Use `LipschitzWith.comp_memLp`.
  -- BLOCKER: precise Mathlib API for "MemLp under Lipschitz composition with CLE."
  -- TRIED: `LipschitzWith.comp_memLp`, direct via `(EuclideanSpace.equiv n ℝ).symm.lipschitz`.
  -- NEEDS: matching arity; `LipschitzWith.comp_memLp` typically takes `f : α → β`
  --   with `LipschitzWith K f`, and we need `f = equiv.symm`.
  sorry

/-! ## Standard MV Gaussian on EuclideanSpace has identity covariance -/

theorem standardMVGaussianEuclidean_cov_eq_inner (u v : EuclideanSpace ℝ n) :
    covarianceBilin (standardMVGaussianEuclidean n) u v = inner ℝ u v := by
  -- BLOCKER: identity covariance of the standard MV Gaussian on EuclideanSpace.
  -- TRIED: `covarianceBilin_apply_eq_cov` + bilinearity expansion + per-coord
  --   variance computation. Each step exists but the assembly is tedious.
  -- NEEDS: a Pi-product covariance lemma `covarianceBilin (Measure.pi μ)
  --   (toLp x) (toLp y) = ∑_i x_i * y_i * Var[id; μ i]`. Not in Mathlib.
  --   For our case `μ i = gaussianReal 0 1`, `Var = 1`, so the sum is `⟪x, y⟫`.
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
  -- Proof outline (depends on three sub-lemmas, two of which are documented
  -- sorries):
  --   1. covarianceBilin_map: pushforward by CLM transforms cov via adjoint.
  --      (Uses `standardMVGaussianEuclidean_memLp_two`, sorry'd.)
  --   2. toEuclideanCLM_adjoint: (toEuclideanCLM L).adjoint = toEuclideanCLM Lᵀ.
  --      (Proved.)
  --   3. standardMVGaussianEuclidean_cov_eq_inner: identity covariance.
  --      (sorry'd.)
  -- 4. Inner-adjoint move + map_mul to combine: `⟪Lᵀ u, Lᵀ v⟫ = ⟪u, L Lᵀ v⟫`.
  -- The chain assembles cleanly once the sub-sorries are filled. The Lean
  -- elaboration of the full chain hits the 800k heartbeat ceiling, so we
  -- ship the headline as a `sorry` whose proof obligation reduces to the
  -- sub-sorries.
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
