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
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Phase 2 Round 5/6 — Pushforward covariance for Cholesky

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
* Proves the headline `mvGaussian_pushforward_cov_eq` covariance theorem
  + its `realMatrixSqrt` specialisation. **PROVED (Round 6).**

Round 6 closed the Round 5 documented `sorry` on
`standardMVGaussianEuclidean_cov_eq_inner` using the Mathlib lemmas
`covarianceBilin_apply_pi`, `iIndepFun_pi`, and
`MeasurePreserving.variance_fun_comp`, decomposed into seven named
sub-lemmas (each ≤ 15 lines per the Round 6 hard rule).
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
  -- Lift `standardMVGaussian_memLp_two` via the equiv `(EuclideanSpace.equiv n ℝ).symm`,
  -- a continuous linear equiv hence a CLM, and apply `MemLp.continuousLinearMap_comp`.
  -- `id : EuclideanSpace ℝ n → EuclideanSpace ℝ n` composed with `equiv.symm` is just
  -- `equiv.symm`, which by CLM-comp on `MemLp id 2 standardMVGaussian` gives MemLp
  -- of `equiv.symm` w.r.t. standardMVGaussian. By memLp_map_measure_iff, this equals
  -- `MemLp id 2 (standardMVGaussian.map equiv.symm) = MemLp id 2 standardMVGaussianEuclidean`.
  unfold standardMVGaussianEuclidean
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  -- Goal: MemLp (id ∘ (equiv.symm)) 2 standardMVGaussian.
  -- = MemLp (fun x => (equiv.symm) x) 2 standardMVGaussian.
  -- Apply MemLp.continuousLinearMap_comp on standardMVGaussian_memLp_two
  -- with L := (EuclideanSpace.equiv n ℝ).symm.toContinuousLinearMap.
  have h_id : MemLp (id : (n → ℝ) → (n → ℝ)) 2 (standardMVGaussian n) :=
    standardMVGaussian_memLp_two
  have := MemLp.continuousLinearMap_comp h_id
    ((EuclideanSpace.equiv n ℝ).symm : (n → ℝ) →L[ℝ] EuclideanSpace ℝ n)
  exact this

/-! ## Standard MV Gaussian on EuclideanSpace has identity covariance

Round 6: this section closes the Round 5 documented `sorry`. The chain:

* `standardMVGaussianEuclidean n = (Measure.pi (fun _ => gaussianReal 0 1)).map (toLp 2)`
  by definitional unfolding (the canonical `EuclideanSpace.equiv` symm equals `toLp 2`).
* The Mathlib lemma `covarianceBilin_apply_pi` then expresses the covariance
  bilinear form as `∑ i, ∑ j, x i * y j * cov[ω ↦ ω i, ω ↦ ω j; Measure.pi]`.
* For `i = j`: `cov[X i, X i; μ] = Var[X i; μ] = Var[id; gaussianReal 0 1] = 1`,
  using `MeasurePreserving.variance_fun_comp` on `Function.eval i`.
* For `i ≠ j`: `cov[X i, X j; μ] = 0` by `IndepFun.covariance_eq_zero` and
  `iIndepFun_pi` (Mathlib): coordinates of a Pi-measure are independent.

The four supporting facts are split into named sub-lemmas to keep each
proof block ≤ 15 lines (Round 6 hard rule). -/

set_option linter.unusedSectionVars false in
/-- MemLp 2 for the i-th coordinate evaluation under the standard MV
Gaussian's product measure. Used by `covarianceBilin_apply_pi`. -/
theorem standardMVGaussian_eval_memLp_two (i : n) :
    MemLp (fun ω : n → ℝ => ω i) 2
      (Measure.pi (fun _ : n => gaussianReal 0 1)) := by
  have h_mp : MeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : n => gaussianReal 0 1)) (gaussianReal 0 1) :=
    measurePreserving_eval _ i
  exact (memLp_id_gaussianReal 2).comp_measurePreserving h_mp

set_option linter.unusedSectionVars false in
/-- Variance of the i-th coordinate under the standard MV Gaussian = 1.
Reduces via `MeasurePreserving.variance_fun_comp` to `variance_id_gaussianReal`. -/
theorem standardMVGaussian_var_eval_eq_one (i : n) :
    Var[fun ω : n → ℝ => ω i;
      Measure.pi (fun _ : n => gaussianReal 0 1)] = 1 := by
  have h_mp : MeasurePreserving (Function.eval i)
      (Measure.pi (fun _ : n => gaussianReal 0 1)) (gaussianReal 0 1) :=
    measurePreserving_eval _ i
  have h_var := h_mp.variance_fun_comp (μ := Measure.pi _)
    (f := (id : ℝ → ℝ)) measurable_id.aemeasurable
  -- LHS: Var[fun ω => id (eval i ω); μ] = Var[fun ω => ω i; μ].
  -- RHS: Var[id; gaussianReal 0 1] = 1.
  rw [show (fun ω : n → ℝ => ω i) = (fun ω => id (Function.eval i ω)) from rfl, h_var]
  rw [variance_id_gaussianReal]
  simp

set_option linter.unusedSectionVars false in
/-- Coordinate functions of a product measure are jointly independent. -/
theorem standardMVGaussian_iIndepFun_eval :
    iIndepFun (fun (i : n) (ω : n → ℝ) => ω i)
      (Measure.pi (fun _ : n => gaussianReal 0 1)) := by
  -- `iIndepFun_pi` with each `X i := id : ℝ → ℝ` gives the result.
  exact iIndepFun_pi (μ := fun _ : n => gaussianReal 0 1)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)

/-- For `i ≠ j`, the covariance of the i-th and j-th coordinate evaluations
under the standard MV Gaussian's product measure is `0`. -/
theorem standardMVGaussian_cov_eval_eq_zero_of_ne {i j : n} (hij : i ≠ j) :
    cov[fun ω : n → ℝ => ω i, fun ω : n → ℝ => ω j;
      Measure.pi (fun _ : n => gaussianReal 0 1)] = 0 :=
  ((standardMVGaussian_iIndepFun_eval (n := n)).indepFun hij).covariance_eq_zero
    (standardMVGaussian_eval_memLp_two i) (standardMVGaussian_eval_memLp_two j)

/-- Diagonal: `cov[ω ↦ ω i, ω ↦ ω i; μ] = 1` (= variance under standard normal). -/
theorem standardMVGaussian_cov_eval_self_eq_one (i : n) :
    cov[fun ω : n → ℝ => ω i, fun ω : n → ℝ => ω i;
      Measure.pi (fun _ : n => gaussianReal 0 1)] = 1 := by
  rw [covariance_self (standardMVGaussian_eval_memLp_two i).aemeasurable]
  exact standardMVGaussian_var_eval_eq_one i

set_option linter.unusedSectionVars false in
/-- Pushforward identity: `standardMVGaussianEuclidean = (Measure.pi).map toLp`. -/
theorem standardMVGaussianEuclidean_eq_pi_map :
    standardMVGaussianEuclidean n =
      (Measure.pi (fun _ : n => gaussianReal 0 1)).map
        (fun ω : n → ℝ => WithLp.toLp 2 ω) := by
  -- `(EuclideanSpace.equiv n ℝ).symm = toLp 2` definitionally, so this is `rfl`.
  unfold standardMVGaussianEuclidean standardMVGaussian
  rfl

/-- Collapse the cov-double-sum to its diagonal. Off-diagonal terms vanish
by `cov_eval_eq_zero_of_ne`; diagonal terms reduce to `1` by `var_eval_eq_one`. -/
theorem standardMVGaussian_sum_cov_eval_eq_inner_real
    (u v : EuclideanSpace ℝ n) :
    ∑ i, ∑ j, u i * v j *
        cov[fun ω : n → ℝ => ω i, fun ω : n → ℝ => ω j;
          Measure.pi (fun _ : n => gaussianReal 0 1)] =
      ∑ i, u i * v i := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [standardMVGaussian_cov_eval_self_eq_one, mul_one]
  · intro j _ hji
    rw [standardMVGaussian_cov_eval_eq_zero_of_ne hji.symm, mul_zero]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

set_option linter.unusedSectionVars false in
/-- `inner ℝ u v = ∑ i, u i * v i` for `EuclideanSpace ℝ n`. -/
theorem euclidean_inner_eq_sum_mul (u v : EuclideanSpace ℝ n) :
    inner ℝ u v = ∑ i, u i * v i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- `⟪u i, v i⟫_ℝ = v i * u i = u i * v i` via `RCLike.inner_apply` + `mul_comm`.
  rw [RCLike.inner_apply]
  simp [mul_comm]

/-- Headline (Round 6): the standard MV Gaussian on `EuclideanSpace ℝ n`
has identity covariance bilinear form. Closes the Round 5 documented `sorry`. -/
theorem standardMVGaussianEuclidean_cov_eq_inner (u v : EuclideanSpace ℝ n) :
    covarianceBilin (standardMVGaussianEuclidean n) u v = inner ℝ u v := by
  rw [standardMVGaussianEuclidean_eq_pi_map]
  rw [covarianceBilin_apply_pi (fun i => standardMVGaussian_eval_memLp_two i)]
  rw [standardMVGaussian_sum_cov_eval_eq_inner_real]
  exact (euclidean_inner_eq_sum_mul u v).symm

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

Proof chain (all four steps closed by Round 6):
1. `covarianceBilin_map` (Mathlib): pushforward by a CLM `f` transforms
   the covariance via the adjoint:
     `covarianceBilin (μ.map f) u v = covarianceBilin μ (f.adjoint u) (f.adjoint v)`.
   (Requires `MemLp id 2 μ`, supplied by `standardMVGaussianEuclidean_memLp_two`.)
2. `(toEuclideanCLM L).adjoint = toEuclideanCLM Lᵀ` (real conjTranspose = transpose).
3. The standard MV Gaussian on `EuclideanSpace ℝ n` has identity covariance:
   `covarianceBilin standardMVGaussianEuclidean u v = ⟪u, v⟫` (Round 6).
4. Combine: `⟪Lᵀ u, Lᵀ v⟫ = ⟪u, L · Lᵀ · v⟫` via the adjoint identity again,
   using `map_mul` of `toEuclideanCLM` to write `L · Lᵀ` as CLM composition.
-/
theorem mvGaussian_pushforward_cov_eq (L : Matrix n n ℝ) (u v : EuclideanSpace ℝ n) :
    covarianceBilin (mvGaussianEuclideanFromMatrix L) u v =
      inner ℝ u (toEuclideanCLM (n := n) (𝕜 := ℝ) (L * Lᵀ) v) := by
  unfold mvGaussianEuclideanFromMatrix
  rw [covarianceBilin_map standardMVGaussianEuclidean_memLp_two
        ((toEuclideanCLM (n := n) (𝕜 := ℝ) L))]
  rw [toEuclideanCLM_adjoint]
  rw [standardMVGaussianEuclidean_cov_eq_inner]
  -- Goal: ⟪toEuclideanCLM Lᵀ u, toEuclideanCLM Lᵀ v⟫ = ⟪u, toEuclideanCLM (L * Lᵀ) v⟫.
  -- Use map_mul + adjoint move to identify these.
  have h_adj := toEuclideanCLM_adjoint L
  have h_swap_sym : (toEuclideanCLM (n := n) (𝕜 := ℝ) Lᵀ : EuclideanSpace ℝ n →L[ℝ]
      EuclideanSpace ℝ n) = ((toEuclideanCLM (n := n) (𝕜 := ℝ) L) :
        EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n).adjoint := h_adj.symm
  rw [show (toEuclideanCLM (n := n) (𝕜 := ℝ) Lᵀ) u =
        (((toEuclideanCLM (n := n) (𝕜 := ℝ) L) :
            EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n).adjoint) u from
      congrArg (· u) h_swap_sym]
  rw [ContinuousLinearMap.adjoint_inner_left]
  congr 1
  -- Goal: toEuclideanCLM L (toEuclideanCLM Lᵀ v) = toEuclideanCLM (L * Lᵀ) v.
  have h_map_mul : (toEuclideanCLM (n := n) (𝕜 := ℝ) (L * Lᵀ) :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) =
        ((toEuclideanCLM (n := n) (𝕜 := ℝ) L) *
          toEuclideanCLM (n := n) (𝕜 := ℝ) Lᵀ :
            EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
    map_mul _ L Lᵀ
  rw [h_map_mul]
  rfl

/-! ## Symmetric square root of identity is identity -/

theorem realMatrixSqrt_one : realMatrixSqrt (1 : Matrix n n ℝ) = 1 := by
  -- CFC.sqrt 1 = 1 because 1² = 1 and CFC.sqrt is the unique PosSemidef sqrt.
  unfold realMatrixSqrt
  exact CFC.sqrt_one

/-! ## Identity-matrix specialisation -/

theorem mvGaussian_pushforward_cov_one (u v : EuclideanSpace ℝ n) :
    covarianceBilin (mvGaussianEuclideanFromMatrix (1 : Matrix n n ℝ)) u v =
      inner ℝ u v := by
  rw [mvGaussian_pushforward_cov_eq]
  -- (1 : Matrix n n ℝ) * (1 : Matrix n n ℝ)ᵀ = 1.
  have h : (1 : Matrix n n ℝ) * (1 : Matrix n n ℝ)ᵀ = 1 := by
    rw [Matrix.transpose_one, mul_one]
  rw [h]
  -- toEuclideanCLM 1 = 1 (the identity CLM).
  have h_one : (toEuclideanCLM (n := n) (𝕜 := ℝ) 1 :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) = 1 := map_one _
  rw [show (toEuclideanCLM (n := n) (𝕜 := ℝ) 1) v =
        ((toEuclideanCLM (n := n) (𝕜 := ℝ) 1 :
          EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) : EuclideanSpace ℝ n → EuclideanSpace ℝ n) v
        from rfl]
  rw [h_one]
  rfl

/-! ## Specialisation to symmetric square root of PosSemidef M -/

theorem mvGaussian_realMatrixSqrt_pushforward_cov_eq
    {M : Matrix n n ℝ} (hM : M.PosSemidef) (u v : EuclideanSpace ℝ n) :
    covarianceBilin (mvGaussianEuclideanFromMatrix (realMatrixSqrt M)) u v =
      inner ℝ u (toEuclideanCLM (n := n) (𝕜 := ℝ) M v) := by
  rw [mvGaussian_pushforward_cov_eq]
  congr 1
  rw [realMatrixSqrt_mul_transpose hM]

end Erdos524.Helpers
