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

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Phase 2 Stage 1 — Symmetric square-root factorization for PosSemidef matrices

For a real PosSemidef matrix `M`, we expose its **symmetric** square root
`L := CFC.sqrt M` with the relations:

* `L * L = M`     (`CFC.sqrt_mul_sqrt_self`)
* `Lᵀ = L`        (`L` is Hermitian; on `ℝ` Hermitian = symmetric)
* `L * Lᵀ = M`    (combining the two)
* `L.PosSemidef`  (square root of PosSemidef is PosSemidef)

This is the matrix-square-root flavour of Cholesky — sufficient for Stage 5's
multivariate-Gaussian construction (which needs any `L` with `L · Lᵀ = M`,
not specifically lower-triangular). Lower-triangularity is unneeded
downstream and would require a heavier algorithmic Cholesky construction.
-/

namespace Erdos524.Helpers
open Matrix
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric square root of a real matrix (CFC sqrt). -/
noncomputable def realMatrixSqrt (M : Matrix n n ℝ) : Matrix n n ℝ := CFC.sqrt M

theorem realMatrixSqrt_mul_self {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    realMatrixSqrt M * realMatrixSqrt M = M := by
  have h_le : (0 : Matrix n n ℝ) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  exact CFC.sqrt_mul_sqrt_self M

theorem realMatrixSqrt_posSemidef (M : Matrix n n ℝ) :
    (realMatrixSqrt M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)

theorem realMatrixSqrt_isHermitian (M : Matrix n n ℝ) :
    (realMatrixSqrt M).IsHermitian :=
  (realMatrixSqrt_posSemidef M).isHermitian

/-- On `ℝ`, Hermitian = symmetric, so `Lᵀ = L`. -/
theorem realMatrixSqrt_transpose (M : Matrix n n ℝ) :
    (realMatrixSqrt M)ᵀ = realMatrixSqrt M :=
  (realMatrixSqrt_isHermitian M).eq

/-- The headline Cholesky-style identity: `L * Lᵀ = M`. -/
theorem realMatrixSqrt_mul_transpose {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    realMatrixSqrt M * (realMatrixSqrt M)ᵀ = M := by
  rw [realMatrixSqrt_transpose]
  exact realMatrixSqrt_mul_self hM

/-! ## Existence packaging

Bundles the four properties Stage 5 will use into one lemma. -/

theorem exists_real_matrix_sqrt {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    ∃ L : Matrix n n ℝ, L * Lᵀ = M ∧ Lᵀ = L ∧ L.PosSemidef :=
  ⟨realMatrixSqrt M,
   realMatrixSqrt_mul_transpose hM,
   realMatrixSqrt_transpose M,
   realMatrixSqrt_posSemidef M⟩

end Erdos524.Helpers
