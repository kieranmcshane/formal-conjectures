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

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed

/-!
# Differentiability of `Matrix.det` and `Matrix.inv` (Phase A R40 infrastructure)

R40 introduces the differentiability scaffolding required by Phase A upper
Option B (Slepian + SF + BTIS via covariance interpolation). The two key
pieces are:

* `Matrix.det.hasFDerivAt` — the determinant of an `n × n` real matrix is
  differentiable as a function of its entries, with the explicit derivative
  given by the cofactor expansion (`d(det A) = tr(adj(A) · dA)`).
* `Matrix.PosDef.inv_hasFDerivAt` — the matrix inverse, restricted to
  positive-definite matrices, is differentiable, with derivative the
  standard Ring.inverse formula `d(A⁻¹) = -A⁻¹ · dA · A⁻¹`. This
  specialisation of `Mathlib`'s `hasFDerivAt_ringInverse` to
  `Matrix n n ℝ` requires only the `Matrix.PosDef → IsUnit` bridge.

## R40 status

Both theorems land in R40 as **TAG'd Stub signatures** with concrete
Mathlib API gap diagnostics:

* `Matrix.det.hasFDerivAt` (T2.1) — TAG'd `R40-T2.1-det-cofactor-route`.
  Path (α) cofactor / adjugate expansion is selected as the closure
  strategy. Estimated 100–200 LOC of careful Lean. R41–R44 closure target
  alongside the multivariate Gaussian density bridge.
* `Matrix.PosDef.inv_hasFDerivAt` (T2.2) — TAG'd
  `R40-T2.2-posdef-ringInverse-bridge`. Body invokes `hasFDerivAt_ringInverse`
  on the unit `(hM.isUnit).unit`, then bridges `Matrix.inv = Ring.inverse`
  via `nonsing_inv_eq_ringInverse`. The bridging step is mechanical
  (~30 LOC) but requires verifying `HasSummableGeomSeries (Matrix n n ℝ)` at
  the pin and the precise statement of `Matrix.nonsing_inv_eq_ringInverse`.

Both are **infrastructure only**; consumers (`PhaseAUpperBound.lean`,
`MultivariateGaussianCDF.lean`) keep their TAG'd Stubs at the Phase A
scaffold layer.

## Mathlib retirement path

When Mathlib gains a packaged `Matrix.det.hasFDerivAt` (likely via the
`MultilinearMap` or `LinearMap` route, or via `Polynomial.contDiff` on the
Leibniz expansion), this file's first theorem can be deleted and consumers
updated to import the upstream version. The PosDef inverse lemma is
unlikely to land in core Mathlib (too domain-specific); it stays here as a
Helpers-tier specialization.

See `Helpers/R40_T1_DifferentiabilityAudit.md` §1–§2 for the full audit.
-/

namespace Erdos524.Helpers

open Matrix

/-! ## T2.1 — `Matrix.det` differentiability -/

/-- **R40-T2.1 — Determinant is differentiable in matrix entries.**

For every `n × n` matrix `M : Matrix n n ℝ`, the determinant function
`A ↦ A.det` is Fréchet-differentiable at `M`, with derivative given by the
cofactor expansion (equivalently, the adjugate `adj(M) = M⁻¹ · det(M)` for
invertible `M`):

    `d(det A)|_{A = M} (H) = tr(adj(M) · H)`.

In Mathlib's normed-space language, the Fréchet derivative is the linear
map `H ↦ tr(adj(M) · H) : Matrix n n ℝ →L[ℝ] ℝ`.

**R40 status: TAG'd Stub.** The signature lands; the body is deferred to
R41–R44 alongside the rest of Phase A upper Option B closure work.

**Closure route (path α from R40-T1.1 audit):**

1. Express `det A = ∑_{σ ∈ Perm n} sign σ · ∏_i A i (σ i)` via
   `Matrix.det_apply'`.
2. Each summand is a polynomial of degree exactly `card n` in the entries
   of `A`.
3. Sum and product of differentiable functions is differentiable; identify
   the entry-extraction `A ↦ A i j` as the continuous linear projection
   `Matrix.entryLinearMap i j` (already differentiable).
4. Compute the derivative via the product rule and re-assemble into the
   adjugate / trace form.

**Mathlib gap diagnostic (concrete):**

* `Matrix.det.differentiable` — **not packaged**. Search at the pin
  (`mathlib4 @ 25ce63313608`) for `Matrix.det.*Differentiable`,
  `Matrix.det.*HasFDeriv`, `Matrix.det.*ContDiff` returns zero matches.
* `MultilinearMap.hasFDerivAt` — **not packaged**. Path (β) blocked by
  this absence; path (α) is the only available route at this pin.
* The polynomial expansion route uses `Matrix.det_apply'` (packaged) +
  `Matrix.entryLinearMap` (packaged) + standard differentiability
  combinators. The challenge is bookkeeping over `Equiv.Perm` rather than
  any conceptual gap.

**Tried alternatives:**

* `MultilinearMap.toContinuousLinearMap.hasFDerivAt` — does not exist;
  multilinear maps in Mathlib do not currently expose Fréchet derivative
  API.
* `Polynomial.eval.hasFDerivAt` — too narrow; the Leibniz expansion is
  multivariate polynomial, not univariate. Would need `MvPolynomial` API,
  also unpackaged for differentiability. -/
theorem Matrix.det.hasFDerivAt
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    ∃ L : Matrix n n ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun A : Matrix n n ℝ => A.det) L M := by
  -- TAG[R40-T2.1-det-cofactor-route] : ~100-200 LOC, Leibniz expansion
  -- + polynomial differentiability. Mathlib gap: no Matrix.det.hasFDerivAt
  -- in mathlib4 @ 25ce63313608. See R40_T1_DifferentiabilityAudit.md §1.
  -- Closure target: R41 (companion to T2.3 pushforward bridge).
  sorry

/-- **Convenience wrapper signature.** `Matrix.det` is differentiable at every matrix.
Follows from `Matrix.det.hasFDerivAt` via `HasFDerivAt.differentiableAt`,
once the appropriate `NormedAddCommGroup (Matrix n n ℝ)` instance is in scope
(via `open Matrix` and `Mathlib.Analysis.Matrix.Normed`).

R40 leaves the body wrapped in the same TAG'd Stub diagnostic as the
`hasFDerivAt` form: closure is gated on Path α body close in R41. -/
theorem Matrix.det.differentiable
    {n : Type*} [Fintype n] [DecidableEq n] :
    Differentiable ℝ (fun A : Matrix n n ℝ => A.det) := by
  -- TAG[R40-T2.1-det-cofactor-route] : derivable from
  -- `Matrix.det.hasFDerivAt` once the `NormedAddCommGroup (Matrix n n ℝ)`
  -- instance synthesis is set up (entry-wise sup norm). For R40 scaffold
  -- purposes the unbundled signature is what consumers (Slepian's
  -- comparison + multivariate-CDF differentiability) need.
  sorry

/-! ## T2.2 — `Matrix.inv` differentiability on PosDef matrices -/

/-- **R40-T2.2 — Matrix inverse is differentiable on the PosDef cone.**

For every positive-definite `M : Matrix n n ℝ`, the inverse function
`A ↦ A⁻¹` is Fréchet-differentiable at `M`, with derivative the standard
`Ring.inverse` formula:

    `d(A⁻¹)|_{A = M} (H) = -M⁻¹ · H · M⁻¹`.

In Mathlib's normed-algebra language, this is the specialisation of
`hasFDerivAt_ringInverse` to `Matrix n n ℝ` units, restricted to the open
PosDef set.

**R40 status: TAG'd Stub.** The signature lands; body invokes
`hasFDerivAt_ringInverse` on `(hM.isUnit).unit`, then bridges
`Matrix.inv ↔ Ring.inverse` for invertible matrices. The bridge is
mechanical (~30 LOC) but resolves to several Mathlib lookups.

**Closure route:**

1. From `hM : M.PosDef`, derive `IsUnit M` via `Matrix.PosDef.isUnit`
   (or `M.det ≠ 0` + `Matrix.isUnit_iff_isUnit_det`).
2. Apply `hasFDerivAt_ringInverse (R := Matrix n n ℝ) (𝕜 := ℝ)
   (hM.isUnit.unit)` to get `HasFDerivAt Ring.inverse _ M`.
3. Bridge `Matrix.inv = Ring.inverse` on units via
   `Matrix.inv_eq_ringInverse` (or whatever Mathlib calls it at the pin).

**Mathlib gap diagnostic (concrete):**

* `Matrix.inv_eq_ringInverse` — **needs verification at pin**. There
  exists `Matrix.nonsing_inv` and `Ring.inverse`; the bridge lemma
  identifying them on units may already be packaged but is not directly
  searchable by name at the audit pin.
* `HasSummableGeomSeries (Matrix n n ℝ)` — required by
  `hasFDerivAt_ringInverse`'s class signature. Should hold for finite-dim
  normed algebras. **Needs verification at pin** (likely an instance via
  `instHasSummableGeomSeriesOfNormBoundedBelow` or similar).
* The PosDef set being **open** is provable (det > 0 is an open condition,
  and PosDef ↔ Hermitian + positive eigenvalues), but Mathlib does not
  package `Matrix.PosDef.isOpen` directly.

**Tried alternatives:**

* Direct `Matrix.inv` differentiability — no Mathlib API; this is the
  natural specialization.
* `MatrixGroup.GLn`-based route — `GLn` has continuous inverse, but
  Fréchet derivative on `GLn` doesn't lift cleanly to `Matrix n n ℝ`
  without the `Ring.inverse` bridge. -/
theorem Matrix.PosDef.inv_hasFDerivAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.PosDef) :
    ∃ L : Matrix n n ℝ →L[ℝ] Matrix n n ℝ,
      HasFDerivAt (fun A : Matrix n n ℝ => A⁻¹) L M := by
  -- **R41-T2.2 Full close.** Strategy:
  --   1. Activate `Matrix.linftyOpNormedRing` + `Matrix.linftyOpNormedAlgebra`
  --      as local instances (Mathlib doesn't make them global because there
  --      are several natural matrix-norm choices, but for Phase A upper
  --      Option B the L1-sup norm is the canonical one).
  --   2. `CompleteSpace (Matrix n n ℝ)` follows from finite-dimensionality;
  --      `HasSummableGeomSeries` is automatic via the
  --      `[NormedRing R] [CompleteSpace R]` instance at
  --      `Mathlib/Analysis/SpecificLimits/Normed.lean:278`.
  --   3. From `hM : M.PosDef` get `IsUnit M` via `hM.isUnit`, then the
  --      unit `u := hM.isUnit.unit : (Matrix n n ℝ)ˣ` with `↑u = M`.
  --   4. `hasFDerivAt_ringInverse u` gives
  --      `HasFDerivAt Ring.inverse (-mulLeftRight ℝ _ M⁻¹ M⁻¹) M`.
  --   5. **Bridge.** `Matrix.nonsing_inv_eq_ringInverse` gives the GLOBAL
  --      function equality `(·⁻¹ : Matrix n n ℝ → Matrix n n ℝ) = Ring.inverse`
  --      (works for non-units too: both return 0). Hence the FDeriv transfers
  --      directly via `funext` rewriting — no open-set / `eventuallyEq`
  --      argument needed.
  letI : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  -- The unit at M.
  set u : (Matrix n n ℝ)ˣ := hM.isUnit.unit with hu_def
  have hu_coe : (↑u : Matrix n n ℝ) = M := IsUnit.unit_spec hM.isUnit
  -- HasFDerivAt for Ring.inverse at the unit.
  have h_ring : HasFDerivAt (Ring.inverse : Matrix n n ℝ → Matrix n n ℝ)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) ↑u⁻¹ ↑u⁻¹) (↑u : Matrix n n ℝ) :=
    hasFDerivAt_ringInverse u
  -- Bridge: `Matrix.inv = Ring.inverse` GLOBALLY (`nonsing_inv_eq_ringInverse`).
  have h_func_eq : (fun A : Matrix n n ℝ => A⁻¹) = Ring.inverse := by
    funext A
    exact Matrix.nonsing_inv_eq_ringInverse (A := A)
  -- Transfer the FDeriv along the function equality + restate at M = ↑u.
  rw [h_func_eq, ← hu_coe]
  exact ⟨_, h_ring⟩

end Erdos524.Helpers
