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

## Status (R53 — γ-floor axiomatization of `Matrix.det.differentiable`)

* `Matrix.det.hasFDerivAt` (T2.1) — **TAG'd Stub** (unchanged from R40).
  TAG'd `R40-T2.1-det-cofactor-route`. Path (α) cofactor / adjugate
  expansion is selected as the closure strategy. Estimated 100–200 LOC
  of careful Lean. R55+ retirement target via Mathlib pin bump or
  in-tree close.
* `Matrix.det.differentiable` (T2.1 wrapper) — **Axiom (Axiom #8,
  γ-floor).** Per BACKGROUND.md post-R52 user-confirmed audit-redirect,
  R53 axiomatized this wrapper Stub to free R54-R58 mainline budget for
  retirements elsewhere. Zero Lean call sites at R53; future consumers
  (Slepian + multivariate-CDF differentiability chains) will use the
  original name. Retirement target R55-R59 post-gate via Mathlib pin
  bump (preferred) or 2-line consumer wrapping `Matrix.det.hasFDerivAt`
  Full close. See `AXIOM_INVENTORY.md` "Axiom #8" and
  `Helpers/Round53_T1_MatrixDetDifferentiableAxiomatization.md` for
  retirement plan + Claims Verification Table.
* `Matrix.PosDef.inv_hasFDerivAt` (T2.2) — **Full** (R41-T2.2 close,
  commit `1e30dda`). Body uses `hasFDerivAt_ringInverse` +
  `Matrix.nonsing_inv_eq_ringInverse` global function-equality bridge
  (~30 LOC).

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

/-- **R53 — γ-floor `Matrix.det.differentiable` axiomatization (post-R52
audit-redirect, user-confirmed γ floor + β R58 extension trajectory).**

For every finite-index `n` with decidable equality and every real
`n × n` matrix, the determinant function `A ↦ A.det : Matrix n n ℝ → ℝ`
is Fréchet-differentiable on the entire matrix space.

This is the **`Differentiable ℝ` wrapper** introduced in R40-T2.1
(TAG `R40-T2.1-det-cofactor-route`). The companion existential form
`Matrix.det.hasFDerivAt` (line 124-132 above) remains a TAG'd Stub for
now; R53 axiomatizes only the wrapper that downstream consumers
(Slepian's comparison + multivariate-CDF differentiability chains) will
import.

**Classical justification**: The determinant is a polynomial in the
matrix entries (Leibniz expansion
`det A = ∑_{σ ∈ Perm n} sign σ · ∏_i A i (σ i)`); polynomials in
finitely many real variables are smooth (in particular Fréchet
differentiable) on `Matrix n n ℝ` viewed as a finite-dimensional real
normed space. References: Lang (2002) "Algebra" Ch. XIII §5; Hörmander
(1990) "Analysis of Linear Partial Differential Operators" Ch. I §1.

**γ-floor strategy (R53)**: per BACKGROUND.md post-R52 user-confirmed
audit-redirect, the wrapper Stub is replaced with an axiom of identical
signature to free R54-R58 mainline budget for retirements elsewhere
(actual Q1c track close attempt, Track C/D parallel work, additional
Mathlib API drift fixes). This is debt-conversion: -1 sorry, +1 axiom,
items unchanged at the R52 gate (sorry-to-axiom swap), continuing the
R49 (axiom #6) + R51 (axiom #7) γ-floor pattern.

**Retirement target — R55-R59 post-gate** (two-path sub-plan):

1. *Mathlib pin bump (preferred).* Monitor Mathlib for landings of
   `Matrix.det.hasFDerivAt` (likely via the `MultilinearMap` or
   `LinearMap` route, or via `Polynomial.contDiff` on the Leibniz
   expansion). Post-`v4.27` toolchain bump may package this directly.
   The wrapper retires as a 2-line consumer:
   `Matrix.det.differentiable := fun M => (Matrix.det.hasFDerivAt
   M).differentiableAt.differentiable`.
2. *From-scratch closure (fallback).* Build the cofactor-route Full
   close in-tree over R55+ — ~100-200 LOC across Leibniz expansion
   (`Matrix.det_apply'`) + per-summand polynomial differentiability
   (`Matrix.entryLinearMap` + `Differentiable.prod_finset` +
   `Differentiable.sum_finset`) + assembly. The wrapper then closes by
   composition.

Retirement is **not required for the R52 gate** (gate measures item
count; +1 axiom / -1 sorry is a wash there). Strategic value of the
γ-floor axiomatization is the freed mainline budget for OTHER
retirements R54-R58.

**Consumers (Lean code)**: zero Lean call sites at R53. Future
consumers will appear when the Slepian's comparison + multivariate-CDF
differentiability chains (`Helpers/PhaseAUpperBound.lean`,
`Helpers/MultivariateGaussianCDF.lean`) reach their R55+ assembly
phases. The axiom is ready to serve those consumers under its original
name.

See `Helpers/Round53_T1_MatrixDetDifferentiableAxiomatization.md` for
the T1.1 Claims Verification Table + signature audit. -/
axiom Matrix.det.differentiable
    {n : Type*} [Fintype n] [DecidableEq n] :
    Differentiable ℝ (fun A : Matrix n n ℝ => A.det)

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
