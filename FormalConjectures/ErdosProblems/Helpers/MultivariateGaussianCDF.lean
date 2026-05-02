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

import BrownianMotion.Gaussian.MultivariateGaussian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis

/-!
# R35 — Multivariate-Gaussian half-space probability differentiability

This file provides the analytic backbone for Slepian's lemma in the GLW
Phase-A upper-bound chain. The key fact is that for a centered multivariate
Gaussian on `EuclideanSpace ℝ ι` with positive-definite covariance matrix
`Σ`, the half-space probability

  `F(Σ; x) := ℙ_{Z ∼ 𝒩(0, Σ)} (∀ i, Z i ≤ x i)`

is differentiable in `Σ` (entry-wise) with derivative expressible via
sub-marginal Gaussian densities. This lemma is the load-bearing analytic
ingredient for the Gaussian-interpolation proof of Slepian's lemma.

## R35 status

The signature is committed (T1.1). The body lands as a TAG'd diagnostic
documenting the concrete Mathlib API gaps that prevent full closure at the
current pin. See `Helpers/R35_T1_DiffLemmaAudit.md` for the full audit.

## R36 status — preserved as research scaffold (Path C3 election)

**Phase A took Option E redux Path C3 in R36** — `gao_li_wellner_small_ball_upper`
is now a user-defined `axiom` in `524.lean`, mirroring the R34 lower-side
regression. This file's differentiability lemma + the three Mathlib gaps it
named (`Matrix.det.differentiable`, `Matrix.PosDef.inv.differentiable`,
`multivariateGaussianPdf`) are **no longer on the active R37 trajectory**.
The signature + concrete-diagnostic body are preserved here as a research
scaffold for the (hypothetical) future round when one or more of those
upstream Mathlib gaps lands and the C3 axiomatization can be retired to
a `theorem` body via the chain laid out in `Helpers/PhaseAUpperBound.lean`.

The R35 audit (`Helpers/R35_T1_DiffLemmaAudit.md`) remains the authoritative
cost estimate (~250-400 LOC if all three pieces land in-tree). See
`Helpers/PhaseAR36Status.md` for the C3 path-decision rationale.

## Mathlib gaps (from `R35_T1_DiffLemmaAudit.md`)

The body needs three pieces, each a separate Mathlib gap:

1. **Determinant differentiability**: `Matrix.det : Matrix n n ℝ → ℝ` is
   smooth (it's a polynomial in entries). Mathlib has `Matrix.det.continuous`
   (`Topology/Instances/Matrix.lean:459`) but no `Matrix.det.differentiable`
   or `Matrix.det.contDiff`. The closure route is `Matrix.det_apply` +
   `Polynomial.contDiff` / `MultilinearMap.contDiff`, ~30-80 LOC of
   plumbing. Not yet packaged.

2. **Matrix inverse differentiability**: `(·)⁻¹ : (Matrix n n ℝ)ˣ → Matrix n n ℝ`
   is differentiable. Mathlib has the generic `HasFDerivAt Ring.inverse`
   (`Analysis/Calculus/FDeriv/Mul.lean:726`) for normed unital algebras
   but no `Matrix.PosDef`-specific specialization through
   `Matrix.GeneralLinearGroup`. ~50 LOC of structural plumbing.

3. **Multivariate Gaussian density formula**: brownian-motion's
   `multivariateGaussian` is defined as a square-root pushforward
   (`MultivariateGaussian.lean:160`); no explicit Lebesgue density is
   exposed. Building it requires the change-of-variables Jacobian formula
   `(2π)^(-n/2) |det Σ|^(-1/2) exp(-x^T Σ^(-1) x / 2)`, which depends on
   gaps 1 and 2 above plus a Jacobian-of-symmetric-square-root computation.

## R36+ retirement options

(a) Build the three Mathlib pieces above and close in-tree (~250-400 LOC).
(b) Pursue the bivariate sign-comparison route (`PhaseAUpperBound.lean`
    `gaussian_density_sign_comparison`, R17 stub) which avoids the
    multivariate CDF entirely.
(c) Axiomatize Slepian directly (Option E, +1 user-defined axiom),
    bypassing this entire chain.
-/

namespace Erdos524.Helpers.MultivariateGaussianCDF

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Local CDF object

We define the half-space probability for the centered multivariate Gaussian
with covariance `Σ` evaluated at threshold `x`. brownian-motion's
`multivariateGaussian` lives on `EuclideanSpace ℝ ι`; we package the
half-space `{z | ∀ i, z i ≤ x i}` and take its measure. -/

/-- Half-space (orthant) for thresholds `x : ι → ℝ` in `EuclideanSpace ℝ ι`.

Set of all `z` satisfying `z i ≤ x i` componentwise.
-/
def orthant (x : ι → ℝ) : Set (EuclideanSpace ℝ ι) :=
  {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i}

/-- The half-space (orthant-CDF) of the centered multivariate Gaussian on
`EuclideanSpace ℝ ι` with covariance `Σ`, evaluated at threshold vector `x`.

This is `ℙ(∀ i, Z i ≤ x i)` for `Z ∼ 𝒩(0, Σ)`. Returned as `ℝ` via
`Measure.real`. -/
noncomputable def multivariateGaussianOrthantCDF
    (S : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real (orthant x)

/-! ## Differentiability theorem (T1.1 signature, T2.1 body) -/

/-- **R35 T1.1 / T2.1 — Differentiability of the multivariate-Gaussian
half-space probability with respect to the covariance matrix.**

For a positive-definite covariance matrix `Σ` and threshold `x`, the
function `S ↦ multivariateGaussianOrthantCDF S x` is differentiable at `Σ`.

This is the analytic backbone of Slepian's lemma in the
covariance-interpolation form: writing `Σ_α = (1-α) Σ_X + α Σ_Y`, the
chain rule `dF/dα = ∑_{i,j} ∂F/∂Σ_{ij} · (Σ_Y - Σ_X)_{ij}` reduces sign
analysis of `dF/dα` to sign analysis of the entry-wise derivatives, which
are positive multiples of bivariate sub-marginal Gaussian densities.

**Body status (R35 T2.1):** TAG'd Mathlib gap. The classical proof uses
the Lebesgue density formula `ρ(z; Σ) = (2π)^(-n/2) (det Σ)^(-1/2)
exp(-z^T Σ^(-1) z / 2)` and differentiation under the integral sign. At
the current Mathlib pin, three load-bearing pieces are missing (see
`R35_T1_DiffLemmaAudit.md` §3-§5):

* `Matrix.det.differentiable` — Mathlib has only `Matrix.det.continuous`
  (`Topology/Instances/Matrix.lean:459`); polynomial expansion route via
  `Matrix.det_apply` + `MultilinearMap.contDiff` is unpackaged.
* `Matrix.PosDef.inv.differentiable` — generic `HasFDerivAt Ring.inverse`
  exists at `Analysis/Calculus/FDeriv/Mul.lean:726` but no
  `Matrix.GeneralLinearGroup` specialization at `Matrix.PosDef` covariances.
* `multivariateGaussianPdf` — brownian-motion's `multivariateGaussian`
  (line 160 of `BrownianMotion/Gaussian/MultivariateGaussian.lean`) is
  defined as a square-root pushforward; no explicit Lebesgue-density
  formula is exposed. The Jacobian-of-`CFC.sqrt`-pushforward derivation
  is itself unpackaged.

Tried alternatives (none viable):
* `multivariateGaussian_density_eq` — does not exist.
* `IsGaussian.density` — generic `IsGaussian` class has no extracted density.
* Diagonal-Σ product of `Real.gaussianReal` densities — covers only
  diagonal case; off-diagonal entries (which are exactly the ones being
  differentiated for Slepian) are inaccessible.
-/
theorem multivariateGaussianOrthantCDF_differentiable_wrt_covariance
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) :
    DifferentiableAt ℝ
      (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀ := by
  -- TAG[R35-T2.1-mathlib-gap-density] : missing density + det.diff + inv.diff
  -- See R35_T1_DiffLemmaAudit.md sections 3, 4, 5 for the three concrete
  -- Mathlib API gaps and the tried alternatives.
  --
  -- **R41-T1.1 audit refinement.** Path B per Grok R41 pre-flight Q2 ("chain
  -- on R40 Stubs as axiom-equivalent") is *partially* applicable: the R40
  -- stubs `Matrix.det.hasFDerivAt`, `Matrix.det.differentiable`, and
  -- `Matrix.PosDef.inv_hasFDerivAt` are real signatures and compose cleanly.
  -- HOWEVER, the R40-T2.3 stubs `multivariateGaussian_eq_lebesgue_withDensity`
  -- (MGE) and `multivariateGaussianOrthantCDF_eq_lebesgue_integral` (MGI) are
  -- `True := by trivial` placeholders, NOT real signatures. The diff-under-
  -- integral closure step requires MGI as a black-box rewrite to recast
  -- `multivariateGaussianOrthantCDF S x = ∫_{orthant} pdf(z; S) dz`; with
  -- MGI = True, that rewrite is impossible. R41-T1.1 audit
  -- (`R41_T1_ChainCompositionAudit.md`) documents this gap in detail.
  --
  -- **Closure prerequisites (R42 work):**
  --
  --   (P1) MGE `True` → real signature: `multivariateGaussian 0 S` admits
  --        `multivariateGaussianPdf S` as Lebesgue density (modulo the
  --        EuclideanSpace ↔ ι → ℝ identification). ~50 LOC.
  --   (P2) MGI `True` → real signature: orthantCDF S x equals the Lebesgue
  --        integral of `multivariateGaussianPdf S` over `orthant x`. ~30 LOC.
  --   (P3) `Matrix.det.hasFDerivAt` Stub → Full body. ~150-300 LOC (R40-T2.1
  --        cofactor route). Currently chainable as black-box.
  --
  -- **Closure body proof (R42 scope, ~400-700 LOC after P1+P2):**
  --
  --   (i)   Rewrite orthant CDF via MGI: orthantCDF S x = ∫_{orthant x} pdf(z; S) dz.
  --   (ii)  Pointwise smoothness of (S, z) ↦ pdf(z; S) via Matrix.det.diff +
  --         Matrix.PosDef.inv_hasFDerivAt + Real.exp.differentiable.
  --   (iii) Diff-under-integral via Lebesgue dominated convergence with a
  --         Σ-uniform integrable dominator on the orthant region.
  --   (iv)  Verify S.PosDef stays in an open neighborhood of S₀ (det > 0
  --         is open + Hermitian is closed + PSD-cone interior).
  sorry

/-! ## Entry-wise partial-derivative formula (R36+ scope, signature here for
documentation) -/

/-! ### R41 — real-signature upgrade for the off-diagonal partial derivative

R40-T2.3 left this signature as `True := by trivial`, a non-informative
placeholder. R41-T1.1 audit (`R41_T1_ChainCompositionAudit.md`) flagged
the `True` shape as the actual blocker for `slepian_comparison_finite`'s
chain-rule + sign-analysis closure: chaining on a `True` Stub gives the
consumer no usable assumption. R41 upgrades the type from `True` to a
real `HasDerivAt`-along-1D-path statement that is directly chainable in
the Slepian body via FTC.

The upgrade carries a `sorry` body — closure of the actual derivative-
non-negativity statement requires the bivariate Gaussian density formula
and the conditional orthant probability on `ι \ {i, j}`, both of which
depend on the R40-T2.3 `multivariateGaussian_eq_lebesgue_withDensity`
bridge (still a `True` placeholder at R41) plus the Stein integration-by-
parts identity. Closure target: R42–R43 alongside MGE / MGI real-
signature upgrades.
-/

/-- **R41 T2.1 — Off-diagonal directional-derivative non-negativity (real
signature, body deferred).**

For a positive-definite covariance `S₀` and threshold `x : ι → ℝ`,
restrict the orthant CDF to the 1-parameter symmetric off-diagonal
perturbation

    `α ↦ multivariateGaussianOrthantCDF (S₀ + α • E_{ij}) x`,

where `E_{ij} := single i j 1 + single j i 1` is the symmetric off-diagonal
basis matrix (preserves the Hermitian / symmetric covariance structure).
This 1-parameter restriction has a derivative at `α = 0`, and that
derivative is **non-negative** for `i ≠ j`.

Per the standard Slepian-via-density derivation, the explicit derivative
equals the bivariate Gaussian density of `(Z_i, Z_j)` at `(x_i, x_j)`
under the marginal `(0, 0; S₀ ii, S₀ ij, S₀ jj)` covariance, times the
conditional orthant probability on `ι \ {i, j}` given `Z_i = x_i` and
`Z_j = x_j`. Since both factors are non-negative, the derivative is
non-negative.

**R41 status: real-signature, TAG'd Stub body.** R40 left this as
`True := by trivial`, which carried no information for downstream chain
composition. R41 upgrades the type to `∃ d, 0 ≤ d ∧ HasDerivAt …`. The
body remains a TAG'd Stub.

**Mathlib gap diagnostic (concrete, refined R41-T1.1):**

Closure of the body requires three concrete pieces, none packaged at
the pin:

1. **Bivariate Gaussian density formula.** The `multivariateGaussian`
   measure has only a *characteristic-function* characterization in
   `brownian-motion`; the explicit Lebesgue density `(2π)^{-1} (det Σ)^{-1/2}
   exp(-x^T Σ^{-1} x / 2)` requires the
   `multivariateGaussian_eq_lebesgue_withDensity` bridge from
   `MultivariateGaussianPdf.lean`, currently a `True` placeholder.
2. **Conditional orthant probability on `ι \ {i, j}`.** No Mathlib API
   for the conditional orthant probability of a centered Gaussian
   conditioned on `Z_i = x_i, Z_j = x_j`. Would need an explicit
   conditional density formula derivation.
3. **Stein integration-by-parts.** The derivative computation reduces
   to a Stein-style integration-by-parts on the bivariate marginal —
   not packaged in `Mathlib.Probability.*`. The classical proof is
   ~50 LOC of integration-by-parts + Gaussian-tail bounds.

Per `R41_T1_ChainCompositionAudit.md`, the upgraded real-signature
unblocks `slepian_comparison_finite`'s body to chain through this Stub
as a black-box assumption: the Slepian body becomes "FTC + the
existential `d` provided here, summed over off-diagonal entries", with
the sign-of-`d` non-negativity providing the FTC monotonicity. -/
theorem multivariateGaussianOrthantCDF_partial_offdiagonal
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) (i j : ι)
    (_hij : i ≠ j) :
    ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt
      (fun α : ℝ =>
        multivariateGaussianOrthantCDF
          (S₀ + α • (Matrix.single i j (1 : ℝ) + Matrix.single j i (1 : ℝ))) x)
      d 0 := by
  -- TAG[R41-T2.1-bivariate-density-conditional] : real-signature upgrade of
  -- R40-T2.3 `True` placeholder. Body deferred to R42-R43 alongside MGE / MGI
  -- real-signature upgrades. Concrete Mathlib gap diagnostic: bivariate-Gaussian-
  -- density (depends on multivariateGaussian_eq_lebesgue_withDensity, which is
  -- itself a True placeholder at R41) + conditional-orthant-probability (no
  -- Mathlib API) + Stein integration-by-parts (no Mathlib API). See
  -- R41_T1_ChainCompositionAudit.md "R41 / R42 split" table for the multi-round
  -- plan.
  sorry

end Erdos524.Helpers.MultivariateGaussianCDF
