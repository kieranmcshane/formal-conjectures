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
import Mathlib.Analysis.Matrix.Normed

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
  -- Outline of the closed-form proof (deferred to R36 or later):
  --   (i)   Express the orthant probability as ∫_{orthant x} ρ(z; Σ) dz
  --         where ρ is the Lebesgue density of multivariateGaussian 0 Σ.
  --   (ii)  Use Matrix.det.differentiable + Matrix.PosDef.inv.differentiable
  --         to get pointwise smoothness of (Σ, z) ↦ ρ(z; Σ).
  --   (iii) Apply HasFDerivAt under the integral sign (Lebesgue dominated
  --         convergence with a Σ-uniform integrable dominator) on the
  --         orthant region.
  --   (iv)  Verify Σ.PosDef stays in an open neighborhood (PosDef is open
  --         in the entry-wise topology — itself a Mathlib gap, though
  --         smaller).
  sorry

/-! ## Entry-wise partial-derivative formula (R36+ scope, signature here for
documentation) -/

/-- **R35 T1.1 ledger — entry-wise derivative formula for the orthant CDF.**

Per the standard derivation, for a centered multivariate Gaussian with
covariance `Σ`, the partial derivative of the orthant CDF at threshold `x`
with respect to off-diagonal entry `Σ_{ij}` (with `i ≠ j`) is given by

  `∂F/∂Σ_{ij}|_{x} = ρ_{ij}(x_i, x_j; Σ_{ii}, Σ_{ij}, Σ_{jj}) · F_{ι\{i,j}}`

where `ρ_{ij}` is the bivariate Gaussian density of `(Z_i, Z_j)` evaluated
at `(x_i, x_j)`, and `F_{ι\{i,j}}` is the conditional orthant probability
on the remaining coordinates conditioned on `Z_i = x_i, Z_j = x_j`.

This is the load-bearing entry-wise positivity fact for Slepian: each
`(N_Y - N_X)_{ij}` factor is non-negative (off-diagonal-domination
hypothesis) and each density factor is non-negative, so `dF/dα ≥ 0`.

**R35 status:** statement only, body deferred to R36 alongside the
multivariate density-existence work. This signature documents the target
formula so R36 has a concrete handle. -/
theorem multivariateGaussianOrthantCDF_partial_offdiagonal
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (_x : ι → ℝ) (_i _j : ι)
    (_hij : _i ≠ _j) :
    -- Statement: the partial derivative w.r.t. the (i,j)-entry equals the
    -- bivariate density of (Z i, Z j) at (x i, x j) times the conditional
    -- orthant probability on ι \ {i, j} given Z i = x i, Z j = x j.
    -- Concrete Lean shape deferred to R36 once the bivariate density and
    -- conditional measure are in hand (both Mathlib gaps).
    True := by
  trivial

end Erdos524.Helpers.MultivariateGaussianCDF
