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

/-- **R49 Path A — Phase 2 body axiomatized.**

For a positive-definite covariance matrix `Σ : Matrix ι ι ℝ` and threshold
`x : ι → ℝ`, the half-space probability

  `F(Σ; x) := ℙ_{Z ∼ 𝒩(0, Σ)} (∀ i, Z i ≤ x i)
            = (multivariateGaussian 0 Σ).real {z | ∀ i, z i ≤ x i}`

is differentiable in `Σ` (in the entry-wise Fréchet sense at any
`S₀ : Matrix ι ι ℝ` with `S₀.PosDef`).

This is the analytic backbone of Slepian's lemma in the covariance-
interpolation form: writing `Σ_α = (1-α) Σ_X + α Σ_Y`, the chain rule
`dF/dα = ∑_{i,j} ∂F/∂Σ_{ij} · (Σ_Y - Σ_X)_{ij}` reduces sign analysis of
`dF/dα` to sign analysis of the entry-wise derivatives.

**Classical justification.** The standard proof uses the Lebesgue density
`ρ(z; Σ) = (2π)^(-n/2) (det Σ)^(-1/2) exp(-z^T Σ^(-1) z / 2)` and
differentiation under the integral sign with a uniform Gaussian-tail
Lipschitz envelope on a `PosDef` neighbourhood of `S₀`. Reference:
Slepian (1962) "The one-sided barrier problem for Gaussian noise", Bell
System Tech. J. 41:463-501; or Tong (1990) "The Multivariate Normal
Distribution" §5.1.

**Why axiomatized at R49 (Path A switch).** The R48-T1.1 audit
(`R48_T1_PathGammaPrimeAudit.md` §2-§3, re-verified in
`Round49_T1_PathAAxiomatization.md` §1) caught two independent misframings
in the brief's Path γ' recipe:

* **(M1)** Lean MGI (`multivariateGaussianOrthantCDF_eq_lebesgue_integral`
  at `MultivariateGaussianPdf.lean:412`) is a measure-vs-Lebesgue-integral
  REWRITE identity — its R44 Full body (lines 412-477) is three sequential
  `rw`s with no derivative content. It does NOT supply
  `HasFDerivAt (fun Σ => multivariateGaussianPdf 0 Σ x) ... Σ`. Pdf
  S-differentiability is a separate ~80-150 LOC chain blocked on R40
  `Matrix.det.differentiable` Stub at `MatrixDetDifferentiable.lean:149`.
* **(M2)** `multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef`
  at `GaussianParametricAnalysis.lean:168` is INSIDE a `/-! ... -/`
  docstring code block — NOT a Lean theorem. The Path γ' DCT chain
  consumer "Gaussian tail majorant" does not exist as a Lean object.

Combined honest LOC for Phase 2 body Full close: ~380-700 LOC across 3-5
rounds with P(Full)/round ~0.30 — incompatible with the R52 milestone
gate (items ≤ 8) under the cumulative ~0.44 sorry/round retirement rate.

Path A axiomatization (this commit) preserves the verbatim type signature,
trades -1 sorry for +1 axiom, and frees 3-5 rounds of mainline budget for
GLW shortcut (R50-R51) + Track C round 3 + Track D round 4 retirements.

**Retirement target: R55-R59 (post-gate).**

1. *Mathlib pin bump (preferred path):* monitor Mathlib for landings of
   pdf-differentiability infrastructure for `multivariateGaussianPdf` /
   `multivariateGaussian` density + uniform Gaussian-tail bound on
   `IsCompact ∘ PosDef` neighbourhoods + `Matrix.det.differentiable`. If
   landed (post-`v4.27` toolchain bump), the axiom retires via direct
   chain composition (~50-100 LOC consumer wrapper).

2. *From-scratch closure (fallback):* build the missing pieces in-tree —
   ~150-300 LOC over 2-3 rounds, anchored on R40 Stub close (~30-80 LOC) +
   tail-bound Full helper (~60-100 LOC) + Phase 2 body Full close
   (~150-300 LOC). This is Path B from the R49 framing, executed
   post-R52-gate when budget is freed.

See `Helpers/Round49_T1_PathAAxiomatization.md` for the full Path A
audit + retirement plan, and `AXIOM_INVENTORY.md` "Axiom #6" for the
debt-tracking entry. -/
axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) :
    DifferentiableAt ℝ
      (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀

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
