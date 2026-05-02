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
  --
  -- **R45-T2.1/T2.2 audit-aligned skeleton (Path γ per Grok R45 Q4).**
  -- R44 retired the MGI Stub Full
  -- (`MultivariateGaussianPdf.lean:278` —
  -- `multivariateGaussianOrthantCDF_eq_lebesgue_integral`), so the rewrite
  -- of the orthant CDF to a Lebesgue integral is now executable. The
  -- single `sorry` here remains; this round (R45) advances the diagnostic
  -- quality of the residual without inflating the sorry count, per the
  -- R45-T1.1 framing-verification audit's revised cost estimate (~400-600
  -- LOC for full body close, NOT Grok Q4's ~300-350 LOC).
  --
  -- **Path γ skeleton (executable on R44+R41 chain, sub-residuals named):**
  --
  --   (i) MGI rewrite — POST-R44 EXECUTABLE.
  --       `multivariateGaussianOrthantCDF S x =
  --          ∫ y in orthant x, multivariateGaussianPdf S (fun i => y i)`
  --       via `MultivariateGaussianPdf.multivariateGaussianOrthantCDF_eq_lebesgue_integral`.
  --       Transferred across `S` via `EventuallyEq` on a PosDef
  --       neighborhood — see sub-gap (A) below for the missing
  --       `Matrix.PosDef.isOpen` step.
  --
  --   (ii) Diff-under-integral — APPLY
  --        `MeasureTheory.hasFDerivAt_integral_of_dominated_loc_of_lip`
  --        (Mathlib `Analysis/Calculus/ParametricIntegral.lean:164`).
  --
  --   (iii) Integrand pointwise differentiability —
  --        `S ↦ multivariateGaussianPdf S y` is differentiable at `S₀.PosDef`
  --        for every `y`, by chain rule on the closed-form formula:
  --          * `Matrix.det.differentiable` — R40 Stub @ line 149,
  --            chainable as black box.
  --          * `Matrix.PosDef.inv_hasFDerivAt` — R41 Full @ line 200.
  --          * `Real.sqrt` differentiability at positive args
  --            (`Mathlib/Analysis/SpecialFunctions/Sqrt.lean:68`).
  --          * `differentiableAt_inv` for `(S.det)⁻¹` at `S₀.det > 0`
  --            (`Mathlib/Analysis/Calculus/FDeriv/Mul.lean:804`).
  --          * `Real.exp.differentiable` (Mathlib).
  --          * Bilinear continuity for `y ⬝ᵥ S⁻¹ *ᵥ y`.
  --        Estimated ~80-150 LOC. Concretely chainable post-R41.
  --
  --   (iv) Three engineering sub-gaps (load-bearing residual):
  --
  --        (A) `Matrix.PosDef.isOpen` — needed for transferring
  --            `multivariateGaussianOrthantCDF S x = ∫ ...` across `S`
  --            in a neighborhood of `S₀`. Mathlib has
  --            `Matrix.PosDef.det_pos` but not the open-set predicate.
  --            Closure: `det > 0` continuous + Hermitian closed + PSD
  --            interior. ~30-80 LOC.
  --
  --        (B) Integrability of `multivariateGaussianPdf S` on `orthant x`.
  --            Mathlib has `IsGaussian.integrable_id` for the abstract
  --            multivariate Gaussian but not the closed-form PDF
  --            integrability. Closure: explicit Gaussian-tail bound
  --            (`exp(-c·‖y‖²)` for `c > 0` from PosDef-inverse positive
  --            spectrum) + `Integrable.exp_neg_quadratic`. ~50-100 LOC.
  --
  --        (C) **Load-bearing.** `LipschitzOnWith` on `S ↦ pdf S y` over
  --            a PosDef neighborhood, with **integrable** Lipschitz
  --            envelope. Requires explicit Fréchet derivative formula
  --            chain (sub-gap iii) + uniform Gaussian-tail bound on the
  --            derivative norm. ~150-300 LOC alone — the dominant
  --            engineering cost of the full Phase 2 body close.
  --
  -- **Combined R45-T1.1 cost estimate**: ~400-600 LOC for full body
  -- close. Single-round full close is high-risk (P~0.30 per audit);
  -- this round preserves the single TAG'd Stub with diagnostic-quality
  -- enhancement (P~0.65 mid-distribution outcome).
  --
  -- **R47-T2.2 deferral diagnostic (this round, per brief abort rules).**
  --
  -- Phase 2 body Full close was a candidate R47 mandatory deliverable
  -- per the brief's aggressive 2-retirement scope. T1.1 grep audit
  -- (`R47_T1_GrepAuditAndFramingVerification.md` §3) verified that
  -- closure is BLOCKED on three prerequisites at pin
  -- `mathlib4 @ 25ce63313608`:
  --
  --   1. **MGE main Full close** (sub-gap (b) chain, R47-T2.1
  --      diagnostic): the integrand `multivariateGaussianPdf S y` is
  --      only a "claimed" Lebesgue density of `multivariateGaussian 0 S`
  --      until MGE main Stub closes. Sub-gap (B) integrability and
  --      sub-gap (C) Lipschitz envelope both consume this density
  --      identification. Closure depends on Bridges (b.A) + (b.B) +
  --      (b.C) — see `MultivariateGaussianPdf.lean:248` for the
  --      three-bridge decomposition and revised LOC estimates.
  --
  --   2. **`Matrix.det.differentiable` (R40 Stub at
  --      `MatrixDetDifferentiable.lean:149`)**: the Lipschitz envelope
  --      sub-gap (C) requires the explicit Fréchet derivative formula
  --      chain through `Matrix.det.differentiable`. Mathlib has only
  --      `Matrix.det.continuous` (`Topology/Instances/Matrix.lean:459`);
  --      polynomial expansion route via `Matrix.det_apply` +
  --      `MultilinearMap.contDiff` is unpackaged (~30-80 LOC of
  --      plumbing).
  --
  --   3. **Uniform Gaussian-tail bound integrability** (sub-gap (B)):
  --      depends on (1) for the closed-form PDF integrability claim.
  --
  -- **R46 helpers contribution to the chain (POSITIVE):**
  --
  --   * `Erdos524.Helpers.posDef_min_eigenvalue_pos` (R46-T2.2,
  --     `PhaseAUpperBound.lean`): supplies the minimum-eigenvalue lower
  --     bound on compact PosDef sets. This is the constructive
  --     ingredient for sub-gap (A) (PosDef compact neighbourhood) AND
  --     for the uniform Gaussian-tail bound in sub-gap (B). **Direct
  --     consumer of the R46 helper.**
  --
  --   * `Erdos524.Helpers.GaussianParametricAnalysis` (R46-T3.1
  --     stretch, cross-track synergy library): provides parametric
  --     Gaussian density bounds + DCT scaffold for `S ↦ ∫ pdf(S) dy`
  --     differentiability. **Foundational; direct consumption requires
  --     MGE main Full first.**
  --
  --   * `Erdos524.Helpers.MultivariateGaussianPdf.det_CFC_sqrt_eq_sqrt_det`
  --     (R46-T2.1): identifies the Jacobian factor in
  --     `multivariateGaussianPdf` as `(det S)^(-1/2)`. **Foundational;
  --     consumed inside MGE main, not directly by Phase 2 body.**
  --
  -- **Realistic LOC for Phase 2 body Full close (post-R46 helpers,
  -- with prerequisites NOT met):** ~300-550 LOC across sub-gaps (A) +
  -- (B) + (C) + DCT chain composition. Single-round close in R47 is
  -- **NOT FEASIBLE** with the prerequisite chain blocked.
  --
  -- **R47 T2.2 outcome (this round):** deferred per brief abort rules
  -- with concrete diagnostic. R47 net retirement: 0 sorries.
  --
  -- **Future-round closure path (R48-R52):**
  --
  --   * R48: close MGE Bridge (b.A) as standalone Full helper
  --     (~80-120 LOC; benefits Track C 1D KMT + indep-coord
  --     Pi-Gaussian). **Indirect Phase 2 prerequisite step 1.**
  --   * R49: close MGE main via (b.B) + (b.C) composition
  --     (~50-150 LOC; net retirement: -1 sorry, MGE main retired).
  --     **Phase 2 prerequisite step 1 done.**
  --   * R50: close `Matrix.det.differentiable` R40 Stub
  --     (~30-80 LOC; net retirement: -1 sorry). **Phase 2 prerequisite
  --     step 2 done.**
  --   * R51-R52: close Phase 2 body via sub-gaps (B) + (C) using
  --     R46-T2.2 helpers + R46-T3.1 library + closed prerequisites
  --     (~200-400 LOC; net retirement: -1 sorry, Phase 2 main retired).
  --
  -- This trajectory retires 3 sorries across R49-R52. Combined with
  -- Track C+D parallel deliveries, sufficient to meet hybrid (c) R52
  -- gate at items ≤ 8 IF Track C + Track D each retire ~2 sorries in
  -- the same window. Without Track C+D contribution: total net
  -- retirements R47-R52 = 3, leaving items at 17 - 3 = 14 → R52 gate
  -- FAILS, Path A (axiomatize BTIS at R54) triggered.
  --
  -- See `Helpers/R47_T1_GrepAuditAndFramingVerification.md` §3-§4 +
  -- `Helpers/PhaseV2R47Status.md` (this round) for full status.
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
