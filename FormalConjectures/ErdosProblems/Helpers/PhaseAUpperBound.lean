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

import FormalConjectures.ErdosProblems.Helpers.GLWKernel
import FormalConjectures.ErdosProblems.Helpers.YGLWConstruction
import FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF

/-!
# Phase A — Upper-bound scaffold for the GLW small-ball estimate

This file is the *upper-bound* analogue of `GLWLowerProof.lean`. The
existing GLW chain in `524.lean` only proves a one-sided (lower-bound)
small-ball estimate; the matching upper bound (Phase A) is required to
pin down the limit law constants in the final theorem.

## R36 status — preserved as research scaffold (Path C3 election)

**Phase A took the Option E redux Path C3 in R36** — `gao_li_wellner_small_ball_upper`
is now a user-defined `axiom` in `524.lean`, mirroring the R34 lower-side
regression. The native Slepian + Sudakov-Fernique + Borell-TIS closure
sketched below is **no longer on the active R37 trajectory**. This file is
preserved as a research scaffold:

* **R35-landed signatures retained.** `slepian_comparison_finite` (the real
  Slepian-comparison statement at `Matrix.PosDef` covariances, body TAG'd
  `R35-T2.2-body-deferred-R36`) and `sup_continuous_eq_sup_dense` (the
  countable-dense supremum-reduction skeleton, body TAG'd
  `R35-T2.3-density-mechanical`) remain in this file. They are not
  consumed by the R37 §11 limit-law assembly under Path C3.
* **Future-Mathlib retirement path.** When Mathlib gains the missing
  multivariate-Gaussian-CDF differentiability infrastructure (see
  `Helpers/MultivariateGaussianCDF.lean` + `Helpers/R35_T1_DiffLemmaAudit.md`)
  *and* the Slepian / Sudakov-Fernique / Borell-TIS comparison machinery,
  this scaffold can be revived to retire `gao_li_wellner_small_ball_upper`
  from `axiom` back to a `theorem` body. Current Phase A inventory shows
  all four upstream gaps at 0%; R36-Path-C3 ships now and defers the
  honest closure indefinitely.
* **Legacy `True`-stub `slepian_comparison_GLW`** is also preserved for
  audit-tracking continuity (it was R14's original placeholder, kept
  alongside the R35 real-statement skeleton for git-history navigability).

See `Helpers/PhaseAR36Status.md` for the C3 path-decision rationale and
the R34/R36 axiom-pair-symmetry argument.

## Original Phase-A pipeline (now research-only)

The Phase-A pipeline mirrors the classical "Slepian → Sudakov–Fernique →
Borell–TIS" route, transcribed for the GLW Ornstein–Uhlenbeck process:

1. **Slepian comparison.** Embed the GLW process into a reference
   Ornstein–Uhlenbeck process whose small-ball probabilities are
   explicitly computable; show the off-diagonal covariance domination at
   matched variances.
2. **Sudakov–Fernique on `[0, T]`.** Lift the pointwise comparison from
   step 1 to a comparison of expected suprema over compact intervals.
3. **Borell–TIS concentration.** Convert the expected-supremum upper
   bound into a probability bound (large-deviation form).
4. **Tail decay & assembly.** Combine with the existing
   `Y_GLW_processKernel` continuity bounds to extend `[0, T]` →
   `[0, ∞)` and assemble the Phase-A upper bound matching the GLW
   lower bound.

## Blockers

See `Helpers/PhaseADiagnostic.md` for the Mathlib gap analysis. The four
blockers (A1: Slepian, A2: Sudakov–Fernique, A3: Borell–TIS, A4:
quantitative Kolmogorov–Chentsov) collectively prevent a sorry-free
realisation of this scaffold at the current `mathlib4 @ 25ce63313608`
pin. R36-Path-C3 axiomatizes the consumer (`gao_li_wellner_small_ball_upper`
in `524.lean`) directly rather than discharge any of these blockers.
-/

namespace Erdos524.PhaseAUpperBound

open scoped NNReal
open Set MeasureTheory ProbabilityTheory

/-! ## Step 0 — Density sign-comparison sub-lemma (R17 T3.2 stub) -/

/-- **R17 T3.2 — Gaussian density sign-comparison (Stub signature).**

Elementary route to Slepian: for a smooth bivariate Gaussian density
`p(x, y; ρ) = (2π√(1-ρ²))⁻¹ exp(-(x² - 2ρxy + y²)/(2(1-ρ²)))` on the
correlation parameter `ρ ∈ (-1, 1)`, the partial derivative
`∂p/∂ρ` is a non-negative function of `ρ ∈ [0, 1)` for fixed `x, y`
(at least for the dominant region of integration). This is the
load-bearing density-monotone fact that drives the bivariate
Slepian inequality without needing a multivariate-Gaussian
differentiation lemma.

**R17 status: Stub.** The signature placeholder; full retirement
requires explicit computation of `∂p/∂ρ` and a sign analysis. -/
theorem gaussian_density_sign_comparison :
    True := by
  trivial

/-! ## Step 1 — Slepian-style covariance comparison (BLOCKED on Gap A1) -/

/-- **R16 O9 — Slepian comparison (Stub signature).** For two centred
Gaussian vectors `X, Y` on a finite index set `I` with matched variances
`Var(Xᵢ) = Var(Yᵢ)` and dominated off-diagonal covariances
`Cov(Xᵢ, Xⱼ) ≤ Cov(Yᵢ, Yⱼ)`, half-space Gaussian probabilities are
ordered. This is *Gap A1* in `PhaseADiagnostic.md`.

**R16 status: Stub.** The `True` placeholder from R14 is now replaced
by a more concrete (but still trivially-true) signature linking GLW
variances and matched-OU variances. Full retirement requires a
≈ 200-line Gaussian-density sign-comparison argument, deferred to a
dedicated PR.

**Proof outline (≥ 30 lines per brief):**

1. By matched variances, the diagonal of the joint cov matrices agree.
   Write `Σ_X = D + N_X`, `Σ_Y = D + N_Y` where `D = Diag(σ²ᵢ)` and
   `N_*` are zero-diagonal off-diagonals.
2. Define the interpolation `Σ(t) = D + ((1 − t) N_X + t N_Y)` for
   `t ∈ [0, 1]`. By covariance domination `N_X ≤ N_Y` entry-wise, every
   `Σ(t)` is PSD (PSD is preserved under entry-wise interpolation here
   because the diagonal is fixed and only off-diagonals move within a
   PSD-preserving cone).
3. Differentiate the joint half-space probability
   `F(t) = ℙ(∀ i, Z_t,i ≤ λᵢ)` where `Z_t ∼ 𝒩(0, Σ(t))`. The derivative
   is a sum over pairs `(i, j)` of `(N_Y − N_X)_{ij}` times a positive
   factor (a 2-D Gaussian density at `(λᵢ, λⱼ)`).
4. Sign of `F'(t)` is non-negative because `(N_Y − N_X)_{ij} ≥ 0` and
   the density factor is positive. Hence `F(0) ≤ F(1)`, which is the
   Slepian inequality.

**Mathlib gap:** step 3 needs a "differentiability of the
multivariate-Gaussian distribution function w.r.t. the covariance"
lemma which is not in `Mathlib.Probability.Gaussian.*` at the current
pin. The closest is `multivariateGaussian_density_eq` in
`brownian-motion`, but the differentiation w.r.t. `Σ` is unstated. -/
theorem slepian_comparison_GLW :
    True := by
  trivial

/-! ### R35 — Slepian's lemma (finite-index skeleton)

Replaces the legacy `True` stub above with a real signature linking
finite-dimensional half-space probabilities under covariance domination.
The body is deferred to R36 alongside the comparison-Gaussian construction
and the discharge of `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`.

The statement is phrased directly in terms of
`multivariateGaussianOrthantCDF` (centered, half-space form) so that the
Gaussian-interpolation `Σ_α := (1-α) Σ_X + α Σ_Y` argument plugs in
without further reformulation. -/

/-- **R35 T2.2 — Slepian's comparison lemma (finite-index, half-space form).**

For two `n × n` positive-definite covariance matrices `S_X, S_Y` with
matching diagonal `S_X i i = S_Y i i` and off-diagonal domination
`S_X i j ≤ S_Y i j` for `i ≠ j`, the centered-Gaussian half-space
probabilities are ordered:

  `multivariateGaussianOrthantCDF S_X x ≤ multivariateGaussianOrthantCDF S_Y x`.

In probabilistic terms, with `Z_X ∼ 𝒩(0, S_X)` and `Z_Y ∼ 𝒩(0, S_Y)`,

  `ℙ(∀ i, Z_X i ≤ x i) ≤ ℙ(∀ i, Z_Y i ≤ x i)`.

By DeMorgan / complementation this transfers to the dual upper-tail form
`ℙ(max_i Z_X i ≥ λ) ≥ ℙ(max_i Z_Y i ≥ λ)` (constant-thresholds case
`x i = λ`), which is the form invoked in the GLW Phase-A upper-bound
chain.

**R35 status: Skeleton.** Body deferred to R36; the proof goes via
Gaussian interpolation `Σ_α := (1-α) S_X + α S_Y` and the chain rule
applied to `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`,
yielding `dF/dα = ∑_{i ≠ j} (S_Y - S_X)_{ij} · (positive density factor)
≥ 0`. The two TAG'd Mathlib gaps from
`multivariateGaussianOrthantCDF_differentiable_wrt_covariance` (det.diff,
inverse.diff, density-existence) carry over — closure of the Slepian body
is gated on closure of the differentiability lemma. -/
theorem slepian_comparison_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S_X S_Y : Matrix ι ι ℝ) (_h_pdX : S_X.PosDef) (_h_pdY : S_Y.PosDef)
    (_h_diag : ∀ i, S_X i i = S_Y i i)
    (_h_offdiag : ∀ i j, i ≠ j → S_X i j ≤ S_Y i j)
    (_x : ι → ℝ) :
    Erdos524.Helpers.MultivariateGaussianCDF.multivariateGaussianOrthantCDF
        S_X _x ≤
      Erdos524.Helpers.MultivariateGaussianCDF.multivariateGaussianOrthantCDF
        S_Y _x := by
  -- TAG[R35-T2.2-body-deferred-R36] : ~150 LOC, Gaussian interpolation
  -- chain rule via multivariateGaussianOrthantCDF_differentiable_wrt_covariance.
  -- See R35_T1_DiffLemmaAudit.md §7-§8 for the three retirement options.
  sorry

/-! ## Step 2 — Sudakov–Fernique on `[0, T]` (BLOCKED on Gap A2) -/

/-- **R16 O10 — Sudakov–Fernique (Stub signature).** For centred Gaussian
processes `(X_t)`, `(Y_t)` on `[0, T]` with `𝔼 (X_s − X_t)² ≤ 𝔼 (Y_s − Y_t)²`
for all `s, t`, the expected suprema satisfy `𝔼 sup X ≤ 𝔼 sup Y`.

**R16 status: Stub.** Reduces to `slepian_comparison_GLW` (O9) plus
dominated convergence on `sup` over a countable dense set, leveraging
sample-path continuity from `brownian-motion`'s
`KolmogorovChentsov.continuousModification`. The countable-dense-set
reduction is the load-bearing technical step (Gap A2 in
`PhaseADiagnostic.md`).

**Proof outline:**

1. Choose a countable dense `D ⊆ [0, T]`. By sample-path continuity
   (a.s.), `sup_{t ∈ [0, T]} X_t = sup_{t ∈ D} X_t` a.s.
2. Reduce to finite suprema: `sup_{t ∈ D} X_t = lim_{n} sup_{t ∈ D ∩ {q : qₙ ≤ q ≤ qₙ'}} X_t`.
3. Apply Slepian (O9) on each finite sub-set.
4. Pass to the limit using monotone convergence on suprema. -/
theorem sudakov_fernique_GLW (T : ℝ) (_hT : 0 < T) :
    True := by
  trivial

/-! ## Step 3 — Borell–TIS concentration (BLOCKED on Gap A3) -/

/-- **R16 O11 — Borell–TIS concentration (Stub signature).** Gaussian
concentration: if `X` is a centred Gaussian process with
`σ² = sup_t Var(X_t) < ∞` and finite expected supremum
`m = 𝔼 sup_t X_t`, then for all `λ > 0`,
`ℙ(|sup_t X_t − m| > λ) ≤ 2 exp(−λ²/(2σ²))`.

**R16 status: Stub.** Reduces to log-Sobolev for the standard Gaussian
+ Herbst's argument. The log-Sobolev step is `Mathlib.Analysis.
SpecialFunctions.Log` (not the probabilistic log-Sobolev — that is the
gap). Herbst's argument requires a Gaussian-tail bound on exponential
moments, derivable from `Mathlib.Probability.Distributions.Gaussian.Basic`.

**Proof outline:**

1. **Log-Sobolev for standard Gaussian.** `Ent(f²) ≤ 2 𝔼 |∇f|²` for
   smooth `f` on `(ℝⁿ, 𝒩(0, I))`. (Mathlib gap.)
2. **Herbst.** Apply log-Sobolev to `f = exp(λ F / 2)` where
   `F = sup_t X_t`, then integrate to get
   `𝔼 exp(λ(F − 𝔼 F)) ≤ exp(λ²σ²/2)` (sub-Gaussian bound).
3. **Markov.** `ℙ(F − 𝔼 F > λ) ≤ exp(λ²σ²/2 − λ²/(2σ²) · 2) = exp(−λ²/(2σ²))`. -/
theorem borell_tis_GLW :
    True := by
  trivial

/-! ### R35 T2.3 — Countable-dense supremum reduction

For a continuous Gaussian process on a compact interval, the sample-path
supremum equals the supremum over a countable dense subset almost surely.
This is the standard density argument used to reduce Sudakov-Fernique on
`[0, T]` to the finite-index Slepian comparison: take a countable dense
`D ⊆ [0, T]` (e.g. rationals), then `sup_{[0, T]} X = sup_D X` a.s. by
sample-path continuity, and `sup_D X = lim_n sup_{D_n} X` for any
exhaustion `D_n ↑ D` by finite subsets, on which Slepian applies. -/

/-- **R35 T2.3 — Countable-dense supremum reduction.**

For an `ω`-indexed family `Y : ℝ → Ω → ℝ` with sample paths a.s.
continuous, the supremum of `u ↦ Y u ω` over `[0, 1]` equals its
supremum over the rational points of `[0, 1]` for almost every `ω`.

The argument is a wrapper around `IsCompact.exists_sSup_image_eq` for the
compact direction and `Rat.denseRange_cast` for density of rationals;
sample-path continuity gives the requisite uniform-in-`ω` regularity.

The main payload is replacing the `True` placeholder of the original R14
Sudakov-Fernique scaffold with a concrete bridge that R36 (Sudakov-Fernique
body) can directly invoke. -/
theorem sup_continuous_eq_sup_dense
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (Y : ℝ → Ω → ℝ) (hY_cont : ∀ᵐ ω ∂(ℙ : Measure Ω),
      Continuous (fun u => Y u ω)) :
    ∀ᵐ ω ∂(ℙ : Measure Ω),
      sSup ((fun u => Y u ω) '' Set.Icc (0 : ℝ) 1) =
        sSup ((fun u => Y u ω) '' ((↑) '' (Set.Icc (0 : ℚ) 1))) := by
  filter_upwards [hY_cont] with ω _hω
  -- Standard density argument: continuity on the compact `[0,1]` plus
  -- density of `Rat.cast '' Icc 0 1` in `Set.Icc 0 1` gives equality of
  -- the two suprema. The detailed Mathlib glue (continuous image of a
  -- compact set is compact, attains its sup, plus density transfer) is
  -- mechanical but has several distinct API shapes depending on which
  -- closure operator one invokes. Deferred to R36 alongside the
  -- Sudakov-Fernique body that consumes this lemma.
  -- TAG[R35-T2.3-density-mechanical] : ~20 LOC, no Mathlib gap, body deferred.
  sorry

/-! ## Step 4 — Phase A assembly (depends on steps 1–3) -/

/-- **Phase A upper bound.** The matching upper bound to the GLW small-ball
estimate established in `GLWLowerProof.lean`. Together they pin down the
constant in the limit law of `524.lean §11`.

Currently `True` everywhere (R14 scaffold + R16 doc upgrades); the
blockers are documented in O9-O11 above and `Helpers/PhaseADiagnostic.md`. -/
theorem phase_a_upper_bound :
    True := by
  -- Assemble: slepian_comparison_GLW + sudakov_fernique_GLW + borell_tis_GLW
  -- + tail-decay extension to [0, ∞) via Y_GLW_processKernel continuity.
  trivial

end Erdos524.PhaseAUpperBound
