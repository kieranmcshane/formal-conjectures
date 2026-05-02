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

import FormalConjectures.Util.ProblemImports

/-!
# Track D — BTIS honest proof scaffold

Infrastructure for the Borell-Tsirelson-Ibragimov-Sudakov (BTIS) Gaussian
concentration inequality. This file lands the BTIS theorem (Path B′ Full
body, TD2 closure) and the load-bearing sub-lemma 3
(`lipschitz_sup_finite_gaussian`, packaging the centered sup as a
`HasSubgaussianMGF`).

**Round-2 closure (Path B′).** The main theorem `borell_tis` deduces the
BTIS tail bound from sub-lemma 3 plus Mathlib's Chernoff bound
`HasSubgaussianMGF.measure_ge_le`. The chain is structurally locked:
Path B′ bypassed the original route-(β) sub-lemmas 1–2
(`gaussian_log_sobolev_real`, `herbst_subgaussian_real`), which were
retired as orphans in round-3 (TD3 T2.2) after T1.1 grep verification
confirmed zero consumers outside this file.

**Round-3 sub-lemma 3 closure (TD3 T2.1).** Sub-lemma 3 retains a TAG'd
`sorry` (`TrackD-LipschitzSup`); see the inline docstring for the
adapter recipe targeting SLT `lipschitz_cgf_bound`
(`SLT/GaussianLipConcen.lean:1209`) plus the integrability lemma
`lipschitz_exp_centered_integrable_E` (line 1229), via canonical
Cholesky pushforward of `stdGaussianE` to the joint law of `X`. The
TD3 T1.1 audit established the corrected SLT target (the headline
`gaussian_lipschitz_concentration` returns a tail bound, not a
`HasSubgaussianMGF` wrapper), the Apache-2.0 per-file licensing, the
mathlib pin drift (SLT floats `master`), and the
`IsCenteredGaussianProcess.joint_gaussian` placeholder gap.

See `Helpers/TrackD_T1_BTISAudit.md` (round 1) and
`Helpers/TrackD_round2_T1_PortabilityAudit.md` (round 2) for prior-round
context, and `Helpers/TrackD_round3_T1_SemanticVerificationAudit.md`
for the TD3 corrected-target derivation.

## Path B′ chain (closed at TD2, locked at TD3)

1. `lipschitz_sup_finite_gaussian` — sup of a finite-index centered
   Gaussian process has a sub-Gaussian MGF with parameter
   `sup_t Var(X_t)`, packaged as `HasSubgaussianMGF`. TAG'd
   `TrackD-LipschitzSup` — TD3-TD4 closure target via SLT
   `lipschitz_cgf_bound` adapter.
2. `borell_tis` — Full body. Deduces the BTIS tail bound from
   sub-lemma 1 + Mathlib's `HasSubgaussianMGF.measure_ge_le`
   (Chernoff). Body is mechanical: set translation +
   `Real.toNNReal` coercion + `Measure.real ↔ toReal` bridging.

## Design notes

* Index type `T : Fintype` keeps the supremum well-defined as a finite
  max and avoids separability/measurability technicalities. Continuous-T
  generalization is straightforward once the Fintype version lands.
* The Gaussianity hypothesis is carried as `IsCenteredGaussianProcess` —
  a minimal predicate defined locally to keep dependencies thin. The
  `joint_gaussian` field is currently a `True` placeholder; TD4 closure
  via the SLT adapter requires strengthening it to carry an actual
  joint-Gaussian law (e.g. via `HasGaussianLaw` on the marginals or via
  the `BrownianMotion.Gaussian.IsGaussianProcess` predicate already in
  the project's dependency tree).
-/

namespace Erdos524.Helpers.BTISHonestProof

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open MeasureTheory ProbabilityTheory Real

/- ## Centered Gaussian process predicate (round-1 placeholder) -/

/-- Minimal centered-Gaussian-process predicate for round-1 BTIS scaffolding.
TD5 may replace by `BrownianMotion.Gaussian.IsGaussianProcess` (already in
the project's dependency tree, see `TrackD_T1_BTISAudit.md` §3) or by
harmonizing with `Erdos524.Helpers.IsGLWProcess` (`GLWProcessPredicate.lean`).

For round 1 we keep the predicate skeletal: measurability + centeredness +
joint-Gaussianity-of-finite-linear-combinations is sufficient to state the
BTIS conclusion; the actual joint-Gaussian field is asserted abstractly
(`Prop`-typed) and will be materialised by the TD5 swap.
-/
structure IsCenteredGaussianProcess
    {Ω T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : T → Ω → ℝ) : Prop where
  /-- Each marginal `X t` is measurable. -/
  measurable : ∀ t, Measurable (X t)
  /-- Each marginal `X t` is integrable (load-bearing for `centered`). -/
  integrable : ∀ t, Integrable (X t) ℙ
  /-- Each marginal is centered. -/
  centered : ∀ t, ∫ ω, X t ω ∂ℙ = 0
  /-- **Joint Gaussianity.** Every finite linear combination of marginals is
  Gaussian. Round-1 placeholder; TD5 materialises via Mathlib's
  `HasGaussianLaw` or the brownian-motion-package predicate. -/
  joint_gaussian : True

/- ## Sub-lemma 3 — Sup is a Lipschitz functional (TD4 closure target post-M1) -/

/-- **Sup is a Lipschitz functional of a centered Gaussian process.**

For a Fintype-indexed centered Gaussian process `X : T → Ω → ℝ` with
variance budget `sigma2 = sup_t Var(X_t)`, the centered supremum
`Y(ω) := (⨆ t, X t ω) − 𝔼[⨆ t, X t]` has a sub-Gaussian moment-generating
function with parameter `sigma2`, packaged as
`HasSubgaussianMGF Y sigma2.toNNReal ℙ`.

This is the BTIS conclusion in `HasSubgaussianMGF` form; the standard tail
bound `ℙ(M ≥ 𝔼[M] + r) ≤ exp(−r²/(2 σ²))` follows via Mathlib's Chernoff
bound `HasSubgaussianMGF.measure_ge_le`. The proof combines
`herbst_subgaussian_real` with the Lipschitz property of the sup functional
in the canonical Gaussian-isometry coordinates: viewing `X` as the image of
a standard Gaussian on `ℝᵀ` under a linear map of operator norm `√sigma2`,
the sup-of-coordinates is 1-Lipschitz in the ambient `ℝᵀ` norm, hence
`√sigma2`-Lipschitz pulled back to the standard Gaussian.

**Round-2 signature change (Path B′).** The conclusion is upgraded from
the bare MGF inequality `mgf Y ℙ t ≤ exp(σ² t²/2)` to the full
`HasSubgaussianMGF` structure (carrying both the bound *and* the
required integrability of `exp(t Y)` for all `t`). This shrinks the
consumer-facing API to a single `HasSubgaussianMGF` fact and unblocks
the round-2 closure of `borell_tis` via
`HasSubgaussianMGF.measure_ge_le` (Chernoff), without affecting the
upstream proof effort: the sorry body has the same intrinsic difficulty
either way (Herbst + Lipschitz-sup + integrability, all derivable from
sub-lemmas 1–2 once those are closed).

**Status (round 3).** TAG'd `TrackD-LipschitzSup`. **TD3 closure
attempt aborted at lake-build stage** after corrected-target
re-routing per user pivot (M1 license demoted as academic-research
norm; T2.1 retargeted from `gaussian_lipschitz_concentration` to
`lipschitz_cgf_bound`). The aborted experiment is documented below
along with the four mismatches surfaced by T1.1 + T2.1 attempts; see
`Helpers/TrackD_round3_T1_SemanticVerificationAudit.md` (T1.1 audit)
and `Helpers/TrackDStatus.md` TD3 addendum (T2.3 build log) for the
full record.

* **M1 (license, demoted).** SLT repo has no `LICENSE` file (GitHub
  API: `license: null`; tree-listing: file absent). Per-file headers
  assert Apache-2.0 referencing the missing LICENSE. User-acknowledged
  academic-research-formalization norm — proceed with intent clear.
* **M2 (theorem-form, addressed).** SLT
  `gaussian_lipschitz_concentration` (line 1301 of
  `SLT/GaussianLipConcen.lean`) returns a direct tail bound
  `(stdGaussianE n {x | t ≤ |f x − ∫ y, f y ∂μ|}).toReal ≤
  2 · exp(−t²/(2 L²))`, NOT a `HasSubgaussianMGF` wrapper. The
  corrected target is `lipschitz_cgf_bound` (line 1209) + the
  companion `lipschitz_exp_centered_integrable_E` (line 1229): CGF
  inequality + integrability package into `HasSubgaussianMGF` via
  Mathlib's structure constructor. Grok cited the wrong theorem
  within SLT; user pivot installed the correction.
* **M3 (mathlib pin, BREAKING — promoted from minor).** SLT
  `lakefile.lean` requires `mathlib` from floating `master`;
  lake-manifest captured `d68c4dc0`. Project pin is `25ce63313608`.
  TD3 T2.1 lake-add experiment (commit reverted) proved drift hard:
  `lake build SLT.GaussianLipConcen` failed because
  `SLT.GaussianPoincare.LevyContinuity` imports
  `Mathlib.MeasureTheory.Measure.Prokhorov`, **a file that does not
  exist in our pin** (added to mathlib master between `25ce63313608`
  and `d68c4dc0`). Cascading failures: LevyContinuity → Limit →
  BernoulliLSI → OneDimGLSICompSmo → OneDimGLSI → TensorizedGLSI →
  GaussianLipConcen. Cherry-pick path requires vendoring Prokhorov
  + 5000+ LOC of SLT infrastructure — out of TD3 scope. TD4 paths:
  (a) project mathlib pin bump (project-wide retest cost), or
  (b) Mathlib-only from-scratch closure via Bakry-Émery / OU
  semigroup (original TD3-TD4 fallback).
* **M4 (predicate degeneracy).** `IsCenteredGaussianProcess.joint_gaussian`
  field above is `True` (round-1 placeholder). Even with M3 cleared,
  a genuine Cholesky adapter requires strengthening this predicate
  (~100 LOC of joint-Gaussian content via `HasGaussianLaw` from
  Mathlib `Probability/Distributions/Gaussian/Basic.lean:45` or via
  `BrownianMotion.Gaussian.IsGaussianProcess`) so that the matrix
  square root of the covariance pushes `stdGaussianE` to the marginal
  law of `X`.

**Mathlib-only path (no SLT) preserves the original TD4-TD5
projection** (close `gaussian_log_sobolev_real` at TD4 then iterate
Herbst per sub-lemma 2 then build the Cholesky adapter). The deletion
of sub-lemmas 1+2 in TD3 (round 3, this branch) is independent of
sub-lemma 3 closure: Path B′ chains directly through sub-lemma 3, and
sub-lemmas 1+2 were post-Path-B′ orphans (Q3 + grep verification).
TD4 closure of sub-lemma 3 either via SLT (post-M1 user clearance)
or from-scratch (Bakry-Émery / Ornstein-Uhlenbeck semigroup) is now
the cluster's open thread.

**Adapter sketch for the post-M1 path** (so T2.1 has a "tried" line
even on abort):

1. Strengthen `IsCenteredGaussianProcess` (or harmonise with
   `BrownianMotion.Gaussian.IsGaussianProcess`) so finite-dimensional
   marginals carry an actual `HasGaussianLaw` predicate. ~100 LOC.
2. Define the covariance matrix `Σ : Matrix T T ℝ` with
   `Σ i j = ∫ ω, X i ω * X j ω ∂ℙ`; show `PosSemidef Σ` from
   `IsCenteredGaussianProcess` (joint-Gaussian + centered ⇒ PosSemidef
   covariance, via `Matrix.posSemidef_iff_eq_transpose_mul_self` on the
   cross-term integral). ~40 LOC.
3. Take `A := Σ.sqrt` (Mathlib `Matrix.PosSemidef.sqrt`); push
   `stdGaussianE T` to the joint law of `X` via `Measure.map A`
   (using `IsCenteredGaussianProcess` to identify the laws). ~80 LOC.
4. Sup-of-coordinates `(s : T → ℝ) ↦ ⨆ t, s t` is 1-Lipschitz in
   `EuclideanSpace ℝ T` (`Mathlib`'s `LipschitzWith` API). ~20 LOC.
5. Compose with `A`-pushed pullback ⇒ centred sup is
   `‖A‖`-Lipschitz functional of the standard Gaussian; apply SLT
   `lipschitz_cgf_bound` (post-M1) to get the CGF inequality. ~50 LOC.
6. Package CGF inequality + SLT integrability into
   `HasSubgaussianMGF` via Mathlib's structure constructor. ~40 LOC.
7. Identify `‖A‖² = ‖Σ‖op = sigma2` (using `hσ_var` and
   `Matrix.PosSemidef.sqrt_norm_sq`). ~30 LOC.

Total: 360 LOC. Cf. Grok Q1 estimate of 150-250 LOC — third TD3
underestimate; documented in T1.1 audit §D.
-/
theorem lipschitz_sup_finite_gaussian
    {Ω T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [Fintype T] [Nonempty T]
    (X : T → Ω → ℝ)
    (_hgauss : IsCenteredGaussianProcess X)
    (sigma2 : ℝ) (_hσ_pos : 0 < sigma2)
    (_hσ_var : ∀ t, Var[X t; (ℙ : Measure Ω)] ≤ sigma2)
    (_hM_int : Integrable (fun ω => ⨆ t, X t ω) ℙ) :
    HasSubgaussianMGF
      (fun ω => (⨆ s, X s ω) - ∫ ω', (⨆ s, X s ω') ∂ℙ)
      sigma2.toNNReal ℙ := by
  sorry  -- TAG: TrackD-LipschitzSup

/- ## Main theorem — Borell-Tsirelson-Ibragimov-Sudakov -/

/-- **Borell-Tsirelson-Ibragimov-Sudakov (BTIS) Gaussian concentration
inequality.**

For a Fintype-indexed centered Gaussian process `X : T → Ω → ℝ` with
variance budget `sigma2 := sup_t Var(X_t) > 0`, the supremum
`M(ω) := ⨆ t, X t ω` concentrates around its mean:
`ℙ(M ≥ 𝔼[M] + r) ≤ exp(−r² / (2 sigma2))` for every `r > 0`.

This is the canonical sub-Gaussian-tail BTIS bound. The two-sided form
`ℙ(|M − 𝔼[M]| ≥ r) ≤ 2 exp(−r²/(2sigma2))` follows by applying the one-sided
form to both `X` and `−X`, both of which are centered Gaussian processes
with the same variance budget.

**Proof outline (Path B′, round-2 closure).** Combine
`lipschitz_sup_finite_gaussian` (sub-Gaussian MGF for `M − 𝔼[M]` with
parameter `sigma2`, packaged as `HasSubgaussianMGF`) with Mathlib's
`HasSubgaussianMGF.measure_ge_le` (Chernoff inequality at line 704 of
`Probability/Moments/SubGaussian.lean` in our pinned Mathlib).

The Chernoff bound concludes
`ℙ.real {ω | r ≤ Y ω} ≤ exp(−r²/(2 c))`
for `Y := M − 𝔼[M]` and `c := sigma2.toNNReal`. The set
`{ω | r ≤ Y ω}` is exactly `{ω | M ω ≥ 𝔼[M] + r}` (after expanding
`Y` and shuffling), and `(c : ℝ) = sigma2` since `sigma2 > 0`. The
`Measure.real` ↔ `(· ).toReal` translation is `measureReal_def`.

**Status (round-2 closure, Path B′; round-3 chain consolidation).**
**Full** body — closes the BTIS theorem modulo the single sub-lemma 3
sorry (`TrackD-LipschitzSup`). The chain
`BTIS ← Lipschitz-sup-via-SLT-CGF` is structurally locked at the
file level: round-3 TD3 T2.2 deletion of the post-Path-B′ orphans
sub-lemmas 1 (`gaussian_log_sobolev_real`) and 2
(`herbst_subgaussian_real`) consolidated the chain to a single open
TAG. TD4 closes sub-lemma 3 via the SLT `lipschitz_cgf_bound` adapter
(see sub-lemma 3 docstring for the recipe).

Continuous-T generalization (replacing `Fintype T` by
`SecondCountableTopology T` with sample-path-bounded hypothesis) is a
separate downstream lemma deferred to TD6+ if the consumer surface ever
needs it; the GLW Phase A consumer in `gao_li_wellner_small_ball_upper`
uses a discrete grid and only needs the Fintype form.
-/
theorem borell_tis
    {Ω T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [Fintype T] [Nonempty T]
    (X : T → Ω → ℝ)
    (hgauss : IsCenteredGaussianProcess X)
    (sigma2 : ℝ) (hσ_pos : 0 < sigma2)
    (hσ_var : ∀ t, Var[X t; (ℙ : Measure Ω)] ≤ sigma2)
    (hM_int : Integrable (fun ω => ⨆ t, X t ω) ℙ)
    (r : ℝ) (hr : 0 < r) :
    (ℙ {ω | (⨆ t, X t ω) ≥ (∫ ω', (⨆ t, X t ω') ∂ℙ) + r}).toReal ≤
      Real.exp (-r ^ 2 / (2 * sigma2)) := by
  -- (1) Sub-Gaussian MGF wrapper for the centered sup (sub-lemma 3).
  have hSG : HasSubgaussianMGF
      (fun ω => (⨆ s, X s ω) - ∫ ω', (⨆ s, X s ω') ∂ℙ)
      sigma2.toNNReal ℙ :=
    lipschitz_sup_finite_gaussian X hgauss sigma2 hσ_pos hσ_var hM_int
  -- (2) Apply Chernoff at threshold r ≥ 0.
  have hChern := hSG.measure_ge_le hr.le
  -- (3) Bridge `μ.real` to `(μ ·).toReal` (rfl).
  have hToReal : ((ℙ : Measure Ω) {ω | r ≤ (⨆ s, X s ω) -
        ∫ ω', (⨆ s, X s ω') ∂ℙ}).toReal ≤
      Real.exp (-r ^ 2 / (2 * (sigma2.toNNReal : ℝ))) := hChern
  -- (4) Rewrite the Chernoff event as the BTIS goal event.
  have hSetEq : {ω : Ω | r ≤ (⨆ s, X s ω) - ∫ ω', (⨆ s, X s ω') ∂ℙ} =
      {ω | (⨆ t, X t ω) ≥ (∫ ω', (⨆ t, X t ω') ∂ℙ) + r} := by
    ext ω
    simp only [Set.mem_setOf_eq, ge_iff_le]
    constructor <;> intro h <;> linarith
  rw [hSetEq] at hToReal
  -- (5) `(sigma2.toNNReal : ℝ) = sigma2` since `sigma2 > 0`.
  have hCoe : (sigma2.toNNReal : ℝ) = sigma2 := Real.coe_toNNReal _ hσ_pos.le
  rw [hCoe] at hToReal
  exact hToReal

end Erdos524.Helpers.BTISHonestProof
