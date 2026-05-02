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

Round-1 infrastructure for the Borell-Tsirelson-Ibragimov-Sudakov (BTIS)
Gaussian concentration inequality. This file lands the BTIS theorem
signature plus three sub-lemma signatures along the route (β) — Gaussian
log-Sobolev → Herbst → Lipschitz functional concentration → BTIS.

**Round-2 closure (Path B′, this round).** The main theorem `borell_tis`
is now a **Full** body: it deduces the BTIS tail bound from sub-lemma 3
(`lipschitz_sup_finite_gaussian`, packaging the centered sup as a
`HasSubgaussianMGF`) plus Mathlib's Chernoff bound
`HasSubgaussianMGF.measure_ge_le`. Sub-lemmas 1–3 retain TAG'd `sorry`
bodies pending TD3-TD4 closure. See
`Helpers/TrackD_round2_T1_PortabilityAudit.md` for the path-decision
rationale.

Closure at TD3-TD4 may proceed either by adapting Yuanhe Zhang et al.'s
`lean-stat-learning-theory` (MIT-licensed, toolchain-matched at
`v4.27.0-rc1`, Mathlib pin offset minor), or from-scratch via
Bakry-Émery / Ornstein-Uhlenbeck semigroup methods. Path B (manual port)
is currently favoured; see the round-2 audit doc for the full ranking.

See `Helpers/TrackD_T1_BTISAudit.md` for the round-1 Mathlib + brownian-motion
audit and the route-(β) feasibility analysis, and
`Helpers/TrackD_round2_T1_PortabilityAudit.md` for the round-2
portability assessment.

## Route (β) chain (Grok Q4)

1. `gaussian_log_sobolev_real` — TD3 bottleneck. Standard 1D Gaussian
   logarithmic Sobolev inequality. Multivariate generalization deferred
   pending Mathlib gradient + entropy infrastructure.
2. `herbst_subgaussian_real` — TD4. Herbst's argument: log-Sobolev +
   Lipschitz hypothesis → sub-Gaussian MGF. Light bookkeeping once (1)
   is in scope.
3. `lipschitz_sup_finite_gaussian` — TD4-TD5. Sup of a finite-index
   centered Gaussian process has a sub-Gaussian MGF with parameter
   `sup_t Var(X_t)`, packaged as `HasSubgaussianMGF`. (Round-2
   signature change: conclusion lifted from bare MGF inequality to the
   full `HasSubgaussianMGF` structure to feed `borell_tis` directly.)
4. `borell_tis` — **Full at round-2 closure (Path B′)**. Deduces the
   BTIS tail bound from sub-lemma 3 + Mathlib's
   `HasSubgaussianMGF.measure_ge_le` (Chernoff). Body is mechanical:
   set translation + `Real.toNNReal` coercion + `Measure.real ↔ toReal`
   bridging.

## Round-1 design notes

* Index type `T : Fintype` keeps the supremum well-defined as a finite
  max and avoids separability/measurability technicalities. Continuous-T
  generalization is straightforward once the Fintype version lands.
* The Gaussianity hypothesis is carried as `IsCenteredGaussianProcess` —
  a minimal predicate defined locally to keep round-1 dependencies thin.
  TD5 can either replace this with `BrownianMotion.Gaussian.IsGaussianProcess`
  or harmonize with `Erdos524.Helpers.IsGLWProcess` (whichever is more
  ergonomic for the consumer surface).
* Sub-lemma 1 is stated for `gaussianReal 0 1` (standard 1D Gaussian)
  rather than multivariate `EuclideanSpace ℝ n` — the multivariate form
  follows by tensor product once 1D log-Sobolev is closed, but the 1D
  case alone exercises every interesting feature of the proof (Herbst
  iteration, entropy ↔ MGF transfer).
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

/- ## Sub-lemma 1 (TD2-TD3 bottleneck) — Gaussian log-Sobolev -/

/-- **Gaussian log-Sobolev inequality (1D).**

For the standard real Gaussian `γ = gaussianReal 0 1`, every smooth
`f : ℝ → ℝ` (with the obvious integrability conditions) satisfies
the entropy bound
`Ent_γ(f²) := 𝔼_γ[f² log f²] − 𝔼_γ[f²] · log 𝔼_γ[f²] ≤ 2 𝔼_γ[(f')²]`.

This is the bottleneck of the route-(β) chain: log-Sobolev + Lipschitz
→ sub-Gaussian MGF (Herbst), and sub-Gaussian MGF + Mathlib Chernoff →
BTIS tail. Multivariate version follows by tensorisation once the 1D
case is closed.

**Status.** TAG'd `TrackD-LogSobolev-bottleneck` — TD2-TD3 closure target.
Closure routes (per `TrackD_T1_BTISAudit.md` §4):
* If `lean-stat-learning-theory` portable: import + adapt;
* Else: from-scratch via Bakry-Émery / Ornstein-Uhlenbeck semigroup.
-/
theorem gaussian_log_sobolev_real
    (f : ℝ → ℝ) (_hf_diff : Differentiable ℝ f)
    (_hf_sq_int : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (_hf_sq_log_int :
        Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (gaussianReal 0 1))
    (_hf_deriv_sq_int : Integrable (fun x => deriv f x ^ 2) (gaussianReal 0 1)) :
    (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(gaussianReal 0 1)) -
        (∫ x, f x ^ 2 ∂(gaussianReal 0 1)) *
          Real.log (∫ x, f x ^ 2 ∂(gaussianReal 0 1)) ≤
      2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1) := by
  sorry  -- TAG: TrackD-LogSobolev-bottleneck

/- ## Sub-lemma 2 (TD3-TD4) — Herbst's argument -/

/-- **Herbst's argument: log-Sobolev + Lipschitz → sub-Gaussian MGF.**

Given the log-Sobolev inequality on `gaussianReal 0 1` and an `L`-Lipschitz
`f : ℝ → ℝ` with `𝔼_γ[f] = 0`, the Herbst iteration on the entropy of
`exp(t f / 2)` yields the sub-Gaussian moment-generating-function bound
`𝔼_γ[exp(t f)] ≤ exp(L² t² / 2)` for all `t : ℝ`.

This is the standard Herbst-iteration corollary; once
`gaussian_log_sobolev_real` is closed, the proof is mechanical
(differentiate `t ↦ log 𝔼[exp(t f)] / t` and apply log-Sobolev to
`exp(t f / 2)`).

**Status.** TAG'd `TrackD-Herbst` — TD3-TD4 closure target.
-/
theorem herbst_subgaussian_real
    (f : ℝ → ℝ) (L : NNReal) (_hL_pos : 0 < L)
    (_hf_lip : LipschitzWith L f)
    (_hf_centered : ∫ x, f x ∂(gaussianReal 0 1) = 0)
    (_hf_int : ∀ t : ℝ, Integrable (fun x => Real.exp (t * f x)) (gaussianReal 0 1))
    (t : ℝ) :
    ∫ x, Real.exp (t * f x) ∂(gaussianReal 0 1) ≤
      Real.exp ((L : ℝ) ^ 2 * t ^ 2 / 2) := by
  sorry  -- TAG: TrackD-Herbst

/- ## Sub-lemma 3 (TD4-TD5) — Sup is a Lipschitz functional -/

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

**Status.** TAG'd `TrackD-LipschitzSup` — TD4-TD5 closure target. Largely
bookkeeping once Sub-lemmas 1–2 are in scope.
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

**Status (round-2 closure, Path B′).** **Full** body — closes the BTIS
theorem modulo the three sub-lemma sorries
(`TrackD-LogSobolev-bottleneck`, `TrackD-Herbst`, `TrackD-LipschitzSup`).
The chain `BTIS ← Lipschitz-sup ← Herbst ← log-Sobolev` is now structurally
locked at the file-level, with each link being either Full (this theorem)
or a single TAG'd sorry. TD3-TD4 close the upstream sub-lemmas.

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
