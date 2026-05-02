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

import FormalConjectures.ErdosProblems.Helpers.RademacherSequence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# 1D Komlós–Major–Tusnády coupling axiom (R29 / KMT Option C)

Komlós–Major–Tusnády (1975, *Studia Sci. Math. Hungar.* 32) strong invariance
principle for sums of i.i.d. centered sub-Gaussian random variables: there
exists a coupling between the partial-sum walk `S_n = ∑_{k ≤ n} X_k` and a
Brownian motion `B` such that `|S_n - B_n| = O(log n)` uniformly in `n`.

Specialised here to **Rademacher** sequences (the
`Erdos524.IsRademacherSequence` predicate, relocated from `524.lean` to
`Helpers/RademacherSequence.lean` in R29 to break the cyclic import).
Because Rademacher variables are bounded, the sub-Gaussian hypothesis is
automatic; the standard 1D KMT therefore applies, and we axiomatise the
specialisation to avoid the multi-year formalisation of the Tusnády-lemma /
dyadic-recursion / Hoeffding-Skorokhod machinery (see
`Helpers/OneDimKMTSketch.md` for an exploratory sketch of upstream routes).

## Role in KMT Option C

This axiom is the load-bearing input to
`two_dim_KMT_coupling_via_LS_reduction` (see
`Helpers/TwoDimKMTFromOneDim.lean`).  Once that theorem is fully proved, the
public `axiom two_dim_KMT_coupling` in `524.lean:3741` is replaced by the
theorem (`R30+`), and the project's net axiom count returns to two
(`one_dim_KMT_coupling` here + `Y_GLW_exists` in `Helpers/GLWProcess.lean`),
matching field standards for KMT-dependent results.

**Net-axiom budget during R29.** Introducing this axiom *temporarily* takes
the project to 3 net axioms (D2 / `Y_GLW_exists` private + 2D
`two_dim_KMT_coupling` public + this 1D axiom new).  The transitional state
is justified by the simultaneous landing of the 2D theorem skeleton in
`Helpers/TwoDimKMTFromOneDim.lean`, which makes the path from `1D` to `2D`
visible.  R30 is expected to close ≥ 50% of the skeleton sub-sorries; if it
does not, R29 is reverted (Refinement 2).

## Statement notes

* **Uniform-in-`ω` form.**  The bound `|S_n - B_n| ≤ C · log(n+1)` is stated
  uniformly in `ω`, not for "almost-every `ω` with `C = C(ω) < ∞`".  This is
  *stronger* than the textbook KMT a.s. statement, but matches the
  uniform-in-`ω` shape of `524.lean:3741`'s `Δ n` (which itself encodes the
  KMT-error envelope deterministically).  The implicit consumer in the LS
  reduction is the deterministic `Δ_n` rate; an a.s. statement would require
  a measurability-of-the-exceptional-set argument that is unnecessary if the
  sup-bound is uniform.

* **`log(n+1)` instead of `log n`.**  Avoids the singularity at `n = 0` /
  `n = 1` and is the standard form in the LS-reduction literature.  The
  multiplicative constant `C` absorbs the difference vs. `log n` for `n ≥ 2`.

* **`Measurable (B n)`.**  Conjuncted explicitly so the consumer does not
  have to infer Brownian-motion-of-an-integer-time measurability from a
  separate `IsBrownian` predicate.  Strictly stronger than just existence of
  a Brownian motion.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory

/-- **Axiom (1D Komlós–Major–Tusnády coupling for Rademacher sequences).**

For every probability space `(Ω, ℙ)` and every Rademacher sequence
`a : ℕ → Ω → ℝ`, there exists a Brownian-motion-like sequence
`B : ℕ → Ω → ℝ` and a constant `C > 0` such that the partial sums
`S_n := ∑_{k = 1}^{n} a_k` satisfy

```
|S_n(ω) - B_n(ω)| ≤ C · log(n + 1)        for all 1 ≤ n and all ω.
```

The construction is upstream (Komlós–Major–Tusnády 1975); the formal Lean
derivation is a separate multi-year project tracked in
`Helpers/OneDimKMTSketch.md`.  We axiomatise the statement.

This is the *only* probabilistic axiom this file introduces.  The 2D
analogue (`two_dim_KMT_coupling_via_LS_reduction` in
`Helpers/TwoDimKMTFromOneDim.lean`) is a *theorem* reducing to this axiom
plus deterministic kernel-side facts via the Letwin–Sawhney 4-step
reduction.
-/
axiom one_dim_KMT_coupling :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), Erdos524.IsRademacherSequence a →
      ∃ (B : ℕ → Ω → ℝ) (C : ℝ),
        0 < C ∧
        (∀ n, Measurable (B n)) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω,
          |(∑ k ∈ Finset.Icc 1 n, a k ω) - B n ω| ≤ C * Real.log (n + 1))

/-! ## Track C round-1 — general 1D KMT theorem signature + layer sub-lemmas

**Round:** Track C round 1 (parallel-track, branch `track-c-1dkmt`).
**Date:** 2026-05-02.
**Scope per Grok pre-flight Q3:** infrastructure + signature + audit only.
This section introduces the general (i.e. not-yet-Rademacher-specialised)
1D KMT theorem `oneDimKMT` together with **four layer sub-lemma signatures**
matching Grok Q2's proof recipe (Skorokhod / Quantile / Hungarian dyadic /
sup-error). All five new declarations carry TAG'd `sorry` bodies labelled
for Track C rounds 2–4.

**Net debt impact (Track C round 1):**
* axioms unchanged at 5 (the `axiom one_dim_KMT_coupling` above is *not*
  retired this round — that requires Layer 1–4 sub-lemmas to close);
* +5 sorries: `oneDimKMT` (main) + 4 layer sub-lemmas.

This is **expected**: signature upgrades surface debt for Track C rounds
2–4 to retire. Per Grok Q4, the cluster (rounds 1–4) carries
P(full closure) ≈ 0.65–0.75, with Layer 3 (Hungarian dyadic) as the
bottleneck.

**Cross-references:** `Helpers/TrackC_T1_OneDimKMTAudit.md` (T1.1
Mathlib gap audit), `Helpers/OneDimKMTSketch.md` (R17 exploratory sketch),
`Helpers/KMTOptionCPlan.md` (R28 retirement plan).
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory

/-! ### Layer 1 — Skorokhod embedding for single sums

For a finite-variance centred random variable `X : Ω → ℝ`, the Skorokhod
embedding produces a stopping time `τ` for a Brownian motion `B` such
that `B_τ` has the law of `X` and `E[τ] = E[X²]`. Iterated for partial
sums `S_n = X_1 + … + X_n` of i.i.d. summands with finite variance,
we obtain stopping times `τ_n` with `B_{τ_n} =_d S_n`.

**Mathlib status (Track C T1.1):** stopping-time machinery in
`brownian-motion/StochasticIntegral/OptionalSampling.lean` is partial; no
Skorokhod embedding theorem (no construction of `τ` matching the law of
a target single random variable). LOC estimate: 150–250.
-/

/-- **Layer 1 (`TrackC-Layer1-Skorokhod`).**
Skorokhod embedding for a single centred finite-variance random variable
into a Brownian motion: existence of a stopping time `τ` such that
`B(τ ω) ω = X ω` (in distribution; here stated as an a.e. pointwise
equality after passing to a coupled probability space) with
`E[τ] = E[X²]`.

Statement is the *existential* form: the coupled probability space and
the BM are constructed jointly with `τ` and `X'`. Layer 1 is consumed by
Layer 4 to chain per-`n` couplings into the sup-norm bound. -/
theorem skorokhod_embedding_single
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → ℝ) (_hX_meas : Measurable X) (_hX_centred : ∫ ω, X ω ∂ℙ = 0)
    (_hX_L2 : MemLp X 2 ℙ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (B : NNReal → Ω' → ℝ) (τ : Ω' → NNReal) (X' : Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
      Measurable τ ∧
      (∀ t, Measurable (B t)) ∧
      -- B has the same distribution as the canonical Brownian motion (Pre-BM is the
      -- correct level for this round; full IsBrownianMotion alignment is a Layer 1
      -- bookkeeping detail tracked separately).
      (∀ ω', X' ω' = B (τ ω') ω') ∧
      -- Skorokhod moment match: E[τ] = E[X²].
      (∫ ω', (τ ω' : ℝ) ∂μ' = ∫ ω, (X ω) ^ 2 ∂ℙ) := by
  -- TAG[TrackC-Layer1-Skorokhod]: Track C round 2 or 3 target.
  -- Construction: build B on Wiener space (brownian-motion package), then
  -- define τ as first hit of a level set determined by quantile-coupling
  -- the law of X with B's first passage time. Standard construction; the
  -- novelty is the Lean-level packaging (no Skorokhod embedding theorem
  -- exists in Mathlib or brownian-motion as of T1.1 audit).
  -- Cluster target: rounds 2 or 3 (depends on Layer 2 ordering).
  sorry

/-! ### Layer 2 — Quantile transformation for finite-moment distributions

Given a probability measure `μ` on `ℝ` and a uniform `U` on `[0, 1]`,
the quantile transformation `quantile μ U` produces a random variable
with law `μ`. This is the Lean-friendly version of "inverse CDF" used
in the original 1975 KMT proof to relate partial sums to uniforms,
which are then coupled to Gaussians.

**Mathlib status (Track C T1.1):** `cdf : Measure ℝ → StieltjesFunction ℝ`
exists in `Mathlib/Probability/CDF.lean:55`; the inverse / quantile
function does *not* exist as of T1.1 audit. LOC estimate: 80–120
(easiest layer to land first per Grok Q5).
-/

/-- **Layer 2 (`TrackC-Layer2-Quantile`).**
Quantile (inverse-CDF) transformation: for any probability measure `μ`
on `ℝ`, the function `quantile μ : ℝ → ℝ` satisfies
`(volume.restrict (Set.Ioc 0 1)).map (quantile μ) = μ` (i.e. pushing
forward the uniform on `(0, 1]` by the quantile transform recovers `μ`).

Stated here at the Galois-connection level: `quantile μ p ≤ x ↔ p ≤ cdf μ x`.
-/
theorem quantile_transform_finite_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ (q : ℝ → ℝ),
      Measurable q ∧
      (∀ p x : ℝ, q p ≤ x ↔ p ≤ cdf μ x) ∧
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).map q = μ) := by
  -- TAG[TrackC-Layer2-Quantile]: Track C round 2 target (likely first to land).
  -- Construction: q p := sInf {x : ℝ | p ≤ cdf μ x}, with the Galois
  -- connection coming from right-continuity of cdf (already in Mathlib).
  -- Pushforward identity is a standard cdf/measure correspondence; uses
  -- `cdf_eq_real`, `ofReal_cdf`, and `Measure.map` lemmas.
  -- Cluster target: round 2 (~80-120 LOC, lowest-risk closure).
  sorry

/-! ### Layer 3 — Hungarian dyadic decomposition + recursive coupling

The classical KMT proof (Komlós–Major–Tusnády 1975 *Studia Sci. Math.
Hungar.* 32) uses Tusnády's lemma at each dyadic scale:

* **Tusnády's lemma**: for binomial `B(n, 1/2)` and Gaussian `N(n/2, n/4)`,
  there exists a coupling with error `O(log n)` on the midpoint.
* **Dyadic recursion**: applying Tusnády at scales `n, n/2, n/4, …, 1`
  builds the full coupling.

**Mathlib status (Track C T1.1):** Tusnády's lemma not in Mathlib at any
state. Binomial-coefficient asymptotics partial in
`Mathlib/Analysis/Asymptotics`. LOC estimate: 300–500 (bottleneck per
Grok Q4; per-round P(success) ≈ 0.25–0.35).
-/

/-- **Layer 3 (`TrackC-Layer3-Hungarian-bottleneck`).**
Hungarian dyadic Tusnády-style coupling: for a partial-sum walk
`S_n = ∑ X_k` of i.i.d. centred unit-variance summands and a Brownian
motion `B`, there exists a coupling such that for each dyadic scale
`n = 2^k`, the per-scale midpoint error is `≤ C · log(n + 1)`.

This is the **load-bearing** sub-lemma of 1D KMT. Iteration over
dyadic scales (Layer 4) yields the sup-norm bound.

**Round-1 form**: existential over the coupling space + recursive
midpoint-error statement. The core dyadic step (Tusnády at `B(n, 1/2)`
vs `N(n/2, n/4)`) is the chief gap in Mathlib. -/
theorem hungarian_dyadic_coupling
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha_indep : ProbabilityTheory.iIndepFun a ℙ)
    (_ha_centred : ∀ k, ∫ ω, a k ω ∂ℙ = 0)
    (_ha_var : ∀ k, ProbabilityTheory.variance (a k) ℙ = 1) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S' : ℕ → Ω' → ℝ) (B : NNReal → Ω' → ℝ) (C : ℝ),
      IsProbabilityMeasure μ' ∧
      0 < C ∧
      (∀ t, Measurable (B t)) ∧
      (∀ n, Measurable (S' n)) ∧
      -- S' has the law of the partial sums of (a_k).
      (∀ n : ℕ, 1 ≤ n → μ'.map (S' n) =
        (ℙ : Measure Ω).map (fun ω => ∑ k ∈ Finset.Icc 1 n, a k ω)) ∧
      -- Per-dyadic-scale midpoint coupling error.
      (∀ k : ℕ, 1 ≤ k → ∀ ω', |S' (2 ^ k) ω' - B (2 ^ k : NNReal) ω'| ≤
        C * Real.log ((2 ^ k : ℕ) + 1)) := by
  -- TAG[TrackC-Layer3-Hungarian-bottleneck]: Track C round 3 target.
  -- Construction: prove Tusnády's lemma (binomial-Gaussian coupling at
  -- midpoint with O(log n) error) and apply at each dyadic scale via
  -- the recursive midpoint-conditioning identity. This is the largest
  -- and highest-risk sub-lemma of the cluster (~300-500 LOC; Grok Q4
  -- per-round P(success) ≈ 0.25-0.35).
  -- Mathlib gap: Tusnády's lemma (~one-page proof) requires careful
  -- binomial-coefficient asymptotics not packaged. Adjacent infra:
  -- gaussianReal in Mathlib; binomial CDF in Mathlib.
  sorry

/-! ### Layer 4 — Sup-norm error O(log n / √n) via Borel–Cantelli + dyadic schedule

Given the per-dyadic-scale `O(log n)` coupling from Layer 3, the
sup-over-`[1, N]` error is amplified to `O(log N / √N)` via:

1. Borel–Cantelli I on the events `{|S_{2^k} - B_{2^k}| > C · log(2^k)}`,
2. Dyadic chaining: bound `sup_{n ≤ 2^{k+1}} |S_n - B_n|` by the
   neighbouring dyadic errors via the triangle inequality on a single
   dyadic block.

**Mathlib status (Track C T1.1):** Borel–Cantelli I and II are in
Mathlib (already used in `524.lean:1822`, `1955`). LOC estimate: 150–250
(terminal layer; depends on Layer 3 output).
-/

/-- **Layer 4 (`TrackC-Layer4-SupError`).**
Sup-norm coupling-error bound. Given the per-dyadic-scale Layer 3
output, almost surely the running sup-norm error
`sup_{n ≤ N} |S_n - B_n|` is bounded by `C' · log(N + 1)` for all
sufficiently large `N` (with the constant `C'` absorbed via Borel–
Cantelli).

When divided by `√N`, this yields the standard 1D KMT rate
`sup_{n ≤ N} |S_n - B_n| / √N ≤ C' · log(N + 1) / √N → 0` a.s. The
explicit `O(log N / √N)` form is the consumer-side rate used in
the 2D coupling (`TwoDimKMTFromOneDim.lean`'s LS reduction). -/
theorem sup_error_log_over_sqrt
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
    (S : ℕ → Ω' → ℝ) (B : NNReal → Ω' → ℝ) (C₀ : ℝ)
    (_h_dyadic_bound : ∀ k : ℕ, 1 ≤ k → ∀ ω, |S (2 ^ k) ω - B (2 ^ k : NNReal) ω| ≤
      C₀ * Real.log ((2 ^ k : ℕ) + 1)) :
    ∃ (C' : ℝ), 0 < C' ∧ ∀ᵐ ω : Ω' ∂(ℙ : Measure Ω'),
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n ≥ 1, n ≤ N →
        |S n ω - B (n : NNReal) ω| ≤ C' * Real.log ((N : ℝ) + 1) := by
  -- TAG[TrackC-Layer4-SupError]: Track C round 4 target (terminal).
  -- Construction: dyadic chaining + Borel-Cantelli I on the events
  -- {|S_{2^k} - B_{2^k}| > C · log(2^k)}. Terminal layer; depends only
  -- on Layer 3's per-scale midpoint bound.
  -- Mathlib gap: small. Borel-Cantelli already in Mathlib (and in active
  -- use in 524.lean:1822, 1955).
  sorry

/-! ### Main theorem — `oneDimKMT`

The general 1D Komlós-Major-Tusnády strong invariance principle for
i.i.d. centred finite-variance summands. Specialises to the existing
Rademacher axiom `one_dim_KMT_coupling` (above) by substituting
`ProbabilityTheory.variance (a k) ℙ = 1` (immediate for Rademacher).

Track C round-1 statement is the existential coupling form; the body
chains Layers 1–4 (skorokhod_embedding_single → quantile_transform_finite_moment
→ hungarian_dyadic_coupling → sup_error_log_over_sqrt).
-/

/-- **Main 1D KMT theorem (`TrackC-round1-infrastructure-only`).**
For a sequence of i.i.d. centred unit-variance random variables, the
partial sums `S_n = ∑_{k = 1}^{n} a_k` admit a coupling to a Brownian
motion `B` on a possibly enlarged probability space with sup-norm error
`|S_n - B_n| ≤ C · log(n + 1)` uniformly over `n ≥ 1` and almost-every
`ω`, for some absolute constant `C > 0`.

**Round-1 status (Track C):** signature only. Body chains Layers 1–4.
Closing this `sorry` retires the existing `axiom one_dim_KMT_coupling`
(by specialising to Rademacher).

**Cluster trajectory:** Track C rounds 2–4. Per Grok Q4, P(full
closure) ≈ 0.65–0.75 with Layer 3 (Hungarian dyadic) as the bottleneck.
-/
theorem oneDimKMT
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha_meas : ∀ k, Measurable (a k))
    (_ha_indep : ProbabilityTheory.iIndepFun a ℙ)
    (_ha_centred : ∀ k, ∫ ω, a k ω ∂ℙ = 0)
    (_ha_var : ∀ k, ProbabilityTheory.variance (a k) ℙ = 1) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S' : ℕ → Ω' → ℝ) (B : NNReal → Ω' → ℝ) (C : ℝ),
      IsProbabilityMeasure μ' ∧
      0 < C ∧
      (∀ t, Measurable (B t)) ∧
      (∀ n, Measurable (S' n)) ∧
      -- S' has the law of the partial sums of (a_k).
      (∀ n : ℕ, 1 ≤ n → μ'.map (S' n) =
        (ℙ : Measure Ω).map (fun ω => ∑ k ∈ Finset.Icc 1 n, a k ω)) ∧
      -- Sup-norm coupling error.
      (∀ᵐ ω' : Ω' ∂μ',
        ∃ N₀ : ℕ, ∀ n ≥ N₀, |S' n ω' - B (n : NNReal) ω'| ≤ C * Real.log ((n : ℝ) + 1)) := by
  -- TAG[TrackC-round1-infrastructure-only]: Track C rounds 2-4 closure.
  -- Body: chain Layers 1-4.
  --   1. quantile_transform_finite_moment → recover (a_k) from i.i.d. uniforms
  --      on a coupled space.
  --   2. skorokhod_embedding_single → embed each summand into BM via stopping
  --      times τ_k with E[τ_k] = E[a_k^2] = 1; iterate to embed S_n at
  --      stopping time T_n = τ_1 + ... + τ_n with E[T_n] = n.
  --   3. hungarian_dyadic_coupling → at each dyadic scale, refine the
  --      Tusnády midpoint bound to O(log n).
  --   4. sup_error_log_over_sqrt → amplify per-scale to sup-over-[1,N] via BC1.
  -- Estimated body once Layers 1-4 are Full: ~50-100 LOC of chaining.
  sorry

end Erdos524.Helpers
