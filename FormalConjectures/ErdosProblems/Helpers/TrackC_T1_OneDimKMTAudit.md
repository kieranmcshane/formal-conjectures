# Track C round 1 — T1.1 Mathlib BM / KMT state audit

**Round:** Track C round 1 (parallel-track, branch `track-c-1dkmt` from
`r33-c-helpers-consolidation` HEAD `37c671f`).
**Date:** 2026-05-02.
**Pinned packages:** `mathlib` and `brownian-motion` at the project's
`r33-c-helpers-consolidation` lockfile (same toolchain as Tracks A/B).
**Scope:** verify Grok Track C pre-flight Q0–Q1 verdicts against actual
codebase state; identify Mathlib gaps for each of Q2's four 1D KMT
proof layers.

This audit closes T1.1 of the Track C round 1 mandatory floor.

## 1. Brownian-motion package availability (Q1(a))

**Verdict: confirmed.** The `brownian-motion` package is present at
`.lake/packages/brownian-motion/` and is imported successfully into the
project at three call sites:

* `Helpers/GLWGaussianProjectiveLimit.lean` (`Continuity.KolmogorovChentsov`,
  `Gaussian.ProjectiveLimit`, `Gaussian.MultivariateGaussian`,
  `Continuity.HasBoundedInternalCoveringNumber`),
* `Helpers/MultivariateGaussianPdf.lean` (`Gaussian.MultivariateGaussian`),
* `Helpers/MultivariateGaussianCDF.lean` (`Gaussian.MultivariateGaussian`).

Relevant package modules (all `.lake/packages/brownian-motion/BrownianMotion/`):

| Module | Provides |
|---|---|
| `Gaussian/BrownianMotion.lean` | `class IsPreBrownian X P` (covariance via `gaussianLimit`); `IsPreBrownian.exists_continuous_modification`; `IsPreBrownian.hasIndepIncrements`; `HasIndepIncrements.isPreBrownian_of_hasLaw`. |
| `Gaussian/ProjectiveLimit.lean` | `gaussianLimit : Measure (ℝ≥0 → ℝ)`; `brownianCovMatrix`; `gaussianProjectiveFamily`. |
| `Continuity/KolmogorovChentsov.lean` | Continuous-modification existence theorem. |
| `Continuity/IsKolmogorovProcess.lean`, `KolmogorovChentsovInequality.lean` | Sample-path Hölder regularity machinery. |
| `Gaussian/Fernique.lean`, `Moment.lean`, `Gaussian.lean` | Sub-Gaussian moment inequalities for Gaussian processes (incl. `gaussianReal`). |
| `StochasticIntegral/*` | Itô / Doob–Meyer / quadratic-variation infrastructure (NOT used for KMT itself but adjacent). |

**`BrownianMotion.Gaussian.BrownianMotion` is not yet imported** anywhere
in the project. The reachable infrastructure is that Brownian motion
exists as a Gaussian process (`IsPreBrownian`, `gaussianLimit`,
continuous modification via Kolmogorov–Chentsov). This matches Grok Q1(a):
"BM construction available via Degenne et al. project, in core or one PR
away."

**Caveat (R34/R38 build hazard).** The companion module
`BrownianMotion.Auxiliary.ENNReal` triggers an environment collision with
`Mathlib.Algebra.Order.Floor.Extended` (`ENat.toENNReal_iSup` redeclared);
see `Helpers/R34_T2_5_BuildLog.md:40` and `Helpers/R38_T1_ENatDiagnostic.md`.
Track C round 1 avoids this module entirely; the four BM imports above
are known-safe.

## 2. KMT / Skorokhod / Donsker / strong-invariance keyword search (Q1(b))

**Verdict: confirmed (zero hits).** Comprehensive recursive grep against
both packages:

```
cd .lake/packages
grep -lriE "(skorokhod|donsker|strong.{0,3}invariance|komlos.{0,3}major|tusnady|hungarian.{0,3}construction)" \
  --include="*.lean" mathlib/Mathlib brownian-motion
# (no output)
```

There is no `ProbabilityTheory.StrongInvariance`, no Komlós–Major–Tusnády
work, and no Donsker / Skorokhod-embedding / Tusnády-lemma file in either
`mathlib` or `brownian-motion`. The only `Komlos` hit is
`brownian-motion/StochasticIntegral/Komlos.lean`, which is the unrelated
**L¹-convex Komlós lemma** used in `DoobMeyer.lean` for martingale
uniform-integrability (already noted at `Helpers/KMTStatusInventory.md:31`).

Likewise no central-limit-theorem / Berry-Esseen / Edgeworth hits in
`Mathlib/Probability` (the only matches for `central.*limit` are in
unrelated topology / dynamical-systems files).

## 3. Closest-distance theorems (Q1(c)–(d))

| Result | Status | Location | Distance to 1D KMT |
|---|---|---|---|
| BM construction (continuous-modification existence) | Available | `BrownianMotion/Gaussian/BrownianMotion.lean:289` | Provides the BM target of the coupling. Foundation, not the coupling itself. |
| Kolmogorov–Chentsov continuous modification | Available | `BrownianMotion/Continuity/KolmogorovChentsov.lean` | Used inside BM existence. Adjacent. |
| Stopping-time machinery for Brownian motion | Partial | `BrownianMotion/StochasticIntegral/OptionalSampling.lean`, `LocalMartingale.lean` | Stopping times exist as a class; **no Skorokhod embedding theorem** (no `τ : Ω → ℝ≥0` with `B_τ` matching `S_n`'s law). |
| Hölder regularity of Brownian paths | Available | `BrownianMotion/Gaussian/BrownianMotion.lean:302` (`memHolder_mk`) | Needed for the Skorokhod-route step "approximate `B_{τ_n}` by `B_n`". Adjacent. |
| Martingale moment / tail bounds | Available (limited) | `Mathlib/Probability/Martingale/*` | Convergence-oriented; quantitative tail bounds incomplete. |
| `cdf` (Stieltjes-style CDF for `Measure ℝ`) | Available | `Mathlib/Probability/CDF.lean:55` | Layer 2 quantile transform foundation. |
| Quantile / inverse-CDF transform | **Absent** | — | Layer 2 dependency. `grep -rnE "noncomputable def quantile" Mathlib` returns no hits; no `StieltjesFunction.inv` either. |
| `Variance`, `evariance` | Available | `Mathlib/Probability/Moments/Variance.lean:58`–`63` | Standard finite-moment hypothesis. |
| `gaussianReal`, `gaussianLimit` | Available | `Mathlib/Probability/Distributions/Gaussian/Real.lean`, `BrownianMotion/Gaussian/ProjectiveLimit.lean:170` | Coupling target distributions. |
| Classical CLT, Donsker, Berry–Esseen | **Absent** | — | Out-of-scope for Track C; cited only as context. |

## 4. Per-layer Mathlib gap audit (Q2's four layers)

Using Grok Q2's four-layer decomposition for 1D KMT (~700–1200 LOC total):

### Layer 1 — Skorokhod embedding for single sums (~150–250 LOC)

**Mathlib gap**: complete. No Skorokhod embedding for random walks
into Brownian motion. Stopping-time machinery exists in `brownian-motion`
but is not connected to BM-side coupling for `S_n`. Building this
requires (a) construction of `τ_n : Ω → ℝ≥0` with `B_{τ_n} =_d S_n`,
(b) `E[τ_n] = E[S_n^2] = n` (moment match), (c) tail control on
`τ_n - n`. Adjacent infrastructure: `Hölder regularity of Brownian
paths` (available, see §3).

**Track C target**: rounds 2–4 (Layer 1 sub-lemma sketched in T2.2).

### Layer 2 — Quantile transformation for finite-moment distributions (~80–120 LOC)

**Mathlib gap**: medium. `Mathlib/Probability/CDF.lean` provides
`cdf : Measure ℝ → StieltjesFunction ℝ` with monotonicity, `Iic`
measure-formula, and right-continuity. The **inverse / quantile** is
not packaged: no `noncomputable def quantile` or `StieltjesFunction.inv`
anywhere in `Mathlib`. The natural Lean construction would use
`sInf {x | F(x) ≥ p}` directly on the `StieltjesFunction`, with right-
continuity giving the standard Galois-connection identity
`F(quantile p) ≥ p ⟺ p ≤ F(quantile p)`. ~50 LOC for the def +
basic API; ~30 LOC for the U-uniform → measure-`μ` transform.

**Track C target**: rounds 2–4 (likely the easiest layer to land first).

### Layer 3 — Hungarian dyadic decomposition + recursive coupling (~300–500 LOC)

**Mathlib gap**: complete. Tusnády's lemma (binomial → Gaussian
coupling at the dyadic midpoint with `O(log n)` error) is not in
Mathlib at any state. Adjacent infrastructure: binomial-coefficient
asymptotics (partial in `Mathlib/Analysis/Asymptotics`). Dyadic
recursion is mechanical induction once Tusnády is in place. Per
`OneDimKMTSketch.md:120`, this route is **smallest of the three**
(~800 LOC for Tusnády + recursion).

**Track C target**: rounds 2–4 — **bottleneck** per Grok Q4
(realism: P(success per round) ≈ 0.25–0.35 for the Hungarian
sub-lemma alone).

### Layer 4 — Sup-norm error O(log n / √n) via Borel–Cantelli + dyadic schedule (~150–250 LOC)

**Mathlib gap**: small. Borel–Cantelli I and II are in Mathlib
(`MeasureTheory.measure_setOf_frequently_eq_zero`,
`measure_limsup_eq_one`); the project already uses both
(`524.lean:1822`, `1955`). The dyadic schedule for amplifying a
per-`n` `O(log n)` coupling to a sup-over-`[1, N]` `O(log N / √N)`
bound is straightforward chaining; ~100 LOC plus reuse of existing
Borel–Cantelli helpers.

**Track C target**: rounds 2–4 (terminal layer; depends on Layer 3
output).

## 5. Distance-to-statement summary

| Layer | LOC estimate | Mathlib infrastructure status | Track C round target |
|---|---|---|---|
| 1 — Skorokhod embedding | 150–250 | Stopping-times: partial. Hölder paths: yes. Skorokhod theorem: absent. | R2 or R3 |
| 2 — Quantile transform | 80–120 | `cdf`: yes. `quantile`: absent. | R2 (likely first to close) |
| 3 — Hungarian dyadic | 300–500 | Tusnády lemma: absent. Binomial asymptotics: partial. | R3 (bottleneck per Grok Q4) |
| 4 — Sup-error bound | 150–250 | Borel–Cantelli: yes (already used). | R4 (terminal; depends on R3) |
| **Total** | **700–1200** | | **3–4 rounds** |

Round-1 (this round) lands infrastructure + signatures only; no
sub-lemma body attempts. Per Grok Q3, this is the highest-P(success)
deliverable shape for Track C round 1.

## 6. Existing project KMT artefacts (cross-reference)

* `Helpers/OneDimKMT.lean` (110 LOC) — defines
  `axiom one_dim_KMT_coupling` (Rademacher specialisation; uniform-in-`ω`
  `O(log n)` form). **Track C extends this file** rather than creating a
  new one (per the brief's "create new file ... or extend existing" clause).
* `Helpers/OneDimKMTSketch.md` (165 LOC) — exploratory R17 sketch with
  three proof routes; recommends Tusnády-dyadic (route 3, ~800 LOC).
  **Track C round-1 audit aligns with route 3 + Skorokhod hybrid:**
  Layer 1 (Skorokhod) provides cleaner moment matching; Layer 3
  (Tusnády) is the load-bearing dyadic step. Combined, this matches
  Grok Q2's recipe.
* `Helpers/KMTStatusInventory.md` (202 LOC) — R23 baseline; confirms
  zero KMT-formalisation code in project at that round.
* `Helpers/KMTOptionCPlan.md` (550 LOC) — R28 retirement-plan stub;
  pre-authorises `axiom one_dim_KMT_coupling` form (matched by extant
  `OneDimKMT.lean:101`).
* `Helpers/TwoDimKMTRetirement.md` — Letwin–Sawhney 2D-via-1D-KMT
  reduction, already a `theorem` (`524.lean:3768`); consumes the 1D
  axiom.
* `Helpers/TwoDimKMTFromOneDim.lean` — the actual LS reduction body.

**No changes proposed to the existing artefacts in Track C round 1.**
Round-1 work is additive: new theorem signature + 4 sub-lemma
signatures, all TAG'd `TrackC-round1-infrastructure-only` /
`TrackC-Layer{1,2,3,4}-…`.

## 7. Framing-misframing check

Grok Q0 verdict: **no misframing detected.** A2 (`one_dim_KMT_coupling`)
is a genuine placeholder for the 1975 Komlós–Major–Tusnády theorem
specialised to Rademacher partial sums. Brownian-motion infrastructure
(Degenne et al. project) is available in the project's lockfile as a
`brownian-motion` Lake package. The four-layer decomposition from
Grok Q2 maps directly onto the Skorokhod / Quantile / Tusnády / sup-
error structure recorded in `OneDimKMTSketch.md`.

The remaining honest uncertainty is the Hungarian dyadic layer (Q4
bottleneck): Grok estimates P(success per round) ≈ 0.25–0.35 even with
clear inductive structure, putting Track C cluster (rounds 1–4) at
P(full closure) ≈ 0.65–0.75. Track C round 1 itself remains in
the >90% landing band per Q3 because the deliverable is signature work,
not closure.

## 8. Status label

* **Track C round 1 T1.1**: Full (this audit, ≥30 LOC line floor met
  with margin; ~190 lines of substantive content).
