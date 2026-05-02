# Track D — Round 1 — T1.1: Mathlib + brownian-motion + external SLT audit

**Branch**: `track-d-btis-honest` (created from `track-b-r33cd-gaps@5596638`).
**Target**: Borell-Tsirelson-Ibragimov-Sudakov (BTIS) Gaussian concentration —
honest proof formalization.
**Round-1 scope (per Grok Track D pre-flight Q3)**: signature + audit + trivial
lemmas only. NO closure attempt; bottleneck closure deferred to TD2-TD3 (or
TD2-TD3 compressed if external SLT formalization portable, per Q5).

---

## 1. Project pin verification (binding, post-R40/R44/R45 misframing precedent)

* `lake-manifest.json` confirms Mathlib pinned at
  `25ce633136084367f182be00fdff7613ea949d27` (HEAD inside `.lake/packages/mathlib`
  matches; commit message: *"feat: a collection of roots in a root system is
  linearly independent iff …"*).
* `brownian-motion` pinned at `91267abd71bd32e9ef6c10c9359938f24a3e1f38`.
* No staged or hidden patches override the relevant directories
  (`Mathlib/Probability`, `BrownianMotion/Gaussian`).

These two pins are the ground truth for all "available / not available" calls
below; any framing that contradicts the audit must cite a counter-example by
file:line in the pin.

## 2. Mathlib audit (rev 25ce6331)

Findings, by Q1 item from Grok Track D pre-flight:

| Q1 item | Verdict in pin | Evidence |
| --- | --- | --- |
| (a) `MeasureTheory.GaussianConcentration` named module | **NOT present** | `grep -rli "GaussianConcentration" Mathlib` → no hits |
| (b) Gaussian isoperimetric inequality | **NOT present** | `grep -rli "isoperim" Mathlib` → no hits |
| (c) Gaussian log-Sobolev / Herbst | **NOT present** | `grep -rli "logSobolev\|log_sobolev\|LogSobolev" Mathlib` → no hits; `grep -rli "herbst\|Herbst" Mathlib` → no hits |
| (d) Ehrhard symmetrization | **NOT present** | `grep -rli "ehrhard\|Ehrhard" Mathlib` → no hits |
| (e) Lipschitz Gaussian concentration | **NOT present** | `grep -rli "lipschitz" Mathlib/Probability` → no hits in concentration sense; the only "concentration" string in `Mathlib/Probability` is one comment in `SubGaussian.lean:35` |
| Borell / Tsirelson (concentration sense) | **NOT present** | `grep -rli "borell" Mathlib` → no hits; `grep -rli "tsirelson" Mathlib` returns only `Algebra/Star/CHSH.lean` (Tsirelson **bound** for Bell inequalities, unrelated to Borell-Tsirelson concentration) |

Grok's Q1 verdict (a)-(e) is therefore **confirmed against the project's
actual pin** — no misframing this round. (Discipline rule: third Grok
misframing in R40→R44→R45 series; this audit was mandatory.)

### What IS present in pin (relevant to BTIS route):

* `Mathlib/Probability/Moments/SubGaussian.lean` — Vershynin §2.5 framework:
  `Kernel.HasSubgaussianMGF`, `HasSubgaussianMGF`, `HasCondSubgaussianMGF`,
  with Chernoff-type tail `HasSubgaussianMGF.measure_ge_le` and the
  conditional / sum / max variants. (Author: Rémy Degenne 2025.)
* `Mathlib/Probability/Distributions/Gaussian/Fernique.lean` — **Fernique's
  theorem**: `IsGaussian.exists_integrable_exp_sq` (existence of `C > 0` with
  `x ↦ exp(C ‖x‖²)` integrable), plus `IsGaussian.memLp_id`
  (finite moments of all orders). (Author: Rémy Degenne 2025, ref Hairer.)

These match Grok's Q0/Q1 claim that "SubGaussian + Fernique are in core
Mathlib"; verified at the pin.

## 3. brownian-motion package audit (additional surface area)

`brownian-motion` is already a dependency; we discovered the following beyond
Mathlib:

* `BrownianMotion/Gaussian/GaussianProcess.lean` — defines class
  `IsGaussianProcess (X : T → Ω → E) (P : Measure Ω)` requiring all
  finite-dimensional restrictions to satisfy `HasGaussianLaw`. Provides
  `IsGaussianProcess.aemeasurable`, `IsGaussianProcess.modification`, and a
  battery of independence consequences (`indepFun`, `iIndepFun` over disjoint
  index sets).

This is the project-blessed predicate for "centered Gaussian process on
arbitrary index `T`, values in normed-space `E`". The BTIS signature in T2.1
will piggy-back on `IsGaussianProcess` rather than rebuilding the predicate.

`grep` for `concentration / log_sobolev / herbst / isoperim / borell` in
`brownian-motion/BrownianMotion/` returns no hits — same picture as Mathlib.

## 4. External SLT formalization portability (Yuanhe et al. 2026)

Grok Q1 cites the Feb 2026 release `lean-stat-learning-theory` (Yuanhe et al.)
as containing Gaussian concentration via log-Sobolev + Herbst route.

**This claim is NOT verifiable from inside the present sandbox**: I do not
have an active network in the current `Bash` environment to clone or fetch
the repo, and the project's `.lake/packages/` contains no copy. Two
verification routes are both deferred (per spec, Track D round 1 = signature
+ audit + portability assessment):

1. `WebFetch` against the GitHub URL (if known, e.g.
   `github.com/yuanhe/lean-stat-learning-theory` or similar) to inspect
   declarations, license, Mathlib pin compatibility.
2. `git clone` outside `.lake/` and a stand-alone build.

**Honest portability assessment for round 1**:

* If repo exists, is on a recent Mathlib pin (≤ 2 months drift from
  `25ce6331`), and is Apache-2.0 / MIT compatible with the project: high
  likelihood of saving 2-3 rounds (compresses the originally-planned
  TD2-TD5 to TD2-TD3, per Grok Q5).
* If repo is on an incompatible pin or proprietary license: stays a 5-round
  cluster (TD1-TD5 from-scratch implementation of log-Sobolev + Herbst +
  Lipschitz-sup-Gaussian).
* If repo does not exist at the cited form: same as above (no saving).

Until the verification fires (in TD2 or earlier with a focused round), Track
D plans for a 5-round cluster as the conservative case, and treats any
compression as an accelerator, not a precondition. **This conservative
posture is binding** — Track D round 2 must NOT ship a closure plan that
*requires* SLT portability without a verified dependency.

## 5. Route feasibility ranking (Grok Q2 verdict, verified)

| Route | Mathlib infrastructure (in pin) | Feasibility |
| --- | --- | --- |
| (α) Ehrhard symmetrization → BTIS | 0% (no Ehrhard, no half-space rearrangement) | **Infeasible** without a multi-month Mathlib PR |
| (β) Gaussian log-Sobolev + Herbst → Lipschitz Gaussian concentration → BTIS | SubGaussian + Fernique present; log-Sobolev + Herbst absent but routinely formalised in SLT-style libraries; isoperimetry-free | **Most feasible** |
| (γ) Direct Borell isoperimetry → Borell-TIS | 0% (no isoperimetric inequality of any kind in Mathlib `Probability`) | **Infeasible** without Mathlib PR |

Route (β) is unambiguously the only path that does not require multi-month
Mathlib infrastructure work. Track D round-1 commits to (β); round-2+ may
revisit only if the SLT portability check fails AND a faster (α)/(γ) route
opens upstream.

## 6. Sub-lemma decomposition (Grok Q4, materialised in T2.2)

The (β) route reduces BTIS to three sub-lemmas:

1. **Gaussian log-Sobolev (`gaussian_log_sobolev`)** — for the standard
   Gaussian measure on `ℝⁿ` (or `EuclideanSpace ℝ (Fin n)`),
   `Ent_γ(f²) ≤ 2 𝔼_γ[‖∇f‖²]` for smooth `f`. Bottleneck at TD2-TD3.
2. **Herbst's argument (`herbst_concentration`)** — log-Sobolev + Lipschitz
   → sub-Gaussian MGF: for `L`-Lipschitz `f` with `𝔼_γ[f] = 0`,
   `𝔼_γ[exp(λ f)] ≤ exp(L² λ² / 2)`. Light bookkeeping once log-Sobolev is
   in scope; TD4 target.
3. **Lipschitz functional of Gaussian process (`lipschitz_sup_gaussian`)** —
   on a Fintype index, the supremum `M(ω) := ⨆ t, X t ω` is `√σ²`-Lipschitz
   in the canonical Gaussian-isometry coordinates (where `σ² = sup_t Var(X_t)`).
   Combine with Herbst → BTIS. TD5 target.

Sub-lemma signatures land in T2.2 with TAG'd sorries
(`TrackD-LogSobolev-bottleneck`, `TrackD-Herbst`, `TrackD-LipschitzSup`).

## 7. Round-1 deliverable summary

| Deliverable | Status |
| --- | --- |
| Mathlib pin audit (Q1 a-e + Borell/Tsirelson) | Complete (this doc) |
| brownian-motion audit (`IsGaussianProcess`) | Complete (this doc) |
| External SLT portability — first-pass | Complete; verification deferred to TD2 |
| Route (β) selection rationale | Complete |
| Sub-lemma decomposition | Complete; signatures land in T2.2 |

**Net debt change projected for round 1**: axioms 5 → 5 (unchanged). Sorries
12 → 16 (+1 BTIS Stub + 3 sub-lemma Stubs); all four are TAG'd
`TrackD-…` and listed in `TrackDStatus.md`. R59 ceiling impact: none (round 1
is scaffolding; closure happens in TD2-TD5 / TD2-TD3 compressed).

## 8. Honest Brier-style status (round-end, infrastructure-only)

| T1 sub-outcome | Predicted P(Full) | Realised | Comment |
| --- | --- | --- | --- |
| Mathlib pin verification | 0.95 | Full | grep + sed audit; no surprise |
| brownian-motion `IsGaussianProcess` discovery | 0.30 | Full (favourable surprise) | Predicate already present; trims TD5 build effort |
| External SLT portability — full verification | 0.15 | Partial (deferred) | Network/clone not done in round 1; acknowledged honestly above |
| Route (β) selection | 0.90 | Full | Verified (α) and (γ) have zero-LOC starting infrastructure |

## 9. Anti-patterns avoided

* No reliance on Grok's claim without pin verification (Discipline rule;
  R40/R44/R45 misframing precedent).
* No premature commitment to `lean-stat-learning-theory` portability without
  a network check; portability flagged as deferred.
* No closure attempt of BTIS proper in round 1 (Grok Q3 explicit infrastructure
  scope).
* No edits to shared Track A / Track B / Track C files (`Helpers/*` other
  than the new BTIS files); branch isolation strict.
