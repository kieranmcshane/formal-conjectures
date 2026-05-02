# Track C status — round 1 closure

**Round:** Track C round 1 (parallel-track, branch `track-c-1dkmt` from
`r33-c-helpers-consolidation` HEAD `37c671f`).
**Date:** 2026-05-02.
**Outcome:** **Full closure of mandatory floor (T1.1 + T2.1 + T2.2 + T2.3).**

This is the Track C-equivalent of `PhaseV2RXXStatus.md`, intentionally
named `TrackCStatus.md` per the brief to keep parallel-track artefacts
distinguishable from Track A's V2 round-status sequence.

## 1. Mandatory floor outcomes

| Outcome | Status | Artefact | Notes |
|---|---|---|---|
| T1.1 — Mathlib BM / KMT / Skorokhod / Donsker state audit | **Full** | `Helpers/TrackC_T1_OneDimKMTAudit.md` (~190 lines, well above the ≥30-line floor) | Confirms Grok pre-flight Q0–Q1 verdicts. `brownian-motion` package available; zero KMT/Skorokhod/Donsker hits in either `mathlib` or `brownian-motion`. Per-layer (Q2) Mathlib gap audit landed. Framing-misframing check: none. |
| T2.1 — Infrastructure file: imports + types + `oneDimKMT` signature | **Full** | `Helpers/OneDimKMT.lean` (extended; was 110 LOC, now 383 LOC). New imports: `Mathlib.Probability.Moments.Variance`, `Mathlib.Probability.CDF`, `Mathlib.MeasureTheory.Measure.Stieltjes`, `Mathlib.Probability.Distributions.Gaussian.Real`. | `theorem oneDimKMT` (line 352) signature: i.i.d. centred unit-variance summands → existential coupling to BM with `O(log(n+1))` sup-norm error a.s. Body TAG'd `TrackC-round1-infrastructure-only`. |
| T2.2 — Sub-lemma signatures for 4 layers | **Full** | Same file, lines 168–324. | Four sub-lemma signatures aligned with Grok Q2's recipe: `skorokhod_embedding_single` (Layer 1, line 168), `quantile_transform_finite_moment` (Layer 2, line 214), `hungarian_dyadic_coupling` (Layer 3, line 256), `sup_error_log_over_sqrt` (Layer 4, line 310). Each TAG'd `TrackC-Layer{1,2,3,4}-…` for round-2/3/4 closure. |
| T2.3 — Build verification + status doc | **Full** | This document + `lake build` output below. | Build of `OneDimKMT.lean` succeeded (2842/2842 jobs, 7.9s). One unrelated `brownian-motion local changes` warning (persistent ENNReal patch from R34/R38, not Track C-induced). |

All four mandatory-floor outcomes Full. Track C round 1 caps at 0
condition triggered: **none.**

## 2. Build verification log (verbatim)

```
$ lake build FormalConjectures.ErdosProblems.Helpers.OneDimKMT
warning: brownian-motion: repository '/Users/kieranmcshane/Documents/formal-conjectures/.lake/packages/brownian-motion' has local changes
✔ [2842/2842] Built FormalConjectures.ErdosProblems.Helpers.OneDimKMT (7.9s)
Build completed successfully (2842 jobs).
```

The `brownian-motion local changes` warning is the persistent ENNReal
patch tracked at `Helpers/R34_T2_5_BuildLog.md:40` and
`Helpers/R38_T1_ENatDiagnostic.md`; it predates Track C and is
unrelated to the round-1 work.

## 3. Net debt change (project ledger update)

### Axioms

* **Before Track C round 1:** 5 user-defined axioms
  (D2 `Cp_T_explicit_pointwise_axiom` private + 1D `one_dim_KMT_coupling`
  public + stepping-stone `kmt_aided_gaussian_process` + GLW lower
  `gao_li_wellner_small_ball_lower` + GLW upper
  `gao_li_wellner_small_ball_upper`).
* **After Track C round 1:** 5 user-defined axioms — **unchanged**.

The existing `axiom one_dim_KMT_coupling` (`OneDimKMT.lean:105`) is
**not** retired this round. Per Grok Q3, round-1 deliverable is
infrastructure + signature + audit only; closure attempts at any of the
four layers would fall under the "anti-pattern: optimistic single-round
closure" prohibition stated in the brief.

### Sorries

* **Before Track C round 1:** 12 TAG'd sorries project-wide (per R44/R45
  inventory).
* **After Track C round 1:** **17 TAG'd sorries** (+5).

The +5 surface area decomposes as:

| Sorry | Line | TAG label | Round-2/3/4 closure target |
|---|---|---|---|
| `oneDimKMT` body | `OneDimKMT.lean:381` | `TrackC-round1-infrastructure-only` | Round 4 (terminal; chains Layers 1–4) |
| `skorokhod_embedding_single` body | `OneDimKMT.lean:190` | `TrackC-Layer1-Skorokhod` | Round 2 or 3 |
| `quantile_transform_finite_moment` body | `OneDimKMT.lean:226` | `TrackC-Layer2-Quantile` | Round 2 (likely first to land; ~80–120 LOC) |
| `hungarian_dyadic_coupling` body | `OneDimKMT.lean:282` | `TrackC-Layer3-Hungarian-bottleneck` | Round 3 (bottleneck per Grok Q4) |
| `sup_error_log_over_sqrt` body | `OneDimKMT.lean:324` | `TrackC-Layer4-SupError` | Round 4 (terminal) |

**This +5 increase is expected** per the brief: "signature upgrades
land sorries to be retired in Track C rounds 2–4." The brief's projected
`12 → 17` ledger move matches exactly.

## 4. Track C cluster trajectory (rounds 2–4)

Per Grok Q2 + Q4 + Q5 budget estimates:

| Round | Target | LOC estimate | P(Full closure) per Grok |
|---|---|---|---|
| Track C round 2 | Layer 2 (`quantile_transform_finite_moment`) — easiest, lowest risk | 80–120 | ~0.40–0.50 |
| Track C round 3 | Layer 3 (`hungarian_dyadic_coupling`) — bottleneck (Tusnády lemma + dyadic recursion) | 300–500 | ~0.25–0.35 |
| Track C round 4 | Layer 1 (`skorokhod_embedding_single`) + Layer 4 (`sup_error_log_over_sqrt`) + assemble main `oneDimKMT` body; specialise to retire `axiom one_dim_KMT_coupling` | 150–250 (Layer 4) + ~50–100 (assembly) | ~0.20–0.30 (Layer 1 may slip to a fifth round) |
| **Cluster total** | A2 (`one_dim_KMT_coupling`) retired; net axioms 5 → 4 | 700–1200 | **~0.65–0.75** |

R59 ceiling impact (calendar): if Track C cluster completes in 3
parallel-rounds while Track A advances 3 V2 rounds (R45, R46, R47),
calendar compression saves ~3 rounds vs. sequential V2 trajectory. If
Layer 3 slips a round (most likely failure mode), saves ~2 rounds.

## 5. Branch coordination (parallel-track)

* Branch `track-c-1dkmt` created from `r33-c-helpers-consolidation` HEAD
  (`37c671f`), parallel to:
  * Track A on `r33-c-helpers-consolidation` (R45 work, HEAD `5596638`),
  * Track B on `track-b-r33cd-gaps` (R33-C/D bridge work).
* Track C round-1 commits land **only** on `track-c-1dkmt`. No
  modifications to shared files outside `Helpers/`.
* Modified files (Track C round 1):
  * `FormalConjectures/ErdosProblems/Helpers/OneDimKMT.lean` (extended).
  * `FormalConjectures/ErdosProblems/Helpers/TrackC_T1_OneDimKMTAudit.md` (new).
  * `FormalConjectures/ErdosProblems/Helpers/TrackCStatus.md` (this doc, new).

No cross-track contamination: Track C does not touch any file modified
by Track A's R45 or Track B's R33-C/D bridge work. Future merge to
`r33-c-helpers-consolidation` should be conflict-free at the file level
(only OneDimKMT.lean is modified, which neither Track A nor Track B has
touched in their parallel work).

## 6. Honesty / framing notes

* **Round 1 is a *milestone*, not a *closure*.** Per the persistent
  feedback memory (`feedback_erdos524_framing`): infrastructure rounds
  are milestones, not closures; this status doc avoids closure-tier
  language for the cluster as a whole and applies it only to the
  round-1 mandatory-floor outcomes.
* **Net axiom debt unchanged.** A2 (`one_dim_KMT_coupling`) remains an
  axiom. Track C round 1 does not claim retirement.
* **Net sorry debt increased.** +5 TAG'd sorries surface as Track C
  rounds 2–4 targets. This is the explicit and intended trade-off:
  exchange one opaque axiom for a five-step inductive structure with
  a clear closure roadmap.
* **Brier-honest predictions vs. actual:** all four mandatory floor
  outcomes had pre-round P(Full) ≥ 0.85; all four landed Full. Track C
  round 1 sits inside its predicted >90% landing band.

## 7. Status label

* **Track C round 1 outcome:** Full (all four mandatory-floor outcomes
  Full; build clean; net axiom unchanged; net sorry +5 as projected).
* **Track C cluster status:** Round 1 of ~4 complete. Layer 2 (lowest
  risk) targeted for round 2. A2 (`one_dim_KMT_coupling`) retirement
  blocked on rounds 2–4.

---

# Track C status — round 2 closure (TC2 resumption)

**Round:** Track C round 2 (parallel-track, branch `track-c-1dkmt`).
**Date:** 2026-05-02 (resumption after API stream timeout interruption of
TC2 first attempt).
**Branch HEAD post-T2.1:** `f018aea`.
**Outcome:** **Full closure of mandatory floor (T2.0 + T2.1 + T2.2).**

T1.1 audit was already committed at `db53be1` from the interrupted TC2
first attempt — reused via T2.0 sync (per process Q4 ii carry-over rule),
not redone.

## TC2.1. Mandatory floor outcomes

| Outcome | Status | Artefact | Notes |
|---|---|---|---|
| T2.0 — audit re-read + cross-synergy import check + sync section | **Full** | `Helpers/TrackC_round2_T1_GrepAudit.md` §7 (~55 lines appended to `db53be1`, committed at `ecc6600`) | Audit re-read confirmed Mathlib API surface (15 lemmas pinned at file:line). §7.1 refinement: Galois iff restriction tightened from `Ioc 0 1` (TC1 audit error) to `Ioo 0 1` (universal-μ form; p=1 fails for unbounded-support μ). §7.2: `GaussianParametricAnalysis.lean` confirmed absent on branch, not needed for L2. |
| T2.1 — Layer 2 `quantile_transform_finite_moment` Full close | **Full** | `Helpers/OneDimKMT.lean:229-371` (~143 LOC; matches Grok Q2 estimate of 80-120 modulo 20% over for the case-split measurability proof), committed at `f018aea` | Definition: `q := if p ∈ Ioo 0 1 then sInf {y \| p ≤ cdf μ y} else 0`. Galois via right-continuity + `csInf_lt_iff` + `monotone_cdf`. Measurability via `measurable_of_Iic` + case split on `0 ≤ x`. Pushforward via `Measure.ext_of_Iic` + `restrict_congr_set` (Ioo =ᵐ Ioc / NoAtoms) + Galois + volume-of-Ioo-intersect-Iic. |
| T2.2 — Build verification + status doc update | **Full** | This document + `lake build` output below. | `lake build FormalConjectures.ErdosProblems.Helpers.OneDimKMT` clean (2842/2842 jobs, 4.4s on first attempt; verified again post-branch-shift incident). |

All three mandatory-floor outcomes Full. Track C round 2 caps at 0
condition triggered: **none.**

## TC2.2. Build verification log (verbatim)

```
$ lake build FormalConjectures.ErdosProblems.Helpers.OneDimKMT
warning: brownian-motion: repository '/Users/kieranmcshane/Documents/formal-conjectures/.lake/packages/brownian-motion' has local changes
✔ [2842/2842] Built FormalConjectures.ErdosProblems.Helpers.OneDimKMT (4.4s)
Build completed successfully (2842 jobs).
```

**Side note on parallel-branch interference.** During the TC2 resumption
session, the working-tree branch repeatedly switched to
`track-d-btis-honest` and `track-d-pinbump-probe` (Track D parallel work)
due to other agent activity. Each switch was followed by an explicit
`git checkout track-c-1dkmt` to recover. The build above was performed on
a confirmed `track-c-1dkmt` checkout (HEAD `f018aea`); a transient failure
of a full-repo `lake build` mid-session was due to Track D's
`lakefile.toml` pin-bump probe regressions, not TC2's content. Branch
isolation principle (per brief §"Branch isolation strict") was preserved:
all TC2 commits on `track-c-1dkmt` only.

## TC2.3. Net debt change (project ledger update)

### Axioms

* **Before TC2:** 5 user-defined axioms (D2 + 1D `one_dim_KMT_coupling`
  + stepping-stone + GLW lower + GLW upper).
* **After TC2:** 5 user-defined axioms — **unchanged**.

A2 (`one_dim_KMT_coupling`) retirement still blocked on Layers 1, 3, 4 +
main body (TC3-TC5 cluster-rounds).

### Sorries on `track-c-1dkmt` branch

* **Before TC2:** 17 TAG'd sorries (12 baseline + 5 from TC1 surface area).
* **After TC2:** **16 TAG'd sorries** (-1, Layer 2 retired).

Surface area decomposition (post-TC2):

| Sorry | Line (post-TC2) | TAG label | Round closure target |
|---|---|---|---|
| `skorokhod_embedding_single` body | `OneDimKMT.lean:191` | `TrackC-Layer1-Skorokhod` | TC4 or TC5 |
| `hungarian_dyadic_coupling` body | `OneDimKMT.lean:410` | `TrackC-Layer3-Hungarian-bottleneck` | **TC3 (bottleneck per Grok Q4)** |
| `sup_error_log_over_sqrt` body | `OneDimKMT.lean:452` | `TrackC-Layer4-SupError` | TC5 |
| `oneDimKMT` main body | `OneDimKMT.lean:509` | `TrackC-round1-infrastructure-only` | TC5+ (chains L1-L4) |

Plus 12 pre-TC1 baseline sorries elsewhere in the project (unchanged by
TC2).

## TC2.4. Anti-mismatch hygiene compliance

Per the resumption brief's binding "Local Claude binding rule for T2.1":

1. **Pre-invocation grep verification:** all 15 Mathlib lemmas used in
   T2.1 were pinned at file:line in T1.1 §7.3 (audit committed at
   `db53be1`). ✅
2. **No Grok-recipe extrapolation:** the only signature extension (Galois
   `Ioc → Ioo`) was derived from local Claude's edge-case analysis
   (see T2.0 §7.1), NOT from Grok recipe. ✅
3. **Multi-lemma compositions documented:** the right-continuity argument
   composes `(cdf μ).right_continuous`, `nhdsWithin_mono`,
   `Tendsto.mono_left`, `ge_of_tendsto`, `csInf_lt_iff`, `monotone_cdf`,
   `self_mem_nhdsWithin` (7 lemmas); each is named in the audit table. ✅
4. **Two minor adjustments during build:** `open scoped Topology` (for
   `𝓝` notation) and `LT.lt.not_le → LT.lt.not_ge` (Mathlib deprecation
   rename, not a semantic mismatch). ✅

No new semantic-mismatch failure was introduced in TC2. The earlier
Galois iff misframing (the 5th cumulative one in V2) was caught BEFORE
T2.1 code was written, not after — the new T1.1-grep-FIRST process
working as intended.

## TC2.5. Honesty / framing notes

* **TC2 is a content-side closure.** Layer 2 is the easiest layer per
  Grok Q5 (P~0.40-0.50). Full close on first content round of the
  cluster validates the 4-round trajectory.
* **TC2 P(Full) prediction was 0.45.** Outcome: Full. Single observation,
  but inside the predicted 0.40-0.50 band.
* **Net axiom debt unchanged at 5.** A2 retirement requires TC3-TC5
  (Layers 1, 3, 4 + main body).
* **Net sorry debt -1 on branch.** 17 → 16. Per V2 trajectory plan, this
  contributes one retirement to the R52 hybrid (c) gate evaluation.
* **Carry-over efficiency:** T1.1 reuse (per process Q4 ii) compressed
  wall-clock by ~30 minutes vs. a fresh round. Resumption brief's stated
  benefit confirmed.
* **Math edge case caught (Galois iff):** the TC1 signature universally
  quantified the Galois iff over `∀ p x : ℝ`, which is provably FALSE
  for `p ∉ Ioo 0 1`. T1.1 audit's grep-FIRST process caught this; T2.0
  sync refined `Ioc 0 1 → Ioo 0 1` for universal-μ correctness. This is
  the 5th consecutive Grok pre-flight misframing in the V2 cluster (R44
  Jacobi, R45 PosSemidef.det_sqrt, R46 PosDef.isOpen-globally, TC1
  unrestricted-Galois, TC1 audit's Ioc-not-Ioo).

## TC2.6. Status label

* **Track C round 2 outcome:** Full (all three mandatory-floor outcomes
  Full; build clean; net axiom unchanged; net sorry -1).
* **Track C cluster status:** Round 2 of ~4 complete. TC3 target: Layer 3
  `hungarian_dyadic_coupling` (300-500 LOC, bottleneck per Grok Q4 with
  P(success/round) ≈ 0.25-0.35; multi-round potential).
* **R52 hybrid (c) gate contribution:** +1 retirement on track-c branch
  toward the 1.875-2.5/round target across V2 main + parallel tracks.
