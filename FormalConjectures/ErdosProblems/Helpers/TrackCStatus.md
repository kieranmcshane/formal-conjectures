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
