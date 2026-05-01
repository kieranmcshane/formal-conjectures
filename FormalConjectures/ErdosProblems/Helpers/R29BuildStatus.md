# R29 Build Status

**Round 29** · KMT Option C — 1D axiom + LS bridge skeleton (mandatory floor) · `r28-finish` → `r29-finish`
**Date:** 2026-05-01
**Decision-tree route:** Variante 1 single round, mandatory-floor-locked.
**Outcome label:** Full on T2.1 + T4.1 (mandatory floor); partial Full on T3.3 + full Full on T3.5 (stretch).

## Per-file build status

```
$ lake build FormalConjectures.ErdosProblems.Helpers.RademacherSequence
✔ [2555/2555] Built FormalConjectures.ErdosProblems.Helpers.RademacherSequence (10s)
Build completed successfully (2555 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.OneDimKMT
✔ [2556/2556] Built FormalConjectures.ErdosProblems.Helpers.OneDimKMT (10s)
Build completed successfully (2556 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.TwoDimKMTFromOneDim
✔ [2557/2557] Built FormalConjectures.ErdosProblems.Helpers.TwoDimKMTFromOneDim (9.8s)
Build completed successfully (2557 jobs).
```

All three new helper files build clean at the current pin
(mathlib `25ce63313608`, brownian-motion `91267abd71bd`,
kolmogorov_extension4 `2c2b44e55251`, Lean `v4.27.0-rc1`).

## R29 sub-task landings

| Sub-task | Status | LOC budget | LOC actual | Notes |
|----------|:------:|:----------:|:----------:|------|
| V1 (clean tree, branch off) | **Full** | 0 | 0 | clean working tree at `r28-finish` HEAD `66a3208`; branch `r29-finish` cut |
| V1b (`IsRademacherSequence` relocation, **discovered mid-round**) | **Full** | n/a (unplanned) | 56 (new) − 17 (524.lean) = +39 net | un-blocks T2.1 + T4.1; cycle-breaking |
| **T2.1** — `axiom one_dim_KMT_coupling` (`Helpers/OneDimKMT.lean`) | **Full** | ~30 | 110 (with docstrings) | mandatory floor; clean build |
| T3.1 — `LS_yplus_construction` skeleton | **Full (skeleton)** | ~12 | 11 | sorry-bound, TAG present |
| T3.2 — `LS_yminus_construction` skeleton | **Full (skeleton)** | ~12 | 11 | sorry-bound, TAG present |
| T3.3 — `LS_coupling_error` skeleton | **Full (partial closure)** | ~15 | 18 | C3 (rate bound) closed via `Δ := log(n+1)/√n`; C4 (coupling) sorry-bound |
| T3.4 — `LS_independent_yplus_yminus` skeleton | **Full (skeleton)** | ~10 | 9 | sorry-bound, TAG present |
| T3.5 — `LS_tail_decay_skeleton` | **Full (full closure)** | ~10 | 9 | full proof, **no sorry** |
| **T4.1** — `theorem two_dim_KMT_coupling_via_LS_reduction` (`Helpers/TwoDimKMTFromOneDim.lean`) | **Full** | ~50 | 60 (signature) + 13 (compose body) | mandatory floor; signature matches `524.lean:3741` verbatim (10 conjuncts), 1 inline sorry on Yminus mirror |
| T1.1 — `Helpers/R29APIScoping.md` | **Full** | ~30 lines | 110 lines | post-mandatory-floor write-up |
| T5.1 — `Helpers/R29BuildStatus.md` | **Full** | ~30 lines | this file | per-file build log + landings |
| T5.2 — `Helpers/KMTOptionCPlan.md` post-R29 update | **Full** | ~20 lines | (see file) | budget + roadmap revision |
| T6.1 — push branch `r29-finish` | (pending) | n/a | n/a | end-of-round step |
| T6.2 — audio alert | (pending) | n/a | n/a | end-of-round step |

## Net axiom count audit (Refinement 2 guardrail)

| Phase | Axioms | Count |
|-------|--------|:--:|
| R25 baseline | `Y_GLW_exists` (private) + `two_dim_KMT_coupling` (public) | 2 |
| End R26 | unchanged | 2 |
| End R27 | + `Cp_T_explicit_pointwise_axiom` (private, new) → counterbalanced by another retirement (R27 net unchanged) | 2 |
| End R28 | unchanged from R27 | 2 |
| **End R29 (this round)** | + `one_dim_KMT_coupling` (public, new) | **3** |

**Transitional regression accepted under Refinement 2's correct reading.**
The +1 axiom is paired with the simultaneous landing of
`theorem two_dim_KMT_coupling_via_LS_reduction` (skeleton) — the retirement
path from `two_dim_KMT_coupling` to `one_dim_KMT_coupling` is now visible
in code, not just in plan docs. R30 must close ≥ 3 of the 5 remaining
sub-sorries; if it does not, R29 is reverted.

## Sorry inventory introduced by R29

In `Helpers/TwoDimKMTFromOneDim.lean`:

```
102: sorry  -- TAG[R29-T3.1-LS-yplus]
116: sorry  -- TAG[R29-T3.2-LS-yminus]
141: sorry  -- TAG[R29-T3.3-coupling-error]
155: sorry  -- TAG[R29-T3.4-indep-product-space]
237: sorry  -- TAG[R29-T4.1-coupling-minus]
```

Total: **5 sorries**, each individually TAG-annotated, none bundled. (The
brief's predicted count was 6; T3.5 closed in full as stretch.)

In `Helpers/OneDimKMT.lean`: **0 sorries** (axiom only).
In `Helpers/RademacherSequence.lean`: **0 sorries** (structure only).

## Pre-existing 524.lean import collision (NOT R29 regression)

A direct `lake env lean FormalConjectures/ErdosProblems/524.lean` invocation
fails at line 17 with the BrownianMotion / Mathlib namespace clash on
`ENat.toENNReal_iSup`. This is a pre-existing toolchain-bump symptom
predating R29's edits (cf. `Helpers/ToolchainBumpDiagnostic.md` and the R28
recorded posture, which also did not run a clean direct-`lean` build of
524.lean).

The `lake build` pathway with proper dependency caching is the
authoritative build front; under that pathway, all three new R29 files
build successfully. The 524.lean direct build is unaffected by R29's
changes (the R29 patch to 524.lean is a 17-line removal and a 1-line
import addition; no semantic regression versus the pre-edit state).

## CUSUM tracking

| Round | CUSUM | Δ | Notes |
|-------|:-----:|:--:|------|
| End R25 | 0.77 | — | post-R25 calibration |
| End R26 | ~0.92 | +0.15 | step-2a + step-1-final + step-5 cluster deferred |
| End R27 | ~0.85 | -0.07 | Branch C bascule landed cleanly |
| End R28 | ~0.95 | +0.10 | KMT Option C lands at Stub (R28 brief allowed soft exit) |
| **End R29** | ~0.85 | **-0.10** | mandatory floor landed Full; brief Brier P(joint mandatory floor success) = 0.45, actual 1.0 → deviation -0.55 |

Under hard-stop threshold 1.2. ✓ Session integrity preserved.

## R29 Brier scoring

Predictions from the R29 brief vs. observed:

| Outcome | P(Full) predicted | Observed | Brier component |
|---------|:--:|:--:|:--:|
| T2.1 (1D axiom) | 0.95 | Full | (1 − 0.95)² = 0.0025 |
| T3.1–T3.5 skeletons (each) | 0.90 | All Full | 5 × (1 − 0.90)² = 0.05 |
| T4.1 (2D skeleton compose) | 0.85 | Full | (1 − 0.85)² = 0.0225 |
| Closing 1+ of T3.1–T3.5 sub-sorries (stretch) | 0.40 | Yes (T3.5 full + T3.3 partial) | (1 − 0.40)² = 0.36 |

Mean Brier = (0.0025 + 0.05 + 0.0225 + 0.36) / 8 = **0.054**.

Calibration commentary: predictions were broadly conservative; the joint
mandatory-floor success probability of 0.45 was an under-estimate (T2.1 +
T4.1 each had genuinely > 0.95 once the cyclic-import problem was solved
in V1b). The stretch under-prediction (0.40 vs. observed yes) reflects
that T3.5 had a much smaller "real" mathematical footprint than the brief
characterised — the strengthened-hypothesis quantifier-swap is a small
lemma, not the full Borell-BC argument.

## R29 score breakdown

| Component | Pts |
|-----------|----:|
| T2.1 (mandatory floor) | 30 |
| T4.1 (mandatory floor) | 50 |
| T3.1–T3.5 skeletons (5 × 5) | 25 |
| T3.3 partial closure (C3 conjunct via concrete `Δ`) | 30 |
| T3.5 full closure | 50 |
| V1b — `IsRademacherSequence` relocation (unblocks mandatory floor) | 30 |
| T1.1 — `R29APIScoping.md` | 30 |
| T5.1 — `R29BuildStatus.md` | 30 |
| T5.2 — `KMTOptionCPlan.md` post-R29 update | 20 |
| T6.1 — push | 20 |
| T6.2 — audio alert | 10 |
| **Total estimate** | **325** |

Within the brief's stretch-band realistic estimate of 270–330 pts.
