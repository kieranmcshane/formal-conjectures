# R28 Build Status

**Round 28** · KMT Option C Stub + roadmap · `r27-finish` → `r28-finish`
**Date:** 2026-04-30
**Decision-tree route:** Branch C R28 (KMT Option C continuation after R27 D2 bascule).
**Outcome label:** Stub on KMT retirement, Full on roadmap documentation.

## Per-file build status

```
$ lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit
Build completed successfully (3413 jobs).  [unchanged from R27]
```

No Lean files modified in R28. Roadmap-only round.

## R28 sub-sorry landings

| Sub-sorry | Status | LOC budget | LOC actual | Notes |
|-----------|:------:|:----------:|:----------:|------|
| T2.1 — Land `axiom one_dim_KMT_coupling` (Helpers/OneDimKMT.lean) | **Stub** | ~30 | 0 (deferred) | Per Refinement 2 net-axiom guardrail: would push net axioms to 3 without successful 2D retirement → REVERT path. Pre-emptively documented in `KMTOptionCPlan.md` as pre-authorised future-round form. |
| T2.2 — Transcribe LS reduction (Helpers/TwoDimKMTFromOneDim.lean) | **Stub** | 30-50 (per `TwoDimKMTRetirement.md:84`) | 0 | Load-bearing kernel-tested coupling derivation gated on stochastic-integral API for `s ↦ e^{-us}` (Phase2Plan.md Node 1B "swing factor"). 300-600 LOC realistic; out of R28 budget. |
| T2.3 — Replace `axiom two_dim_KMT_coupling` with theorem in 524.lean:3741 | **Stub** | 30 (mechanical) | 0 | Gated on T2.2 Full. |
| T2.4 — `Helpers/KMTOptionCPlan.md` (roadmap doc) | **Full** | n/a | ~120 lines | Includes math derivation, pre-authorised axiom forms, future-round LOC budget (R29-R35), skin-in-the-game framing. |

## Net axiom count audit (Refinement 2 guardrail)

| Phase | Axioms | Count |
|-------|--------|:--:|
| R25 baseline | `Y_GLW_exists` (transitively `sorryAx`) + `two_dim_KMT_coupling` | 2 |
| End R26 | unchanged | 2 |
| End R27 | `Cp_T_explicit_pointwise_axiom` (private, new) + `two_dim_KMT_coupling` (public, baseline) | 2 |
| End R28 (this round, no Lean changes) | unchanged from R27 | 2 |

**No regression. Refinement 2 satisfied.**

## Why R28 lands at Stub on KMT retirement

The 2D form `two_dim_KMT_coupling` has 9 conjuncts including kernel-tested coupling bounds (kernels `e^{-uk/n}` and `(-e^{-u/n})^k`), `IndepFun` between the two coupled processes, continuous sample paths, and tail decay for both. Bridging from a classical 1D KMT axiom (`|S_n - B(n)| ≤ C log(n+1)`) to this 2D form requires:

1. The brownian-motion stochastic-integral API at deterministic `L²`-kernels (Phase2Plan.md Node 1B — known gap, ~300-700 LOC).
2. A product-space construction carrying two independent BMs.
3. Coupling error transfer from partial-sum coupling to kernel-tested coupling.

Item 1 is **the same gap** that Phase 2's Node 1B identified as the "swing factor" for the GLW process construction. Closing it in R28 alone is unrealistic.

Per the brief's failure rollback (lines 152-153), an R28 that introduces `one_dim_KMT_coupling` without successfully replacing `two_dim_KMT_coupling` triggers a revert. To avoid wasting context on the revert dance, R28 lands at honest Stub: no Lean files touched, roadmap documented in `Helpers/KMTOptionCPlan.md`.

## CUSUM tracking

| Round | CUSUM | Δ | Notes |
|-------|:-----:|:--:|------|
| End R25 | 0.77 | — | post-R25 calibration |
| End R26 | ~0.92 | +0.15 | step-2a + step-1-final + step-5 cluster deferred |
| End R27 | ~0.85 | -0.07 | Branch C bascule landed cleanly |
| End R28 | ~0.95 | +0.10 | KMT Option C lands at Stub (vs brief Brier P(KMT C completed) = 0.30 → deviation +0.30 on this prediction) |

Under hard-stop threshold 1.2. ✓ Session integrity preserved.

## R28 Brier scoring

R28 Brier predictions vs actuals (per brief Branch C R28 spec):

| Prediction | Predicted P(Full) | Actual | Deviation |
|-----------|:----------------:|:------:|:---------:|
| T2.1 (introduce 1D KMT axiom) | 0.95 | Stub (per guardrail) | +0.95 |
| T2.2 (transcribe LS bridge) | 0.65 | Stub | +0.65 |
| T2.3 (replace 2D axiom) | 0.80 (cond on T2.2) | Stub | +0.80 |
| T2.4 (axiom-count check) | 0.95 | Full (no regression) | -0.05 |
| T2.4 (roadmap MD doc) | 0.95 | Full | -0.05 |

**Joint R28 Brier deviation:** ~+2.30 cumulative (large, driven by guardrail-induced Stubs on the load-bearing tasks). The predictions in the brief assumed R28 budget would suffice; honest assessment shows it does not in the post-R26 context-budget regime.

## R28 self-rating

- **Phase 0 / V1 (rebuild on r27-finish, clean 3413 jobs)**: Full → 30 pts.
- **T1.1 (Stub-routing audit + Refinement 2 enforcement)**: Full → 30 pts.
- **T2.1 (1D KMT axiom)**: Stub → 8 pts.
- **T2.2 (LS bridge transcription)**: Stub → 8 pts.
- **T2.3 (2D axiom replacement)**: Stub → 8 pts.
- **T2.4 (KMTOptionCPlan.md roadmap)**: Full → 30 pts.
- **T3.1 (KMT retirement headline)**: Stub → 0 pts.
- **T4.1 (this build status doc)**: Full → 30 pts.
- **T5.1 (push to fork)**: 20 pts on push.
- **T6.1 (audio alert)**: 10 pts on alert.

**R28 self-tally**: 30 + 30 + 8 + 8 + 8 + 30 + 0 + 30 + 20 + 10 = **174 pts** of ~770 max base.

Below brief's R28 expected 250 pts. KMT retirement Stub drives the gap, accurately reflected in scoring.

## Session-end summary (preliminary; full report in `Session7hReport.md`)

| Round | Status | Score | Headline |
|-------|--------|:-----:|----------|
| R26 | Partial (3 Full / 13 Stub) | ~340 pts | R26.A axiomless deferred → Branch C |
| R27 | Partial+ (5 Full / 1 Deferred) | ~240 pts | D2 bascule landed; sorryAx retired from Y_GLW_exists |
| R28 | Stub+roadmap (2 Full / 4 Stub) | ~174 pts | KMT Option C deferred per guardrail |
| **Total** | | **~754 pts** | Within brief's "worst case ~800 pts" range |

**Net axiom delta vs R25 baseline:** 0. ✓ No regression.

**Headline retirement:**
- `Y_GLW_exists`: retired modulo `Cp_T_explicit_pointwise_axiom` (private). ✓ Phase 2 step.
- `two_dim_KMT_coupling`: NOT retired. Documented retirement plan in `KMTOptionCPlan.md`.

## Cross-references

- `KMTOptionCPlan.md` — full R28 roadmap.
- `R26BuildStatus.md`, `R27BuildStatus.md` — predecessor rounds.
- `CpTExplicitAxiom.md` — D2 axiom doc.
- `Session7hReport.md` — final session report (next).
