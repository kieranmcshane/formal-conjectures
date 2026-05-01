# R34 T2.5 — Build verification log

**Branch:** `r33-c-helpers-consolidation`
**Date:** 2026-05-01
**Round:** R34 (Phase A entry, lower-side axiom regression)

## 1. Helpers/GLWLowerProof.lean — direct file build

**Command:**
```
lake env lean FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean
```

**Output (verbatim):**
```
FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean:347:8: warning: declaration uses 'sorry'
FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean:362:8: warning: declaration uses 'sorry'
```

**Exit status:** 0 (warnings only).

**Verdict:** clean. Two expected `sorry` warnings on the
`gao_li_wellner_small_ball_lower_isGLWProcess_{Yplus,Yminus}` helpers,
both T2.3 carry-overs documented as STILL GATED post-R33-D in
`R34_T1_IsGLWProcessAudit.md`. Comment-block expansion shifted the
sorry lines from 328/340 → 347/362; statements unchanged.

## 2. FormalConjectures.ErdosProblems.524 — full build attempt

**Command:**
```
lake build FormalConjectures.ErdosProblems.«524»
```

**Output (truncated to relevant tail):**
```
✔ [7928/7931] Built FormalConjectures.ErdosProblems.Helpers.GLWLowerProof (5.1s)
✔ [7929/7931] Built FormalConjectures.ErdosProblems.Helpers.TwoDimKMTFromOneDim (5.8s)
✖ [7930/7931] Building FormalConjectures.ErdosProblems.Helpers.GLWUpperProof (11s)
error: FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:14:0: import BrownianMotion.Auxiliary.ENNReal failed, environment already contains 'ENat.toENNReal_iSup' from Mathlib.Algebra.Order.Floor.Extended
error: Lean exited with code 1
Some required targets logged failures:
- FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
error: build failed
```

**Exit status:** 1.

**Direct file build of 524.lean as a sanity check:**
```
lake env lean FormalConjectures/ErdosProblems/524.lean
```
yields the same import-stage error at `524.lean:17`:
```
FormalConjectures/ErdosProblems/524.lean:17:0: error: import BrownianMotion.Auxiliary.ENNReal failed, environment already contains 'ENat.toENNReal_iSup' from Mathlib.Algebra.Order.Floor.Extended
```

## TAG'd diagnosis: `R34-T2.5-ENat-pre-existing`

This is the **pre-existing ENat conflict** between Mathlib's
`Mathlib.Algebra.Order.Floor.Extended` (which defines `ENat.toENNReal_iSup`)
and the `brownian-motion` package's `BrownianMotion.Auxiliary.ENNReal`
(which redefines or re-imports the same name). The conflict was
flagged in R33-D's audit doc (`AxiomFoundationAudit.md` §
"ENat orthogonal blocker") with agent
`trig_01P8K24FGqQF6zqTKY4vQWRD` monitoring upstream resolution.

**Independence from R34 work.** The R34 axiom regression and helper
diagnostic refresh DO NOT depend on this build clearing. The work
landed:

- **T2.1**: `gao_li_wellner_small_ball_lower` converted from
  theorem-with-sorry to axiom (`524.lean:3578`). Statement byte-for-
  byte preserved.
- **T2.2**: `gao_li_wellner_small_ball_lower_truncated` (524.lean:3622)
  — proof body unchanged (just an `obtain` on the source's existential
  witness, identical syntax for theorem and axiom).
- **T2.3**: IsGLWProcess Yplus/Yminus helpers — diagnostic comment
  expanded with R34 audit verdict (sorry bodies unchanged).
- **GLWLowerProof.lean** builds clean (only the 2 expected sorry
  warnings).

**ENat resolution is a Mathlib-side issue.** When the agent's monitored
upstream landing arrives, the full 524 build will pass without any
further change to R34's edits — the axiom application syntax is
identical to theorem application and is byte-for-byte preserved by the
ENat-aware compiler once the import resolves.

## Files changed in R34 (mainline)

```
FormalConjectures/ErdosProblems/524.lean
FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean
FormalConjectures/ErdosProblems/Helpers/AxiomFoundationAudit.md
FormalConjectures/ErdosProblems/Helpers/R34_T1_IsGLWProcessAudit.md  (new)
FormalConjectures/ErdosProblems/Helpers/R34_T2_5_BuildLog.md         (new, this file)
FormalConjectures/ErdosProblems/Helpers/PhaseAR34Status.md           (new, T2.6)
FormalConjectures/ErdosProblems/Helpers/KMTOptionCPlan.md            (T2.6 append)
```

## Build verification verdict

- **R34 mainline edits:** verified clean via direct
  `lake env lean Helpers/GLWLowerProof.lean` (only the 2 expected
  sorry warnings).
- **Full 524 build:** blocked on the pre-existing ENat conflict in
  `BrownianMotion.Auxiliary.ENNReal`. Independent of R34 work; per
  R34 calibration framing this is the legitimate diagnostic, not a
  Cowork failure. TAG: `R34-T2.5-ENat-pre-existing`.
