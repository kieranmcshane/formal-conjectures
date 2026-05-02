# R38 T2.5 — Final build verification + closure-tier certification

## Verification timestamp

`Sat May  2 07:10:58 CEST 2026`

## Method

Direct `lake env lean <file>` compile (the authoritative compile path
on this toolchain — the `lake build FormalConjectures.ErdosProblems.524`
CLI route exhibits an unrelated Lake-internal stack trace on the
`«524»` numeric module name; see `R38_T2_ConsumerBuildLog.md` for
the side-note).

## Per-target final state

| # | Target | Exit | `error:` count | `sorry`-warning count | Status |
|---|---|---:|---:|---:|---|
| 1 | `Helpers/GLWLowerProof.lean` | 0 | 0 | 0 | ✅ GREEN |
| 2 | `Helpers/PhaseAUpperBound.lean` | 0 | 0 | 2 | ✅ GREEN (2 R35 PhaseA scaffolds, TAG'd, expected) |
| 3 | `Helpers/GLWUpperProof.lean` | 0 | 0 | 0 | ✅ GREEN (was R36-T2.5-ENat-pre-existing — RESOLVED) |
| 4 | `524.lean` (consumer) | 0 | 0 | 1 | ✅ GREEN (1 consumer sorry, TAG'd, expected) |

Logs at:

```
/tmp/r38_T25_GLWLowerProof.log
/tmp/r38_T25_PhaseAUpperBound.log
/tmp/r38_T25_GLWUpperProof.log
/tmp/r38_T25_524.log
```

## Regression check vs R37 baseline

| Target | R37 status | R38 status | Δ |
|---|---|---|---|
| `GLWLowerProof.lean` | green, 0 sorries | green, 0 sorries | none |
| `PhaseAUpperBound.lean` | green, 2 sorries (R35 scaffolds) | green, 2 sorries (same) | none |
| `GLWUpperProof.lean` | ENat-blocked | green, 0 sorries | **+green** |
| `524.lean` | ENat-blocked | green, 1 sorry (consumer) | **+green** |

No regression introduced by R38. The two previously-blocked targets
moved to green; the two previously-green targets are unchanged.

## Closure-tier certification

**Phase A consumer-level Scope 3 closure: GREEN-CONSUMER (achieved at R38).**

Per the R38 brief criteria:

* T1.1 diagnostic: produced (`R38_T1_ENatDiagnostic.md`, ≥30 lines).
* T2.1 execution: P2 patch executed (two-file surgical edit on
  `.lake/packages/brownian-motion/`), verified to rebuild bm cleanly.
* T2.2 consumer build: green (this document, `R38_T2_ConsumerBuildLog.md`).
* T2.3 audit doc: extended (`AxiomFoundationAudit.md` R38 section).
* T2.4 closure declaration: committed (`PhaseAR38Status.md`).
* T2.5 final verification: this document.
* T2.6 ship checklist: pending (next).

Mandatory floor: **6/6 land**. No P4 fallback needed. No
helpers-tier regression introduced. Tier is **GREEN-CONSUMER**, the
best of the three R38 exit paths.
