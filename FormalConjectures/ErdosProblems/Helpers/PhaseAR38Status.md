# Phase A R38 Status — consumer-build-green milestone (NOT closure)

## Headline

**R38 is a build-infrastructure MILESTONE, not a mathematical closure.**

The pre-existing ENat duplicate-declaration import collision that
blocked the consumer-level build of
`FormalConjectures/ErdosProblems/524.lean` since R29 is resolved
via a P2 local-patch on the pinned `brownian-motion` checkout. All
four critical compile targets are now green:

```
GLWLowerProof.lean       : exit 0,  errors 0,  sorries 0
PhaseAUpperBound.lean    : exit 0,  errors 0,  sorries 2 (R35 PhaseA scaffolds, TAG'd)
GLWUpperProof.lean       : exit 0,  errors 0,  sorries 0
524.lean (consumer)      : exit 0,  errors 0,  sorries 1 (consumer side, TAG'd)
```

## Build status: consumer-build-green

Per the R38 brief's exit-path table:

| Tier | Definition | This run |
|---|---|---|
| GREEN-CONSUMER | ENat resolved, 524.lean compiles, code+consumer green | ✅ achieved (BUILD only) |
| DECLARED-PERSISTENT | Code-level closure only, ENat documented as upstream-pending | superseded |
| PARTIAL-FIX | ENat partially resolved | superseded |

R38's build mission is achieved. The mathematical mission
(sorry-free **and** axiom-free 524.lean) is **NOT** done; see
"Outstanding technical debt" below.

## User priority #1 (still open)

> A sorry-free **and** axiom-free Lean formalization of Erdős
> Problem 524.

R38 makes the build green; it does **not** retire any axiom or
close any sorry. The 8 user-defined axioms remain as **technical
debt**.

## What R38 changed

R38 is **infrastructure-tier**, not math-tier. The math content is
locked at R37. R38 changed exactly two source files (both inside the
vendored `.lake/packages/brownian-motion/` tree) and added five
artifacts inside `FormalConjectures/ErdosProblems/Helpers/`:

### Source patches (vendored brownian-motion)

1. `BrownianMotion/Auxiliary/ENNReal.lean`: removed lines 39–59
   (the duplicate `ENat.toENNReal_iSup` lemma + its proof body).
   This mirrors upstream `4fa8fc0 bump` on `brownian-motion`
   master, where the same lemma was deleted because Mathlib
   upstreamed an identically-stated declaration to
   `Algebra/Order/Floor/Extended.lean:211`.

2. `BrownianMotion/Continuity/CoveringNumber.lean`: added
   `import Mathlib.Algebra.Order.Floor.Extended` so the only
   intra-bm consumer of the deleted lemma (line 662) resolves to
   the Mathlib-provided version.

### Helpers tier artifacts

| File | Purpose |
|---|---|
| `R38_T1_ENatDiagnostic.md` | T1.1 diagnostic + path-selection rationale |
| `R38_T2_ConsumerBuildLog.md` | T2.2 verbatim build log |
| `R38_T2_BrownianMotionENNRealPatch.diff` | Patch artifact for reapplication |
| `R38_T2_BrownianMotionENNReal_PRE.bak.lean` | Pre-patch original file |
| `PhaseAR38Status.md` | This document |
| `R38_T6_ShipChecklist.md` | T2.6 ship-readiness checklist |

`AxiomFoundationAudit.md` was extended with an "R38 — consumer-level
Scope 3 closure" section.

## What R38 did NOT change

* **No new axioms.** The 8 user-defined axiom inventory is identical
  to R37.
* **No retired axioms.** R38 stretch task T3.3 (retroactive α-attempt
  on an `IsGLWProcess` β axiom) was not executed; budget went to
  T2.6 ship checklist instead.
* **No closed sorries.** The 6 TAG'd sorries (3 R33-C/D Mathlib
  gaps + 3 R35 Phase A scaffolds) are unchanged.
* **No proof body modifications.** `chojecki_sparse_lower_envelope_proof`
  remains at 2433 LOC; all R29–R37 helpers are byte-identical except
  for the patched bm files.
* **No project-toolchain bump.** Lean v4.27.0-rc1 and Mathlib
  `25ce6331` are unchanged; the durable upstream-bump path (P1) is
  deliberately deferred to V2.

## Outstanding technical debt (R39+ targets)

R38 leaves the following **debt** on the mainline 524 chain — items
the project must reduce before the user-priority-#1 mission
(sorry-free + axiom-free) is met.

### 8 user-defined axioms (debt class A — must retire)

All 8 are classically correct and currently labelled
upstream-Mathlib-pending. None of them is "permanent": each admits
at least one retire-path. R38 stretch task T3.1 (per-axiom retire
path mapping) was **not** executed and is carried into R39.

### 6 TAG'd `sorry` sites (debt class B — must close)

3 R33-C/D Mathlib version-skew gaps + 3 R35 Phase A scaffolds.

### Local-patch durability (debt class C — minor)

R38's bm patch is not durable across `lake update`. Durable fix is
the upstream `brownian-motion` `4fa8fc0` bump tied to a Lean v4.28
+ Mathlib bump. Deferred.

## R39+ debt-reduction roadmap

| Round | Focus | Target |
|---|---|---|
| R39 | Per-axiom retire-path audit (T3.1 from R38) | Map each of the 8 axioms to a Mathlib roadmap or local retire strategy |
| R40 | First α-path attempt on IsGLWProcess β-axioms (T3.3 from R38) | Retire 1+ of A7/A8/A9 if upstream IndepFun/Gaussian-decomposition kit suffices |
| R41+ | Stepping-stone Mathlib-PR pipeline | Long-horizon contribution path for D2 + 1D KMT + GLW lower/upper + KMT-aided-Gaussian |
| Mathlib-bump round | Toolchain bump to Lean v4.28 + Mathlib `55c8532e…` | Retires R38 local-patch durably; possibly also resolves R33-C/D gaps |

The visible 10-round span (R29–R38) brings only **build
infrastructure** to green. The mathematical infrastructure (axiom
retirement, sorry closure) is the next program.

## Ship status

R38 commits + tags `r38-consumer-build-green` and pushes the
infrastructure milestone to fork. **Not** a Phase-A-closure ship.
See `R38_T6_ShipChecklist.md` for the milestone-push sequence.

## Honest calibration retrospective

| Metric | Value |
|---|---|
| Visible round count (R29–R38) | 10 |
| Initial project projection | 2–3 |
| Calibration error | ~3–5× over budget |
| Mandatory floor land rate | 100% across all 10 rounds |
| User-defined axioms (post-R38) | 8 — **debt** |
| TAG'd sorries (post-R38) | 6 — **debt** |
| ENat blocker (R29–R37) | RESOLVED at R38 (build infra only) |
| User-priority-#1 (sorry-free + axiom-free 524) | OPEN |
