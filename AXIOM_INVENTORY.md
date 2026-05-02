# Axiom Inventory — Erdős Problem 524 (technical debt, fork branch)

This document is **fork-specific** to the
`r33-c-helpers-consolidation` branch and tracks the user-defined
axiom and Mathlib-version-skew **technical debt** of the
Gao–Li–Wellner small-ball formalization for Erdős Problem 524.

> **Project priority #1: a sorry-free *and* axiom-free Lean
> formalization of Erdős Problem 524.**
>
> The 8 axioms below are **debt to be retired**, not foundations
> to declare on. R38 makes the consumer build green so future
> axiom-retirement work has a compilable target; R38 retires no
> axiom and closes no sorry.

For the full audit, see
[`FormalConjectures/ErdosProblems/Helpers/AxiomFoundationAudit.md`](FormalConjectures/ErdosProblems/Helpers/AxiomFoundationAudit.md).

For the round-by-round status docs, see
[`FormalConjectures/ErdosProblems/Helpers/PhaseAR{34..38}Status.md`](FormalConjectures/ErdosProblems/Helpers/).

## Build status (R38 milestone, NOT closure)

* **Build infrastructure:** consumer-build-green (R38, 2026-05-02).
* **Mathematical content:** locked at R37; **no axiom retired** in
  R38, **no sorry closed** in R38.
* **All four critical compile targets:** green via
  `lake env lean <file>` (see `R38_T2_ConsumerBuildLog.md` and
  `R38_T5_FinalBuildVerification.md`).

## 8 user-defined axioms (technical debt — must retire)

| # | Axiom | Source round | Provisional retire-path |
|---|---|---|---|
| 1 | `Cp_T_explicit_pointwise_axiom` (D2) | pre-Phase-A | Mathlib-PR pipeline (1D KMT explicit constant) |
| 2 | `one_dim_KMT_coupling` | pre-Phase-A | Mathlib-PR pipeline (1D KMT statement) |
| 3 | `kmt_aided_gaussian_process` | pre-Phase-A | derive from #1+#2 once those land |
| 4 | `gao_li_wellner_small_ball_lower` | R34 | Mathlib-PR pipeline (GLW lower-side) |
| 5 | `gao_li_wellner_small_ball_upper` | R36 | Mathlib-PR pipeline (GLW upper-side) |
| 6 | `IsGLWProcess` β-path lower-Yplus | R37 | retroactive α-attempt once IndepFun/Gaussian-decomposition kit lands |
| 7 | `IsGLWProcess` β-path lower-Yminus | R37 | retroactive α-attempt (parallel to #6) |
| 8 | `IsGLWProcess` β-path upper-Yplus | R37 | retroactive α-attempt (parallel to #6/#7) |

All eight are classically correct (see the audit doc for the
classical-justification chain). The retire-paths above are
**provisional** — R39 is scheduled to harden them into a binding
roadmap (R38 stretch T3.1, deferred → R39 mandatory floor).

## 6 TAG'd `sorry` sites

* **3 R33-C / R33-D Mathlib version-skew gaps** — orthogonal to ENat,
  documented as upstream-Mathlib-pending.
* **3 R35 Phase A scaffolds** (orphan-preserved Option (a)) —
  visible at:
  * `FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean:199`
  * `FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean:290`
  * `FormalConjectures/ErdosProblems/524.lean:3889`

## ENat duplicate-declaration import collision

Pre-R38 status: blocked the consumer-level build of `524.lean`
(`error: import BrownianMotion.Auxiliary.ENNReal failed,
environment already contains 'ENat.toENNReal_iSup' from
Mathlib.Algebra.Order.Floor.Extended`).

Post-R38 status: **RESOLVED** via a P2 local-patch on the pinned
`brownian-motion` checkout. See
[`FormalConjectures/ErdosProblems/Helpers/R38_T1_ENatDiagnostic.md`](FormalConjectures/ErdosProblems/Helpers/R38_T1_ENatDiagnostic.md)
for the diagnostic, and
[`FormalConjectures/ErdosProblems/Helpers/R38_T2_BrownianMotionENNRealPatch.diff`](FormalConjectures/ErdosProblems/Helpers/R38_T2_BrownianMotionENNRealPatch.diff)
for the patch artifact.

The patch is **not durable across `lake update`**; the durable fix
is the upstream `brownian-motion` commit `4fa8fc0 bump` (which
deletes the duplicate lemma upstream), tied to a Lean v4.27 → v4.28
+ Mathlib bump. Toolchain bump deferred to V2.

## Pinned versions

* Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
* Mathlib: `25ce633136084367f182be00fdff7613ea949d27`
* brownian-motion: `91267abd71bd32e9ef6c10c9359938f24a3e1f38` (with R38 local-patch)
* kolmogorov_extension4: `2c2b44e5525186fbe23b01e6acc76460db616009`
