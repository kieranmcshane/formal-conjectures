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

## Build status (R41 V2 round 3 — chain composition advance)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R41 update):** chain composition advance for
  Phase A upper Option B. Three deliverables:
  (1) `Matrix.PosDef.inv_hasFDerivAt` Stub→Full close in
  `Helpers/MatrixDetDifferentiable.lean:200-238` (commit `1e30dda`),
  composing `hasFDerivAt_ringInverse` with the global function-equality
  bridge `Matrix.nonsing_inv_eq_ringInverse`. (2)
  `multivariateGaussianOrthantCDF_partial_offdiagonal` (MGP)
  `True := by trivial` → real `∃ d, 0 ≤ d ∧ HasDerivAt …` signature in
  `Helpers/MultivariateGaussianCDF.lean:201`. (3)
  `posDef_convex_combination` helper added (fully proved, no `sorry`)
  in `Helpers/PhaseAUpperBound.lean:182-200`, used in the
  `slepian_comparison_finite` body restructure. New audit
  `Helpers/R41_T1_ChainCompositionAudit.md` documents the refinement
  of Grok R41 pre-flight Q2: chain composition presupposes real
  signatures, not `True` placeholders.
* **All build targets remain green** (Helpers + 524 consumer); R38
  consumer-build-green + R39 + R40 V2 milestones preserved. See
  `Helpers/R41_T1_ChainCompositionAudit.md` for the cold audit and
  `Helpers/PhaseV2R41Status.md` for the round status.

## Build status (R40 V2 round 2 — differentiability infrastructure)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R40 update):** lands the differentiability
  scaffolding required by Phase A upper Option B (Slepian + SF + BTIS
  via covariance interpolation). Three new files:
  `Helpers/MatrixDetDifferentiable.lean` (T2.1 + T2.2 scaffolds),
  `Helpers/MultivariateGaussianPdf.lean` (T2.3 PDF def + bridge sig),
  `Helpers/R40_T1_DifferentiabilityAudit.md` (T1.1 Mathlib re-audit).
  T2.4 closes `sup_continuous_eq_sup_dense` body in
  `Helpers/PhaseAUpperBound.lean` with a real ε–δ density-of-rationals
  proof, retiring the `R35-T2.3-density-mechanical` sorry.
* **All build targets remain green** (Helpers + 524 consumer); R38
  consumer-build-green + R39 V2 milestones preserved. See
  `Helpers/R40_T1_DifferentiabilityAudit.md` for the cold re-audit and
  `Helpers/PhaseV2R40Status.md` for the round status.

## Build status (R39 V2 round 1 — α-tighten / α-redirect)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R39 update):** R37 cold re-audit revealed the
  3 IsGLWProcess axioms (A6/A7/A8) were unsound as stated (signature
  `Y measurable → IsGLWProcess Y` falsifiable on `Y ≡ 0`). R39
  converted them to `theorem ... := by sorry` with α-tightened
  signatures (now sound modulo {axioms #1, #2, scaling-limit theorem}).
* **All build targets remain green** (Helpers + 524 consumer); R38
  consumer-build-green milestone preserved. See
  `Helpers/R39_T1_AlphaConversionAudit.md` for the cold re-audit and
  `Helpers/PhaseV2R39Status.md` for the round status.

## 5 user-defined axioms (technical debt — must retire)

| # | Axiom | Source round | Provisional retire-path |
|---|---|---|---|
| 1 | `Cp_T_explicit_pointwise_axiom` (D2) | pre-Phase-A | V2 R54-R55 (Komlós explicit constant via decomposition + #2) |
| 2 | `one_dim_KMT_coupling` | pre-Phase-A | V2 R49-R53 (in-scope 1D KMT formalization) |
| 3 | `kmt_aided_gaussian_process` | pre-Phase-A | V2 R49-R53 (derive from #1+#2 + scaling-limit theorem; also closes V2-R39 sorries 7-9) |
| 4 | `gao_li_wellner_small_ball_lower` | R34 | V2 R40-R48 (Slepian + SF + BTIS composition) |
| 5 | `gao_li_wellner_small_ball_upper` | R36 | V2 R40-R48 (parallel to #4) |

All five are classically correct (see the audit doc for the
classical-justification chain).

**R39 retired axioms 6-8** (the 3 IsGLWProcess β-axioms) by α-tighten:
sound tightened signatures requiring KMT-coupling-rate hypothesis;
content deferred to V2 R49-R53 cluster (bundled with axiom #3
retirement). See `Helpers/AxiomFoundationAudit.md` "R39 — V2 round 1"
section.

## 11 TAG'd `sorry` sites (post-R41)

* **3 R33-C / R33-D Mathlib version-skew gaps** — orthogonal to ENat,
  documented as upstream-Mathlib-pending.
  * `FormalConjectures/ErdosProblems/Helpers/TwoDimKMTFromOneDim.lean:609`
    (R33-C iIndepFun-prod-mathlib-gap)
  * `FormalConjectures/ErdosProblems/Helpers/TwoDimKMTFromOneDim.lean:885`
    (R33-C gaussian-uncorrelated-indep-mathlib-gap)
  * `FormalConjectures/ErdosProblems/524.lean:3913`
    (R33-D form-β-to-fullsum bridge)
* **2 R35 Phase A scaffolds** (orphan-preserved Option (a)) —
  R40-T2.4 retired the `sup_continuous_eq_sup_dense` mechanical
  scaffold (was at line 290); remaining (R41 strengthened diagnostics):
  * `FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean:320`
    (`slepian_comparison_finite`, TAG `R41-T2.2-FTC-via-Stein-and-real-MGP`)
  * `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:290`
    (`multivariateGaussianOrthantCDF_differentiable_wrt_covariance`,
    TAG `R35-T2.1-mathlib-gap-density`)
* **3 V2-R39 IsGLWProcess α-tightened theorems** (axiom→sorry
  conversion with sound signature):
  * `FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean:343`
    (`gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`)
  * `FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean:367`
    (`gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`)
  * `FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:288`
    (`gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`)
* **2 V2-R40 differentiability infrastructure scaffolds** (signature
  + TAG'd Stub with concrete Mathlib API gap diagnostics; R41-T2.2
  closed PosDef.inv_hasFDerivAt Stub→Full):
  * `FormalConjectures/ErdosProblems/Helpers/MatrixDetDifferentiable.lean:132`
    (`Matrix.det.hasFDerivAt`, TAG `R40-T2.1-det-cofactor-route`)
  * `FormalConjectures/ErdosProblems/Helpers/MatrixDetDifferentiable.lean:149`
    (`Matrix.det.differentiable` wrapper, TAG `R40-T2.1-det-cofactor-route`)
  * (`Matrix.PosDef.inv_hasFDerivAt` was the third R40-T2.2 stub;
    closed by R41-T2.2 commit `1e30dda` — now Full body using
    `hasFDerivAt_ringInverse` + `Matrix.nonsing_inv_eq_ringInverse`
    bridge.)
* **1 V2-R41 MGP real-signature upgrade** (added in R41-T2.1):
  * `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:199`
    (`multivariateGaussianOrthantCDF_partial_offdiagonal`,
    TAG `R41-T2.1-bivariate-density-conditional`,
    upgraded from R40 `True := by trivial` to real
    `∃ d, 0 ≤ d ∧ HasDerivAt …` signature with TAG'd Stub body)

**R41 net Δ:** -1 sorry (PosDef.inv_hasFDerivAt closed) +1 sorry (MGP
real-signature upgrade) = 0 net change. Quality upgrade: 1 stub closure
+ 1 real-signature upgrade + `posDef_convex_combination` helper added
(fully proved, no `sorry`).

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
