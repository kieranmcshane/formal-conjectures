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

## Build status (R47 V2 round 9 — MGE three-bridge diagnostic + Phase 2 deferral)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone).
* **Branch:** `r46-track-a-mge-posdef` HEAD `03699d8`.
* **Net debt change:** 0 sorries retired across R47 (12 → 12). Round
  outcome: lower distribution per T1.1 audit prediction. Foundational
  + diagnostic-quality only.
* **Total mainline debt:** 5 user-defined axioms + 12 TAG'd sorries =
  17 items.
* **Cumulative R40-R47 retirement rate:** ~0.5 sorry/round (was
  ~0.43/round at R46 close); 8 rounds total elapsed since R39.
* **Three deliverables this round:**
  * **R47-T1.1 grep audit + framing verification**
    (`Helpers/R47_T1_GrepAuditAndFramingVerification.md`, ~269 lines)
    catches the R44/R45/R46 sub-gap (b) "80-120 LOC" cost estimate
    error. Verified at pin `mathlib4 @ 25ce63313608` that sub-gap (b)
    decomposes into THREE intermediate Mathlib bridges — n-ary
    Pi-withDensity factorization (~80-120 LOC), Map-withDensity
    through measurable equiv (~30-50 LOC), Lebesgue-on-EuclideanSpace
    identification (~20-100 LOC). Revised total: ~150-280 LOC, NOT
    80-120. Also flagged Phase 2 body Full close as blocked on three
    prerequisites (MGE main + `Matrix.det.differentiable` R40 Stub +
    uniform Gaussian-tail integrability).
  * **R47-T2.1 MGE Stub diagnostic-quality enhancement** (commit
    `dfc88bc`). MGE main Stub body updated with the three-bridge
    decomposition + concrete LOC estimates + Mathlib API gap citations
    + R48-R49 closure path. Round-attempt at Bridge (b.A) Full helper
    revealed non-trivial typeclass-inference issues (`SigmaFinite`
    constraint propagation, `lintegral_mul_const` finiteness side-
    conditions); aborted per honest-deferral rules. Net retirement: 0.
  * **R47-T2.2 Phase 2 body deferral diagnostic** (commit `03699d8`).
    Phase 2 body Stub body updated with concrete prerequisite chain
    citing MGE main close dependency, `Matrix.det.differentiable` R40
    Stub, uniform tail bound dependency. R46 helper consumption
    pathways identified explicitly (`posDef_min_eigenvalue_pos` direct
    consumer, `GaussianParametricAnalysis` foundational scaffold,
    `det_CFC_sqrt_eq_sqrt_det` consumed inside MGE main). Net
    retirement: 0.
* **R52 milestone gate trajectory:** items at 17, gate threshold ≤ 8.
  Mainline R48-R52 trajectory retires ~4 sorries (MGE main + det.diff
  + Phase 2 sub-gaps); cumulative items 17 - 4 = 13. R52 GATE FAILS
  without Track C/D parallel contribution. Path A (axiomatize BTIS at
  R54) likelihood promoted to **probable outcome**.
* **Process discipline:** R47 experienced repeated agent-infrastructure
  branch-switching causing ~0.5h overhead. Future rounds should batch
  git operations to maintain branch context across sub-tasks.

## Build status (R45 V2 round 7 — Phase 2 diagnostic-quality enhancement)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R45 update):** lands per R45-T1.1
  framing-verification audit's mid-distribution prediction
  ("Phase 2 partial — diagnostic enhancement only"). Three deliverables:
  * **R45-T1.1 framing verification audit**
    (`Helpers/R45_T1_FramingVerificationAudit.md`, ~353 lines)
    catches two specific Grok R45 pre-flight misframings:
    * Q1.a (`Matrix.PosSemidef.det_sqrt`) claimed in
      `Mathlib.Analysis.Matrix.Order` — NOT in Mathlib at the
      project pin (0 grep hits). Closure recipe revised to ~30-50
      LOC bridge (Grok said ~20-40).
    * Q3 (Phase 2 dependency) claimed MGI Full directly provides
      `HasFDerivAt` of pdf — partially mis-attributed. MGI gives
      only the rewrite; pdf differentiability requires R40/R41
      stubs + closed-form chain rule.
    Q1.b + Q1.c verified CORRECT. Mathlib API
    `hasFDerivAt_integral_of_dominated_loc_of_lip` confirmed at
    `Mathlib/Analysis/Calculus/ParametricIntegral.lean:164`.
  * **R45-T2.1+T2.2 Phase 2 body diagnostic enhancement.** Replaces
    stale R41/R42 comment block on `MultivariateGaussianCDF.lean:160`
    R35-T2.1 sorry with audit-aligned Path γ skeleton documenting
    (i) MGI rewrite (POST-R44 EXECUTABLE), (ii) diff-under-integral
    Mathlib API target, (iii) integrand pointwise differentiability
    chain (R40 Stub black-box + R41 Full + Mathlib chain rules),
    and (iv) THREE engineering sub-gaps:
    * (A) `Matrix.PosDef.isOpen` — not packaged. ~30-80 LOC.
    * (B) Integrability of `multivariateGaussianPdf S` on
      `orthant x`. ~50-100 LOC.
    * (C) **Load-bearing.** `LipschitzOnWith` with integrable
      Lipschitz envelope. ~150-300 LOC alone.
    Single TAG'd `sorry` preserved at the same site.
  * **MGE Full close stretch (T3.1) NOT attempted** per the brief's
    hard-stop rule (mid-distribution outcome elected over optimistic
    stretch).
* **Net debt change R44 → R45:** axioms 5 → 5 (unchanged); sorries
  12 → 12 (unchanged — diagnostic-quality progress without count
  inflation).
* **All build targets remain green** (`lake env lean` clean on
  `MultivariateGaussianCDF.lean`, `MultivariateGaussianPdf.lean`,
  `MatrixDetDifferentiable.lean`, `PhaseAUpperBound.lean`); R38 +
  R39 + R40 + R41 + R42 + R43 + R44 milestones preserved.
* **R59 ceiling check:** boundary case maintained via Q5 BTIS-merge
  compression option. R45 mid-distribution outcome → 15 remaining
  rounds for pure axiom-free target (R46-R59 with zero buffer at
  R59 boundary). Recommendation for R46: Option C — MGE Full close
  (~180-290 LOC) + Phase 2 sub-gap (A) `Matrix.PosDef.isOpen`
  stretch (~30-80 LOC).

See `Helpers/PhaseV2R45Status.md` and
`Helpers/R45_T1_FramingVerificationAudit.md` for the round status
doc + framing audit.

## Track B status (parallel to R44 Track A — Mathlib re-verification round)

* **Branch:** `track-b-r33cd-gaps` (created from `r33-c-helpers-consolidation`
  at `6783d38`, after Track A's R44-T1.1 + R44-T2.2 commits had landed
  on the parent branch — a non-conflicting interleaving since the two
  tracks modify file-disjoint sets). First parallel-pattern test
  post-R43.
* **Track B contribution:** axioms 5 → 5 (unchanged), sorries
  unchanged (Track A R44-T2.2 already retired the MGI Stub, 13 → 12).
  Three TAG'd sub-Stubs refreshed at the R33-C/D Mathlib-version-skew
  gaps (`Helpers/TwoDimKMTFromOneDim.lean:660`, `:943`, `524.lean:3920`)
  with re-verification stamps confirming the gaps stand at current
  Mathlib HEAD.
* **Calibration data:** brief over-estimated single-round closure
  feasibility for Mathlib-gap sorries (P(Full) actually ~0.05–0.20 per
  sorry, not 0.55–0.65). Apply 0.5× discount for Track C/D briefs.
* See `Helpers/TrackBStatus.md` and
  `Helpers/TrackB_T1_R33cdGapsAudit.md`.

## Build status (R43 V2 round 5 — MGE/MGI signatures + Phase 1A/1B chain rule)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R43 update):** lands per Grok R43 pre-flight
  Q4 verdict (b): signatures + Phase 1A + Phase 1B in a single round.
  * **MGE / MGI signature upgrade.** `multivariateGaussian_eq_lebesgue_withDensity`
    (MGE) + `multivariateGaussianOrthantCDF_eq_lebesgue_integral` (MGI)
    upgraded from R40 `True := by trivial` placeholders to real Lean
    signatures with TAG'd Stub bodies (TAG[R43-T2.1-MGE-pushforward-jacobian-body]
    + TAG[R43-T2.1-MGI-orthant-via-MGE-body]) in
    `Helpers/MultivariateGaussianPdf.lean`.
  * **Phase 1A** (`Sα_path_hasDerivAt`) — Full Lean proof of
    `HasDerivAt (fun α => (1-α) • S_X + α • S_Y) (S_Y - S_X) α` in
    `Helpers/PhaseAUpperBound.lean:245`.
  * **Phase 1B** (`multivariateGaussianOrthantCDF_differentiableAt_along_Sα_path`)
    — Full Lean chain-rule composition giving `DifferentiableAt ℝ` for
    the composite `α ↦ orthantCDF (Σ_path α) x` at `α ∈ (0, 1)` in
    `Helpers/PhaseAUpperBound.lean:297`. No deferred R44 sub-Stub.
  * R43 elects the audit's R44 trajectory: Phase 2 (MGE/MGI body close +
    CDF diff Full body) lands in R44, then Slepian Full body in R45.
* **Net debt change R42 → R43:** axioms 5 → 5 (unchanged); sorries 11 → 13
  (+2 from MGE/MGI signature upgrades — quality upgrade replacing
  uninformative `True` placeholders with TAG'd Stubs carrying real
  mathematical content).
* **All build targets remain green** (`lake env lean` clean on
  `MultivariateGaussianPdf.lean`, `PhaseAUpperBound.lean`,
  `MultivariateGaussianCDF.lean`, `524.lean`).
* **R59 ceiling check:** preserved with 1 round buffer via Grok Q5
  BTIS-merge compression option. R43 mid-distribution outcome → 17
  remaining rounds for pure axiom-free target.

See `Helpers/PhaseV2R43Status.md` and `Helpers/R43_T1_SignatureUpgradeAudit.md`
for the round status doc + audit.

## Build status (R42 V2 round 4 — Slepian diagnostic strengthening, audit-aligned lower outcome)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R42 update):** ships the audit-aligned lower
  outcome. Strengthens the `slepian_comparison_finite` TAG'd Stub
  diagnostic in `Helpers/PhaseAUpperBound.lean:299-372` with explicit
  Mathlib API + failed-tactic citations (5 named missing symbols + 3
  failed tactics), satisfying the R42 brief's 50%-cap clause for
  "concrete sign-analysis diagnostic." Status doc
  `Helpers/PhaseV2R42Status.md` reconciles the round brief's optimistic
  single-turn-Slepian-close target (200-300 LOC per the brief) with the
  load-bearing R41 cold audit's grounded estimate (~1080 LOC across
  R43-R45). R42 elects the audit's R43+ trajectory: MGE/MGI signatures
  → CDF diff body → Slepian body, with R59 ceiling preservation
  (8 rounds slack).
* **Net debt change R41 → R42:** axioms 5 → 5, sorries 11 → 11
  (zero formal-debt change; quality upgrade via diagnostic precision).
* **All build targets remain green** (`lake env lean` clean on
  PhaseAUpperBound + MultivariateGaussianCDF; only expected sorry
  warnings); R38 + R39 + R40 + R41 milestones preserved. See
  `Helpers/PhaseV2R42Status.md` for the round status doc.

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

## 13 TAG'd `sorry` sites (post-R43 — +2 over post-R42 from MGE/MGI signature upgrades)

(Same 11 sites listed below from post-R42, plus 2 new sites:)

* **2 V2-R43 MGE/MGI real-signature upgrades** (added in R43-T2.1):
  * `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean:183`
    (`multivariateGaussian_eq_lebesgue_withDensity`,
    TAG `R43-T2.1-MGE-pushforward-jacobian-body`,
    upgraded from R40 `True := by trivial` to real
    `multivariateGaussian 0 S = volume.withDensity (ofReal ∘ pdf)`
    signature with TAG'd Stub body. Closure prerequisites: (a)
    det_CFC_sqrt_eq_sqrt_det, (b) stdGaussian_eq_lebesgue_withDensity,
    (c) constant-Jacobian linear-pushforward change-of-variables.)
  * `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean:226`
    (`multivariateGaussianOrthantCDF_eq_lebesgue_integral`,
    TAG `R43-T2.1-MGI-orthant-via-MGE-body`,
    upgraded from R40 `True := by trivial` to real orthant-CDF =
    Lebesgue-integral signature with TAG'd Stub body. Closure
    prerequisite: MGE body + standard withDensity-to-set-integral
    transfer.)

R43 also adds two **fully proved** lemmas (no `sorry`):
  * `Helpers.Sα_path_hasDerivAt` — Phase 1A linear path differentiability.
  * `Helpers.multivariateGaussianOrthantCDF_differentiableAt_along_Sα_path`
    — Phase 1B chain rule composition.

## 11 TAG'd `sorry` sites (post-R42 — pre-R43 baseline)

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
