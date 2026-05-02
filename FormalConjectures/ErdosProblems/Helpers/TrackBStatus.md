# Track B status — R33-C/D Mathlib gaps closure (parallel-pattern test)

**Branch.** `track-b-r33cd-gaps`, base `r33-c-helpers-consolidation`
HEAD `37c671f` (R43 V2 round 5 close, 2026-05-02).

**Track B HEAD at close.** This branch carries audit + three TAG
diagnostic refreshes + this status doc; net axiom change 0, net sorry
change 0.

**Parallel pattern.** Track B runs in parallel to Track A (R44 MGE+MGI
bodies + Phase 2 CDF differentiability on `r33-c-helpers-consolidation`
branch). First parallel-pattern test post-R43 upper-distribution
success.

---

## 1. Round outcome — five mandatory floor items

| # | Item | Status | Notes |
|---|---|---|---|
| T1.1 | Track B audit doc | **Complete** | `Helpers/TrackB_T1_R33cdGapsAudit.md` (~230 LOC). Read-only audit confirming R33-C verdicts at current Mathlib HEAD. |
| T2.1 | `IndepFun.covariance_eq_zero` reverse for Gaussians | **TAG'd sub-Stub refresh** | `Helpers/TwoDimKMTFromOneDim.lean:943` `?indep` case. Diagnostic preserved + Track B re-verification stamp added (~20 LOC comment). Closure-blocked by Mathlib + axiom-output gap. |
| T2.2 | `iIndepFun_prod` packaged | **TAG'd sub-Stub refresh** | `Helpers/TwoDimKMTFromOneDim.lean:660` `?ha'.iIndepFun` case. Diagnostic preserved + Track B re-verification stamp added (~30 LOC comment). Borderline closure-feasible at ~150–250 LOC; deferred to Track B-2 with wider envelope. |
| T2.3 | Ω/Ω×Ω bridge at 524.lean:3920 | **TAG'd sub-Stub refresh** | `524.lean:3920` `two_dim_KMT_coupling_legacy_Ω_form` body. Diagnostic preserved + Track B re-verification stamp added (~12 LOC comment). Dependency-blocked on T2.1 closure (path ii) and round-budget-blocked on path (i) consumer rewrite (~600–1400 LOC). |
| T2.4 | Build verification + status doc | **Complete** | `lake env lean` clean on both `Helpers/TwoDimKMTFromOneDim.lean` and `524.lean`. Only pre-existing warnings (sorry preservation + style lints). |

**Outcome distribution.** Lower-end of brief's predicted distribution
(P~0.15 stated): 0 Full closures, 3 refreshed TAG'd sub-Stubs with
concrete Mathlib API gap diagnostics + tried-tactics blocks.

**Brier-honest calibration.** Brief's per-sorry confidence estimates
(T2.1: 0.55, T2.2: 0.65) over-estimated single-round closure feasibility.
Track B ships at the lower-tail outcome that the audit's verdict
(0.05–0.20 actual per sorry) predicted, validating the conservative
read-only-first audit pattern over optimistic per-sorry triage.

---

## 2. Net debt change

* **Axioms:** 5 → 5 (unchanged).
* **Sorries:** 13 → 13 (unchanged; three refreshed diagnostics).
* **Track B branch state:** ready for merge into
  `r33-c-helpers-consolidation` post-R44 Track A landing.
* **Anticipated merge surface:** TrackBStatus.md (new) +
  TrackB_T1_R33cdGapsAudit.md (new) + comment additions in two
  existing files (no functional changes). Likely zero conflicts with
  Track A R44 since Track A modifies different files
  (`MultivariateGaussianPdf.lean`, `PhaseAUpperBound.lean`,
  `MultivariateGaussianCDF.lean`); the only shared file is
  `AXIOM_INVENTORY.md`, where Track B adds a small Track B section
  (kept ≤ 30 lines, easy three-way merge).

---

## 3. Build verification (T2.4)

Two `lake env lean` invocations on Track B HEAD:

```
$ lake env lean FormalConjectures/ErdosProblems/Helpers/TwoDimKMTFromOneDim.lean
warning: brownian-motion: repository ... has local changes
FormalConjectures/ErdosProblems/Helpers/TwoDimKMTFromOneDim.lean:556:8:
  warning: declaration uses 'sorry'
```

```
$ lake env lean FormalConjectures/ErdosProblems/524.lean
warning: brownian-motion: repository ... has local changes
... (pre-existing AMS/category/moduleDocstring style lints)
FormalConjectures/ErdosProblems/524.lean:3889:16: warning: declaration uses 'sorry'
... (more pre-existing style lints)
```

All warnings are pre-existing:

* `declaration uses 'sorry'` warnings at 556 (helper) and 3889 (legacy
  bridge) — the three sorries refreshed in T2.1, T2.2, T2.3 are
  preserved exactly (only comment blocks added above each sorry token).
* AMS/category/moduleDocstring style lints are pre-existing
  (R43 → Track B unchanged).

**Track B verdict:** comment additions did not introduce compilation
errors or new warnings.

---

## 4. Parallel pattern validation (Track B's primary purpose)

Track B was the first parallel-pattern test post-R43. Test results:

* ✅ Branch creation from `r33-c-helpers-consolidation` HEAD `37c671f`
  clean.
* ✅ No interference with Track A's `r33-c-helpers-consolidation`
  branch (Track A continues independently).
* ✅ All Track B commits land on `track-b-r33cd-gaps`; zero pushes to
  Track A branch.
* ✅ Build verification on Track B HEAD passes.
* ✅ Anticipated merge surface tiny (two new docs + comment additions
  + small AXIOM_INVENTORY note).
* ⚠️ Sorry closure rate matched lower-tail brief prediction (P~0.15):
  0 Full out of 3 attempts. Calibration data for Track C/D briefs:
  apply ~0.5× discount to per-sorry P(Full) for Mathlib-version-skew
  closures; the structural read-only audit pattern (R33-C/D style)
  predicts closure feasibility more accurately than per-sorry triage.

**Pattern verdict (parallel test):** **Validated for documentation +
diagnostic-refresh tracks.** A single Track B round delivers consistent
audit/diagnostic value without interfering with Track A.

For *closure tracks* (Track C 1D KMT, Track D BTIS honest), the
per-sorry P(Full) numbers from Track B and R33-C suggest:

* Each Mathlib-gap closure independently requires 200–500 LOC of careful
  plumbing, often with non-trivial Mathlib API uncertainty.
* A "single round, ≤150 LOC per sorry" budget is too tight for
  Mathlib-gap closures.
* Realistic Track C/D scaling: budget 2–3 rounds per Mathlib-gap closure,
  with a read-only audit round upfront to right-size the per-sorry
  envelope.

---

## 5. Track B-2 / Track C/D recommendations

For **Track B-2** (follow-up Mathlib-gap closure attempts):

1. Target file Sorry #1 (line 660, `iIndepFun` merge) FIRST: ~150–250
   LOC, no axiom-side dependency, mathematically standard.
2. Use `iIndepFun_iff_measure_inter_preimage_eq_mul` (no Fintype
   constraint) as the entry point.
3. Allocate two rounds: round 1 builds the Finset partition + cylinder
   factorization + measure-product invocation; round 2 cleans up + ships.
4. Defer file Sorry #2 (line 943, joint-Gaussian-cov-zero) until either
   Mathlib lands joint-Gaussian char-fun factorization OR
   `kmt_aided_gaussian_process` axiom is strengthened to certify
   joint Gaussianness (Track A R45+ trajectory).

For **Track C** (1D KMT) and **Track D** (BTIS honest):

* Apply 0.5× discount to brief's per-sorry P(Full) estimates for
  Mathlib-version-skew closures.
* Right-size LOC budget at 200–500 per Mathlib-gap closure.
* Always start with a read-only audit round (Track B / R33-C pattern).

---

## 6. R59 ceiling impact

Track B does not retire any sorries this round; therefore zero
contribution to R59 ceiling progress. Track B's value is in
parallel-pattern validation + Mathlib re-verification + calibration
data, all of which inform Track A R44+ trajectory and Track C/D
scaling.

R59 ceiling check: still 17 rounds remaining for pure axiom-free target
(post-R43 + 1 buffer via Q5 BTIS-merge compression). Track B ships
within budget by not consuming Track A round budget.
