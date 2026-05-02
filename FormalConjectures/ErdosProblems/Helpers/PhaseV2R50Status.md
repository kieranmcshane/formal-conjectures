# Phase V2 — Round R50 status (Track A mainline, GLW determinant shortcut audit)

**Date:** 2026-05-02. **Branch:** `r46-track-a-mge-posdef` HEAD post-R50
(T1.1 audit `a8b660c`, T2.1+T2.2 sub-Stubs `dbdb042`, T2.5 this entry).
**Round type:** Variante 1, single round, mainline. **T1.1 audit caught
chain mismatch on R50 brief premise** before code budget committed;
round shipped honest deferral instead of fake retirement.

## Round outcome summary

**Net debt change:** +2 sorries, 0 axiom retirement. Items 17 → 19
mainline. Worse-than-baseline by 2 items, but **honest deferral
preferred over polluting AXIOM_INVENTORY.md with a faulty A4/A5
retirement claim**.

**Distribution outcome:** **lower** (P(joint mandatory floor
audit-redirect) ~0.10 prediction at brief draft, materialized as T1.1
caught mismatch and shipped honest deferral). T2.3 + T2.4 explicitly
SKIPPED per discipline rule "if any claim cannot be verified, flag and
propose alternative".

| Sub-task | Status | Net debt impact | Commit |
|---|---|---|---|
| T1.1 Claims Verification Table + grep audit | Full ✓ (357 lines, audit doc) | 0 (audit) | `a8b660c` |
| T2.1 Lemma 4.1 deferred-paper sub-Stub | Full sub-Stub ✓ | +1 sorry | `dbdb042` |
| T2.2 Lemma 4.2 deferred-paper sub-Stub | Full sub-Stub ✓ | +1 sorry | `dbdb042` |
| T2.3 A4 + A5 axiom-to-theorem swap | **SKIPPED** (premise unverified) | 0 | n/a |
| T2.4 Q3.3 strengthening (stretch) | **SKIPPED** (depends on T2.1+T2.2 Full) | 0 | n/a |
| T2.5 build verification + AXIOM_INVENTORY + status doc + push | Full ✓ | n/a | (this commit) |

## Round mechanics

### T1.1 GLW determinant shortcut audit (commit `a8b660c`)

Comprehensive Claims Verification Table (8 rows) + grep audit + chain-
mismatch finding + alternative-path proposal. 357 lines.

**Claims VERIFIED (5/8):**
* Claim 1: `Mathlib.LinearAlgebra.Matrix.Permanent.permanent` exists
  at pin (`mathlib4/Mathlib/LinearAlgebra/Matrix/Permanent.lean:32`).
* Claim 2: `Matrix.det_smul`, `det_fromBlocks_zero₂₁`, `det_fromBlocks_zero₁₂`
  available at pin
  (`mathlib4/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:272, :674,
  :724`). `Matrix.det_tridiagonal` is NOT in Mathlib at pin (0 grep hits).
* Claim 3: `Matrix.det.differentiable` is the project Stub at
  `Helpers/MatrixDetDifferentiable.lean:144` (TAG[R40-T2.1-det-cofactor-route]),
  not Mathlib infrastructure.
* Claim 4: A4 axiom signature verified verbatim at
  `FormalConjectures/ErdosProblems/524.lean:3643` —
  `gao_li_wellner_small_ball_lower (glw : GaoLiWellnerConstants)` over
  `IsGLWProcess Y` on full half-line `u ≥ 0`.
* Claim 5: A5 axiom signature verified verbatim at
  `FormalConjectures/ErdosProblems/524.lean:3574` —
  `gao_li_wellner_small_ball_upper` truncated form
  `Icc 0 (T ε)` with existential `T : ℝ → ℝ`.

**Claims UNVERIFIED with alternative path (3/8):**
* Claim 6 (Lemma 4.1 = "matrix-level structural identity"):
  signature not specifiable from brief alone — `K_GLW^(n)` not
  defined, perturbation parameter not stated, conclusion not pinned.
  Paper not in audit window.
* Claim 7 (Lemma 4.2 = `per(A) = 1` + `det(A) = 32m·(240e⁻³)^m`):
  matrix `A` entries unstated; even the formula `32m` is ambiguous
  between `32 · m` and `32^m` interpretations. Paper not in audit
  window.
* Claim 8 (Q3.3 strengthening): exploratory, dependent on 6+7.

**Central finding: chain mismatch.** A4/A5 are Gaussian-process small-
ball asymptotics over `IsGLWProcess Y` on continuous index `u ≥ 0`;
Lemmas 4.1+4.2 are finite-dim deterministic determinant + permanent
identities for a single specific matrix. The bridge requires at
minimum the chain α/β/γ/δ/ε:
* (α) discretization of sup-over-continuous to finite grid,
* (β) Anderson's multivariate inequality (Mathlib status: 0% at pin,
  confirmed via `grep -rln "Anderson\|anderson_inequality" Mathlib/` →
  0 hits),
* (γ) tail handling for the FULL-window lower (Ledoux §1.3 bridge,
  baked into A4 signature per `524.lean:3624-3630` axiom docstring),
* (δ) optimization `m(ε) ~ |log ε|`,
* (ε) `IsGLWProcess` covariance extraction (no consumer at HEAD
  `76e9ef1`).

None of α/β/γ/δ/ε is within the brief's 110-150 LOC scope estimate.
Per axiom docstring at `524.lean:3534-3535, :3596`: "the residual
blocker was a multi-year Mathlib formalization project, not a
tactical proof gap" + "A native upper closure would require ~600-1000
LOC across 4-6 rounds" — the axioms self-identify as multi-year
Mathlib gaps.

**Existing in-tree alternate track (5909+ LOC).** Mainline already
contains an in-flight no-Gaussian / no-KMT path toward A5 retirement
via Fourier smoothing + Berry-Esseen + hierarchical Cauchy
(Q1a/b/c). Files: `CauchyDetLowerBound.lean` (3126 LOC),
`CharFunCrossBlock.lean` (635), `MultivariateSmallBallUpper.lean`
(621), `SurgicalDensityAtZero.lean` (543), `EsseenSmoothing.lean`
(817), `GaussianHierCauchyBox.lean` (167). Total: 5909 LOC in 6 files
on the mainline branch at HEAD `76e9ef1`. **The brief's "GLW
determinant shortcut" approach does not connect to this in-tree work
and would be discarded if pursued.**

**Mismatch ledger entry #16** (Cowork+Grok shared chain-level
scope-mismatch). Same family as #14 (Cowork+Grok shared per-step vs
chain-level form on Tusnády). Pattern: Cowork drafts brief
presupposing finite-dim identity = bridge to continuous-process
asymptotic; Grok validates the finite-dim identity feasibility
without flagging the bridge gap. T1.1 audit pipeline catches the
mismatch before code budget commits.

### T2.1 + T2.2 deferred-paper sub-Stubs (commit `dbdb042`)

Two honest TAG'd sub-Stubs added to
`Helpers/GLWSmallBallShortcut.lean` (un-imported file, isolated
sorries):

```lean
/-- TAG[R50-T2.1-glw-lemma-4-1-deferred-paper] -/
theorem glw_lemma_4_1_deferred_paper :
    ∀ (n : ℕ) (K E : Matrix (Fin n) (Fin n) ℝ),
      ∃ c : ℝ, HasDerivAt (fun ε : ℝ => (K + ε • E).det) c 0 := by
  sorry

/-- TAG[R50-T2.2-glw-lemma-4-2-deferred-paper] -/
theorem glw_lemma_4_2_deferred_paper :
    ∀ m : ℕ, 1 ≤ m → ∃ A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ,
      A.permanent = 1 ∧
      A.det = (32 : ℝ) * (m : ℝ) * ((240 : ℝ) * Real.exp (-3)) ^ m := by
  sorry
```

Conservative-shape signatures intended as forward-compatible deferral
records. R51+ should refine signatures (potentially adjusting
dimension or value formula) once paper access is available, or close
Full, or replace with concrete in-tree consumer construction.

T2.1 body genuinely loads on R40 `Matrix.det.differentiable` Stub at
`MatrixDetDifferentiable.lean:144`. T2.2 body genuinely requires
construction of the structured matrix `A` per GLW 2010 §4.

**File-level change**: 1 file, 95 insertions, 15 deletions
(replaced "imports + scaffolding only — no new TAG'd Stubs" docstring
with R50-deferral context + 2 sub-Stubs). Imports added:
`Mathlib.LinearAlgebra.Matrix.Permanent`.

### T2.3 + T2.4 explicit SKIP decisions

Per R50 brief discipline rule "if any claim cannot be verified, flag
explicitly and propose alternative":

* **T2.3 (A4 + A5 axiom-to-theorem swap)** — SKIPPED. The premise
  (Lemmas 4.1+4.2 = sufficient bridge) was unverified at T1.1 audit.
  Performing the swap would introduce a fake "retirement" with a
  load-bearing sorry chain that masquerades as a closed theorem.
  Per BACKGROUND.md SEMANTIC-MISMATCH DISCIPLINE rule (post-R48
  binding): "documentation from callable code" must be distinguished;
  fake retirements pollute the inventory.
* **T2.4 (Q3.3 strengthening)** — SKIPPED. Stretch goal contingent
  on T2.1+T2.2 Full closure plus a strengthened formulation, neither
  of which is viable in R50 scope.

### T2.5 build verification + push (this entry)

See §"Build verification" + §"Fork push" below.

## Mainline state at R50 close

* **6 user-defined axioms** (unchanged from R49 close).
* **13 TAG'd sorries** (was 11 at R49 close — +2 from R50-T2.1+T2.2
  deferred-paper sub-Stubs).
* **Total debt:** 19 items (was 17 at R49 close — +2 worse-than-
  baseline; honest deferral preferred over faulty retirement).
* **Cumulative R40-R50 retirement rate:** ~0.4 sorry/round (was
  ~0.5 at R49 close; R50 added +2 sub-Stubs without retirement).

## Hybrid (c) gate trajectory analysis (post-R50)

**R52 milestone gate:** items ≤ 8 required for Path B continuation.
At R50 close, items at **19** → **11 retirements needed across
R51-R52 (2 rounds) → 5.5/round average**, **infeasible under any
realistic scope**.

**R52 gate verdict (post-R50): fails decisively under hybrid (c)
without major Track C/D/branch-fork contribution.** γ floor + β R58
extension (BACKGROUND.md confirmed commitment from user post-R49/TC3)
remains the active trajectory.

**Realistic R51-R52 trajectory options:**

| Round | Candidate target | Net retirement |
|---|---|---|
| R51 | (i) Q1a/b/c track consolidation (close 1 of 3 named sorries in `MultivariateSmallBallUpper.lean:73, :238, :616`) | -1 sorry |
| R51 | (ii) γ-floor MGE axiomatization at `MultivariateGaussianPdf.lean:260` | -1 sorry, +1 axiom (item-neutral; frees R52 budget) |
| R51 | (iii) γ-floor `Matrix.det.differentiable` axiomatization at `MatrixDetDifferentiable.lean:144` | -1 sorry, +1 axiom (item-neutral) |
| R52 | continuation of R51 path + Track C/D parallel | -1 to -3 |

**Cumulative R51-R52 mainline projection:** 2-4 retirements (or
item-neutral via γ-floor). Track C/Track D parallel rounds need to
contribute ~7-9 additional retirements to reach R52 gate target ≤ 8
items — not realistic at current Track C/D pace.

**Recommendation: pivot to γ floor (β R58 extension) explicitly
acknowledged at R52 gate.** R52 gate becomes administrative count-
and-lock per BACKGROUND.md γ+β confirmed commitment; R53-R58 cluster
retires γ axioms via Mathlib upstream / from-scratch / pin-bump
coordination.

## Build verification

R50 follows the R40+ "named critical build target" convention. Full
project `lake build` (8000+ modules) includes orphan WIP files with
pre-existing build errors unrelated to Erdős 524 mainline; these
were broken at HEAD `76e9ef1` pre-R50 and remain broken post-R50.

R50 targeted-build verification (8 R50-relevant targets, all green):

```
$ lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut \
             FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF \
             FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf \
             FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound \
             FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable \
             FormalConjectures.ErdosProblems.Helpers.GLWLowerProof \
             FormalConjectures.ErdosProblems.Helpers.GLWUpperProof \
             'FormalConjectures.ErdosProblems.«524»'
✔ [7937/7937] Built FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut (19s)
Build completed successfully (7937 jobs).
```

Critical-target summary:

| Target | Status | R50 milestone |
|---|---|---|
| `GLWSmallBallShortcut` | ✅ Green | +2 deferred-paper sub-Stubs landed (T2.1+T2.2). R48-T3.2 docstring code blocks retained. |
| `MultivariateGaussianCDF` | ✅ Green | R49 axiom #6 unchanged at line 190 |
| `MultivariateGaussianPdf` | ✅ Green | R43 MGE Stub unchanged |
| `PhaseAUpperBound` | ✅ Green | Direct consumer of axiom #6 at line 404 unchanged |
| `MatrixDetDifferentiable` | ✅ Green | R40 Stubs unchanged (load-bearing on T2.1 sub-Stub) |
| `GLWLowerProof` | ✅ Green | A4 consumers unchanged |
| `GLWUpperProof` | ✅ Green | A5 consumers unchanged |
| `«524»` | ✅ Green | A4 + A5 axiom declarations unchanged at `:3574, :3643` |

Sorry-warning audit at R50 close (mainline `r46-track-a-mge-posdef`):

* **R50-T2.1-glw-lemma-4-1-deferred-paper** at
  `Helpers/GLWSmallBallShortcut.lean:226` (NEW).
* **R50-T2.2-glw-lemma-4-2-deferred-paper** at
  `Helpers/GLWSmallBallShortcut.lean:256` (NEW).
* All R49 sorry-warnings unchanged
  (`MultivariateGaussianCDF.lean:284`, `PhaseAUpperBound.lean:450`,
  `MatrixDetDifferentiable.lean:128, :144`,
  `MultivariateGaussianPdf.lean:260`, GLW α-tightened sorries,
  `524.lean:3913`, 2 `TwoDimKMTFromOneDim.lean` sorries).

**Total mainline TAG'd sorry: 13 sites** (was 11 pre-R50).

## Fork push

`r46-track-a-mge-posdef` HEAD pushed to fork at R50 wrap. R50 push
consists of:

* `a8b660c` — R50-T1.1: GLW determinant shortcut audit — chain mismatch flagged.
* `dbdb042` — R50-T2.1+T2.2: GLW Lemmas 4.1+4.2 deferred-paper sub-Stubs.
* (this commit) — R50-T2.5: build verification + AXIOM_INVENTORY.md update + this status doc.

## Round score (skin-in-the-game evaluation)

Per R50 brief skin-in-the-game caps:

* **0pt cap items (none triggered):**
  * Claims Verification Table produced ✓ (8 rows, with 5 VERIFIED
    + 3 UNVERIFIED with alternative path documentation per
    `Round50_T1_GLWShortcutAudit.md`).
  * T2.1 Lemma 4.1 sub-Stub committed ✓ (`dbdb042`,
    `Helpers/GLWSmallBallShortcut.lean:226`, `lake env lean` clean).
  * T2.2 Lemma 4.2 sub-Stub committed ✓ (`dbdb042`,
    `Helpers/GLWSmallBallShortcut.lean:256`).
  * T2.5 build verified + push completed ✓.
  * Track branches not modified ✓.
* **50% cap items (none triggered):**
  * No axiom-to-theorem swap done (T2.3 explicitly SKIPPED with
    documented justification — no fake retirement).
  * Anti-mismatch hygiene maintained (every Mathlib lemma in T1.1
    audit grep-verified at pin; chain mismatch caught and flagged).
  * Internal consistency between anchor block and skin-in-the-game:
    audit + status doc internally consistent on the +2 sorry / 0
    axiom retirement outcome.

**Realistic round score**: lower distribution (audit-redirect outcome,
+2 worse-than-baseline mainline items but T1.1 pipeline saved round
budget that would have been wasted on misframed code attempt). Per
brief's prediction table, this maps to "Mid-low (P~0.35): Lemma
4.1+4.2 Full but A4+A5 callers don't compose cleanly → 0 items, T2.3
deferred R51" — actual outcome was T1.1 caught the mismatch *before*
T2.1+T2.2 attempts, redirecting to honest deferral. **Realistic
score ~150-200 pts on ~470 base ceiling**, dominated by T1.1 audit
quality (357 lines, 8-row Claims Verification Table, chain mismatch
finding with concrete alternative path proposal).

## V1 calibration

Per V1 protocol skin-in-the-game telemetry:

* **Predicted joint mandatory floor probability** at brief draft:
  0.45 (per brief). Materialized as ~0.10 (T1.1 audit-redirect).
* **Predicted distribution outcome** at brief draft: "Mid-low
  (P~0.35)" — actual is "Audit-redirect / lower".
* **Calibration update:** brief's P(Full)/round ~0.55-0.65 estimate
  for Lemmas 4.1+4.2 close was based on Grok Q4's *finite-dim
  identity* feasibility; the bridge to A4/A5 was implicit and
  unverified. **R50 outcome confirms ledger #16 attribution: Cowork
  brief + Grok Q4 shared chain-level scope-mismatch.** Future rounds
  must verify CHAIN connectivity (not just feasibility of individual
  pieces) before scope commitment.

## What R50 did NOT do (scope discipline)

* Did NOT modify A4 axiom declaration at `524.lean:3643`.
* Did NOT modify A5 axiom declaration at `524.lean:3574`.
* Did NOT modify R49 axiom #6 declaration at
  `MultivariateGaussianCDF.lean:190`.
* Did NOT touch any track branches (`track-c-1dkmt`,
  `track-d-btis-honest`, `kmc-erdos-glw-*`).
* Did NOT advance the in-tree Q1a/b/c track (deferred to R51 with
  pivoted scope).
* Did NOT attempt MGE / `Matrix.det.differentiable` axiomatization
  (γ floor work, deferred to R51).
* Did NOT attempt Q3.3 sub-lemma 3 bypass (depends on T2.1+T2.2
  Full closure, not viable in R50).
* Did NOT dispatch Grok pre-flight (T1.1 audit is the substantive
  R50 deliverable; no math content close, no T1.1-then-Grok pipeline
  needed because the brief's premise was unverified).

## Recommendations for R51

Per `Round50_T1_GLWShortcutAudit.md` §"Alternative path proposal" and
the gate-trajectory analysis above:

1. **Q1a/b/c track consolidation (preferred).** Pivot R51 to close 1
   of the 3 named sorries in `Helpers/MultivariateSmallBallUpper.lean`
   (lines 73, 238, 616 — three "deep multivariate analytic identities"
   per file header). These are the *real* in-tree blockers for A5
   retirement at HEAD.
2. **γ-floor MGE axiomatization.** Replace `MultivariateGaussianPdf.lean:260`
   Stub with axiom of identical signature. Net: -1 sorry, +1 axiom,
   item-neutral; frees R52 budget for further work.
3. **γ-floor `Matrix.det.differentiable` axiomatization.** Replace
   `MatrixDetDifferentiable.lean:144` Stub with axiom of identical
   signature. Net: -1 sorry, +1 axiom, item-neutral.
4. **NOT recommended for R51:** continued GLW determinant shortcut
   work (premise unverified at R50-T1.1; Q1a/b/c track is the real
   in-tree path).

R52 gate evaluation per BACKGROUND.md γ+β confirmed commitment:
administrative count-and-lock at R52, β extension to R58 for γ
axiom retirements via Mathlib upstream / from-scratch / pin-bump
coordination.

## Build log

(Summary above suffices for the audit trail; full build log not
externalized as the round modified only one file with 2 expected
sorry warnings.)

---

**R50 outcome:** T1.1 audit caught chain mismatch on R50 brief
premise before code budget committed. R50 ships honest deferral
(audit doc + 2 deferred-paper sub-Stubs in un-imported file) instead
of fake A4/A5 retirement. Net debt +2 sorries / 0 axiom retirement;
items 17 → 19. R52 gate now decisively fails under hybrid (c); γ
floor + β R58 extension is the binding trajectory. R51 should pivot
to Q1a/b/c track consolidation OR γ-floor axiomatization.
