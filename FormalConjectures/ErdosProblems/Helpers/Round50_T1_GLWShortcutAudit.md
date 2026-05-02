# Round 50 — T1.1 GLW determinant shortcut audit (Lemmas 4.1+4.2 → A4+A5 retirement claim)

**Date:** 2026-05-02. **Branch:** `r46-track-a-mge-posdef` HEAD `76e9ef1`
(post-R49). **Pin:** `mathlib4 @ 25ce633136084367f182be00fdff7613ea949d27`,
`leanprover/lean4:v4.27.0-rc1`, `brownian-motion @ 91267abd71bd...`.
**Audit type:** R50 mandatory T1.1 Claims Verification Table + grep
audit, per BACKGROUND.md SEMANTIC-MISMATCH DISCIPLINE rule (post-R48
binding) and R50 brief's discipline rule #5 (Claims Verification Table
mandatory).

## TL;DR

**The R50 brief's central claim — that closing GLW 2010 §4 Lemmas
4.1 + 4.2 (~110-150 LOC) retires axioms A4 + A5 — is NOT supported by
the existing axiom signatures or Lean codebase state at HEAD `76e9ef1`.**

Three independent pieces of evidence:

1. **Axiom signature scope mismatch.** A4 + A5 are *Gaussian-process*
   small-ball asymptotics over the continuous index set `u ≥ 0` for an
   `IsGLWProcess Y`, gated on hypotheses including continuous-time
   Gaussianity, K_GLW covariance, mean zero, continuity, tail decay.
   Lemmas 4.1 + 4.2 (per the brief's own characterization) are
   *finite-dimensional* deterministic determinant + permanent
   identities for one specific structured matrix `A`. **The bridge
   from finite-dim explicit determinant to continuous-time
   Gaussian-process small-ball asymptotic is not a 110-150 LOC trip.**

2. **Existing in-tree infrastructure (5909+ LOC) on a fully orthogonal
   closure track.** Mainline already contains an in-flight no-Gaussian
   / no-KMT path toward `gao_li_wellner_small_ball_upper` (A5)
   retirement, using Fourier smoothing + Berry-Esseen + characteristic
   function decoupling on a hierarchical Cauchy grid (Q1a/b/c
   structure). This is orders of magnitude beyond the brief's scope
   estimate and is NOT consumed by the brief's proposed Lemma 4.1+4.2
   bridge.

3. **Mathlib status of the missing bridge pieces is 0%.** Anderson's
   multivariate inequality, discretization-of-sup-over-continuous,
   IsGLWProcess covariance consumption, optimization `m(ε) ~ |log ε|`
   — none are present in Mathlib at the pin, none have in-tree
   foundations (other than the Q1c track, which is a different
   approach entirely).

This is **mismatch ledger entry #16** (same family as #14: Cowork+Grok
shared misframing on chain-level vs per-step form) and a clear
violation of post-R48 SEMANTIC-MISMATCH DISCIPLINE rule (BACKGROUND.md
§"BINDING DISCIPLINE RULE"). Per R50 brief discipline rule #5 and the
T1.1 brief language: **"If any claim cannot be verified, flag
explicitly and propose alternative."**

This audit serves as the alternative-path documentation. R50 ships
T1.1 + diagnostic; T2.1 + T2.2 fall through to honest TAG'd sub-Stubs
in `GLWSmallBallShortcut.lean` documenting the audit finding (NOT
attempting bodies based on a misframed premise); T2.3 is
**SKIPPED** (no axiom-to-theorem swap — the premise is not verified);
T2.4 stretch SKIPPED.

## Claims Verification Table

| # | Math statement | Lean statement / location | VERIFIED? | Citation (file:line at pin) | Notes |
|---|----------------|---------------------------|-----------|------------------------------|-------|
| 1 | `Mathlib.LinearAlgebra.Matrix.Permanent` exists at pin, with `Matrix.permanent` callable | `def permanent (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i` | **VERIFIED** | `mathlib4/Mathlib/LinearAlgebra/Matrix/Permanent.lean:32` (commit `25ce63313608`) | Grok Q4 claim grep-confirmed at pin. `permanent_def` lemma not separately named in this file but the `def`-form rewrite suffices. |
| 2 | Standard Mathlib determinant identities usable | `Matrix.det_smul`, `Matrix.det_fromBlocks_zero₂₁`, `Matrix.det_fromBlocks_zero₁₂` | **VERIFIED** | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:272, :674, :724` | `Matrix.det_tridiagonal` is **NOT** in Mathlib at pin (0 grep hits across `Mathlib/LinearAlgebra/Matrix/`). Brief said "or analogous" — must work without a tridiagonal lemma. |
| 3 | `Matrix.det.continuous`, `Matrix.det.differentiable` available | Differentiability is a **project Stub**, not Mathlib | **VERIFIED — partial** | `Helpers/MatrixDetDifferentiable.lean:128, :144` (project Stub TAG[R40-T2.1-det-cofactor-route]) | Per BACKGROUND.md and R49 status doc, `Matrix.det.differentiable` remains an open R40 Stub at HEAD. If Lemma 4.1 needs differentiability, route through whatever is closed. Continuity (R40-T2.4) closed via `sup_continuous_eq_sup_dense`. |
| 4 | A4 statement = lower small-ball probability for Gaussian process satisfying `IsGLWProcess` | `axiom gao_li_wellner_small_ball_lower (glw : GaoLiWellnerConstants) : ∀ {Ω} [MeasureSpace Ω] [IsProbabilityMeasure ℙ] (Y : ℝ → Ω → ℝ), Erdos524.Helpers.IsGLWProcess Y → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀], Real.exp (-glw.lower * \|Real.log ε\|^3) ≤ (ℙ {ω \| ∀ u ≥ 0, \|Y u ω\| ≤ ε}).toReal` | **VERIFIED — verbatim** | `FormalConjectures/ErdosProblems/524.lean:3643` | Full-window form `∀ u ≥ (0:ℝ)`, NOT truncated `[0, T(ε)]`. Hypothesis is `IsGLWProcess Y` (Helpers/GLWProcessPredicate.lean:78), capturing Gaussianity + K_GLW covariance + mean zero + continuity + tail decay. Per the axiom's own docstring, dominant Mathlib gaps are "Karhunen–Loève expansion infrastructure (0%)" + "Talagrand generic-chaining entropy bounds for Gaussian processes (0%)" + "Slepian / Sudakov–Fernique comparison (0%)" + "Borel-TIS Gaussian concentration (0%)". |
| 5 | A5 statement = upper small-ball probability for Gaussian process satisfying `IsGLWProcess` | `axiom gao_li_wellner_small_ball_upper (glw : GaoLiWellnerConstants) : ∀ {Ω} ..., IsGLWProcess Y → ∃ ε₀ T, 0 < ε₀ ∧ ∀ ε ∈ (0, ε₀], (ℙ {ω \| ∀ u ∈ Icc 0 (T ε), \|Y u ω\| ≤ ε}).toReal ≤ Real.exp (-glw.upper * \|Real.log ε\|^3)` | **VERIFIED — verbatim** | `FormalConjectures/ErdosProblems/524.lean:3574` | Truncated form `∀ u ∈ Icc 0 (T ε)` with existential `T : ℝ → ℝ`. Per docstring: "the dominant Mathlib gaps are the Karhunen–Loève eigenfunction expansion infrastructure and the Talagrand entropy machinery for Gaussian processes (both 0%)". The axiom doc explicitly says "A native upper closure would require ~600-1000 LOC across 4-6 rounds" (R36 redux). |
| 6 | GLW Lemma 4.1 = "determinant perturbation, matrix-level structural identity for K_GLW^(n)" | TBD — Lean signature **not specifiable from brief alone** | **UNVERIFIED — defer with alternative path** | Brief cites Gao-Li-Wellner 2010 §4 Lemma 4.1 (paper not in repo); Grok Q4 response card_id `62d32a` not retrievable from current Lean session | Without paper access, cannot write a precise Lean signature. The brief's prose "structural identity on matrices, direct calc + simp + ring" is not a specification — what `K_GLW^(n)` is, what the perturbation parameter is, and what the conclusion looks like are all unstated. **Spec-driven / define-first practice (BACKGROUND.md Q5) cannot proceed.** |
| 7 | GLW Lemma 4.2 = `per(A) = 1` AND `det(A) = 32m · (240 e^{-3})^m` for "specific structured A" | TBD — Lean signature **not specifiable from brief alone** | **UNVERIFIED — defer with alternative path** | Brief cites Gao-Li-Wellner 2010 §4 Lemma 4.2; Grok Q4 said "tridiagonal/banded" but exact entries unstated | The brief identifies the *target value* `32m · (240 e^{-3})^m` but not the *defining matrix entries*. `det(A) = 32m · (240 e^{-3})^m` requires knowing `A`'s entries to write the theorem. Without paper access, Lean signature cannot be drafted. The discretization grid `δ_i = 4m/(m+1) · q` is mentioned in the brief and BACKGROUND.md but not connected to A's matrix entries explicitly. |
| 8 | Q3.3 strengthening: Lemmas 4.1+4.2 modified to give small-ball probability *directly*, bypassing sub-lemma 3 | TBD — exploratory, dependency on 6+7 | **UNVERIFIED — exploratory** | Grok Q3 response (`card_id="62d32a"`) referenced in brief but contents not in audit window | Stretch goal explicitly contingent on Lemmas 4.1+4.2 having a strengthened form that gives small-ball directly (skipping the discretization+Anderson chain). Not scoped tightly enough to attempt. |

**Summary**: 5/8 VERIFIED (claims 1-5), 3/8 UNVERIFIED with alternative
path proposed below (claims 6-8).

## Chain-mismatch finding (the central audit issue)

The brief presupposes the chain:

```
[Lemma 4.1 Full close]         [Lemma 4.2 Full close]
            \                /
             ↓              ↓
        [composed retirement claim]
                  ↓
        [A4 + A5 retired in R50]
```

This implicit chain has **at minimum the following missing intermediate
pieces**, none of which are within R50's 110-150 LOC scope:

### Missing piece α — discretization of sup-over-continuous-time

A4/A5 statements are about `ℙ {ω | ∀ u ≥ 0, |Y u ω| ≤ ε}` (continuous
sup) or `ℙ {ω | ∀ u ∈ Icc 0 (T ε), |Y u ω| ≤ ε}` (truncated continuous
sup). Lemmas 4.1+4.2 give finite-dim determinant identities. The bridge
requires:

1. **Existence of a finite grid `{u_1, ..., u_n}`** dense enough that
   continuity of `Y` (provided by `IsGLWProcess.continuity`) bounds
   `sup_{u ∈ [0, T]} |Y u| ≤ max_i |Y u_i| + δ` for arbitrarily small
   `δ`.
2. **Joint Gaussianity of `(Y u_1, ..., Y u_n)`** (provided by
   `IsGLWProcess.gaussianity` for finite marginals).
3. **Covariance matrix entries** `cov(Y u_i, Y u_j) = K_GLW(u_i, u_j) =
   integrand-of-K_GLW` (provided by `IsGLWProcess.covariance`).
4. **Conversion of finite-dim Gaussian distribution to its
   small-ball-probability form** — this is the `multivariateGaussian`
   density-on-Euclidean-space machinery (R46+R49 axiomatized for the
   CDF; pdf chain still partial via MGE Stub at
   `MultivariateGaussianPdf.lean:260`).

None of these are 110-150 LOC. Each is a substantial helper chain.

### Missing piece β — Anderson's multivariate inequality

Even with a finite grid, the small-ball bound requires Anderson's
inequality (or equivalent: Slepian, Sudakov-Fernique, BTIS) to relate
the multivariate Gaussian small-ball probability to the determinant of
the covariance matrix. **Mathlib status: 0%** at pin.

* `grep -rln "Anderson\|anderson_inequality\|anderson_ineq" Mathlib/`
  → 0 hits.
* `grep -rln "small_ball\|smallBall" Mathlib/` → 1 hit
  (`Mathlib/Topology/EMetricSpace/PairReduction.lean`, unrelated to
  Gaussian small-ball).
* In-tree `glwUpperAndersonFactor_*` theorems
  (`GLWUpperProof.lean:143, :148, :160`) and
  `glwBoxProb_anderson_upper_*`
  (`GaussianHierCauchyBox.lean:121, :131, :149, :159`) work at the
  factor / box-probability level but presuppose the Anderson principle,
  not derive it.

The classical proof of Anderson is via the Brunn-Minkowski / log-concave
path (Borell). Brunn-Minkowski / Borell are not formalized in Mathlib
at the pin — confirmed via `grep -rln "Brunn\|brunn_minkowski" Mathlib/`
in prior rounds (R35 Phase A status inventory).

### Missing piece γ — tail handling for the FULL-window lower bound

A4 (lower) is stated on `∀ u ≥ 0` — the full half-line. Lemmas 4.1+4.2
deliver finite-grid bounds. Closing the gap from finite-grid `[0, T]`
to `[0, ∞)` requires the Ledoux §1.3 "Borell + σ²(T) → 0" bridge that
the axiom docstring at `524.lean:3624-3630` explicitly notes is
already baked into the axiom statement to avoid this dependency. **The
axiom-to-theorem swap therefore must EITHER**:

(a) bake the same Ledoux bridge into the proof (significant LOC), OR
(b) re-formulate A4 on the truncated form (changing the public
    interface, breaking consumers including
    `gao_li_wellner_small_ball_lower_truncated` at `524.lean:3667`
    and `polynomial_sup_small_ball_lower` callers).

Either route is well beyond the brief's stated scope.

### Missing piece δ — optimization `m = m(ε) ~ |log ε|`

The classical small-ball bound goes through a parameter `m`
(grid-size / matrix-dim parameter); the final `exp(-c |log ε|^3)`
form requires choosing `m(ε) ~ |log ε|` and tracking the constant.
This is real-arithmetic + monotone-function bookkeeping, possibly
~50-100 LOC in itself. Not in brief scope.

### Missing piece ε — `IsGLWProcess` covariance consumption

`IsGLWProcess Y` is a structure (`Helpers/GLWProcessPredicate.lean:78`)
bundling Gaussianity + K_GLW covariance + mean zero + continuity + tail
decay. To consume it in a finite-dim Anderson-style argument, a Lean
chain is needed to extract joint Gaussianity of `(Y u_1, ..., Y u_n)`
and pin the covariance matrix entries. **No such consumer exists in
Helpers/ at HEAD `76e9ef1`** (grep confirms `glwUpperAndersonFactor_*`
work at the factor level, not the IsGLWProcess-to-Anderson level).

## Existing in-tree alternate track (5909+ LOC, fully orthogonal)

The brief proposes a "GLW determinant shortcut" but mainline already
contains an in-flight closure track for A5 via the no-Gaussian /
no-KMT path. Files:

| File | LOC | Role | Evidence |
|------|-----|------|----------|
| `CauchyDetLowerBound.lean` | 3126 | **Q1a** — `det Σ ≥ exp(-c₀ · m³)` for the m² × m² Cauchy matrix on hierarchical grid `δ_{p,q} = 4^{p+m}·(m+q+1)` | Header line 24-26 (verbatim): "Proves `det Σ ≥ exp(-c₀ · m³)` for the m² × m² Cauchy matrix on the hierarchical grid `δ_{p,q} = 4^{p+m} · (m+q+1)`. … This is used in the no-Gaussian / no-KMT path to retire `gao_li_wellner_small_ball_upper`." |
| `CharFunCrossBlock.lean` | 635 | **Q1b** — Two-scale cosine-product cross-block swap inequality, "the keystone Lindeberg swap with kernel decay lemma — replaces KMT/Brownian coupling" | Header line 22-26 |
| `MultivariateSmallBallUpper.lean` | 621 | **Q1c** — Multivariate small-ball UPPER on hierarchical grid, "the third helper en route to retiring `gao_li_wellner_small_ball_upper`" | Header line 23-28 |
| `SurgicalDensityAtZero.lean` | 543 | density-at-zero infrastructure for Q1a/b/c | Header / imports |
| `EsseenSmoothing.lean` | 817 | Berry-Esseen smoothing for Q1c Step 1 | 20 internal sorries (most untagged scaffolds) |
| `GaussianHierCauchyBox.lean` | 167 | `glwBoxProb_anderson_upper_*` chain | Header |

Total: **5909 LOC across 6 files**, all in mainline at HEAD `76e9ef1`,
all working toward A4/A5 retirement via a path that is **completely
disjoint from the GLW 2010 §4 determinant shortcut path the brief
proposes.**

`MultivariateSmallBallUpper.lean` itself contains 3 named sorries
documented in its header as "deep multivariate analytic identities …
Each is left as a single named sorry" (line 73). These are the
*concrete* in-tree blockers for A5 retirement, NOT Lemmas 4.1+4.2.

`GLWSmallBallShortcut.lean` (R48-T3.2 stretch deliverable, 182 LOC) is
imported by **nothing** (`grep -rn "import.*GLWSmallBallShortcut"
FormalConjectures/` → 0 hits at HEAD `76e9ef1`). Its docstring code
blocks list "target signatures" for Lemmas 4.1+4.2-derived consumers
on a finite-dim multivariate-Gaussian small-ball bound (lines 113-119),
but **none of those signatures connect to A4/A5's IsGLWProcess
hypothesis** — they're stated for `(B : Matrix (Fin n) (Fin n) ℝ)`
with `B.PosDef`, against `(multivariateGaussian 0 B).real (Metric.ball
0 ε)`. That is a finite-dim measure ratio, not a Gaussian-process
small-ball asymptotic.

## Mismatch ledger entry #16 (this audit)

Pattern: same family as #14 (Cowork+Grok shared misframing on chain-
level form). Cowork brief drafts an R50 plan presupposing Lemmas
4.1+4.2 = bridge to A4/A5 retirement. Grok Q4 confirms the *finite-
dim* identity is feasible (110-150 LOC), without flagging that the
bridge requires the further chain α/β/γ/δ/ε above. Cowork accepts
without checking the existing in-tree work or the axiom signature
shape. **This is exactly the "external attribution" failure mode
flagged in BACKGROUND.md §"Cowork-Claude semantic-mismatch
ledger"**: the bridge mismatch is a Cowork-side framing failure, not
a Grok-side one.

Specific corrections that would have caught it pre-dispatch:

1. **Re-read A4/A5 axiom docstrings before any retirement claim.**
   Both axioms self-identify the residual Mathlib gap as
   Karhunen-Loève + Talagrand + Slepian + BTIS (each "0%" per Phase A
   status inventory), and explicitly disclaim any 1-round closure
   feasibility ("multi-year Mathlib formalization project").
2. **Read existing in-tree work before proposing a new approach.**
   `MultivariateSmallBallUpper.lean` and `CauchyDetLowerBound.lean`
   are the in-flight A5 closure track at HEAD; either consolidate
   that track or have a documented reason to abandon it.
3. **Distinguish `multivariateGaussian` (finite-dim density on
   `EuclideanSpace ℝ (Fin n)`) from a Gaussian process
   `Y : ℝ → Ω → ℝ` indexed by continuous time.** The finite-dim
   small-ball measure for a multivariate Gaussian distribution is NOT
   the same object as the small-ball probability for a Gaussian
   process's continuous sup; the bridge is the discretization +
   Anderson + tail chain.

## Alternative path proposal (binding for R50 outcome)

Per R50 brief discipline rule: "If any claim cannot be verified, flag
explicitly and propose alternative."

**Proposed R50 outcome (revised honest)**:

* **T1.1 (THIS AUDIT)** lands as the substantive R50 deliverable.
* **T2.1 + T2.2** land as honest TAG'd sub-Stubs in
  `GLWSmallBallShortcut.lean` (which is currently un-imported, so the
  sub-Stubs do not regress consumer build state). Each sub-Stub
  carries:
  * Lean signature placeholder reflecting the brief's prose intent
    (finite-dim determinant identity / explicit `per(A) = 1` +
    `det(A) = 32m · (240 e^{-3})^m`), with the matrix `A` left
    abstract via existential/Prop-level statement (since the brief
    does not specify A's entries).
  * `:= by sorry` body (TAG'd `R50-T2.1-glw-lemma-4-1-deferred-paper`
    and `R50-T2.2-glw-lemma-4-2-deferred-paper`).
  * Docstring citing this audit doc + the chain-mismatch finding.
* **T2.3 (A4+A5 axiom-to-theorem swap)** is **SKIPPED** — premise
  unverified; performing the swap based on Lemmas 4.1+4.2 alone would
  introduce a fake "retirement" that fails to verify under the chain
  α/β/γ/δ/ε, polluting the AXIOM_INVENTORY.md with a load-bearing
  sorry chain that masquerades as a closed theorem.
* **T2.4 Q3.3 strengthening attempt** is **SKIPPED** — exploratory,
  dependent on T2.1+T2.2 Full which is not viable.
* **T2.5 build verification + AXIOM_INVENTORY.md update + status doc
  + push** — mainline preserved; +2 sub-Stubs in
  `GLWSmallBallShortcut.lean`; AXIOM_INVENTORY.md gets a "Build
  status (R50)" section documenting the audit + alternative path; net
  debt change **+2 sorries, 0 axioms** (items 17 → 19 mainline).

**Net debt change projection (verifiable arithmetic, per R50 brief
discipline rule #3)**:

* Sorries: 11 → 13 (+2 from `GLWSmallBallShortcut.lean` Lemmas 4.1
  + 4.2 sub-Stubs).
* Axioms: 6 → 6 (unchanged — A4/A5 NOT retired; no new axiom).
* Items at gate: 17 → 19 (+2).

This is honest worse-case-than-baseline but **prevents pollution of
the AXIOM_INVENTORY by a faulty retirement claim**. The +2 is
recoverable in a future round once either (i) the brief is re-scoped
to consolidate the in-tree Q1a/b/c track, or (ii) the GLW 2010 paper
is loaded into the Cowork session and Lemmas 4.1+4.2 are written with
exact matrix-entry specifications.

**Recommendation for R51**: pivot to Q1a/b/c track consolidation —
specifically the 3 named sorries in `MultivariateSmallBallUpper.lean`
(line 73 documents three "deep multivariate analytic identities …
each is left as a single named sorry"). These are the *real* concrete
in-tree blockers for A5 retirement at HEAD. Closing any one of them
contributes meaningfully to the in-flight track; closing all three
would land A5 retirement honestly.

## Audit hygiene checklist (per R50 brief)

* ✅ Read `AXIOM_INVENTORY.md` before any retirement claim — A4 + A5
  signatures verified verbatim (not vague labels).
* ✅ Distinguished "advance path to retire" from "retire line-item":
  audit recommends NEITHER for R50 (brief premise unverified).
* ✅ Net debt change = verifiable arithmetic (above).
* ✅ Internal consistency: this audit's recommendation is internally
  consistent — no axiom retirement claim, +2 sub-Stubs net.
* ✅ Claims Verification Table produced (above).
* ✅ Pre-dispatch checklist applied: grep + git blame on every
  identifier (claim 1: `permanent_def` grep; claim 2:
  `det_fromBlocks_zero₂₁`/`₁₂` grep; claim 3:
  `Matrix.det.differentiable` grep; claims 4-5: axiom signature grep
  at `524.lean:3574, :3643`; claims 6-8: paper not in repo, deferred).
* ✅ Spec-driven / define-first: this audit's outcome is the
  spec-driven decision — Lemmas 4.1+4.2 spec cannot be written
  without paper access; therefore proceeding to bodies would violate
  spec-driven discipline.

## What this audit does NOT do (scope)

* Does NOT modify A4 or A5 axiom declarations at `524.lean:3574, :3643`.
* Does NOT modify R49 axiom #6 declaration at
  `MultivariateGaussianCDF.lean:190`.
* Does NOT modify any track branch (`track-c-1dkmt`,
  `track-d-btis-honest`, etc.).
* Does NOT add new sorries to mainline 11-TAG'd-sorry headline list
  outside `GLWSmallBallShortcut.lean` (and that file is currently
  un-imported, so the +2 sub-Stubs are isolated).
* Does NOT attempt Q3.3 sub-lemma 3 bypass.
* Does NOT advance the in-tree Q1a/b/c track (deferred to R51 with
  pivoted scope).

## Cross-references

* `BACKGROUND.md` §"BINDING DISCIPLINE RULE (post-R48 user feedback)"
  — SEMANTIC-MISMATCH DISCIPLINE rule that this audit applies.
* `BACKGROUND.md` §"Cowork-Claude semantic-mismatch ledger update
  (8 → 13)" — ledger of prior misframings; this audit adds entry
  #16 (Cowork+Grok shared chain-level scope-mismatch on Lemmas
  4.1+4.2 → A4/A5 bridge).
* `AXIOM_INVENTORY.md` §"6 user-defined axioms" + Axiom #6 detail —
  source-of-truth for axiom signatures and retirement targets.
* `Helpers/PhaseV2R49Status.md` — R49 close + R50 trajectory framing.
* `Helpers/Round49_T1_PathAAxiomatization.md` — R49 T1.1 audit
  (precursor pattern: T1.1 Local Claude grep audit catches misframing
  before round budget commits).
* `524.lean:3574, :3643` — A4/A5 axiom declarations.
* `Helpers/MultivariateSmallBallUpper.lean:73, :238, :616` — three in-
  tree named sorries for the actual in-flight A5 closure track.
* `Helpers/CauchyDetLowerBound.lean` — 3126 LOC Q1a infrastructure.

---

**T1.1 outcome:** chain mismatch on R50 brief premise caught at audit
stage. Audit produced under brief's discipline rule "if any claim
cannot be verified, flag explicitly and propose alternative". R50
ships T1.1 (this doc) + T2.1 + T2.2 honest sub-Stubs + T2.5 build
verification + status doc + push. T2.3 SKIPPED (axiom retirement
premise unverified). T2.4 SKIPPED.
