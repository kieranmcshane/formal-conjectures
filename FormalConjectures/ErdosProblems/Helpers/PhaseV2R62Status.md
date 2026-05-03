# Phase V2 — Round R62 status (Track A mainline, GLW small-ball A4+A5 retirement audit)

**Date:** 2026-05-03. **Branch:** `r46-track-a-mge-posdef` HEAD post-R62
(T1.0+T1.1+T1.2 audit + status doc + BACKGROUND.md append).
**Round type:** Variante 1, single round, mainline. **T1.0+T1.1 audit
caught chain mismatch on R62 brief premise** (recurrence of R50
finding, same family) BEFORE code budget committed; round shipped
honest deferral instead of fake retirement, mirroring R50 pattern.

## Round outcome summary

**Net debt change:** 0 sorries / 0 axioms / 0 retirements = **0 net**.
Mainline ledger 18 → 18 (unchanged); axiom inventory 10 → 10
(unchanged); project total 38 → 38 (unchanged). **Audit-redirect, NOT
closure round.**

**Distribution outcome:** **lower** (P(joint mandatory floor
audit-redirect) materialized as T1.0+T1.1 caught the mismatch and
shipped honest deferral). T2.1 + T2.2 explicitly SKIPPED per
discipline rule "if any claim cannot be verified, flag and propose
alternative" (`feedback_paper_recheck_t10` standing protocol).

**This is the second consecutive Cowork-drafted Track A round (R50,
R62) where the GLW-shortcut → A4/A5 retirement claim has been
audit-rejected; the underlying chain mismatch is structural, not a
brief-quality issue.** R59 → R60 → R61 closed the deterministic
finite-dim half (Cauchy matrix Lemma 4.1 + Lemma 4.2 per ≤ 1 Full +
det side axiomatized) but did not bridge to the continuous-process
asymptotic α/β/γ/δ/ε chain.

| Sub-task | Status | Net debt impact | Commit |
|---|---|---|---|
| T1.0 paper recheck (per `feedback_paper_recheck_t10`) | Full ✓ | 0 (audit) | this commit |
| T1.1 Mathlib API + caller list audit | Full ✓ | 0 (audit) | this commit |
| T1.2 chain-mismatch finding (entry #18) | Full ✓ | 0 (audit) | this commit |
| T2.1 A5 axiom-to-theorem swap | **SKIPPED** (chain mismatch persists) | 0 | n/a |
| T2.2 A4 axiom-to-theorem swap | **SKIPPED** (chain mismatch persists) | 0 | n/a |
| T3 build verification (helper-only, mainline-only) | Full ✓ | 0 | (pre-audit, HEAD `f4011b9`) |
| T4 commit + push (audit doc + status doc + BG append) | Full ✓ | 0 | this commit |

## Round mechanics

### T1.0 — paper recheck

Per `feedback_paper_recheck_t10` standing protocol (Cowork-drafted
brief depending on paper claims requires mandatory T1.0 paper-fetch
BEFORE T1.1 grep audit). The R60 attempt-2 audit
(`TrackA_R60_T1_PerLemma41Audit.md` §T1.6) is the verbatim
arXiv:1001.0200v1 §4 source-of-truth at the project pin. R59→R60
used this fetch to correct the R59 sigs to paper-faithful form
(Cauchy `a_{ij} = 1/(δ_i+δ_j)`, inequalities `per(a) ≤ 1` + `det(a)
≥ (240·e)^{-2m³}`, ratio-based perturbation in Lemma 4.1).

**T1.0 verdict:** the brief's "60–130 LOC" Probe 3 + Bonus 3 estimate
relies on "*After Cauchy det + Lemma 4.1 land*" — implicitly assuming
"land" includes the bridge from finite-dim Lemmas to the
continuous-process small-ball application chain. GLW 2010 §4 itself
runs ~6 pages of dense classical machinery on top of the Lemmas
(α/β/γ/δ/ε in `TrackA_R62_T1_SmallBallRetirementAudit.md` §T1.0);
this is the multi-year Mathlib gap that the A4/A5 axiom docstrings
(`524.lean:3552–3565`, `:3632–3641`) explicitly call out.

### T1.1 — Mathlib + in-tree API audit

A4 (`524.lean:3643`) + A5 (`524.lean:3574`) signatures verified
verbatim — both are continuous-index Gaussian-process small-ball
asymptotics over `IsGLWProcess Y` with `|log ε|^3` rate. Caller-site
list:

* A4 declared at `524.lean:3643`, consumed at `:3675`, `:4421-4426`,
  `:4801-4806`, `:6866-6868`.
* A5 declared at `524.lean:3574`, consumed at `:4107`, `:4265`,
  `:7638`.
* Helper-side reference: `Helpers/CauchyDetLowerBound.lean:25`
  (docstring only, no proof consumption).

R59 → R61 helper consumers (`glwMatrixA | glwMatrixB |
hierarchicalGrid | glw_lemma_4_1 | glw_lemma_4_2 |
glw_det_lower_bound`) — `grep -l` returns exactly one file:
`Helpers/GLWSmallBallShortcut.lean` itself. Zero downstream.

Mathlib bridge components at pin `25ce63313608` reconfirmed 0%:
Anderson's multivariate inequality (grep
`Anderson|anderson_inequality|anderson_ball` in `Mathlib/` → 0 hits),
KL spectral expansion of `K_GLW`, Talagrand entropy, Slepian /
Sudakov–Fernique, discretization-of-sup-over-continuous,
`IsGLWProcess` covariance extraction at finite grid. Borel-TIS is
in-tree Full via Path B' (TD2) but is a sup-deviation concentration
bound, NOT a small-ball tightness bound (different inequality, not
applicable here).

### T1.2 — Chain-mismatch finding (mismatch ledger entry #18)

The R62 brief presupposes the chain `[R61 finite-dim Lemmas] → [R62
60–130 LOC body] → [continuous-time IsGLWProcess small-ball bound]`.
The arrow requires α/β/γ/δ/ε (discretization + Anderson +
tail-handling-for-A4 + optimization + IsGLWProcess covariance
extraction), each individually beyond a single round's LOC budget,
with their composition being the multi-year Mathlib formalization
project the A4/A5 docstrings explicitly call out.

**Mismatch ledger entry #18** (Cowork+Grok shared chain-level
scope-mismatch, recurrence of #16 family — #17 was the R59 sig-form
drift fully resolved at R60 attempt-2). Pattern: Cowork drafts brief
presupposing finite-dim deterministic identity = bridge to
continuous-process asymptotic; Grok strategic review (Probe 3 + Bonus
3) validates the deterministic-half feasibility ("60–130 LOC after
Cauchy det + Lemma 4.1 land") without flagging that "land" doesn't
include the bridge. T1.0+T1.1 audit pipeline catches the mismatch
before code budget commits.

### T2.1 + T2.2 explicit SKIP decisions

Per `feedback_paper_recheck_t10` standing protocol — *"if any claim
cannot be verified, flag explicitly and propose alternative"* — and
per the R50 precedent (`PhaseV2R50Status.md`), R62 ships:

* **T2.1 (A5 retirement) — SKIPPED.** No honest 50–80 LOC body for
  the bridge α/β/γ/δ/ε exists at this pin.
* **T2.2 (A4 retirement) — SKIPPED.** Same chain-mismatch finding;
  additionally, A4's full-window form requires (γ) Ledoux §1.3 tail
  handling on top of the (α/β/δ/ε) of A5.

Performing either swap would introduce a fake "retirement" with a
load-bearing sorry chain or a circular `exact gao_li_wellner_*`
appeal that masquerades as a closed theorem — exactly what the
`feedback_erdos524_framing` memory directs me to avoid ("axioms = tech
debt; do not export closure-tier language to user-facing artifacts").

### T3 build verification

Pre-audit `lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut`
green at HEAD `f4011b9` (3026/3026 jobs, "Build completed
successfully"). No file modifications in this round outside three
markdown documents (audit doc, this status doc, BACKGROUND.md
append), so no further build verification needed at R62 close.

### T4 push

Single commit on `r46-track-a-mge-posdef` containing the audit doc,
this status doc, and the BACKGROUND.md R62 audit-redirect section.
Push to `fork` per standing convention.

## Mainline state at R62 close

Per `BACKGROUND.md` R61 section: "axiom inventory: was 9 (R57 close),
becomes **10** post-R61" + "10 axioms + 8 sorries" mainline gate count.
R62 audit-redirect leaves all counts unchanged:

* **10 user-defined axioms** (unchanged: A1 D2-property, A2 1D KMT,
  A3 stepping-stone, A4 GLW lower, A5 GLW upper, R49 axiom #6,
  R51 axiom #7 γ-floor MGE, R53 axiom #8 γ-floor `Matrix.det.differentiable`,
  R56 axiom #9 companion `Matrix.det.hasFDerivAt`, R61 axiom #10
  `glw_det_lower_bound`).
* **8 TAG'd sorries mainline.**
* **Total mainline debt:** 18 items (unchanged from R61 close).
* **Project total:** 38 items (unchanged).
* **Cumulative R40-R62 retirement rate:** unchanged from R61 close
  (R62 contributes 0 retirements; 0 new debt).

**Note on AXIOM_INVENTORY.md drift:** the file's most recent entry is
`R57 V2 round 19` (line 22), pre-dating R58-R61. Per user dispatch on
this round, R62 leaves AXIOM_INVENTORY.md unchanged. The R58-R61
catch-up is a separate concern, not in R62 scope.

## Hybrid (c) gate trajectory analysis (post-R62)

R52 milestone gate already failed decisively (per `PhaseV2R50Status.md`
line 178-184). β R58 extension was the binding trajectory at R50 close;
post-R62 nothing changes on this front.

The R62 audit-redirect closes the door on the R47-strategic-Grok-pre-
flight estimate that A4 + A5 are jointly closeable in 110-150 LOC via
the GLW deterministic shortcut alone. Compression-bundle item (iv)
per `BACKGROUND.md` lines 51-52 is structurally unachievable as
scoped.

**Realistic alternative paths for honest A4/A5 retirement** (per audit
doc §T1.4):

1. **Mathlib-Anderson path (canonical).** Multi-year horizon. R59-R61
   finite-dim deterministic Lemmas are *contributing* infrastructure
   for step (δ) plug-in.
2. **In-tree no-Gaussian / no-KMT path (Q1a/b/c, 5909+ LOC alternate
   track).** Different matrix construction, different bridge
   philosophy; does NOT consume R59-R61 GLW-Cauchy-form helpers.
   Status at HEAD `f4011b9` not re-audited in this round.
3. **Hybrid (Path A pragmatic, R52 gate authorisation).** Bridge
   components as their own quantitative axioms; net-neutral on count,
   shape-changing on debt.

None of (1), (2), (3) is a single 60–130 LOC round.

## Build verification

R62 modifies only three markdown files; no Lean source changes. The
HEAD `f4011b9` build state (post-R61, GLWSmallBallShortcut green at
3026/3026 jobs) is preserved unchanged.

## Fork push

`r46-track-a-mge-posdef` HEAD pushed to `fork` at R62 wrap. R62 push
consists of one commit: T1 audit doc + R62 status doc + BACKGROUND.md
R62 section append.

## Round score (skin-in-the-game evaluation)

Per the R50-precedent skin-in-the-game cap structure:

* **0pt cap items (none triggered):**
  * T1.0 paper recheck performed ✓ (per `feedback_paper_recheck_t10`).
  * T1.1 Mathlib API + caller-list audit produced ✓ (audit doc).
  * No fake A4/A5 retirement attempted ✓ (T2.1 + T2.2 SKIPPED with
    documented justification per discipline rule).
  * AXIOM_INVENTORY.md unchanged ✓ (no fake retirement to record).
  * Track branches not modified ✓ (mainline-only, no FS-cluster work).
* **50% cap items (none triggered):**
  * Anti-mismatch hygiene maintained ✓ (every Mathlib bridge component
    grep-verified at pin; chain mismatch flagged as ledger entry #18).
  * Internal consistency between audit doc and this status doc on the
    0 sorry / 0 axiom retirement outcome ✓.

**Realistic round score:** lower distribution (audit-redirect outcome,
0 retirement but 0 new debt — strict improvement over R50 which added
+2 sub-Stub sorries; R62 ships pure-audit, no new debt). Per
`feedback_paper_recheck_t10`, the audit-redirect outcome IS the
correct shipped artifact when brief premise fails verification.

## V1 calibration

* **Predicted joint mandatory floor probability** at brief draft:
  not committed in brief (Cowork-drafted, Probe 3 + Bonus 3 only
  surfaced the deterministic-half estimate). Materialized as T1.0+T1.1
  audit-redirect, identical to R50 pattern.
* **Calibration update:** the second consecutive Cowork-drafted Track
  A round (R50 → R62) where finite-dim → continuous-process bridge
  was implicitly assumed and not verified is sufficient evidence to
  treat the entire "GLW determinant shortcut" compression-bundle item
  (iv) as unverified-as-scoped. Future briefs targeting A4/A5 must
  either:
  - explicitly include the α/β/γ/δ/ε bridge in scope (multi-round,
    ~600-1000 LOC per the axiom docstrings), OR
  - pivot to the in-tree Q1a/b/c track (different bridge philosophy),
    OR
  - propose the Path A hybrid (axiomatize bridge components separately
    for net-neutral count change).

## What R62 did NOT do (scope discipline)

* Did NOT modify A4 axiom declaration at `524.lean:3643`.
* Did NOT modify A5 axiom declaration at `524.lean:3574`.
* Did NOT modify R61 `glw_det_lower_bound` axiom at
  `Helpers/GLWSmallBallShortcut.lean`.
* Did NOT modify R59-R61 `glwMatrixA`/`glwMatrixB`/`hierarchicalGrid`
  definitions or `glw_lemma_4_1_perturbation` /
  `glw_lemma_4_2_paper_specs` Full bodies.
* Did NOT modify the R50 historical sub-Stubs
  (`glw_lemma_4_1_deferred_paper`, `glw_lemma_4_2_deferred_paper`)
  preserved per R60 convention.
* Did NOT touch any track branches (`track-c-1dkmt`,
  `track-d-btis-honest`, `kmc-erdos-glw-*`).
* Did NOT advance the in-tree Q1a/b/c track (deferred to future
  rounds; not in R62 scope).
* Did NOT dispatch Grok pre-flight (T1.0+T1.1 audit is the substantive
  R62 deliverable; no math content close, no Grok-recipe needed
  because the brief's premise was unverified).
* Did NOT touch AXIOM_INVENTORY.md (no fake retirement to record).

## Recommendations for R63+

Per the brief's R63 preview ("Cauchy det identity + grid bound chain,
250–450 LOC" to retire `glw_det_lower_bound` axiom #6) and this audit:

1. **R63 Cauchy det retirement** — per the brief preview, R63 is on
   the deterministic side (retire `glw_det_lower_bound` via Cauchy
   determinant identity from-scratch). **R63 is unaffected by the
   R62 finding** and can proceed as drafted. Net: -1 axiom.
2. **NOT recommended for R63 or any single round:** continued attempt
   at A4/A5 retirement via the GLW deterministic shortcut alone
   (premise structurally unverified at R50-T1.1 and R62-T1.1 — two
   independent audits, same finding).
3. **For honest A4/A5 retirement (multi-round program):** pivot to
   one of the three alternative paths in audit doc §T1.4 (Mathlib-
   Anderson canonical, in-tree Q1a/b/c, or Path A hybrid axiom-shape).
   Whichever is chosen, the entry-point round should produce a Claims
   Verification Table for the chosen bridge component, NOT a code
   round.

## Build log

(Pre-audit HEAD `f4011b9` helper-build green; R62 added no Lean
source modifications. Full build log not externalized; nothing to
re-verify post-R62.)

---

**R62 outcome:** T1.0+T1.1 audit reconfirmed R50 chain-mismatch
finding (entry #16) under post-R59-R60-R61 conditions; new mismatch
ledger entry #18. R62 ships pure-audit honest deferral (audit doc +
this status doc + BACKGROUND.md append) instead of fake A4/A5
retirement. Net debt 0 sorries / 0 axioms / 0 retirements; mainline
ledger 18 → 18 (unchanged); axiom inventory 10 → 10 (unchanged);
project total 38 → 38 (unchanged). R63 Cauchy det retirement remains
independently dispatchable (deterministic side, unaffected by R62
finding).
