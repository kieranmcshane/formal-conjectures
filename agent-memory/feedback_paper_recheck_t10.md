---
name: paper-recheck mandatory T1.0 (before T1.1) for Cowork-drafted briefs
description: Erdős 524 round process — when a brief is drafted from Cowork-derived paper recall (no independent verification at draft time), next round's audit MUST fetch the paper before writing any body. Generalises beyond Track C. R59→R60 (sig-form drift) + R62 (chain-level scope-mismatch for §4 application of Lemmas to small-ball) + R63 (constant-gap on paper-stated quantitative bound vs in-tree existing weaker constant) = three confirmed positive applications.
type: feedback
originSessionId: 1405fca5-3885-425f-b308-37a871e18830
---
For any Erdős 524 round whose mandatory floor depends on a claim the
brief sources from a paper (e.g. arXiv §X form / constants /
inequality direction), the executing round's audit MUST fetch the
paper verbatim before any body work.

**Rule**:

* If the brief's sig / claim was drafted from Cowork-derived paper
  recall (no independent verification at draft time, typically
  flagged in the prior round's audit doc as a hedge clause),
  promote paper-recheck to a **mandatory T1.0 step** that runs
  BEFORE the T1.1 grep audit.
* T1.0 = fetch the paper (WebFetch or external source), confirm
  the brief's claimed entries / constants / inequality direction
  verbatim. Record the verbatim extract in the audit doc.
* If T1.0 surfaces a mismatch, halt the round at audit and surface
  to user (paper-faithful sig revision or claim refinement is then
  scoped as an INFRA round, NOT closure).

**Why**: R59 → R60 attempt 1 → R60 attempt 2 (mainline Track A,
2026-05-03, commits `fc957a2` → halt → `daf3d9d`). R59 sigs were
Cowork-derived from arXiv:1001.0200v1 §4 recall; the R59 audit
explicitly hedged on independence (`TrackA_R59_T1_GrepAudit.md`
lines 94–108). R60 attempt 1 dispatched as twin closure under that
unchecked assumption; T1.1 surfaced empirical disproofs at m=1 of
both R59 closure claims. R60 attempt 2 fetched the paper, revised
6 distinct items (grid formula, matrix entries, +new auxiliary
matrix, 2× lemma form changes from equality to inequality,
Lemma 4.1 ratio vs absolute). The audit-first halt + paper-fetch
revision is the correct discipline; without it, attempt 1 would
have committed fabricated body proofs of a false claim.

**R63 third-application evidence — constant-gap refinement**
(mainline Track A, 2026-05-03, commit `7ac78d4`, audit doc
`Helpers/TrackA_R63_T1_CauchyDetAudit.md`). R63 brief was Cowork-
drafted with central premise "Cauchy det identity (40-60 LOC,
Vandermonde + multilinearity) + grid bound chain (150-300 LOC) retires
`glw_det_lower_bound` axiom (paper-stated `(240·e)^{-2m³}`)". T1.0
paper recheck (Krattenthaler 1999 + arXiv:1001.0200v1 §4 Lemma 4.2
second half) reconfirmed paper claims unchanged from R60 attempt-2.
T1.1 grep audit at pin `25ce63313608` surfaced two structural
findings the brief did not score: (a) Cauchy 1841 det identity
already proven in-tree as `cauchy_det_formula_fin` /
`cauchy_det_formula` (`Helpers/CauchyDetLowerBound.lean:337`/`:488`,
`private theorem`, ~250 LOC Schur-style row/column reduction Full
at pin) — brief's Vandermonde-multilinearity re-derivation
redundant; (b) **constant gap ~9.16x** — same file already exposes
public `cauchy_hierarchical_det_lower_bound_explicit:3093` with
`det Σ ≥ exp(-120·m³)` but paper bound is
`(240·e)^{-2m³} = exp(-2m³·log(240·e)) ≈ exp(-12.9613·m³)`; since
`-118.77·m³ ≤ -12.96·m³` for m ≥ 1 and exp is monotone,
`exp(-118.77·m³) ≤ exp(-12.96·m³) = (240·e)^{-2m³}` so the in-tree
result is **strictly weaker** and **does NOT imply** the paper-
stated axiom. T2.1+T2.2 SKIPPED; audit-redirect shipped (mismatch
ledger entry #18 sub-iteration). **Refinement to the protocol**:
when a brief covers a paper-stated *quantitative* bound (specific
constants, not just shape), and the in-tree state already provides
the same identity at a *different constant*, mandatory pre-dispatch
verification must include **numerical comparison** of the in-tree
constant against the paper constant, not just identity-form checking.
Probe-style strategic review's "Mathlib gap" framing must explicitly
score whether the entire chain is already in-tree at a different
constant — gap-relative-to-Mathlib is not the same as gap-relative-
to-project. Audit doc must document numerical comparison in §T1.2
when paper bound is constant-specific. T1.1 grep audit must
explicitly grep for project-local quantitative theorems
(`grep -rn` on a candidate target, not just Mathlib API).

**R62 second-application evidence** (mainline Track A, 2026-05-03,
commit `8fdee54`, audit doc
`Helpers/TrackA_R62_T1_SmallBallRetirementAudit.md`). R62 brief was
Cowork-drafted with central premise "after R61 GLW finite-dim
Lemmas land, A4+A5 retire in 60-130 LOC of body composition".
T1.0 paper-recheck (this protocol) extended to verifying not just
the Lemma statements (R60 attempt-2 already paper-faithful) but
the **§4 application chain** of Lemmas to the continuous-process
small-ball bound — α/β/γ/δ/ε (discretization + Anderson +
A4-tail-handling + optimization + IsGLWProcess covariance
extraction). T1.0 verdict: brief's "60-130 LOC" hand-waves a
multi-year Mathlib gap that the A4/A5 axiom docstrings explicitly
call out. T2.1+T2.2 SKIPPED, audit-redirect shipped (mismatch
ledger entry #18, same family as #16/R50). Lesson: the protocol
applies not just to sig-form drift but to chain-level scope
assumptions about *how* paper Lemmas connect to the round target;
"after X lands" must verify "lands" includes the load-bearing
bridge, not just the local lemma statements.

**How to apply**:

* Before reading the body of a Cowork-drafted brief, scan the audit
  doc of the **previous** round for paper-recheck independence.
  Look for hedge clauses like "paper recheck performed by Cowork
  during brief composition, NOT independently re-verified at
  dispatch time" or equivalent.
* If such a hedge exists AND the current brief depends on the
  unchecked claim, treat that as a T1.0 trigger.
* T1.0 fetch via WebFetch (preferred) or surface to user requesting
  paper access. Record the verbatim claim extract in the audit doc
  alongside the brief's restatement, side by side.
* If verbatim ≠ brief, halt the closure attempt, write the audit doc
  flagging each delta, surface to user with resolution paths
  (paper-faithful sig revision, claim refinement, defer round, etc).
* Do NOT charge through with body work on an unchecked-paper claim.
  Fabricated proofs of false claims pollute the project even if they
  type-check (they would not, but the discipline is to never even
  attempt).
* Generalises beyond Track C — applies to any track / any round
  whose floor depends on an external math paper. The Track-C-specific
  process memory (`feedback_track_c_round_process`) is unchanged;
  this memory is the cross-track promotion.
