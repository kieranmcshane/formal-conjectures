# Phase V2 — Round R63 status (Track A mainline, GLW det lower bound axiom retirement audit)

**Date:** 2026-05-03. **Branch:** `r46-track-a-mge-posdef` HEAD post-R63
(T1.0+T1.1+T1.2 audit + status doc + BACKGROUND.md append).
**Round type:** Variante 1, single round, mainline. **T1.0+T1.1 audit
caught a constant-gap mismatch on R63 brief premise** (third
consecutive Cowork-drafted Track A round to be audit-redirected:
R50, R62, R63) BEFORE code budget committed; round shipped honest
deferral instead of paper-fidelity downgrade, mirroring R50 / R62
pattern.

## Round outcome summary

**Net debt change:** 0 sorries / 0 axioms / 0 retirements = **0 net**.
Mainline ledger 18 → 18 (unchanged); axiom inventory 10 → 10
(unchanged); project total 38 → 38 (unchanged). **Audit-redirect, NOT
closure round.**

**Distribution outcome:** **lower** (P(audit-redirect on constant gap)
materialized as T1.1 grep audit caught that
`cauchy_hierarchical_det_lower_bound_explicit` was already in-tree
at `CauchyDetLowerBound.lean:3093` with a constant 9.16x looser than
the paper bound). T2.1 + T2.2 explicitly SKIPPED per discipline rule
"if any claim cannot be verified, flag and propose alternative"
(`feedback_paper_recheck_t10` standing protocol).

**The R63 audit is mismatch ledger entry #18.** Same Cowork+Grok
shared scope-mismatch family as #16 (R50 GLW shortcut bridge gap)
and #17 (R62 GLW Path A bridge gap). Pattern: brief's LOC estimate
is conditioned on a quantitative chain "landing" in the abstract,
without auditing whether the in-tree quantitative analysis already
exhausts the budget OR meets the paper's constant.

| Sub-task | Status | Net debt impact | Commit |
|---|---|---|---|
| T1.0 paper recheck (per `feedback_paper_recheck_t10`) | Full ✓ | 0 (audit) | this commit |
| T1.1 Mathlib API + in-tree Cauchy det availability + GLW grid audit | Full ✓ | 0 (audit) | this commit |
| T1.2 constant-gap finding (in-tree 118.77 vs paper 12.96) | Full ✓ | 0 (audit) | this commit |
| T2.1 Cauchy det identity from scratch | **SKIPPED** (already proven in-tree as `cauchy_det_formula`) | 0 | n/a |
| T2.2 axiom retirement via paper-faithful body | **SKIPPED** (constant gap blocks) | 0 | n/a |
| T3 build verification (helper-only, mainline-only) | Full ✓ | 0 | (pre-commit `lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut` → green at 3026 jobs, HEAD `f4011b9`) |
| T4 commit + push (audit doc + status doc + BG append) | Full ✓ | 0 | this commit |

## Round mechanics

### T1.0 — paper recheck

Per `feedback_paper_recheck_t10` standing protocol. The R60 attempt-2
audit (`TrackA_R60_T1_PerLemma41Audit.md` §T1.6) provides the
verbatim arXiv:1001.0200v1 §4 source-of-truth: GLW Lemma 4.2 second
half asserts `det(a) ≥ (240·e)^{-2m³}` for the m²×m² Cauchy-form
matrix on the hierarchical grid. The Cauchy 1841 determinant identity
(textbook; Krattenthaler 1999 arXiv:math/9902004 §2.2) was confirmed
NOT-in-Mathlib at pin `25ce63313608` (only
`Mathlib/LinearAlgebra/Vandermonde.lean` is present, no Cauchy variant).

**T1.0 verdict:** paper claims well-formed and unchanged from R60
attempt-2; no paper-fidelity issue with the brief's *statement*. The
brief's *feasibility estimate* is the audit issue (T1.2).

### T1.1 — Mathlib + in-tree API audit

`Matrix.vandermonde` / `Matrix.det_vandermonde` confirmed present in
Mathlib at pin (`Mathlib/LinearAlgebra/Vandermonde.lean`); brief's
Route 1 plan (Vandermonde + multilinearity) viable in principle.

**Critical finding 1 — T2.1 redundant.** In-tree Cauchy det identity
already proven:

| Line | Symbol | Status |
|------|--------|--------|
| `CauchyDetLowerBound.lean:337` | `cauchy_det_formula_fin` | `private theorem`, Fin version, full identity Full |
| `CauchyDetLowerBound.lean:488` | `cauchy_det_formula` | `private theorem`, general type, full identity Full |

Both discharge the classical Cauchy 1841 identity at the project
pin. R63 T2.1 (40–60 LOC re-derivation via `Matrix.vandermonde_det` +
multilinearity) is **redundant** — making one of these existing
theorems non-`private` is a 1-LOC change.

**Critical finding 2 — T2.2 constant gap.** In-tree hierarchical
bound also already proven, with constant 120:

| Line | Symbol | Form |
|------|--------|------|
| `CauchyDetLowerBound.lean:3067` | `cauchy_hierarchical_det_lower_bound` | `theorem` (public), `∃ c₀ > 0, ∀ m ≥ 1, exp(-c₀·m³) ≤ det Σ` |
| `CauchyDetLowerBound.lean:3093` | `cauchy_hierarchical_det_lower_bound_explicit` | `theorem` (public), `∀ m ≥ 1, exp(-120·m³) ≤ det Σ` |

The implicit witness from `hierarchical_log_det_lower_bound` (line
3054) is `c₀ = 116 + 2·log(4) ≈ 118.77`, with breakdown:
* `100·m³` from `shapeM_log_det_ge_explicit` (Stirling)
* `16·m³` from `crossblock_log_lb` (artanh + η chain)
* `2·log(4)·m³ ≈ 2.77·m³` from geometric scale-ratio

### T1.2 — constant-gap finding (mismatch ledger entry #18)

| Quantity | log form | m=1 numerical |
|----------|----------|---------------|
| Paper bound `(240·e)^{-2m³}` | `exp(-12.96·m³)` | `≈ 2.35×10⁻⁶` |
| In-tree explicit | `exp(-120·m³)` | `≈ 7.67×10⁻⁵³` |
| Gap (paper / in-tree) | factor ~9.16x in the constant | (paper much tighter) |

Since `-118.77·m³ ≤ -12.96·m³` for `m ≥ 1`, we have
`exp(-118.77·m³) ≤ exp(-12.96·m³) = (240·e)^{-2m³}`. The in-tree
explicit lower bound on `det Σ` is **strictly weaker** than the paper
bound. **The in-tree result does NOT imply the paper-stated axiom.**

To close the gap requires multi-round constant-tightening at the
existing 3000-LOC analysis level (`shapeM_log_det_ge_explicit`
constant 100 → ≤ 10; cross-block constant 16 → ≤ 8) — not a single
150–300 LOC body. See `TrackA_R63_T1_CauchyDetAudit.md` §T1.2 for
full numerical analysis and §T1.4 for R64+ alternative paths.

### T2.1 + T2.2 — SKIPPED per discipline

* **T2.1 (Cauchy det identity from scratch) — SKIPPED.** Identity
  already proven in-tree (lines 337/488). Re-derivation via
  `Matrix.vandermonde_det` is redundant.
* **T2.2 (paper-faithful body for `glw_det_lower_bound`) — SKIPPED.**
  Constant gap structurally blocks; closing requires multi-round
  Stirling/cross-block tightening.

Anti-pattern explicitly avoided: writing a wrapper
`theorem glw_det_lower_bound` that swaps the constant from
`(240·e)^{-2m³}` to `exp(-120·m³)` without flagging the paper-fidelity
downgrade. This would have falsely registered as axiom retirement
while silently changing the bound shape. R64a (option d in audit
doc) would do this honestly with explicit user authorization.

### T3 — build verification

`lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut`
→ `Build completed successfully (3026 jobs)` at HEAD `f4011b9`. No
.lean changes in R63 (audit-redirect ships only .md artifacts), so
build state is HEAD-unchanged.

### T4 — push

Single audit-only commit on `r46-track-a-mge-posdef`:
- `TrackA_R63_T1_CauchyDetAudit.md` (new)
- `PhaseV2R63Status.md` (this file, new)
- `BACKGROUND.md` (append R63 status section; tracked locally only
  per R62 pattern)

AXIOM_INVENTORY.md unchanged (no axiom retirement to record).
Lean source unchanged.

## Out-of-scope / R64+ planning

R64a (option d in audit doc) — **honest weakening**. Replace
`axiom glw_det_lower_bound` with
`theorem glw_det_lower_bound_weak : ∃ c > 0, ∀ m ≥ 1, exp(-c·m³) ≤ det A`,
discharged via reindexing
`glwMatrixA m hm ↔ Matrix.of (1/(hierGrid m _ + hierGrid m _))` plus
`cauchy_hierarchical_det_lower_bound`. Estimated ~50 LOC. **Net: -1
axiom, but loses paper-stated `(240·e)^{-2m³}` constant — needs user
sign-off on the paper-fidelity tradeoff before dispatch.**

R64b (option a) — Stirling tightening. Sharpen
`shapeM_log_det_ge_explicit` from `100·m²` to `≤ 10·m²`. Estimated
200–400 LOC, risk medium-high (unclear if structural m² coefficient
supports tightening to 10·m²).

R64c (option b) — cross-block tightening. Sharpen `crossblock_log_lb`
from `16·m³` to `≤ 8·m³`. Estimated 100–200 LOC, risk medium.

R64d (option a+b combined) — full constant chain refit. Estimated
300–500 LOC, risk medium-high.

R64e (option c) — paper-faithful constant analysis from scratch.
Duplicates 3000 LOC at sharper constants throughout. Out of scope
for any single round.

**No round of (a)–(e) is the simple T2.1 + T2.2 the R63 brief
proposed.** R63 audit-redirect closes the door on the R47-strategic-
Grok pre-flight estimate that `glw_det_lower_bound` is closeable in
190–360 LOC via the Cauchy det identity + grid bound chain alone.

## Calibration

Brief budget: 190–360 LOC bodies (T2.1 40–60 + T2.2 150–300).
Actual: 0 LOC (audit-redirect, both SKIPPED).

Brief realistic wall-clock: 3–4 build cycles. Actual: T1.0+T1.1+T1.2
audit completed in single session, no Lean build cycles needed (only
helper-build sanity check at HEAD `f4011b9`).

Brief risk band: medium. **Audit verdict**: brief's risk assessment
mistargeted — the deterministic Cauchy det identity side is low risk
(already done!), but the paper-constant side is multi-round high
risk (or paper-fidelity downgrade), neither of which the brief
contemplated.

**Calibration lesson (memory-worthy)**: when a brief's LOC estimate
covers a paper-stated *quantitative* bound that the in-tree state
already provides at a *different constant*, mandatory pre-dispatch
verification must include numerical comparison of the in-tree
constant against the paper constant. The R63 brief's Probe 2 strategic
review confirmed the deterministic *identity* coverage but did not
score the *constant* gap. This is the third recurrence (R50, R62, R63)
of the same audit-redirect pattern — the underlying issue is shared-
context-poverty between brief drafting and in-tree quantitative
state, not a brief-quality issue per se.

## R63 artifacts

- `FormalConjectures/.../Helpers/TrackA_R63_T1_CauchyDetAudit.md`
  — new (audit doc, T1.0 + T1.1 + T1.2 + T1.3 disposition + T1.4
  alternative paths + T1.5 anti-patterns avoided).
- `FormalConjectures/.../Helpers/PhaseV2R63Status.md` — this file, new.
- `BACKGROUND.md` — appended R63 status section.
- AXIOM_INVENTORY.md — **unchanged** (no fake retirement).
- Lean source: **unchanged** (no swaps performed).
