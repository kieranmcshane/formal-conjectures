# Round 63 — T1 audit (mainline, `r46-track-a-mge-posdef`)

**Date:** 2026-05-03. **Branch:** `r46-track-a-mge-posdef` HEAD `f4011b9`
(post-R61 GLW Path A pragmatic close, post-R62 audit-redirect).
**Pin:** `mathlib4 @ 25ce63313608`, `leanprover/lean4 v4.27.0-rc1`,
`brownian-motion @ 91267abd71bd`.
**Audit type:** R63 mandatory T1.0 + T1.1 (per
`feedback_paper_recheck_t10` and `feedback_track_c_round_process` —
Cowork-drafted brief depending on paper-stated quantitative bound;
T1.0 paper-recheck must precede T1.1 grep audit; if any claim
cannot be verified, flag explicitly and propose alternative).

## TL;DR

**The R63 brief's central claim — that `glw_det_lower_bound` (paper-stated
`(240·e)^{-2m³}`) can be retired in 190–360 LOC by writing a fresh
`Matrix.det_cauchy` (T2.1, 40–60 LOC) plus a paper-faithful grid
application (T2.2, 150–300 LOC) — does NOT survive the in-tree audit
at HEAD `f4011b9`.**

Two structural findings:

1. **T2.1 is essentially already done (and the brief did not know).**
   The Cauchy determinant identity is proven in-tree at
   [`Helpers/CauchyDetLowerBound.lean:488`](CauchyDetLowerBound.lean)
   as `cauchy_det_formula` (general type version) and `:337`
   as `cauchy_det_formula_fin` (Fin version). Both are `private` to
   the file but mathematically complete (Schur-style row/column
   reduction; ~250 LOC across the two aux lemmas + the inductive
   formula). The R63 brief proposed re-deriving this via
   `Matrix.vandermonde_det` + multilinearity, unaware of the existing
   in-tree work.

2. **T2.2 has a ~9.16x constant gap.** The same file already exposes
   `cauchy_hierarchical_det_lower_bound_explicit`
   ([line 3093](CauchyDetLowerBound.lean#L3093)) with the bound
   `det Σ ≥ exp(-120·m³)` for the m²×m² Cauchy matrix on the
   hierarchical grid `δ_{p,q} = 4^(p+m)·(m+q+1)` (indexed by
   `Fin m × Fin m`, equal up to reindexing to GLWSmallBallShortcut's
   `hierarchicalGrid` on `Fin (m·m)`; both use shape part `m+q+1`
   for `q ∈ {0,…,m-1}`, i.e. range `{m+1,…,2m}`). The paper-stated
   axiom target is `(240·e)^{-2m³} = exp(-2m³·log(240·e))
   ≈ exp(-12.96·m³)`. Since
   `-118.77·m³ ≤ -12.96·m³` (numerically, with `m³ ≥ 1`),
   we have `exp(-118.77·m³) ≤ exp(-12.96·m³) = (240·e)^{-2m³}`,
   so the in-tree explicit bound is **strictly weaker** than the
   paper bound and **cannot imply it**. To close the gap the existing
   3000+ LOC Stirling / artanh / cross-block analysis would need
   constant-tightening at the analysis level (`shapeM_log_det_ge_explicit`
   constant 100 → <10; cross-block constant 16 → <8), not a single
   150–300 LOC body.

This is **mismatch ledger entry #18**, same family as #17 (R62) and
#16 (R50): a Cowork-drafted brief presupposing a quantitative
constant-level claim without auditing the in-tree quantitative state
first. R63 was scoped as "deterministic side, unaffected by R62
finding" (per R62 audit T1.4 path 1 carve-out); T1.0 + T1.1 confirm
the **deterministic existence** half is unaffected, but the
**deterministic constant** half hits a structural ceiling at the
in-tree `shapeM_log_det_ge_explicit` Stirling tightness.

Per `feedback_paper_recheck_t10` standing protocol and the R50 / R62
precedent (`PhaseV2R50Status.md`, `TrackA_R62_T1_SmallBallRetirementAudit.md`),
R63 ships **T1.0 + T1.1 audit only**; **T2.1 + T2.2 SKIPPED**;
**T3 + T4 reduced to status doc + audit commit**. **Net debt change:
0 sorries / 0 axioms = 0 net.** Mainline ledger 18 → 18; axiom
inventory 10 → 10. **Audit-redirect, not closure round.**

---

## T1.0 — Paper recheck (per `feedback_paper_recheck_t10`)

### Cauchy 1841 determinant identity (textbook / Krattenthaler 1999)

> **Cauchy determinant.** For any `n` and any pairwise distinct
> `x_1, …, x_n, y_1, …, y_n` such that `x_i + y_j ≠ 0` for all `i, j`,
>
> `det(1/(x_i + y_j))_{i,j=1..n}
>   = ∏_{1 ≤ i < j ≤ n} (x_j − x_i)(y_j − y_i) / ∏_{i,j=1..n} (x_i + y_j)`

Reference: Krattenthaler, "Advanced Determinant Calculus" (1999),
arXiv:math/9902004, §2.2. The symmetric case `x = y = δ` reduces to
`det(1/(δ_i + δ_j)) = (∏_{i<j}(δ_j-δ_i))² / ∏_{i,j}(δ_i+δ_j)`
(squared Vandermonde-style numerator over divisor product).

This identity is **NOT in Mathlib at pin `25ce63313608`** (see grep
of `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/`: only
`Mathlib/LinearAlgebra/Vandermonde.lean` exists, with
`Matrix.det_vandermonde`; no Cauchy determinant lemma).

### GLW 2010 §4 Lemma 4.2 — paper-stated bound

Per the R60 attempt-2 audit `Helpers/TrackA_R60_T1_PerLemma41Audit.md`
§T1.6 (verbatim arXiv:1001.0200v1 §4 source-of-truth at the project
pin), the paper claim is:

> **Lemma 4.2 (second half).** For the Cauchy-form matrix
> `a_{ij} = 1/(δ_i + δ_j)` on the hierarchical grid
> `δ_{m·p+q} = 4^{p+m}·(m+q)` (paper indexing `0 ≤ p < m`,
> `1 ≤ q ≤ m`, encoded flat on `Fin (m·m)` as
> `(p, q-1) ↦ m·p + (q-1)` with shape part `m + (q-1) + 1 = m + q`),
> `det(a) ≥ (240·e)^{-2m³}`.

Numerically `(240·e)^{-2m³} = exp(-2m³·log(240·e)) ≈ exp(-12.9613·m³)`.

### T1.0 verdict

**Paper claims are well-formed and unchanged from R60 attempt-2.**
The Cauchy det identity is classical; the paper bound `(240·e)^{-2m³}`
is the verbatim Lemma 4.2 second half. No paper-fidelity issue with
the brief's *statement*. The brief's *feasibility estimate* is the
audit issue — see T1.2.

---

## T1.1 — Mathlib + in-tree API verification at pin

### Mathlib API at pin `25ce63313608`

| Symbol | Location | Status |
|--------|----------|--------|
| `Matrix.vandermonde` | `Mathlib/LinearAlgebra/Vandermonde.lean` | ✓ present |
| `Matrix.det_vandermonde` | same | ✓ present (Vandermonde det formula `∏_{i<j}(v j - v i)`) |
| `Matrix.det_cauchy` / `cauchy_det` | nowhere in `Mathlib/` | ✗ absent |
| `Matrix.det_succ_row_zero` | `Mathlib/LinearAlgebra/Matrix/Determinant/` | ✓ present (Laplace expansion) |
| `Matrix.det_apply` (Leibniz) | same | ✓ present |
| `Matrix.det_eq_of_forall_row_eq_smul_add_const` | same | ✓ present (used by in-tree aux1) |

The brief's Mathlib audit is **correct that Vandermonde-based Route 1
is feasible**. But the brief did not check whether the project itself
already provides a Cauchy det identity — it does.

### In-tree Cauchy det identity — already proven, `private`

`grep -n` on `cauchy_det_formula\|cauchy_det_pos` in
`FormalConjectures/ErdosProblems/Helpers/CauchyDetLowerBound.lean`:

| Line | Symbol | Form |
|------|--------|------|
| 53 | `cauchy_det_pos_aux1` | `private lemma`, row-reduction step |
| 143 | `cauchy_det_pos_aux2` | `private lemma`, column-reduction step |
| 239 | `cauchy_det_pos_fin` | `private lemma`, Fin-indexed positivity |
| 304 | `cauchy_det_pos` | `private theorem`, general type, `∀ ι [Fintype ι] [DecidableEq ι]`, `0 < det` |
| 337 | `cauchy_det_formula_fin` | **`private theorem`, Fin version, full identity `det = (∏_{i<j}(δ_j-δ_i))² / ∏_{i,j}(δ_i+δ_j)`** |
| 488 | `cauchy_det_formula` | **`private theorem`, general type, full identity** |

Both `cauchy_det_formula_fin` and `cauchy_det_formula` discharge the
classical Cauchy 1841 identity Full at the project pin. The R63
brief's T2.1 (40–60 LOC re-derivation via `Matrix.vandermonde_det` +
multilinearity) is **redundant** — making one of these existing
theorems non-`private` is a 1-LOC change.

### In-tree hierarchical bound — already proven, public, but with constant 120

`grep -n` on `cauchy_hierarchical_det_lower_bound`:

| Line | Symbol | Form |
|------|--------|------|
| 3050 | `hierarchical_log_det_lower_bound` | `private theorem`, existential c₀ |
| 3067 | **`cauchy_hierarchical_det_lower_bound`** | **`theorem` (public), existential c₀ form: `∃ c₀ > 0, ∀ m ≥ 1, exp(-c₀·m³) ≤ det Σ`** |
| 3093 | **`cauchy_hierarchical_det_lower_bound_explicit`** | **`theorem` (public), explicit constant: `∀ m ≥ 1, exp(-120·m³) ≤ det Σ`** |

The witness from `hierarchical_log_det_lower_bound` is
`c₀ = 116 + 2·log(4) ≈ 118.77` (line 3054), rounded up to 120 in the
explicit form (line 3093, with the `116 + 2·log(4) ≤ 120` step
discharged via `Real.log_two_lt_d9`). The constant breakdown
documented at lines 2877–2881:

* `100·m³` from `shapeM_log_det_ge_explicit` (Stirling, `c = 100·m²`
  scaled by `m` for the m blocks)
* `16·m³` from cross-block `crossblock_log_lb` (artanh + η chain)
* `2·log(4)·m³ ≈ 2.77·m³` from geometric scale-ratio
  `sum_log_scaleA_le`

Total: `100 + 16 + 2.77 = 118.77`.

### Index reindexing: `glwMatrixA` ↔ `Matrix.of (1/(hierGrid + hierGrid))`

| File | Index type | Shape part for `q ∈ Fin m` | Scale part for `p ∈ Fin m` |
|------|-----------|---------------------------|---------------------------|
| `GLWSmallBallShortcut.lean:317` `hierarchicalGrid` | `Fin (m·m)` (flat: `i ↦ (i/m, i%m)`) | `(m + (i%m + 1)) ∈ {m+1,…,2m}` | `4^(i/m + m)` |
| `CauchyDetLowerBound.lean:636` `hierGrid` | `Fin m × Fin m` | `(m + q.val + 1) ∈ {m+1,…,2m}` | `4^(p.val + m)` |

**The two grids are equal up to the standard `Fin (m·m) ≃ Fin m × Fin m`
bijection.** No paper-fidelity issue; the GLW comment at line 309–311
states `δ_{m·p+q} = 4^{p+m}·(m+q)` for `1 ≤ q ≤ m`, which after
substituting `q ∈ {1,…,m}` gives shape range `{m+1,…,2m}` — identical
to `hierGrid`'s `{m+1,…,2m}`.

### Consumer audit for `glw_det_lower_bound`

`grep -rn "glw_det_lower_bound" --include="*.lean"`:

| Site | Use |
|------|-----|
| `Helpers/GLWSmallBallShortcut.lean:364` | axiom declaration |
| `Helpers/GLWSmallBallShortcut.lean:389` | consumed by `glw_lemma_4_2_paper_specs` (det side via `refine ⟨_, glw_det_lower_bound m hm⟩`) |

`grep -rn "glw_lemma_4_2_paper_specs" --include="*.lean"`:

| Site | Use |
|------|-----|
| `Helpers/GLWSmallBallShortcut.lean:385` | declaration |

**Zero downstream consumers** outside `GLWSmallBallShortcut.lean`.
This matches the R60 audit finding "NOT consumed by any other file at
R60 close" and the R62 audit reconfirmation "R59 → R61 in-tree helper
consumers — zero outside the defining file".

---

## T1.2 — The constant-gap finding (mismatch ledger entry #18)

### Numerical comparison

| Quantity | Numerical value | log form |
|----------|-----------------|----------|
| Paper bound `(240·e)^{-2m³}` | for m=1: `≈ 2.35 × 10⁻⁶` | `exp(-12.9613·m³)` |
| In-tree `cauchy_hierarchical_det_lower_bound_explicit` | for m=1: `≈ 7.67 × 10⁻⁵³` | `exp(-120·m³)` (or `exp(-118.77·m³)` non-rounded) |
| Ratio (in-tree / paper) at m=1 | `≈ 3.27 × 10⁻⁴⁷` | (paper is much tighter) |
| Constant gap factor | — | `118.77 / 12.96 ≈ 9.16x looser` |

### Direction of the inequality

* The paper bound is a **stronger** lower bound (asserts `det` is at
  least `2.35e-6` for m=1, vs in-tree's `7.67e-53`).
* `exp(-118.77·m³) ≤ exp(-12.96·m³) = (240·e)^{-2m³}` for `m ≥ 1`
  (since `-118.77·m³ ≤ -12.96·m³` and `exp` is monotone).
* Therefore `det ≥ exp(-118.77·m³)` does **NOT** imply
  `det ≥ (240·e)^{-2m³}`. The in-tree result is implied *by* the
  paper claim, not the other way around.

### What it would take to close the gap

To prove `det Σ ≥ (240·e)^{-2m³}` in Lean, one of:

* (a) **Tighten `shapeM_log_det_ge_explicit` (constant `100·m²` →
  `≤ ~10·m²`).** This would require sharper Stirling on the
  `shapeS m q = m + q + 1` family (the file uses
  `Helpers/StirlingTwoSided.lean`'s two-sided Stirling, currently
  configured for the `100·m²` budget). Plausible scope: 200–400 LOC
  of Stirling refinement, but blocked on whether the actual
  Stirling-style bound *can* hit `10·m²` — the m² coefficient is
  structural, dominated by `∑_{q,q'} log(s_q + s_{q'})` over an m×m
  off-diag, and the paper's tighter constant comes from a sharper
  balance of `log(2 s)` vs `log|s_q - s_{q'}|`.
* (b) **Tighten cross-block (constant `16·m³` → `≤ ~8·m³`).** The
  `crossblock_log_lb` chain runs `8/3 m³` per `(p < r, q, s)`
  contribution then a factor of 6 from grouping (line 2833–2834
  `nlinarith [hbnd_eta]` discharges `3 · 2 · (8/3) m³ = 16 m³`).
  Tightening would require a sharper artanh / η decomposition; the
  factor-of-6 in `3 · 2 · (8/3)` looks like the loose place
  (e.g. could the `2` from squaring be absorbed elsewhere?), but
  it's not immediately a single round's tweak.
* (c) **Re-derive from scratch following the paper's explicit chain.**
  GLW 2010 §4 Lemma 4.2 has its own explicit computation. Rebuilding
  in Lean would duplicate ~3000 LOC of `CauchyDetLowerBound.lean`
  with sharper constants throughout.
* (d) **Weaken the axiom statement.** Replace
  `(glwMatrixA m hm).det ≥ (240·e)^{-2m³}` with
  `∃ c > 0, ∀ m ≥ 1, exp(-c·m³) ≤ (glwMatrixA m hm).det`
  (matching `cauchy_hierarchical_det_lower_bound`'s shape).
  Net axiom change: 0 (one axiom replaced by a Full theorem with
  weaker post-condition). Loses paper-fidelity in the statement;
  acceptable since `glw_lemma_4_2_paper_specs` has zero downstream
  consumers, but breaks the documented project goal of paper-faithful
  axiom shapes (per `feedback_erdos524_framing` "axioms = tech
  debt; infra rounds = milestones, NOT closures").

**None of (a), (b), (c) is a single 150–300 LOC round at HEAD `f4011b9`.**
Option (d) is in scope LOC-wise but is a paper-fidelity downgrade.

### Why the brief missed this

The brief's Probe 2 strategic estimate (40–60 LOC for the Cauchy
identity, 150–300 LOC for the grid application) was made without
checking the in-tree state of `CauchyDetLowerBound.lean`. The brief's
Strategy step 3 — "Lower-bound numerator and upper-bound denominator
using explicit grid values. Match against the paper's `(240·e)^{-2m³}`
bound. Paper's derivation (§4 / Lemma 4.2) walks this chain ; we
reproduce it" — describes the existing 3000-LOC analysis at the level
of a paragraph, with no LOC accounting for the constant-tightening
that the existing analysis doesn't deliver.

This is mismatch ledger entry #18, same Cowork+Grok shared scope-
mismatch family as #17 (R62 GLW Path A bridge gap) and #16 (R50 GLW
shortcut). Pattern: brief's LOC estimate is conditioned on the
deterministic chain "landing" in the abstract, without auditing
whether the in-tree quantitative analysis already exhausts the
budget.

---

## T1.3 — Disposition: T2.1 + T2.2 SKIP

Per `feedback_paper_recheck_t10` standing protocol — *"R59 audit
discipline rule 'if any claim cannot be verified, flag explicitly and
propose alternative'"* — and per the R50 / R62 precedent (audit-
redirect, honest deferral over fake retirement, weak-bound
substitution avoided), R63 ships:

* **T1.0 + T1.1 + T1.2 — Full ✓** (this audit doc).
* **T2.1 (Cauchy det identity from scratch) — SKIPPED.** The identity
  is already proven in-tree as `cauchy_det_formula_fin` /
  `cauchy_det_formula`; re-deriving it would be redundant. If a
  future round wants a public Cauchy det identity, the 1-LOC change
  is "remove `private` from `cauchy_det_formula`" — out of scope for
  R63 since no caller currently needs it.
* **T2.2 (axiom retirement via paper-faithful body) — SKIPPED.** The
  in-tree `exp(-120·m³)` bound is structurally weaker than the paper
  `(240·e)^{-2m³} ≈ exp(-12.96·m³)` bound; closing the gap requires
  multi-round Stirling/cross-block tightening (option (a) + (b)) or
  axiom-shape downgrade (option (d)) — neither is a single 150–300
  LOC round.
* **T3 (build verification) — reduced to confirming HEAD `f4011b9`
  helper-build green** (already done at audit dispatch:
  `lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut`
  → green at R61 close per `TrackA_R61_T1_PathAAudit.md`).
* **T4 (push) — reduced to single audit-doc commit + BACKGROUND.md
  status section + AXIOM_INVENTORY.md unchanged** (no axiom
  retirement to record).

**Net debt change R62 → R63: 0 sorries / 0 axioms = 0 net.** Mainline
ledger 18 → 18 (unchanged); axiom inventory 10 → 10 (unchanged);
project total 38 → 38 (unchanged). **Audit-redirect, NOT closure
round.** This is the third consecutive Cowork-drafted Track A round
(R50, R62, R63) where the headline claim has been audit-rejected at
the T1 floor; the underlying issue is shared-context-poverty between
brief drafting and in-tree state, not a brief-quality issue per se.

---

## T1.4 — Alternative paths (for R64+ planning, not R63 execution)

**R64a — Honest weakening (option d).** Replace
`axiom glw_det_lower_bound` with
```lean
theorem glw_det_lower_bound_weak (m : ℕ) (hm : 0 < m) :
    ∃ c > 0, Real.exp (-(c * (m : ℝ) ^ 3)) ≤ (glwMatrixA m hm).det
```
Body: reindex `glwMatrixA m hm` to `Matrix.of (1/(hierGrid m _ + hierGrid m _))`
on `Fin m × Fin m` (~30 LOC, standard `Fintype.equivFin`-style),
then apply `cauchy_hierarchical_det_lower_bound` (~5 LOC). Total
~50 LOC. **Net: -1 axiom, but loses the paper-stated `(240·e)^{-2m³}`
constant — is technically an axiom-shape change rather than a clean
retirement.** Weigh against project's paper-fidelity goal.

**R64b — Stirling tightening (option a).** Sharpen
`shapeM_log_det_ge_explicit` from `100·m²` to `≤ 10·m²`. Estimated
200–400 LOC of Stirling/Cauchy-on-shapeS refinement. Risk: medium-
high — unclear whether the structural m² coefficient supports
`10·m²` without a different decomposition. Probe needed.

**R64c — Cross-block tightening (option b).** Sharpen
`crossblock_log_lb` from `16·m³` to `≤ 8·m³`. Estimated 100–200 LOC.
Risk: medium — the `3 · 2 · (8/3) m³ = 16 m³` chain has identifiable
slack (the factor 2 from squaring; the 6 from grouping) but tightening
to 8·m³ may not be sufficient on its own — the total budget needs
both shapeM (≤ 10·m²) and cross-block (≤ 8/3·m³) tightening.

**R64d — Path retreat to weakened paper claim.** Investigate whether
GLW 2010's downstream §5–7 application of Lemma 4.2 actually requires
the sharp `(240·e)^{-2m³}` constant or just the `exp(-c·m³)` shape.
If the latter, the project can use the existing in-tree result with
no axiom (option d) and absorb the constant change in §5–7 callers
when those land. Paper-fidelity loss is then localized to a
constant remark.

None of R64a–R64d is the simple T2.1 + T2.2 the R63 brief proposed.
**R63 audit-redirect closes the door on the R47-strategic-Grok-pre-
flight estimate that `glw_det_lower_bound` is closeable in 190–360
LOC via the Cauchy det identity + grid bound chain alone.**

---

## T1.5 — Anti-patterns avoided in this audit

* Skipping T1.0 paper recheck (would have duplicated the brief's
  optimism about identity coverage). Avoided.
* Writing a thin wrapper `theorem glw_det_lower_bound` that swaps
  the constant from `(240·e)^{-2m³}` to `exp(-120·m³)` without
  flagging the paper-fidelity downgrade. Would have falsely
  registered as axiom retirement while silently changing the bound
  shape. Avoided — option (d) is flagged and deferred to R64a for
  explicit user decision.
* Re-deriving `cauchy_det_formula` from `Matrix.vandermonde_det`
  without checking the in-tree state. Would have wasted 40–60 LOC
  on a redundant identity. Avoided.
* Exporting closure-tier language to AXIOM_INVENTORY.md /
  BACKGROUND.md for a structurally-blocked closure (per
  `feedback_erdos524_framing`). Avoided.

End audit.
