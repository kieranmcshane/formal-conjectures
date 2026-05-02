# Round 57 status — Q1c full close (V2 round 19)

**Date**: 2026-05-02.

**Branch**: `r46-track-a-mge-posdef`, mainline-only.

**Round type**: Variante 1, single round, mainline. Math-content full
close attempt on Q1c alternate-track per R52-T2.1 recipe. **First
post-batch math-content close attempt** on the project. ~3.5h
estimated, ~2.5h actual (under budget).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Round commits** (all on `r46-track-a-mge-posdef`):
- T1.1 audit: `Helpers/Round57_T1_Q1cFullCloseAttempt.md` + Q1c Stub
  reconnaissance.
- T2.1 Q1c full close: ~108 LOC body replacing
  `Helpers/MultivariateSmallBallUpper.lean:267-275` sorry.
- T2.2 + T2.3: AXIOM_INVENTORY.md + this status doc + build verification +
  push.

---

## Net debt change (R56 → R57)

| Metric | R56 close | R57 close | Δ |
|--------|-----------|-----------|---|
| User-defined axioms (mainline) | 9 | **9** | 0 |
| TAG'd sorries (mainline) | 10 | **10** | 0 |
| Items at R52 gate (mainline) | 19 | **19** | 0 |
| Sorries (alternate-track Q1c) | 2 | **1** | -1 |
| Project total items | 40 | **39** | -1 |

**Strategic value**: -1 alternate-track sorry; mainline gate counts
unchanged (file is alternate-track per R52 audit Claim 7). Closes the
pure-arithmetic combinatorial gap blocking the Q1c assembly's
geometric-series bookkeeping. Demonstrates **Q1c track engineering
tractability** post-R51 γ-floor pivot — first time a pure
math-content close has landed on alternate-track in a single round.
Pattern establishes recipe for follow-on math-content rounds.

---

## Round deliverables

### T1.1 — Claims Verification Table + recipe extraction

`Helpers/Round57_T1_Q1cFullCloseAttempt.md` (~140 lines, well above
≥30-line floor). All 8 Claims Verification Table rows VERIFIED.

Key findings:
- Stub at `Helpers/MultivariateSmallBallUpper.lean:267-275` (line shifted
  from R52 audit's 230-238 due to R52-T2.1 docstring expansion).
- Mathlib `sum_geometric_two_le` (`SpecificLimits/Basic.lean:351`) closes
  R52 audit gap (b) directly (no `Finset.` prefix; root namespace).
- R52 audit gap (a) (per-distance partition) circumvented by sum-split +
  reindex via `Finset.sum_range_reflect` + `Finset.sum_Ico_eq_sum_range`
  rather than Mathlib partition lemma.
- `multivariate_small_ball_upper` Stub at line 619 (was R52) /
  current line 765 untouched per R52+R57 audit (R58+ scope, multivariate
  Fourier infrastructure Mathlib gap).

### T2.1 — Q1c full close (`geomSeries_offDiag_le`)

`Helpers/MultivariateSmallBallUpper.lean:267-375` (sorry → ~108 LOC
proof body). Statement signature preserved verbatim:

```lean
lemma geomSeries_offDiag_le (M : ℕ) :
    ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
      (2 : ℝ) ^ (-(|(pq.2.val : ℤ) - (pq.1.val : ℤ)| : ℤ)) ≤ 4 * M
```

Proof structure:

1. **Term-rewrite helper** (3 LOC).
   `(2:ℝ)^(-(|a-b|:ℤ)) = (1/2:ℝ)^(a-b).natAbs` for `a, b : ℤ`,
   via `Int.natCast_natAbs` + `_root_.zpow_neg` + `zpow_natCast` +
   `inv_pow`. Note: `_root_.zpow_neg` disambiguation needed because
   `Matrix.zpow_neg` exists in scope.

2. **Per-row bound** (~75 LOC).
   For each `p : Fin M`, `∑ q : Fin M, (2:ℝ)^(-(|q.val - p.val|:ℤ)) ≤ 4`.
   Steps:
   * Convert `∑ q : Fin M, ...` to `∑ i ∈ range M, ...` via
     `Fin.sum_univ_eq_sum_range`.
   * Split `range M = range (p.val + 1) ∪ Ico (p.val + 1) M`
     (disjoint union via `Finset.sum_union`).
   * **Left part** (`i ≤ p.val`): rewrite `(i - p.val).natAbs = p.val - i`,
     then via `Finset.sum_range_reflect` reduce to
     `∑ i ∈ range (p.val + 1), (1/2)^i ≤ 2` (`sum_geometric_two_le`).
   * **Right part** (`i > p.val`): rewrite
     `(i - p.val).natAbs = i - p.val`, then via `Finset.sum_Ico_eq_sum_range`
     reindex to `∑ k ∈ range (M - (p.val + 1)), (1/2)^(k+1)`
     `= (1/2) · ∑ k ∈ range (...), (1/2)^k ≤ (1/2) · 2 = 1`.
   * Total per row: ≤ 2 + 1 = 3 ≤ 4.

3. **Main bound** (~25 LOC).
   * Relax `offDiag ⊆ univ ×ˢ univ` via
     `Finset.sum_le_sum_of_subset_of_nonneg` (term non-negativity from
     `zpow_nonneg`).
   * Factor as nested sum via `Finset.sum_product`.
   * Apply per-row bound to each `p : Fin M`.
   * Cardinality `card (Fin M) = M` via `Finset.card_univ` +
     `Fintype.card_fin`, multiply `M • 4 = 4M` via `nsmul_eq_mul` +
     `ring`.

Total: ~108 LOC, within R52 audit estimate (100-180 LOC).

### T2.2 — Build verification + AXIOM_INVENTORY.md + status doc

8 critical targets + `MultivariateSmallBallUpper` (alternate-track) +
`524.lean` all verified green via:

```
lake build \
  FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF \
  FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf \
  FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound \
  FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable \
  FormalConjectures.ErdosProblems.Helpers.GLWLowerProof \
  FormalConjectures.ErdosProblems.Helpers.GLWUpperProof \
  FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut \
  FormalConjectures.ErdosProblems.Helpers.MVGaussianDensityBound \
  FormalConjectures.ErdosProblems.Helpers.MultivariateSmallBallUpper \
  FormalConjectures.ErdosProblems.«524»
```

Output: `Build completed successfully (7947 jobs).` Only pre-existing
warnings (copyright style on `GLWUpperProof.lean:1:0`, AMS attribute on
`524.lean:3855`, module docstring on `524.lean:7631`, brownian-motion
local-changes warning, `ring` info at `MultivariateSmallBallUpper.lean:704`
which was at 595 pre-edit). No new sorry warnings.

AXIOM_INVENTORY.md updated: R57 section prepended, R56 section preserved
verbatim. R52 milestone gate trajectory updated post-R57.

### T2.3 — Push

Mainline pushed to fork (`r46-track-a-mge-posdef`).

---

## R57 outcome distribution actuals vs predictions

| Outcome | P(Full) predicted | Actual |
|---------|-------------------|--------|
| T1.1 audit | 0.90 | ✅ Full (Claims Verification Table 8/8) |
| T2.1 Q1c Full close | 0.55 | ✅ **Full** (geomSeries_offDiag_le sorry retired) |
| T2.2 build + status | 0.95 | ✅ Full (8 critical green + status doc) |
| T2.3 push | 0.95 | ✅ Full |
| Joint mandatory floor | ~0.55 | ✅ **Upper outcome** (-1 sorry, items 40 → 39) |

Actual joint Brier-honest read: **upper outcome landed**, -1 alternate-track
sorry. Mainline gate counts unchanged (alternate-track close per R52
audit Claim 7). First post-batch math-content close on the project, in
a single round, well within time budget (~2.5h vs 3.5h estimated).

---

## R58 candidate priority

1. **`multivariate_small_ball_upper` full close attempt** at
   `MultivariateSmallBallUpper.lean:765` (was 619 pre-R57). Status:
   blocked on multivariate Fourier infrastructure Mathlib gap per
   R52 audit. Likely requires either Mathlib pin bump (post-`v4.28`
   toolchain) or local development of Esseen smoothing /
   multivariate Fourier inversion infrastructure. Type B (Mathlib gap),
   not Type A. Lower P(Full)/round than R57.

2. **Continued alternate-track API drift fixes** — Errors C/D/E per
   R55 catalog; Type B/C, each ≥3-15 LOC restructure.

3. **TD5 close attempt** — track-d sub-lemma 3, depends on pin bump
   window per BACKGROUND.md TD4 note.

4. **Mainline retirement** — return to mainline 524.lean track if
   alternate-track candidates exhausted; subject to γ floor + β R58
   extension binding per BACKGROUND.md.

---

## Anti-mismatch hygiene 8/8

1. ✅ Statement signature preserved verbatim — only `:= by ... sorry`
   body replaced.
2. ✅ No imports added — proof uses only existing imports
   (`ProblemImports` via `CharFunCrossBlock` + others; `SpecificLimits`
   reachable via standard `Mathlib` import chain).
3. ✅ No other lemma in file modified —
   `multivariate_small_ball_upper` Stub at line 765 untouched.
4. ✅ R49 axiom #6 + R51 axiom #7 + R53 axiom #8 + R56 axiom #9
   preserved.
5. ✅ A1-A5 axioms at `524.lean:3574, :3643` preserved.
6. ✅ Track branches not touched (mainline only).
7. ✅ Build green on all 8 critical targets + alternate-track file +
   524.lean.
8. ✅ Mainline-only modification (single helper file body edit).

---

## Skin-in-the-game outcome

**Joint mandatory floor**: ~0.55 → **upper outcome landed**.

* T1.1 Claims Verification Table: ✅ (would have been 0 pts cap if absent).
* T2.1 committed (Full close, not just diagnostic): ✅ (would have been
  50% cap if partial without Mathlib gap citation).
* T2.3 push: ✅ (would have been 0 pts cap if missing).
* No axioms / other Q1c track theorems modified: ✅.
* Track branches not modified: ✅.

Full skin-in-the-game payout (no caps applied).
