# Round 58 status — Alternate-track drift fix sweep continuation (V2 round 20)

**Date**: 2026-05-02.

**Branch**: `r46-track-a-mge-posdef`, mainline-only.

**Round type**: Variante 1, single round, mainline. Mechanical multi-target
API/simp-set drift fix sweep, continuation of R55. R58 revisits the three
errors deferred as Type B/C in R55 catalog (Errors C/D/E), and finds all
three are in fact Type A under deeper investigation. ~2.5h budget,
~1.5h actual (well under budget).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Round commits** (all on `r46-track-a-mge-posdef`):
- T1.1 audit: `Helpers/Round58_T1_DriftSweepContinued.md` (8/8 Claims
  Verification Table + per-error diagnostic + post-T2.1 amendments).
- T2.1 fixes: 3 minimal edits across `508.lean`, `26.lean`,
  `HartshorneConjecture.lean`.
- T2.2 + T2.3: this status doc + 15-target build verification + push.

---

## Net debt change (R57 → R58)

| Metric | R57 close | R58 close | Δ |
|--------|-----------|-----------|---|
| User-defined axioms (mainline) | 9 | **9** | 0 |
| TAG'd sorries (mainline) | 10 | **10** | 0 |
| Items at R52 gate (mainline) | 19 | **19** | 0 |
| Sorries (alternate-track Q1c) | 1 | **1** | 0 |
| Project total items | 39 | **39** | 0 |
| Alternate-track build state | 5 errors (R55 closed 2/5) | **0 errors (R55+R58 closed 5/5)** | -3 build errors |

**Strategic value**: 0 sorry / 0 axiom / 0 gate item retirement, but
**alternate-track build state fully unblocked** — the entire project
build now runs clean on the 15 verification targets. The five-error
catalog from R55 is now fully retired (R55 closed Errors A/B; R58 closes
Errors C/D/E). All five fixes turned out to be Type A; R55 underestimated
C/D/E as B/C under the time pressure of that round, but each was 1-2 LOC
under deeper investigation in R58. Pattern reinforces: **alternate-track
drift errors should default to Type A presumption with deeper Mathlib API
search before classifying as Type B/C.**

---

## Round deliverables

### T1.1 — Claims Verification Table + per-error diagnostic

`Helpers/Round58_T1_DriftSweepContinued.md` (~150 lines, well above
≥30-line floor). All 8 Claims Verification Table rows VERIFIED.

Key findings:
- Error C (`508.lean:99`): `pairwise_fin_succ_iff_of_isSymm` requires
  `[IsSymm _ R]` typeclass; for the anonymous symmetric-by-arithmetic
  relation Lean cannot synthesize this. Mathlib also exposes
  `pairwise_fin_succ_iff` (no IsSymm requirement, `Logic/Pairwise.lean:62`)
  which decomposes `Pairwise R` over `Fin (n+1)` directly. **1-token
  rename** suffices.
- Error D (`26.lean:74`): After `simp [..., Set.partialDensity]`, goal
  becomes `↑n / ↑n = 1` (real division). `lia` (delegating to grind
  e-matching) lacks `div_self` registration. Replace with explicit
  `have hn' : (n : ℝ) ≠ 0 := ...` + `simp [..., div_self hn']`.
  **+2 LOC.**
- Error E (`HartshorneConjecture.lean:69`): `SheafOfModules.Hom` field
  `hom` was renamed to `val` in current Mathlib pin
  (`Algebra/Category/ModuleCat/Sheaf.lean:46`). However, the InducedCategory
  pattern at `Category S.VectorBundles` means the morphism IS already
  `X.carrier ⟶ Y.carrier`. **`map f := f`** suffices (1-token deletion of
  `.hom` projection).

### T2.1 — 3 Type A fixes applied

Three minimal edits across three files:

1. **`FormalConjectures/ErdosProblems/508.lean:99`** — `pairwise_fin_succ_iff_of_isSymm`
   → `pairwise_fin_succ_iff` (1-token, P~0.75 → realized Full).
2. **`FormalConjectures/ErdosProblems/26.lean:72-74`** — added
   `have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)`
   line + replaced `lia` with `simp [..., div_self hn']` arg
   (P~0.80 → realized Full after intermediate `mul_inv_cancel₀` →
   `div_self` correction).
3. **`FormalConjectures/Paper/HartshorneConjecture.lean:69`** — `f.hom` →
   `f` (1-token, P~0.90 → realized Full after intermediate `f.val` →
   `f` correction).

Per-file `lake env lean` clean on all three after the corrections.

### T2.2 — 15-target build verification

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
  FormalConjectures.ErdosProblems.«524» \
  FormalConjectures.Wikipedia.DiameterSimpleFiniteGroups \
  FormalConjectures.ErdosProblems.«1141» \
  FormalConjectures.ErdosProblems.«508» \
  FormalConjectures.ErdosProblems.«26» \
  FormalConjectures.Paper.HartshorneConjecture
```

Output: `Build completed successfully (7952 jobs).` Pre-existing warnings
only (copyright style on `GLWUpperProof.lean:1:0`, AMS attribute on
`524.lean:3651, :3784, :3855`, module docstring on `524.lean:7631`,
brownian-motion local-changes warning, ring-tactic warning at
`MultivariateSmallBallUpper.lean:704`). **No new sorry warnings, no new
errors, no R57 Q1c regression, no axiom regression.**

### T2.3 — Push

Mainline pushed to fork (`r46-track-a-mge-posdef`).

---

## R58 outcome distribution actuals vs predictions

| Outcome | P(Full) predicted | Actual |
|---------|-------------------|--------|
| T1.1 audit | 0.90 | ✅ Full (Claims Verification Table 8/8) |
| T2.1 1-3 fixes | 0.65-0.80 | ✅ **Full × 3** (all 3 errors C/D/E closed) |
| T2.2 build + status | 0.95 | ✅ Full (15-target build green + status doc) |
| T2.3 push | 0.95 | ✅ Full |
| Joint mandatory floor | ~0.60 | ✅ **Best outcome** (-3 alternate-track build errors) |

Best-outcome distribution actually realized: 3 fixes Full, alternate-track
build state fully unblocked. **Calibration note**: the R58 brief's outcome
distribution placed best-case at P~0.20 (3 fixes Full); the actual best
case landed because R55's Type B/C classification of Errors C/D/E was
overcautious — under deeper Mathlib API search (which fits R58's full
budget but not R55's 30-LOC-per-fix budget), all three are Type A.

---

## R59 candidate priority

1. **`multivariate_small_ball_upper` full close attempt** at
   `MultivariateSmallBallUpper.lean:765`. Status: blocked on multivariate
   Fourier infrastructure Mathlib gap per R52 audit. Likely requires
   either Mathlib pin bump (post-`v4.28` toolchain) or local development
   of Esseen smoothing / multivariate Fourier inversion infrastructure.
   Type B (Mathlib gap), not Type A. Lower P(Full)/round than R57 / R58.

2. **TD5 close attempt** — track-d sub-lemma 3, depends on pin bump
   window per BACKGROUND.md TD4 note.

3. **Mainline retirement** — return to mainline 524.lean track if
   alternate-track candidates exhausted; subject to γ floor + β R58
   extension binding per BACKGROUND.md.

4. **Continued alternate-track maintenance** — full project `lake build`
   sweep to detect any newly-surfaced drift errors not covered in
   R55+R58 catalog.

---

## Anti-mismatch hygiene 8/8

1. ✅ Three non-524 files modified (`508.lean`, `26.lean`,
   `HartshorneConjecture.lean`). No 524.lean / no Helpers/ touched.
2. ✅ No imports added — all replacements use already-imported Mathlib API.
3. ✅ Mathlib pin `25ce633136` confirmed contains: `pairwise_fin_succ_iff`
   (`Logic/Pairwise.lean:62`), `div_self` (Mathlib core),
   `Nat.one_le_iff_ne_zero`, `SheafOfModules.Hom.val`
   (`Algebra/Category/ModuleCat/Sheaf.lean:46`), InducedCategory pattern
   (`CategoryTheory/Functor/InducedCategory.lean`).
4. ✅ R49/R51/R53/R56/A1-A5 axioms untouched.
5. ✅ R57 Q1c Full close untouched.
6. ✅ Track branches not touched (mainline only).
7. ✅ 15-target build green (8 critical + R57 alternate-track + 524 +
   R55 unblocks + R58 fix targets).
8. ✅ No γ-floor / β-extension axioms added.

---

## Skin-in-the-game outcome

**Joint mandatory floor**: ~0.60 → **best outcome landed**.

* T1.1 Claims Verification Table: ✅ (would have been 0 pts cap if absent).
* T2.1 committed (3 Full fixes): ✅ (would have been 50% cap if partial
  without Mathlib drift citation; would have been "honest empty +
  diagnostic" if T1.1 yielded zero Type A).
* T2.3 push: ✅ (would have been 0 pts cap if missing).
* No axioms / R57 Q1c / R55 alternate-track theorems modified: ✅.
* Track branches not modified: ✅.

Full skin-in-the-game payout (no caps applied).
