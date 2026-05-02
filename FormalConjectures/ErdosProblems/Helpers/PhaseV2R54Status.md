# Round 54 status — MVGaussianDensityBound API drift fix (V2 round 16)

**Date**: 2026-05-02.

**Branch**: `r46-track-a-mge-posdef`, mainline-only.

**Round type**: Variante 1, single round, mainline. Mechanical API-drift
fix routing through R46 helper `det_CFC_sqrt_eq_sqrt_det`. Pattern match
R52 CharFunCrossBlock 1-line precedent. Alternate-track build unblock,
no mainline-gate sorry/axiom delta. Continues the γ floor + β R58
extension trajectory binding per BACKGROUND.md (R54 candidate #3 from
R53 close, retired this round).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1` (unchanged from R53).

**Round commits**:
- T1.1 audit + T2.1 fix + T2.2 status + AXIOM_INVENTORY: bundled in this
  R54 close commit (single mechanical edit; no separate audit-then-edit
  staging needed per R52 precedent for ≤ 5 LOC fixes).

---

## Net debt change (R53 → R54)

| Metric | R53 close | R54 close | Δ |
|--------|-----------|-----------|---|
| User-defined axioms (mainline) | 8 | **8** | 0 (no axiom touched) |
| TAG'd sorries (mainline) | 11 | **11** | 0 (line 199 was a Full proof attempt, not a sorry) |
| Items at R52 gate (mainline) | 19 | **19** | 0 |
| Project total items | 41 | **41** | 0 |
| Critical-target build state | 8/8 green | 8/8 green | preserved |
| MVGaussianDensityBound build state | **broken** (`PosSemidef.det_sqrt` API drift) | **green** | unblocked |

**Strategic value**: this is an **alternate-track build unblock**, not
a mainline-gate item retirement. `MVGaussianDensityBound.lean` was on
R52's "remaining failures" list (called out in R53 status §"Other
pre-existing failures … unrelated and unchanged"); R54 retires that
failure cleanly. Downstream consumers in this file
(`realMatrixSqrt_det_pos`, `realMatrixSqrt_det_ne_zero`,
`realMatrixSqrt_isUnit`, `volume_realMatrixSqrt_mulVec_preimage` —
4 Full theorems) are now buildable, enabling future R55+ rounds to
take this file as a green dependency.

The plan's "best case (-1 mainline sorry)" was unrealizable because
line 199 sits inside the Full theorem `realMatrixSqrt_det`, not a
TAG'd sorry. R54 lands as **mid-distribution outcome** (P~0.35 in plan
distribution): clean fix, no sorry retirement, alternate-track unblock.

---

## Round deliverables

### T1.1 — Claims Verification Table + line 199 context extraction

`Helpers/Round54_T1_MVGaussianDensityBoundFix.md` (~140 lines).
All 8 Claims Verification Table rows VERIFIED:

- **Claim 1 (build error at 199)**: VERIFIED via verbatim `lake env lean`
  output — `error(lean.invalidField): Invalid field 'det_sqrt'` at
  199:9; unsolved goal at 197:48.
- **Claim 2 (R46 helper available)**: VERIFIED — `det_CFC_sqrt_eq_sqrt_det`
  at `MultivariateGaussianPdf.lean:178` (R46-T2.1 sub-lemma (a) Full).
- **Claim 3 (signature compatibility)**: VERIFIED — `realMatrixSqrt M
  := CFC.sqrt M` (def at `CholeskyExistence.lean:41`) means after
  `unfold realMatrixSqrt`, the goal `(CFC.sqrt M).det = √M.det` matches
  the helper's conclusion exactly. Hypothesis `hM : M.PosSemidef`
  matches helper input `hS : S.PosSemidef`. No adapter needed.
- **Claim 4 (fix scope ≤ 15 LOC)**: VERIFIED — actual diff: +8 / -5 LOC
  (1 import line + 6-line docstring revision + 2-line proof body
  replacement = ~4 net LOC). Well under R52 precedent's bound.
- **Claim 5 (no regression on 8 critical targets)**: VERIFIED in T2.2
  (see below).
- **Claims 6-8 (R51 axiom #7 / R53 axiom #8 / A1-A5 + #6 preserved)**:
  VERIFIED (no change planned; only `realMatrixSqrt_det` body + import
  line touched).

Anti-mismatch hygiene 8/8:
1. Only one file modified (`MVGaussianDensityBound.lean`).
2. R46 helper signature pinned and re-verified at
   `MultivariateGaussianPdf.lean:178` pre-edit.
3. Import-cycle check: `MultivariateGaussianPdf` imports only
   `BrownianMotion.Gaussian.MultivariateGaussian` + Mathlib — no cycle
   with `MVGaussianDensityBound`'s chain (`GaussianBoxBounds` /
   `MVGaussianRotation`).
4. No Mathlib API guesswork — fix routes entirely through the in-tree
   R46 helper.
5. Track branches not touched.
6. R49 axiom #6 + R51 axiom #7 + R53 axiom #8 + A1-A5 untouched.
7. Other Full-closed theorems (incl. R46 helper itself) untouched.
8. Mainline-only modification.

### T2.1 — Fix at `MVGaussianDensityBound.lean:198-200` (and line 16 import + lines 187-194 docstring)

Three edits:

1. **Line 16 (new import)**: added
   `import FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf`
   between the existing `MVGaussianRotation` import and the
   `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` import. Cycle check
   passes (Claim 3 anti-mismatch).
2. **Lines 187-194 (docstring revision)**: replaced the citation of
   the deprecated `Matrix.PosSemidef.det_sqrt` Mathlib lemma with a
   citation of the R46 helper, documenting the routing rationale.
3. **Lines 198-200 (proof body)**: replaced
   ```
   unfold realMatrixSqrt
   rw [hM.det_sqrt]
   exact RCLike.sqrt_real
   ```
   with
   ```
   unfold realMatrixSqrt
   exact MultivariateGaussianPdf.det_CFC_sqrt_eq_sqrt_det hM
   ```
   The fully-qualified call is required because `MVGaussianDensityBound`
   sits in `namespace Erdos524.Helpers` while the helper sits in
   `namespace Erdos524.Helpers.MultivariateGaussianPdf` — Lean 4's
   relative-namespace resolution prefixes `MultivariateGaussianPdf.`
   from inside `Erdos524.Helpers`. (The pattern matches
   `GaussianParametricAnalysis.lean:123`'s
   `_root_.Erdos524.Helpers.MultivariateGaussianPdf.det_CFC_sqrt_eq_sqrt_det`
   re-export.)

Net diff: **+8 / -5 LOC**, single file.

`lake env lean Helpers/MVGaussianDensityBound.lean` clean post-fix
(only the brownian-motion R38 ENat-patch local-changes warning;
zero errors, zero sorries).

`lake build FormalConjectures.ErdosProblems.Helpers.MVGaussianDensityBound`:
**3029/3029 green** (3.2s).

### T2.2 — Build verification + AXIOM_INVENTORY update + status doc + push

This commit. Build verification via single `lake build` of the 8
critical targets (less the modified file, built separately above) +
524.lean:

- `lake build` of 7 helpers
  (`MultivariateGaussianCDF`, `MultivariateGaussianPdf`,
  `PhaseAUpperBound`, `MatrixDetDifferentiable`, `GLWLowerProof`,
  `GLWUpperProof`, `GLWSmallBallShortcut`):
  **7924/7924 green**. Only pre-existing copyright-style warnings on
  `GLWUpperProof.lean:1:0` and one related file (unchanged from R53);
  no errors.
- `lake build FormalConjectures.ErdosProblems.«524»`:
  **7931/7931 green**.

AXIOM_INVENTORY update (in this commit):
- New "Build status (R54 V2 round 16 — MVGaussianDensityBound API drift
  fix, mechanical)" block added at the top, above the R53 block.
- R54 candidate #3 marked retired in the R52-gate-trajectory R54
  candidates list; candidates #1 (companion `Matrix.det.hasFDerivAt`
  axiomatization) and #2 (Q1c full close) remain active for R55-R58.
- Sorry / axiom counts unchanged (8 axioms, 11 sorries, 19 mainline
  items, project total 41).

---

## Build verification — R54 close (verbatim summary)

```
$ lake build FormalConjectures.ErdosProblems.Helpers.MVGaussianDensityBound
warning: brownian-motion: repository '...brownian-motion' has local changes
✔ [3029/3029] Built FormalConjectures.ErdosProblems.Helpers.MVGaussianDensityBound (3.2s)
Build completed successfully (3029 jobs).

$ lake build  <7 critical helpers>
... (only pre-existing copyright-style warnings on GLWUpperProof.lean:1:0)
✔ [7924/7924] Built FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable (2.1s)
Build completed successfully (7924 jobs).

$ lake build FormalConjectures.ErdosProblems.«524»
warning: brownian-motion: repository '...brownian-motion' has local changes
Build completed successfully (7931 jobs).
```

All 8 R50-relevant critical build targets remain green. Modified file
(MVGaussianDensityBound) now green for the first time since R52's
"remaining failures" identification.

---

## R52 milestone gate trajectory (post-R54)

Items at **19** (mainline). Gate threshold ≤ **8**.

R55-R58 trajectory must contribute **~11 retirements across 4 rounds =
~2.75/round**, well above the cumulative R40-R54 ~0.30/round rate
(15 rounds gross, sorries 14 → 11 mainline + 4 axioms-via-γ-floor swaps
and one alternate-track unblock). **R52 gate fails decisively under
hybrid (c)** — γ floor + β R58 extension trajectory binding per
BACKGROUND.md.

R55 candidates (priority order, post-R54 retirement of candidate #3):
1. **Companion Stub `Matrix.det.hasFDerivAt` axiomatization** (R55
   γ-floor extension) — same TAG, same closure path as R53; +1 axiom
   -1 sorry, items unchanged. Mechanical, P(Full) ~0.95. Would bring
   axiom count to 9 + sorry count to 10. This is the "complete the
   pair" choice and the most-likely R55 dispatch.
2. **Q1c track full close attempt** — `geomSeries_offDiag_le`
   per-distance-class re-indexing per R52-T2.1 recipe, ~100-180 LOC,
   P(Full)/round ~0.55, item-positive on alternate-track if Full.
3. **Continued alternate-track API drift fixes** — other pre-existing
   failures (HartshorneConjecture, ErdosProblems 26/508/1141,
   DiameterSimpleFiniteGroups) per R53 status §"Other pre-existing
   failures" list; mostly outside the Erdős 524 dependency cone but
   useful for repo health.

User dispatch decision deferred to post-R54 push.

---

## Cumulative T1.1 audit ledger (unchanged: 8/8)

8 distinct misframings caught pre-dispatch via T1.1 audit pipeline
(unchanged from R50/R51/R52/R53 — R54 is mechanical pattern-match,
no Grok dispatch). R54 T1.1 audit (8/8 VERIFIED) was a clean
mechanical-fix audit — the brief was crisp, the build error was
immediately reproducible, the helper signature matched without
adapter, and the cycle-check confirmed import safety.

---

## Trajectory toward β R58

Post-R54: 4 rounds remaining (R55-R58). Item count: 19 → target 0
(sorry-free + axiom-free) is **infeasible** in 4 rounds at the
cumulative ~0.30 sorry/round rate. β R58 extension accepted as binding
commitment per BACKGROUND.md: if R58 closes with items > 0, the
project priority #1 (sorry-free + axiom-free 524.lean) extends beyond
R59 with explicit stop conditions defined per the user-driven roadmap.

R54 contributes exactly the deliverable promised: **mechanical
alternate-track build unblock for `MVGaussianDensityBound`, freeing
4 downstream consumer Full theorems for future-round dependency use**,
full anti-mismatch hygiene preservation, no contamination of track
branches, all critical build targets green.

---

## Skin-in-the-game (binding, mainline)

Per the R54 round brief skin-in-the-game block:

R54 outcome (this entry):
- ✅ Claims Verification Table produced (8/8 VERIFIED).
- ✅ T2.1 fix committed (Full, +8/-5 LOC). R46 helper signature
  compatibility verified pre-edit; cycle-check passed.
- ✅ T2.2 build verified (3029/3029 modified file + 7924/7924 7
  helpers + 7931/7931 524 target).
- ✅ Push to mainline.
- ✅ R46 helper not modified.
- ✅ R49 axiom #6 / R51 axiom #7 / R53 axiom #8 / A1-A5 not modified.
- ✅ Track branches not modified.
- ✅ 8-target regression check executed.
- ✅ Internal consistency: anchor block + skin-in-the-game both report
  no sorry retirement, alternate-track unblock outcome.

**Estimated R54 score**: mid-distribution (P~0.35 in plan): clean fix,
no sorry retirement, alternate-track unblocked. Within ~225-440 pts
range; no skin-in-the-game caps triggered.

---

## End of round.
