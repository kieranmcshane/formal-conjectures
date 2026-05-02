# Round 55 status — Alternate-track drift fix sweep (V2 round 17)

**Date**: 2026-05-02.

**Branch**: `r46-track-a-mge-posdef`, mainline-only.

**Round type**: Variante 1, single round, mainline. Multi-target
mechanical API/simp drift fix sweep. Pattern match R52 CharFunCrossBlock
+ R54 MVGaussianDensityBound 1-line / few-line precedents. **Two
alternate-track build unblocks**, no mainline-gate sorry/axiom delta.
Continues the γ floor + β R58 extension trajectory binding per
BACKGROUND.md (R55 candidate #3 from R54 close, retired this round).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1` (unchanged from R54).

**Round commits**:
- T1.1 audit: `2d330e0` ("R55-T1.1: drift error catalog + Claims
  Verification Table").
- T2.1 fixes: `9c7818f` ("R55-T2.1: alternate-track drift fixes
  (DiameterSimpleFiniteGroups + 1141)").
- T2.2 + T2.3 status + AXIOM_INVENTORY + push: this commit.

---

## Net debt change (R54 → R55)

| Metric | R54 close | R55 close | Δ |
|--------|-----------|-----------|---|
| User-defined axioms (mainline) | 8 | **8** | 0 (no axiom touched) |
| TAG'd sorries (mainline) | 11 | **11** | 0 (both fix sites were Full proof attempts broken by drift, not TAG'd sorries) |
| Items at R52 gate (mainline) | 19 | **19** | 0 |
| Project total items | 41 | **41** | 0 |
| Critical-target build state | 8/8 green | 8/8 green | preserved |
| MVGaussianDensityBound build state | green (R54 unblock) | green | preserved |
| DiameterSimpleFiniteGroups build state | **broken** (`eq_top_iff_forall_ne_adj` not in pin) | **green** | unblocked |
| 1141.lean build state | **broken** (Decidable instance simp drift) | **green** | unblocked |
| Drift errors (full project) | 5 | **3** | -2 (HartshorneConjecture + 26 + 508 still Type B/C, deferred R56+) |

**Strategic value**: this is a **two-target alternate-track build
unblock**, not a mainline-gate item retirement. Both target files sit
*outside* the Erdős 524 dependency cone (per R53/R54 status §"Other
pre-existing failures"). R55 retires them cleanly:

- `Wikipedia/DiameterSimpleFiniteGroups.lean`: two `@[category test]`
  group-diameter test theorems
  (`groupDiam_alternating_three`, `groupDiam_perm_two`) become buildable.
- `ErdosProblems/1141.lean`: the `Decidable (Erdos1141Prop n)` scaffold
  instance becomes buildable. The Erdős 1141 problem itself remains
  open (`erdos_1141` line 56 sorry, unchanged).

The plan's "best case (-3 mainline sorries)" was unrealizable because
all 5 drift errors sit on Full proof attempts or test-tier theorems,
none are TAG'd sorries. R55 lands as **mid-distribution outcome**
(P~0.40 in plan distribution): two clean fixes, no sorry retirement,
two alternate-track unblocks.

---

## Round deliverables

### T1.1 — Drift error catalog + Claims Verification Table

`Helpers/Round55_T1_DriftSweep.md` (~268 lines, commit `2d330e0`).
All 8 Claims Verification Table rows VERIFIED. Five build errors
catalogued at HEAD `9ba0c27`:

- **Error A** (DiameterSimpleFiniteGroups, 2 sites): Type A — Mathlib
  pin behind PR #30129 commit `eae0ea4f18`. Fix: inline private helper.
- **Error B** (1141.lean, 1 site): Type A — simp normal-form drift
  needing `Nat.lt_succ_iff` augmentation.
- **Error C** (508.lean, 1 site): Type B — `Pairwise` simp drift
  needing per-pair restructure (~10-25 LOC). Deferred to R56+.
- **Error D** (26.lean, 1 site): Type B/C — `lia`/`grind` tactic drift
  needing `field_simp [mul_inv_cancel]` restructure (~3-5 LOC).
  Deferred to R56+.
- **Error E** (HartshorneConjecture, 1 site): Type C —
  `SheafOfModules.Hom.hom` field renamed; needs new-API investigation
  (≥15 LOC). Deferred to R56+.

T2.1 dispatch decision: apply Errors A + B (highest-confidence Type A),
defer C/D/E to R56+ per ≤30-LOC budget.

Anti-mismatch hygiene 8/8 verified pre-dispatch:
1. Only two non-524 files modified.
2. Helper proof for Error A inlined as `private` — no namespace
   pollution.
3. No new imports needed.
4. `top_le_iff`, `SimpleGraph.le_iff_adj`, `top_adj`, `Nat.lt_succ_iff`
   all confirmed present in pinned Mathlib HEAD `25ce633136`.
5. Track branches not touched.
6. R49 axiom #6 + R51 axiom #7 + R53 axiom #8 + A1-A5 untouched.
7. R46 helper `det_CFC_sqrt_eq_sqrt_det` not modified.
8. Q1c / track-c / track-d alternate-track infrastructure not modified.

### T2.1 — Apply 2 Type A fixes (commit `9c7818f`)

**Fix 1: `Wikipedia/DiameterSimpleFiniteGroups.lean`** (+12 / -2 LOC).

Three edits (single file, `private` helper + 2 call-site renames):
1. **Lines 43-51 (new helper)**: added `private theorem
   eq_top_iff_forall_ne_adj'` with proof body
   `simp [← top_le_iff, SimpleGraph.le_iff_adj]` — verbatim match for
   the upstream Mathlib commit eae0ea4f18 body. Annotated
   `@[category API, AMS 5]` to satisfy linter style requirements.
2. **Line 86** (was 84): replaced `rw [SimpleGraph.eq_top_iff_forall_ne_adj]`
   with `rw [eq_top_iff_forall_ne_adj']` (relative-namespace resolution
   inside `BabaiSeressConjectures`).
3. **Line 124** (was 122): same rename at the second call site.

`lake env lean Helpers/Wikipedia/DiameterSimpleFiniteGroups.lean`
clean post-fix (only the brownian-motion R38 ENat-patch local-changes
warning + the two pre-existing `'sorry'` warnings on lines 163/175 —
unrelated open conjectures `groupDiam_perm_n` etc.; zero errors).

**Fix 2: `ErdosProblems/1141.lean`** (+1 / -1 LOC, single token).

One edit:
1. **Line 44**: replaced
   `simp [Erdos1141Prop, le_sqrt, pow_two]` with
   `simp [Erdos1141Prop, le_sqrt, pow_two, Nat.lt_succ_iff]` — adds
   the `Nat.lt_succ_iff : a < n + 1 ↔ a ≤ n` simp lemma to bridge the
   `k * k ≤ n'` vs `k * k < n' + 1` normal-form mismatch.

`lake env lean ErdosProblems/1141.lean` clean post-fix (only the
brownian-motion warning + the pre-existing `'sorry'` warning on line
56 = the open Erdős 1141 problem itself, unchanged).

Net diff: **+13 / -3 LOC** total across 2 files.

### T2.2 — Build verification + AXIOM_INVENTORY update + status doc + push

This commit. Build verification via `lake build` of the 8
R50-relevant critical targets + 524 consumer + the two modified files:

```
$ lake build  <8 critical helpers + MVGaussianDensityBound>
   FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF
   FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf
   FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
   FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable
   FormalConjectures.ErdosProblems.Helpers.GLWLowerProof
   FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
   FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut
   FormalConjectures.ErdosProblems.Helpers.MVGaussianDensityBound
Build completed successfully (7930 jobs).

$ lake build FormalConjectures.ErdosProblems.«524»
                FormalConjectures.Wikipedia.DiameterSimpleFiniteGroups
                FormalConjectures.ErdosProblems.«1141»
... (only pre-existing copyright-style warnings on GLWUpperProof.lean:1:0
     + the 524.lean module-docstring linter warning at 7631:0)
✔ [7932/7933] Built FormalConjectures.ErdosProblems.«1141» (13s)
✔ [7933/7933] Built FormalConjectures.Wikipedia.DiameterSimpleFiniteGroups (13s)
Build completed successfully (7933 jobs).
```

All 8 R50-relevant critical build targets remain green. Both modified
files now green for the first time since the respective Mathlib pin /
simp-set drift events.

AXIOM_INVENTORY update (in this commit):
- New "Build status (R55 V2 round 17 — alternate-track drift fix sweep,
  mechanical)" block added at the top, above the R54 block.
- R55 candidate #3 marked retired in the R52-gate-trajectory R55
  candidates list; candidates #1 (companion `Matrix.det.hasFDerivAt`
  axiomatization) and #2 (Q1c full close) remain active for R56-R58.
- Sorry / axiom counts unchanged (8 axioms, 11 sorries, 19 mainline
  items, project total 41).

---

## Build verification — R55 close (verbatim summary)

```
$ lake build  <8 critical helpers + MVGaussianDensityBound>
warning: brownian-motion: repository '...brownian-motion' has local changes
... (only pre-existing copyright-style warnings on GLWUpperProof.lean:1:0)
Build completed successfully (7930 jobs).

$ lake build FormalConjectures.ErdosProblems.«524»  <2 modified files>
✔ [7932/7933] Built FormalConjectures.ErdosProblems.«1141» (13s)
✔ [7933/7933] Built FormalConjectures.Wikipedia.DiameterSimpleFiniteGroups (13s)
Build completed successfully (7933 jobs).
```

All 8 R50-relevant critical build targets remain green.
DiameterSimpleFiniteGroups + 1141 modified files now green for the
first time since the respective Mathlib pin / simp-set drift events.

---

## R52 milestone gate trajectory (post-R55)

Items at **19** (mainline). Gate threshold ≤ **8**.

R56-R58 trajectory must contribute **~11 retirements across 3 rounds =
~3.67/round**, well above the cumulative R40-R55 ~0.28/round rate
(16 rounds gross, sorries 14 → 11 mainline + 4 axioms-via-γ-floor swaps
and three alternate-track unblocks). **R52 gate fails decisively under
hybrid (c)** — γ floor + β R58 extension trajectory binding per
BACKGROUND.md.

R56 candidates (priority order, post-R55 retirement of candidate #3):
1. **Companion Stub `Matrix.det.hasFDerivAt` axiomatization** (R56
   γ-floor extension) — same TAG, same closure path as R53; +1 axiom
   -1 sorry, items unchanged. Mechanical, P(Full) ~0.95. Would bring
   axiom count to 9 + sorry count to 10. This is the "complete the
   pair" choice and the most-likely R56 dispatch.
2. **Q1c track full close attempt** — `geomSeries_offDiag_le`
   per-distance-class re-indexing per R52-T2.1 recipe, ~100-180 LOC,
   P(Full)/round ~0.55, item-positive on alternate-track if Full.
3. **Continued alternate-track API drift fixes** — Errors C/D/E from
   R55 catalog (508, 26, HartshorneConjecture); Type B/C, each
   exceeding ≤30-LOC R55 budget. Higher-LOC budget rounds could
   batch one or two.

User dispatch decision deferred to post-R55 push.

---

## Cumulative T1.1 audit ledger (unchanged: 8/8)

8 distinct misframings caught pre-dispatch via T1.1 audit pipeline
(unchanged from R50/R51/R52/R53/R54 — R55 is mechanical multi-target
pattern-match, no Grok dispatch). R55 T1.1 audit (8/8 VERIFIED) was a
clean catalog audit — five errors enumerated at full-project `lake
build`, two classified Type A and applied per-fix verbatim per the
brief, three classified Type B/C and deferred per ≤30-LOC discipline.
The catalog explicitly identifies Mathlib commit `eae0ea4f18` as the
source of Error A (lemma added in PR #30129 ahead of pin); discipline
rule "no Mathlib API guesswork" preserved by routing through the
upstream commit's verbatim proof body.

---

## Trajectory toward β R58

Post-R55: 3 rounds remaining (R56-R58). Item count: 19 → target 0
(sorry-free + axiom-free) is **infeasible** in 3 rounds at the
cumulative ~0.28 sorry/round rate. β R58 extension accepted as binding
commitment per BACKGROUND.md: if R58 closes with items > 0, the
project priority #1 (sorry-free + axiom-free 524.lean) extends beyond
R59 with explicit stop conditions defined per the user-driven roadmap.

R55 contributes exactly the deliverable promised: **mechanical
multi-target alternate-track build unblock for
`DiameterSimpleFiniteGroups` + `1141`, freeing two test-tier and
scaffold theorems for repo-health regression preservation**, full
anti-mismatch hygiene preservation, no contamination of track
branches, all critical build targets green.

---

## Skin-in-the-game (binding, mainline)

Per the R55 round brief skin-in-the-game block:

R55 outcome (this entry):
- ✅ Claims Verification Table produced (8/8 VERIFIED, T1.1 commit
  `2d330e0`).
- ✅ T2.1 fixes committed (Full, +13/-3 LOC across 2 files, T2.1
  commit `9c7818f`). Both helper / simp lemma signatures pinned and
  re-verified pre-edit.
- ✅ T2.2 build verified (7930 jobs across 8 critical helpers +
  MVGaussianDensityBound + 7933 jobs across 524 + 2 modified files).
- ✅ Push to mainline (T2.3, this commit).
- ✅ R46 helper not modified.
- ✅ R49 axiom #6 / R51 axiom #7 / R53 axiom #8 / A1-A5 not modified.
- ✅ Track branches not modified.
- ✅ 8-target regression check executed.
- ✅ Internal consistency: anchor block + skin-in-the-game both report
  no sorry retirement, two-target alternate-track unblock outcome.

**Estimated R55 score**: mid-distribution (P~0.40 in plan): clean
fixes, no sorry retirement, two alternate-track unblocked. Within
~225-440 pts range; no skin-in-the-game caps triggered.

---

## End of round.
