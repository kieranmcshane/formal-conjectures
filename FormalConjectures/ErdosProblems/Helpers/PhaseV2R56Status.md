# Round 56 status — companion `Matrix.det.hasFDerivAt` γ-floor axiomatization (V2 round 18)

**Date**: 2026-05-02.

**Branch**: `r46-track-a-mge-posdef`, mainline-only.

**Round type**: Variante 1, single round, mainline. Mechanical
γ-floor extension axiomatization. Pattern match R49 + R51 + R53
precedents (4× successful precedent now post-this round). Continues the
γ floor + β R58 extension trajectory binding per BACKGROUND.md.

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Round commits** (all on `r46-track-a-mge-posdef`):
- T1.1 audit: `8a09995` — `R56-T1.1: Claims Verification Table +
  signature extraction audit`.
- T2.1 axiom replacement: `c3a0ac1` — `R56-T2.1: companion
  Matrix.det.hasFDerivAt γ-floor axiomatization`.
- T2.2 AXIOM_INVENTORY.md update: `34ff848` — `R56-T2.2: AXIOM_INVENTORY.md
  update — Axiom #9 entry + counts 8→9`.
- T2.3 status doc + build verification + push: this commit.

---

## Net debt change (R55 → R56)

| Metric | R55 close | R56 close | Δ |
|--------|-----------|-----------|---|
| User-defined axioms (mainline) | 8 | **9** | +1 (Axiom #9 added) |
| TAG'd sorries (mainline) | 11 | **10** | -1 (companion `Matrix.det.hasFDerivAt` existential-form Stub retired) |
| Items at R52 gate (mainline) | 19 | **19** | 0 (sorry-to-axiom swap) |
| Project total items | 41 | 41 | 0 |

**Strategic value**: -1 sorry, +1 axiom is a wash for gate counting,
but it frees R57+ mainline budget for retirement work elsewhere
(Q1c track full close attempt, additional Mathlib API drift fixes,
Track C/D parallel work merge). **Pair-retirement bonus**: axioms #8 +
#9 retire simultaneously on Mathlib pin bump (post-`v4.28` toolchain)
or single from-scratch round (~100-200 LOC), giving -2 axioms in one
move.

---

## Round deliverables

### T1.1 — Claims Verification Table + Stub signature extraction

`Helpers/Round56_T1_HasFDerivAtAxiomatization.md` (~232 lines, well
above ≥30-line floor; commit `8a09995`). All 8 Claims Verification
Table rows VERIFIED.

Key findings:
- **Sole status: ZERO Lean call sites** at HEAD `a43ce68`. All grep
  hits for `Matrix.det.hasFDerivAt` are docstrings/comments
  (self-references in `MatrixDetDifferentiable.lean` at lines 30, 41,
  52, 63, 79–125 theorem-docstring, 145, 169, 173, plus `.md` audit
  docs in `R45/R44/R43/R41/R40_T1_*.md`, `PhaseV2R{40,41,44,53}Status.md`,
  `Round53_T1_*.md`, `AxiomFoundationAudit.md`).
- The companion `Matrix.det.hasFDerivAt` Stub at lines 126-134 was
  deliberately preserved at R53 per
  `Round53_T1_MatrixDetDifferentiableAxiomatization.md` §1 row 8 —
  R56 closes it via the same mechanical pattern.
- R53 axiom #8 `Matrix.det.differentiable` at line 196 (now 244
  post-R56) preserved verbatim; R49 axiom #6 + R51 axiom #7 + A1-A5 +
  R50 sub-Stubs all re-confirmed intact at HEAD `a43ce68`.
- R55 alternate-track build unblocks
  (`DiameterSimpleFiniteGroups`, `1141`) untouched.
- Q1a/b/c track infrastructure files (`CauchyDetLowerBound`,
  `CharFunCrossBlock`, `MultivariateSmallBallUpper`,
  `SurgicalDensityAtZero`, `EsseenSmoothing`, `GaussianHierCauchyBox`)
  untouched.

Anti-mismatch hygiene 8/8:
1. Type signature verbatim including all typeclass binders + explicit
   `(M : Matrix n n ℝ)` point.
2. No surrounding `variable` block (theorem binds typeclasses + point
   directly).
3. Zero Lean call sites pre/post.
4. R53 axiom #8 `Matrix.det.differentiable` at line 244 unaffected.
5. R49 axiom #6 + R51 axiom #7 + A1-A5 + R50 sub-Stubs unaffected.
6. R55 alternate-track build unblocks
   (`DiameterSimpleFiniteGroups`, `1141`) untouched.
7. Track branches not touched (mainline only).
8. No new imports needed.

### T2.1 — companion `Matrix.det.hasFDerivAt` Stub → axiom replacement

`Helpers/MatrixDetDifferentiable.lean` (commit `c3a0ac1`):

- Top-of-file Status block (lines 39-58 pre-R56) updated: header
  `R53 → R56`; new "axiom #9" entry added above the existing axiom #8
  entry; companion-pair retirement note added.
- Theorem docstring (lines 79-125 pre-R56) hoisted/expanded into
  γ-floor narrative + retirement plan (R57-R59 post-gate two-path
  sub-plan: Mathlib pin bump preferred, from-scratch fallback
  ~100-200 LOC for both axioms #8 + #9 as a pair). New docstring
  documents:
  - Mathematical content (Fréchet differentiability of determinant
    function with explicit cofactor / adjugate derivative).
  - γ-floor strategy rationale (BACKGROUND.md post-R55 directive).
  - Classical justification (Leibniz expansion + polynomial
    differentiability, Lang 2002 / Hörmander 1990 / Magnus & Neudecker
    1999).
  - Two-path R57-R59 retirement sub-plan with explicit pair-retirement
    bonus on Mathlib pin bump.
  - Closure-route detail (path α — Leibniz expansion + polynomial
    differentiability bookkeeping over `Equiv.Perm`).
  - Mathlib gap diagnostic (unchanged from R40-T2.1).
  - Future-readiness note: zero Lean call sites; future consumers
    (Slepian + multivariate-CDF chains) will use original axiom name.
- Existential-form `theorem Matrix.det.hasFDerivAt ... := by ... sorry`
  at lines 126-134 pre-R56 replaced with `axiom Matrix.det.hasFDerivAt`
  of identical signature (typeclass binders + explicit
  `(M : Matrix n n ℝ)` point + conclusion `∃ L, HasFDerivAt … L M`
  preserved verbatim).
- `lake env lean Helpers/MatrixDetDifferentiable.lean` clean (only
  unrelated brownian-motion local-changes warning; no sorry warnings
  on the axiomatized declaration).
- Net diff: **-40 / +88 LOC** (single file).

### T2.2 — AXIOM_INVENTORY.md update

Commit `34ff848`:
- Added R56 build-status block at top (above R55 block).
- Updated user-defined axioms count `8 → 9` + table row 9 for companion
  `Matrix.det.hasFDerivAt`.
- Added "Axiom #9 detail" section: Lean signature (verbatim with
  typeclass + explicit point annotation), mathematical content (plain
  English with Lang/Hörmander/Magnus & Neudecker references), why
  axiomatized at R56 (R40-T2.1 companion Stub deliberately preserved
  at R53; R56 closes via same mechanical pattern; γ-floor rationale +
  4× successful precedent now), retirement target R57-R59 with two-path
  sub-plan + explicit pair-retirement bonus on Mathlib pin bump,
  status (ACTIVE), zero Lean call sites at R56.
- Updated sorry-sites section title `11 → 10` with R56 retirement
  note + R50 deferred-paper sub-Stubs reference preserved.
- R55 block's R56-candidates list updated: candidate #1 marked
  retired this round; #2 (Q1c full close) + #3 (alternate-track API
  drift fixes) promoted/carried forward to R57 candidates.
- All commit hashes wired into the build-status block.

### T2.3 — Build verification + status doc + push

This commit. Build verification:

```
$ lake build  <8 critical helpers>
   FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF
   FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf
   FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
   FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable
   FormalConjectures.ErdosProblems.Helpers.GLWLowerProof
   FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
   FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut
   FormalConjectures.ErdosProblems.Helpers.MVGaussianDensityBound
warning: brownian-motion: ...local changes
... (only pre-existing copyright-style warnings on GLWUpperProof.lean:1:0)
✔ [7930/7930] Built FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable (10s)
Build completed successfully (7930 jobs).

$ lake build FormalConjectures.ErdosProblems.«524»
                FormalConjectures.Wikipedia.DiameterSimpleFiniteGroups
                FormalConjectures.ErdosProblems.«1141»
... (only pre-existing 524.lean linter warnings: line 3855 AMS / category
     attributes + line 7631 multi-module-docstring; all unchanged from R55)
Build completed successfully (7933 jobs).
```

All 8 R50-relevant critical build targets remain green
(7930/7930 jobs). 524 consumer + R55 alternate-track build unblocks
(`DiameterSimpleFiniteGroups`, `1141`) preserved (7933/7933 jobs).
Only pre-existing copyright-style warnings on `GLWUpperProof.lean:1:0`
+ pre-existing 524.lean style/docstring linter warnings — all
unchanged from R55 close.

---

## Build verification — R56 close

`lake env lean Helpers/MatrixDetDifferentiable.lean`:
✅ clean (only the brownian-motion R38 ENat-patch local-changes warning;
no sorry warnings on the axiomatized declaration — the companion Stub
that previously emitted a sorry warning is now an axiom).

All 8 R50-relevant critical build targets preserved (no changes to
mainline-gate-affecting files outside `MatrixDetDifferentiable.lean`).

---

## R52 milestone gate trajectory (post-R56)

Items at **19** (mainline). Gate threshold ≤ **8**.

R57-R58 trajectory must contribute **~11 retirements across 2 rounds =
~5.5/round**, well above the cumulative R40-R56 ~0.31/round rate.
**R52 gate fails decisively under hybrid (c)** — γ floor + β R58
extension trajectory binding per BACKGROUND.md.

R57 candidates (priority order, post-R56):
1. **Q1c track full close attempt** — `geomSeries_offDiag_le`
   per-distance-class re-indexing per R52-T2.1 recipe, ~100-180 LOC,
   P(Full)/round ~0.55, item-positive on alternate-track if Full.
2. **Continued alternate-track API drift fixes** — Errors C
   (508.lean Pairwise simp drift), D (26.lean lia/grind tactic drift),
   E (HartshorneConjecture SheafOfModules.Hom.hom field rename) per
   R55 catalog §"Build error catalog"; Type B/C, each ≥3-15 LOC
   restructure or new-API investigation.
3. **TD5 close attempt** — track-d sub-lemma 3 close (depends on
   pin bump window per BACKGROUND.md TD4 note); item-positive on
   track-d if Full.

User dispatch decision deferred to post-R56 push.

---

## Cumulative T1.1 audit ledger (unchanged)

8 distinct misframings caught pre-dispatch via T1.1 audit pipeline
through R55. R56 T1.1 audit (8/8 VERIFIED) was a clean
mechanical-axiomatization audit with no Grok dispatch — the brief was
crisp, the companion Stub statement was already verified by R40-T2.1 +
R45-R55 audits (cited by R53 as deliberately-preserved candidate), and
the consumer analysis (zero Lean call sites) is decisive.

---

## Trajectory toward β R58

Post-R56: 2 rounds remaining (R57-R58) before the β R58 extension
endpoint. Item count: 19 → target 0 (sorry-free + axiom-free) is
**infeasible** in 2 rounds at the cumulative ~0.31 sorry/round rate. β
R58 extension accepted as binding commitment per BACKGROUND.md: if R58
closes with items > 0, the project priority #1 (sorry-free + axiom-free
524.lean) extends beyond R59 with explicit stop conditions defined per
the user-driven roadmap.

R56 contributes exactly the deliverable promised: **mechanical
axiomatization of the companion `Matrix.det.hasFDerivAt` existential-form
Stub, freed mainline budget for downstream retirement rounds**, full
anti-mismatch hygiene preservation, no contamination of track branches,
all critical build targets green.

---

## Skin-in-the-game (binding, mainline)

Per the round brief implicit rules + R49/R51/R53 precedent:

R56 outcome (this entry):
- ✅ Claims Verification Table produced (8/8 VERIFIED), commit
  `8a09995`.
- ✅ T2.1 axiom committed with verbatim signature preservation, commit
  `c3a0ac1`. Zero Lean call sites verified pre/post via grep at HEAD
  `a43ce68`.
- ✅ T2.2 AXIOM_INVENTORY.md updated with full Axiom #9 detail +
  retirement plan + axiom count `8 → 9` + table row 9 + sorry count
  `11 → 10`, commit `34ff848`.
- ✅ T2.3 build verification (8 critical helpers + 524 + 1141 +
  DiameterSimpleFiniteGroups all green via `lake build`) + status doc
  (this) + push.
- ✅ Original name `Matrix.det.hasFDerivAt` preserved (not generic / not
  renamed) — searchable via `grep` at original location.
- ✅ Retirement target R57-R59 documented with concrete two-path
  sub-plan (Mathlib pin bump preferred with explicit pair-retirement
  bonus; from-scratch ~100-200 LOC fallback for both axioms #8 + #9 as
  a pair).
- ✅ Math content documented in both the Lean docstring (axiom site)
  and the AXIOM_INVENTORY.md "Axiom #9 detail" section
  (Lang/Hörmander/Magnus & Neudecker references).
- ✅ Other axioms (R49 axiom #6, R51 axiom #7, R53 axiom #8, A1-A5),
  R50 deferred-paper sub-Stubs, R55 alternate-track build unblocks NOT
  modified — verified via T1.1 §4 re-confirmations.

**Estimated R56 score**: upper-distribution outcome (0 skin-in-the-game
caps triggered).

---

## End of round.
