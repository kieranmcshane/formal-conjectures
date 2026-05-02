# Axiom Inventory — Erdős Problem 524 (technical debt, fork branch)

This document is **fork-specific** to the
`r33-c-helpers-consolidation` branch and tracks the user-defined
axiom and Mathlib-version-skew **technical debt** of the
Gao–Li–Wellner small-ball formalization for Erdős Problem 524.

> **Project priority #1: a sorry-free *and* axiom-free Lean
> formalization of Erdős Problem 524.**
>
> The 8 axioms below are **debt to be retired**, not foundations
> to declare on. R38 makes the consumer build green so future
> axiom-retirement work has a compilable target; R38 retires no
> axiom and closes no sorry.

For the full audit, see
[`FormalConjectures/ErdosProblems/Helpers/AxiomFoundationAudit.md`](FormalConjectures/ErdosProblems/Helpers/AxiomFoundationAudit.md).

For the round-by-round status docs, see
[`FormalConjectures/ErdosProblems/Helpers/PhaseAR{34..38}Status.md`](FormalConjectures/ErdosProblems/Helpers/).

## Build status (R56 V2 round 18 — companion `Matrix.det.hasFDerivAt` γ-floor axiomatization, mechanical)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone). All 8 R50-relevant critical build targets remain green
  post-R56; R52's CharFunCrossBlock + MultivariateSmallBallUpper +
  R53's MatrixDetDifferentiable + R54's MVGaussianDensityBound + R55's
  alternate-track build state preserved.
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R56 (T1.1 audit
  `8a09995`, T2.1 axiomatization `c3a0ac1`, T2.2 + T2.3 + AXIOM_INVENTORY
  bundled in this R56 close commit).
* **Round type:** Variante 1, single round, mainline. Mechanical
  γ-floor extension axiomatization. Pattern match R49 + R51 + R53
  precedents (4× successful precedent now post-this round). Companion
  existential form Stub deliberately left in place at R53 — closed at
  R56 to extend γ-floor + β R58 trajectory.
* **Net debt change:**
  * Sorries: **11 → 10** (-1, companion `Matrix.det.hasFDerivAt`
    existential-form Stub at `MatrixDetDifferentiable.lean:126-134`
    retired via γ-floor axiomatization).
  * User-defined axioms: **8 → 9** (+1, `Matrix.det.hasFDerivAt`
    axiom #9 added at `MatrixDetDifferentiable.lean:179`).
  * Items at gate: **19 → 19** (0; sorry-to-axiom swap, no net delta).
  * Strategic value: continues γ-floor + β R58 extension trajectory
    per BACKGROUND.md post-R49/TC3 user directive; frees R57+
    mainline budget for retirements elsewhere (Q1c track full close
    attempt, additional Mathlib API drift fixes, Track C/D parallel
    work merge). **Companion-pair retirement bonus**: axioms #8 + #9
    retire together on Mathlib pin bump (post-`v4.28` toolchain) or
    single from-scratch round (~100-200 LOC), giving -2 axioms in one
    move.
* **Total mainline debt:** 9 user-defined axioms + 10 TAG'd sorries =
  19 items (unchanged from R55 close).
* **Cumulative R40-R56 retirement rate:** ~0.31 sorry/round (sorry
  count R39→R56: 14 → 10 across 17 rounds gross, with 5 axioms-via-γ-floor
  swaps and three alternate-track unblocks along the way).
* **Three deliverables this round:**
  * **R56-T1.1 Claims Verification Table + signature extraction**
    (`Helpers/Round56_T1_HasFDerivAtAxiomatization.md`, ~232 lines,
    well above ≥30-line floor; commit `8a09995`). All 8 claims
    VERIFIED. Companion existential form signature extracted verbatim
    from `MatrixDetDifferentiable.lean:126-134`. Caller analysis
    confirms zero Lean call sites at HEAD `a43ce68` — axiomatization
    is consumer-safe with zero call-site adjustment. R49 + R51 + R53
    8/8 anti-mismatch hygiene checklist applied; all 8 items green.
  * **R56-T2.1 axiom replacement** (commit `c3a0ac1`, +88 / -40 LOC
    in `Helpers/MatrixDetDifferentiable.lean`). Edits:
    1. Top-of-file Status block updated (`R53 →` → `R56 →`); axiom #9
       entry added above axiom #8 entry; companion-pair retirement
       note added.
    2. Theorem docstring (lines 79-125 pre-R56) hoisted/expanded into
       γ-floor narrative + retirement plan (R57-R59 post-gate
       two-path sub-plan: Mathlib pin bump preferred, from-scratch
       fallback ~100-200 LOC for both axioms #8 + #9 as a pair).
    3. `theorem Matrix.det.hasFDerivAt ... := by ... sorry` (lines
       126-134) replaced with `axiom Matrix.det.hasFDerivAt` of
       identical signature (typeclass binders + explicit
       `(M : Matrix n n ℝ)` point preserved verbatim, conclusion
       `∃ L, HasFDerivAt … L M` preserved verbatim).
    `lake env lean` clean per-file post-fix (only unrelated
    brownian-motion local-changes warning; no sorry warnings on the
    axiomatized declaration).
  * **R56-T2.2 build verification + AXIOM_INVENTORY + status doc + push**
    (this entry; `Helpers/PhaseV2R56Status.md`). Build verified: 8
    critical targets all green; only pre-existing copyright-style
    warnings on `GLWUpperProof.lean:1:0` + module-docstring linter
    warning on `524.lean:7631:0` (unchanged from R55).
* **R52 milestone gate trajectory (post-R56):** items at 19, gate
  threshold ≤ 8. R57-R58 trajectory must contribute **~11 retirements
  across 2 rounds = ~5.5/round**, well above the cumulative
  ~0.31/round rate. **R52 gate fails decisively under hybrid (c)** —
  γ floor + β R58 extension trajectory binding per BACKGROUND.md.
  R57 candidates (priority order):
  1. **Q1c track full close attempt** — `geomSeries_offDiag_le`
     per-distance-class re-indexing per R52-T2.1 recipe, ~100-180 LOC,
     P(Full)/round ~0.55, item-positive on alternate-track if Full.
  2. **Continued alternate-track API drift fixes** — Errors C
     (508.lean Pairwise simp drift), D (26.lean lia/grind tactic
     drift), E (HartshorneConjecture SheafOfModules.Hom.hom field
     rename) per R55 catalog §"Build error catalog"; Type B/C, each
     ≥3-15 LOC restructure or new-API investigation.
  3. **TD5 close attempt** — track-d sub-lemma 3 close (depends on
     pin bump window per BACKGROUND.md TD4 note); item-positive
     on track-d if Full.
* **Cumulative T1.1 audit ledger:** 8 distinct misframings caught
  pre-dispatch (unchanged from R50/R51/R52/R53/R54/R55 — R56 is
  mechanical pattern-match, no Grok dispatch).
* **Anti-mismatch hygiene 8/8:**
  type signature verbatim including all typeclass binders + explicit
  `(M : Matrix n n ℝ)` point; no surrounding `variable` block
  (theorem binds typeclasses + point directly); zero Lean call sites
  pre/post; R53 axiom #8 `Matrix.det.differentiable` at line 244
  unaffected; R49 axiom #6 + R51 axiom #7 + A1-A5 + R50 sub-Stubs
  unaffected; R55 alternate-track build unblocks
  (`DiameterSimpleFiniteGroups`, `1141`) untouched; track branches
  not touched (mainline only); no new imports needed; mainline-only
  modification (single helper file edited).

See `Helpers/PhaseV2R56Status.md` and
`Helpers/Round56_T1_HasFDerivAtAxiomatization.md` for the round
status doc + T1.1 Claims Verification Table.

## Build status (R55 V2 round 17 — alternate-track drift fix sweep, mechanical)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone). All 8 R50-relevant critical build targets remain green
  post-R55; R52's CharFunCrossBlock + MultivariateSmallBallUpper +
  R53's MatrixDetDifferentiable + R54's MVGaussianDensityBound build
  state preserved. **In addition,
  `Wikipedia/DiameterSimpleFiniteGroups.lean` and
  `ErdosProblems/1141.lean` now build green** for the first time
  since the respective Mathlib pin (PR #30129 commit `eae0ea4f18`,
  ahead of pin) / simp-set drift events — both are alternate-track
  build unblocks, not mainline-gate item retirements.
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R55 (T1.1 audit
  `2d330e0`, T2.1 fixes `9c7818f`, T2.2 + T2.3 + AXIOM_INVENTORY
  bundled in this R55 close commit).
* **Round type:** Variante 1, single round, mainline. Mechanical
  multi-target API/simp-set drift fix sweep. Pattern match R52
  CharFunCrossBlock 1-line + R54 MVGaussianDensityBound 8-LOC
  precedents. **Two alternate-track build unblocks**, no
  mainline-gate sorry/axiom delta.
* **Net debt change:**
  * Sorries: **11 → 11** (0; both fix sites were Full proof attempts /
    Decidable instance scaffold broken by Mathlib drift, not TAG'd
    sorries).
  * User-defined axioms: **8 → 8** (0; no axiom touched).
  * Items at gate: **19 → 19** (0; alternate-track unblock, not gate
    retirement). Strategic value: 2 `@[category test]` group-diameter
    test theorems in `DiameterSimpleFiniteGroups.lean`
    (`groupDiam_alternating_three`, `groupDiam_perm_two`) and the
    `Decidable (Erdos1141Prop n)` scaffold instance in `1141.lean`
    become buildable — repo-health regression preservation, no
    Erdős-524 cone delta.
* **Total mainline debt:** 8 user-defined axioms + 11 TAG'd sorries =
  19 items (unchanged from R54 close).
* **Cumulative R40-R55 retirement rate:** ~0.28 sorry/round (sorry
  count R39→R55: 14 → 11 across 16 rounds gross, with 4 axioms-via-γ-floor
  swaps and three alternate-track unblocks along the way).
* **Three deliverables this round:**
  * **R55-T1.1 Claims Verification Table + drift error catalog**
    (`Helpers/Round55_T1_DriftSweep.md`, ~268 lines, commit `2d330e0`).
    All 8 claims VERIFIED. Five build errors catalogued at HEAD
    `9ba0c27`: Errors A (DiameterSimpleFiniteGroups, 2 sites) + B
    (1141.lean, 1 site) classified Type A and applied; Errors C
    (508.lean) + D (26.lean) + E (HartshorneConjecture) classified
    Type B/C and deferred R56+ per ≤30-LOC budget.
  * **R55-T2.1 fix application** (commit `9c7818f`, +13/-3 LOC across
    2 files). Two edits:
    1. `Wikipedia/DiameterSimpleFiniteGroups.lean` (+12/-2 LOC):
       added `private theorem eq_top_iff_forall_ne_adj'` at lines
       43-51 with proof body
       `simp [← top_le_iff, SimpleGraph.le_iff_adj]` matching upstream
       Mathlib commit `eae0ea4f18` verbatim; replaced 2 call sites
       (lines 86, 124) of the pre-Mathlib-pin lemma name.
    2. `ErdosProblems/1141.lean` (+1/-1 LOC, single token): added
       `Nat.lt_succ_iff` to the Decidable instance simp set on line
       44 to bridge `k * k ≤ n'` ↔ `k * k < n' + 1` normal-form
       mismatch.
    `lake env lean` clean per-file post-fix.
  * **R55-T2.2 build verification + AXIOM_INVENTORY + status doc + push**
    (this entry; `Helpers/PhaseV2R55Status.md`). Build verified: 8
    critical targets all green (7930/7930 helpers + 7933/7933 with
    524 + 2 modified files); only pre-existing copyright-style
    warnings on `GLWUpperProof.lean:1:0` + module-docstring linter
    warning on `524.lean:7631:0` (unchanged from R54).
* **R52 milestone gate trajectory (post-R55):** items at 19, gate
  threshold ≤ 8. R56-R58 trajectory must contribute **~11 retirements
  across 3 rounds = ~3.67/round**, well above the cumulative
  ~0.28/round rate. **R52 gate fails decisively under hybrid (c)** —
  γ floor + β R58 extension trajectory binding per BACKGROUND.md.
  R56 candidates (priority order, post-R55 retirement of R55's
  candidate #3) — **candidate #1 retired this round at R56**:
  1. ~~**Companion Stub `Matrix.det.hasFDerivAt` axiomatization**~~
     **RETIRED THIS ROUND (R56)** — same TAG, same closure path as R53;
     +1 axiom -1 sorry, items unchanged. Mechanical, landed Full per
     R56-T2.1 commit `c3a0ac1`.
  2. **Q1c track full close attempt** — `geomSeries_offDiag_le`
     per-distance-class re-indexing per R52-T2.1 recipe, ~100-180 LOC,
     P(Full)/round ~0.55, item-positive on alternate-track if Full.
     **Promoted to R57 candidate #1.**
  3. **Continued alternate-track API drift fixes** — Errors C
     (508.lean Pairwise simp drift), D (26.lean lia/grind tactic
     drift), E (HartshorneConjecture SheafOfModules.Hom.hom field
     rename) per R55 catalog §"Build error catalog"; Type B/C, each
     ≥3-15 LOC restructure or new-API investigation.
     **Carried forward to R57 candidate #2.**
* **Cumulative T1.1 audit ledger:** 8 distinct misframings caught
  pre-dispatch (unchanged from R50/R51/R52/R53/R54 — R55 is mechanical
  multi-target pattern-match, no Grok dispatch).
* **Anti-mismatch hygiene 8/8:**
  only 2 non-524 files modified (single-file scope per fix;
  `DiameterSimpleFiniteGroups.lean` +12/-2 LOC, `1141.lean` +1/-1
  LOC); helper proof for Error A pinned and re-verified pre-edit
  (matches upstream Mathlib commit `eae0ea4f18` body verbatim);
  no new imports needed
  (`top_le_iff`/`SimpleGraph.le_iff_adj`/`top_adj`/`Nat.lt_succ_iff`
  all reachable through pre-existing
  `FormalConjectures.Util.ProblemImports` chain); no Mathlib API
  guesswork (helper proof copied verbatim from upstream, simp
  augmentation a single named Mathlib lemma); track branches not
  touched (mainline only); R49 axiom #6 + R51 axiom #7 + R53 axiom
  #8 + A1-A5 + R50 sub-Stubs untouched; R46 helper itself untouched;
  mainline-only modification.

See `Helpers/PhaseV2R55Status.md` and
`Helpers/Round55_T1_DriftSweep.md` for the round status doc + T1.1
Claims Verification Table.

## Build status (R54 V2 round 16 — MVGaussianDensityBound API drift fix, mechanical)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone). All 8 R50-relevant critical build targets remain green
  post-R54; R52's CharFunCrossBlock + MultivariateSmallBallUpper +
  R53's MatrixDetDifferentiable build state preserved. **In addition,
  `MVGaussianDensityBound.lean` now builds green** for the first time
  since R52's "remaining failures" identification — this is an
  alternate-track build unblock, not a mainline-gate item retirement.
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R54 (T1.1 audit +
  T2.1 fix + T2.2 status + AXIOM_INVENTORY: bundled in this R54 close
  commit per R52 precedent for ≤ 5 LOC mechanical fixes).
* **Round type:** Variante 1, single round, mainline. Mechanical
  API-drift fix routing through R46 helper `det_CFC_sqrt_eq_sqrt_det`
  at `Helpers/MultivariateGaussianPdf.lean:178`. Replaces the
  deprecated `Matrix.PosSemidef.det_sqrt` Mathlib dot-notation call at
  `Helpers/MVGaussianDensityBound.lean:199` (inside the Full theorem
  `realMatrixSqrt_det`) with a direct application of the in-tree R46
  helper. Pattern match R52 CharFunCrossBlock 1-line precedent.
* **Net debt change:**
  * Sorries: **11 → 11** (0; line 199 was a Full proof attempt broken
    by Mathlib API drift, not a TAG'd sorry).
  * User-defined axioms: **8 → 8** (0; no axiom touched).
  * Items at gate: **19 → 19** (0; alternate-track unblock, not gate
    retirement). Strategic value: 4 downstream Full theorems in
    `MVGaussianDensityBound.lean` (`realMatrixSqrt_det_pos`,
    `realMatrixSqrt_det_ne_zero`, `realMatrixSqrt_isUnit`,
    `volume_realMatrixSqrt_mulVec_preimage`) become available as
    green dependencies for R55+ rounds.
* **Total mainline debt:** 8 user-defined axioms + 11 TAG'd sorries =
  19 items (unchanged from R53 close).
* **Cumulative R40-R54 retirement rate:** ~0.30 sorry/round (sorry
  count R39→R54: 14 → 11 across 15 rounds gross, with 4 axioms-via-γ-floor
  swaps and one alternate-track unblock along the way).
* **Three deliverables this round (bundled commit):**
  * **R54-T1.1 Claims Verification Table + line 199 context extraction**
    (`Helpers/Round54_T1_MVGaussianDensityBoundFix.md`, ~140 lines).
    All 8 claims VERIFIED. Sole status: build error reproduced verbatim
    (`error(lean.invalidField): Invalid field 'det_sqrt'` at 199:9
    + unsolved goal `(CFC.sqrt M).det = √M.det` at 197:48); R46 helper
    signature confirmed compatible (after `unfold realMatrixSqrt`,
    goal exactly matches helper conclusion); fix scope ≤ 4 net LOC;
    cycle-check on new import passed.
  * **R54-T2.1 fix application** (`Helpers/MVGaussianDensityBound.lean`,
    +8/-5 LOC, single file). Three edits: line 16 (new import of
    `MultivariateGaussianPdf`), lines 187-194 (docstring revision
    citing R46 helper), lines 198-200 (proof body replaced
    `rw [hM.det_sqrt]; exact RCLike.sqrt_real` with
    `exact MultivariateGaussianPdf.det_CFC_sqrt_eq_sqrt_det hM`).
    `lake env lean` clean post-fix; `lake build` 3029/3029 on
    modified file.
  * **R54-T2.2 build verification + AXIOM_INVENTORY + status doc + push**
    (this entry; `Helpers/PhaseV2R54Status.md`). Build verified: 8 critical
    targets all green (7924/7924 helpers + 7931/7931 «524»); only
    pre-existing copyright-style warning on `GLWUpperProof.lean:1:0`
    (unchanged from R53).
* **R52 milestone gate trajectory (post-R54):** items at 19, gate
  threshold ≤ 8. R55-R58 trajectory must contribute **~11 retirements
  across 4 rounds = ~2.75/round**, well above the cumulative
  ~0.30/round rate. **R52 gate fails decisively under hybrid (c)** —
  γ floor + β R58 extension trajectory binding per BACKGROUND.md.
  R55 candidates (priority order, post-R54 retirement of R53's
  candidate #3):
  1. **Companion Stub `Matrix.det.hasFDerivAt` axiomatization** (R55
     γ-floor extension) — same TAG, same closure path as R53; +1
     axiom -1 sorry, items unchanged. Mechanical, P(Full) ~0.95.
  2. **Q1c track full close attempt** — `geomSeries_offDiag_le`
     per-distance-class re-indexing per R52-T2.1 recipe, ~100-180 LOC,
     P(Full)/round ~0.55, item-positive on alternate-track if Full.
  3. **Continued alternate-track API drift fixes** — other pre-existing
     failures (HartshorneConjecture, ErdosProblems 26/508/1141,
     DiameterSimpleFiniteGroups) per R53 status §"Other pre-existing
     failures" list; mostly outside the Erdős 524 dependency cone.
* **Cumulative T1.1 audit ledger:** 8 distinct misframings caught
  pre-dispatch (unchanged from R50/R51/R52/R53 — R54 is mechanical
  pattern-match, no Grok dispatch).
* **Anti-mismatch hygiene 8/8:**
  only `MVGaussianDensityBound.lean` touched (single file, +8/-5 LOC);
  R46 helper signature pinned and re-verified pre-edit; import-cycle
  check passed (`MultivariateGaussianPdf` imports only Mathlib +
  brownian-motion); no Mathlib API guesswork (routes through in-tree
  R46 helper); track branches not touched (mainline only); R49 axiom
  #6 + R51 axiom #7 + R53 axiom #8 + A1-A5 + R50 sub-Stubs untouched;
  R46 helper itself untouched; mainline-only modification.

See `Helpers/PhaseV2R54Status.md` and
`Helpers/Round54_T1_MVGaussianDensityBoundFix.md` for the round
status doc + T1.1 Claims Verification Table.

## Build status (R53 V2 round 15 — γ-floor `Matrix.det.differentiable` axiomatization, mechanical)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone). All 8 R50-relevant critical build targets remain green
  post-R53 axiom replacement; R52's CharFunCrossBlock + MultivariateSmallBallUpper
  build state preserved.
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R53 (T1.1 audit
  `b42485b`, T2.1 axiom replacement `1b25996`, T2.2 this
  entry, T2.3 build + status + push).
* **Round type:** Variante 1, single round, mainline. **γ-floor
  mechanical axiomatization**, not a math content close. Replaces
  `Matrix.det.differentiable` Stub at
  `Helpers/MatrixDetDifferentiable.lean:141` with axiom of identical
  signature. Continues the R49 (axiom #6) + R51 (axiom #7) γ-floor
  pattern.
* **Net debt change:**
  * Sorries: **12 → 11** (-1, `Matrix.det.differentiable` wrapper Stub
    retired via debt-conversion at
    `Helpers/MatrixDetDifferentiable.lean:141`).
  * User-defined axioms: **7 → 8** (+1, Axiom #8 added — see "Axiom #8"
    section below).
  * Items at gate: **19 → 19** (no change; sorry-to-axiom is a wash for
    gate counting). Strategic value: freed R54-R58 mainline budget for
    actual retirement work elsewhere.
* **Total mainline debt:** 8 user-defined axioms + 11 TAG'd sorries =
  19 items.
* **Cumulative R40-R53 retirement rate:** ~0.32 sorry/round (sorry count
  R39→R53: 14 → 11 across 14 rounds gross, with 4 axioms-via-γ-floor
  swaps along the way).
* **Three deliverables this round:**
  * **R53-T1.1 Claims Verification Table + `Matrix.det.differentiable`
    Stub signature extraction**
    (`Helpers/Round53_T1_MatrixDetDifferentiableAxiomatization.md`,
    ~197 lines, commit `b42485b`). All 8 claims VERIFIED. Sole
    status: **ZERO Lean call sites** at HEAD `c38c250` — all 6 grep
    hits for `Matrix.det.differentiable` / `Matrix.det.hasFDerivAt` are
    docstrings/comments (`524.lean:3514`,
    `MultivariateGaussianPdf.lean:242`,
    `GLWSmallBallShortcut.lean:220`,
    `MultivariateGaussianCDF.lean:46/63/177`). Companion Stub
    `Matrix.det.hasFDerivAt` (line 124-132) deliberately NOT modified
    in R53 (R54+ candidate). R49 axiom #6 + R51 axiom #7 + A1-A5 + R50
    sub-Stubs all re-confirmed intact at HEAD `c38c250`.
  * **R53-T2.1 `Matrix.det.differentiable` Stub → axiom replacement**
    (commit `1b25996`). In `Helpers/MatrixDetDifferentiable.lean`:
    * Deleted the 5-line `:= by ... sorry` body block.
    * Replaced `theorem` with `axiom` keyword; preserved exact signature
      including typeclass binders `{n : Type*} [Fintype n]
      [DecidableEq n]` and conclusion `Differentiable ℝ (fun A : Matrix
      n n ℝ => A.det)`.
    * Added a 50-line Lean docstring above the axiom documenting the
      γ-floor strategy, classical justification (Leibniz expansion +
      polynomial differentiability, Lang 2002 / Hörmander 1990), the
      two-path R55-R59 retirement plan, and the consumer-future-readiness
      note.
    * Top-of-file docstring updated (lines 39-58) to reflect the
      axiomatization status (companion `Matrix.det.hasFDerivAt` remains
      Stub, `Matrix.PosDef.inv_hasFDerivAt` retains R41-T2.2 Full state).
    * `lake env lean Helpers/MatrixDetDifferentiable.lean` clean (only
      the expected sorry warning from the unchanged companion Stub at
      line 124-132).
    * Net diff: -34 / +83 LOC.
  * **R53-T2.2 + T2.3 AXIOM_INVENTORY.md update + status doc + push**
    (this entry; `Helpers/PhaseV2R53Status.md`).
* **R52 milestone gate trajectory (post-R53):** items at 19, gate
  threshold ≤ 8. Mainline R54-R58 trajectory must contribute **~11
  retirements across 5 rounds = ~2.2/round**, well above the cumulative
  ~0.32/round rate. **R52 gate fails decisively under hybrid (c)** —
  γ floor + β R58 extension trajectory binding per BACKGROUND.md. R54
  candidates (priority order):
  1. **Companion Stub `Matrix.det.hasFDerivAt` axiomatization** (R54
     γ-floor extension) — same TAG, same closure path, +1 axiom -1
     sorry, items unchanged.
  2. **Q1c track full close attempt** — `geomSeries_offDiag_le`
     per-distance-class re-indexing per R52-T2.1 recipe, ~100-180 LOC,
     P(Full)/round ~0.55, item-positive on alternate-track if Full.
  3. **MVGaussianDensityBound API drift fix** (~5-15 LOC using R46
     helper `det_CFC_sqrt_eq_sqrt_det`) — Full close of pre-existing
     build error from R52's "remaining failures" list.
* **Cumulative T1.1 audit ledger:** 8 distinct misframings caught
  pre-dispatch (unchanged from R50/R51/R52 — R53 is mechanical
  axiomatization, no Grok dispatch).
* **Anti-mismatch hygiene 8/8:**
  type signature verbatim including all typeclass binders; no surrounding
  `variable` block (theorem binds typeclasses directly); zero Lean call
  sites pre/post; companion `Matrix.det.hasFDerivAt` Stub at line
  124-132 unaffected; R49 axiom #6 + R51 axiom #7 + A1-A5 + R50 sub-Stubs
  unaffected; track branches not touched (mainline only); no new imports
  needed.

See `Helpers/PhaseV2R53Status.md` and
`Helpers/Round53_T1_MatrixDetDifferentiableAxiomatization.md` for the
round status doc + T1.1 Claims Verification Table.

## Build status (R52 V2 round 14 — Q1c track consolidation, mid-distribution + Mathlib API drift fix)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone). All 8 R50-relevant critical build targets remain green.
  **Bonus**: `CharFunCrossBlock` + `MultivariateSmallBallUpper` (Q1c
  alternate-track) now compile cleanly for the first time since the
  Mathlib `offDiag_insert` API drift, lifting these from the "pre-
  existing failure" list flagged in R51's build verification.
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R52 (T1.1 audit
  `9d03cc3`, R51-followup placeholder fix `5d0682a`, T2.1
  CharFunCrossBlock + diagnostic upgrade `15ca171`, T2.2 this
  entry + status doc, T2.3 build + push).
* **Round type:** Variante 1, single round, mainline. **Q1c track
  consolidation, mid-distribution outcome** per the user dispatch
  ("Q1a/b/c track consolidation (item-positive if Full close lands)").
  T2.1 attempted Full close of `geomSeries_offDiag_le`
  (`Helpers/MultivariateSmallBallUpper.lean:230-238`) but determined
  the general `4M` bound requires per-distance-class fibre re-indexing
  (~100-180 LOC, P(Full)/round ~0.55) beyond the single-round R52
  budget; shipped diagnostic upgrade with concrete proof recipe + three
  Mathlib gaps decomposed.
* **Net debt change:**
  * Sorries (mainline gate): **12 → 12** (unchanged; `geomSeries_offDiag_le`
    is in `Helpers/MultivariateSmallBallUpper.lean`, an alternate-track
    file un-imported in mainline build path).
  * User-defined axioms: **7 → 7** (unchanged).
  * Items at gate: **19 → 19** (no mainline-gate change).
  * **Project-total side effect**: alternate-track build state
    improved — `CharFunCrossBlock` (635 LOC) + `MultivariateSmallBallUpper`
    (621 LOC) now compile for the first time since the Mathlib API drift.
    Project sorry-count on the alternate Q1c chain: 2
    (`geomSeries_offDiag_le` + `multivariate_small_ball_upper`),
    diagnostic-quality upgraded.
* **Total mainline debt:** 7 user-defined axioms + 12 TAG'd sorries =
  19 items (unchanged).
* **Three deliverables this round:**
  * **R52-T1.1 Q1c consolidation audit** (`Helpers/Round52_T1_Q1cConsolidationAudit.md`,
    ~173 lines, commit `9d03cc3`). All 8 Claims Verification Table
    rows VERIFIED. Catches the brief's slightly-off line numbers
    (brief said sorries at 73/238/616; actual sorries at 238/619, with
    line 73 a docstring reference). `multivariate_small_ball_upper`
    (line 619) flagged as **NOT closeable in R52** per the body
    comment's fundamental ε-cancellation issue (multivariate Fourier
    infrastructure gap, R55+ scope). `geomSeries_offDiag_le` (line 238)
    selected as T2.1 target with P(Full) 0.55.
  * **R52-T2.1a CharFunCrossBlock API drift fix** (commit `15ca171`).
    `Finset.offDiag_insert` now requires the element `a` as an explicit
    argument (Mathlib `variable (a : α)` ahead of the theorem); patched
    `CharFunCrossBlock.lean:397` from `Finset.offDiag_insert has` to
    `Finset.offDiag_insert a has`. **Full close of pre-existing build
    error** that was on the R49+R50+R51 "pre-existing failure" list.
    `lake build CharFunCrossBlock` 7867/7867 green;
    `lake build MultivariateSmallBallUpper` 7872/7872 green. First time
    the Q1c alternate-track compiles cleanly post-Mathlib-API-drift.
  * **R52-T2.1b geomSeries_offDiag_le diagnostic upgrade** (same commit).
    Per the brief's "if Full close lands" qualifier, the lemma body
    remains a TAG'd Stub with an enriched docstring documenting:
    (i) per-distance-class proof recipe
    `∑_{d=1}^{M-1} 2(M-d)·(1/2)^d ≤ 2M ≤ 4M`,
    (ii) three Mathlib gaps blocking single-round close —
    `Finset.partition_by_distance` (per-distance fibre cardinality),
    `Finset.sum_geometric_two_le_one` (finite-partial geometric bound),
    composition glue (~30-50 LOC),
    (iii) two tried alternative crude bounds (term ≤ 1 covers M ≤ 5;
    term ≤ 1/2 covers M ≤ 9) and their failure for general M,
    (iv) R53+ closure plan ~100-180 LOC, P(Full)/round ~0.55.
* **R52 milestone gate trajectory (post-R52):** items at 19, gate
  threshold ≤ 8. R53-R58 trajectory must contribute **~11 retirements
  across 6 rounds = ~1.83/round**, above the cumulative ~0.4/round rate.
  R52 demonstrated that the alternate Q1c track is now build-verifiable
  (CharFunCrossBlock + MultivariateSmallBallUpper cleanly compile) —
  this preserves R55-R58 optionality for actual track-Q1 retirements.
  R53 candidate per BACKGROUND.md: γ-floor `Matrix.det.differentiable`
  Stub axiomatization (item-neutral but frees more budget) OR Track C
  round 5 dispatch.
* **Cumulative T1.1 audit ledger:** 8 distinct misframings caught
  pre-dispatch (unchanged from R50/R51). R52 T1.1 audit (8/8 VERIFIED)
  did not catch any new misframings — the brief's line-number drift
  (73/616 vs 238/619) was minor positional, not semantic.
* **Anti-mismatch hygiene 8/8:**
  CharFunCrossBlock fix is a 1-line argument-position adjustment matching
  current Mathlib API; MultivariateSmallBallUpper change is docstring +
  comment-only (lemma body and signature unchanged at sorry); R49 axiom
  #6, A1-A5, R50 deferred-paper sub-Stubs, R51 axiom #7 all unaffected;
  no track branch contamination; mainline-only.

See `Helpers/PhaseV2R52Status.md` and
`Helpers/Round52_T1_Q1cConsolidationAudit.md` for the round status doc +
Claims Verification Table.

## Build status (R51 V2 round 13 — γ-floor MGE axiomatization, mechanical)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone). All R50-relevant critical build targets remain green
  post-R51 axiom replacement.
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R51 (T1.1 audit
  `d65514e`, T2.1 axiom replacement `5653eb7`, T2.2 commit
  `48e51ec`, T2.3 this entry + build verification).
* **Round type:** Variante 1, single round, mainline. **γ-floor
  mechanical axiomatization**, not a math content close. Replaces MGE
  Stub at `Helpers/MultivariateGaussianPdf.lean:248` with axiom of
  identical signature per the post-R50 user-confirmed audit-redirect
  ("γ floor + β R58 extension" trajectory).
* **Net debt change:**
  * Sorries: **13 → 12** (-1, MGE Stub `multivariateGaussian_eq_lebesgue_withDensity`
    retired via debt-conversion at `Helpers/MultivariateGaussianPdf.lean:248`).
  * User-defined axioms: **6 → 7** (+1, Axiom #7 added — see "Axiom #7"
    section below).
  * Items at gate: **19 → 19** (no change; sorry-to-axiom is a wash for
    gate counting). Strategic value: freed R52-R58 mainline budget for
    actual retirement work elsewhere.
* **Total mainline debt:** 7 user-defined axioms + 12 TAG'd sorries =
  19 items.
* **Cumulative R40-R51 retirement rate:** ~0.4 sorry/round (sorry count
  went 13 → 12 this round; cumulative decline R39→R51 = 14 → 12 across
  12 rounds, ~0.17 sorry/round when counting only R39-R51 against R39
  baseline 14, but ~0.4 if counting R40 onwards across the same
  retire/upgrade ledger). γ-floor swap is part of the R55-R59
  retirement plan: -1 sorry now in exchange for +1 axiom now, but the
  axiom retirement at R55-R59 then nets the original retirement at
  one-time cost.
* **Three deliverables this round:**
  * **R51-T1.1 Claims Verification Table + MGE Stub signature
    extraction** (`Helpers/Round51_T1_MGEAxiomatization.md`, ~194
    lines). All 8 claims VERIFIED (mandatory floor for T2.1 dispatch).
    Sole non-comment Lean caller of MGE confirmed at
    `Helpers/MultivariateGaussianPdf.lean:466` (`rw
    [multivariateGaussian_eq_lebesgue_withDensity S _hS]` inside
    `multivariateGaussianOrthantCDF_eq_lebesgue_integral`); identical-
    signature axiom swap preserves this caller. R49 axiom #6 + A1-A5 +
    R50 deferred-paper sub-Stubs all re-confirmed intact at HEAD
    `e682be7`.
  * **R51-T2.1 MGE Stub → axiom replacement.** In
    `Helpers/MultivariateGaussianPdf.lean:248`:
    * Deleted the 143-line `:= by ... sorry` body block (TAG
      `R43-T2.1-MGE-pushforward-jacobian-body`).
    * Replaced `theorem` with `axiom` keyword; preserved the exact
      signature including binders `(S : Matrix ι ι ℝ) (_hS : S.PosDef)`
      and section variables `{ι : Type*} [Fintype ι] [DecidableEq ι]`
      auto-bound from the namespace `variable` block.
    * New 75-line Lean docstring above the axiom documenting the γ-floor
      strategy, the three sub-gaps (a)+(b)+(c) decomposed (with sub-gap
      (a) noted as already closed at R46), the two-path R55-R59
      retirement plan (Mathlib pin bump preferred / from-scratch
      ~150-300 LOC fallback), and the consumer site at line 466.
    * Top-of-file docstring updated (lines 38-58) to reflect the
      axiomatization status.
    * `lake env lean
      FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean`
      clean.
    * Net diff: -199 / +84 LOC (the 143-LOC body comment block + ~50
      LOC of mid-signature comments removed; +75 LOC γ-floor docstring +
      6 LOC axiom declaration + 9 LOC top-of-file docstring update).
  * **R51-T2.2 AXIOM_INVENTORY.md update + R51-T2.3 build verification +
    status doc + push** (this entry; `Helpers/PhaseV2R51Status.md`).
* **R52 milestone gate trajectory (post-R51):** items at 19, gate
  threshold ≤ 8. Mainline R52-R58 trajectory must contribute ~11
  retirements across 7 rounds = ~1.6/round, which remains above the
  cumulative ~0.4/round rate. **R52 gate fails decisively under hybrid
  (c)** without major Track C/D contribution (BACKGROUND.md confirmed
  commitment to γ floor + β R58 extension). R52 candidate: either
  (i) Q1a/b/c track consolidation (close one of the 3 named sorries in
  `MultivariateSmallBallUpper.lean:73, :238, :616`), OR
  (ii) γ-floor `Matrix.det.differentiable` Stub axiomatization
  (item-neutral but frees more budget), OR
  (iii) γ-floor MGI Stub axiomatization (already Full per R44; not
  needed).
* **Cumulative T1.1 audit ledger:** 8 distinct misframings caught
  pre-dispatch via T1.1 audit pipeline (unchanged from R50 — R51 was a
  mechanical axiomatization round with no Grok dispatch, just the
  Claims Verification Table audit confirming MGE signature + caller
  preservation).
* **Anti-mismatch hygiene 8/8:**
  type signature verbatim (binders + conclusion); `_hS` underscore
  preserved at consumer site; section variables `{ι} [Fintype ι]
  [DecidableEq ι]` auto-bound identically; positional arity 2 (S, _hS)
  unchanged; sole Lean caller `MultivariateGaussianPdf.lean:466`
  verified to use positional form; no other consumer in mainline; R49
  axiom #6 + A1-A5 + R50 sub-Stubs unaffected; track branches not
  touched.

See `Helpers/PhaseV2R51Status.md` and
`Helpers/Round51_T1_MGEAxiomatization.md` for the round status doc +
T1.1 Claims Verification Table.

## Build status (R50 V2 round 12 — GLW determinant shortcut audit + deferred-paper sub-Stubs)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone). All 8 R50-relevant critical build targets remain green
  (7937 jobs, 19s incremental).
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R50 (T1.1 audit
  `a8b660c`, T2.1+T2.2 sub-Stubs `dbdb042`, T2.5 this entry).
* **Round type:** Variante 1, single round, mainline. **T1.1 audit
  caught chain mismatch on R50 brief premise** before code budget
  committed; round shipped honest deferral instead of fake retirement.
* **Net debt change:**
  * Sorries: **11 → 13** (+2, deferred-paper sub-Stubs in
    `Helpers/GLWSmallBallShortcut.lean:226, :256` —
    `glw_lemma_4_1_deferred_paper`, `glw_lemma_4_2_deferred_paper`).
  * User-defined axioms: **6 → 6** (unchanged — A4 + A5 NOT retired;
    the brief's premise that closing GLW Lemmas 4.1+4.2 retires them
    was unverified at T1.1 audit, see `Round50_T1_GLWShortcutAudit.md`).
  * Items at gate: **17 → 19** (+2, worse-than-baseline; honest
    deferral preferred over polluting `AXIOM_INVENTORY.md` with a
    faulty retirement claim).
* **Total mainline debt:** 6 user-defined axioms + 13 TAG'd sorries =
  19 items.
* **Cumulative R40-R50 retirement rate:** ~0.4 sorry/round (was ~0.5
  at R49 close; R50 added +2 sub-Stubs without retirement).
* **Three deliverables this round:**
  * **R50-T1.1 GLW determinant shortcut audit**
    (`Helpers/Round50_T1_GLWShortcutAudit.md`, 357 lines, commit
    `a8b660c`). Claims Verification Table verified claims 1-5;
    flagged claims 6-8 UNVERIFIED with alternative path proposed.
    Central finding: A4/A5 are Gaussian-process small-ball
    asymptotics over `IsGLWProcess Y` on continuous `u ≥ 0`;
    Lemmas 4.1+4.2 are finite-dim deterministic determinant +
    permanent identities. Bridge requires:
    * (α) discretization of sup-over-continuous to finite grid,
    * (β) Anderson's multivariate inequality (Mathlib status: 0%),
    * (γ) tail handling for full-window lower (`Ledoux §1.3` bridge),
    * (δ) optimization `m(ε) ~ |log ε|`,
    * (ε) `IsGLWProcess` covariance consumption.
    None are within the brief's 110-150 LOC scope. Mainline already
    contains a 5909+ LOC alternate in-tree closure track for A5
    (Q1a/b/c via Fourier smoothing + Berry-Esseen + hierarchical
    Cauchy: `CauchyDetLowerBound.lean` 3126 LOC, `CharFunCrossBlock.lean`
    635, `MultivariateSmallBallUpper.lean` 621, `SurgicalDensityAtZero.lean`
    543, `EsseenSmoothing.lean` 817, `GaussianHierCauchyBox.lean` 167)
    that the brief's GLW determinant shortcut does not connect to.
  * **R50-T2.1+T2.2 deferred-paper sub-Stubs** (commit `dbdb042`).
    Two TAG'd sub-Stubs added to `Helpers/GLWSmallBallShortcut.lean`:
    * `glw_lemma_4_1_deferred_paper` (Jacobi-style first-order
      determinant expansion along scalar path; load-bearing on R40
      `Matrix.det.differentiable` Stub),
    * `glw_lemma_4_2_deferred_paper` (existence of structured matrix
      with `per(A) = 1` and `det(A) = 32·m·(240·e⁻³)^m` of dim
      `m² × m²`).
    Conservative-shape forward-compatible signatures; exact GLW 2010
    §4 form requires paper access (not in R50 audit window). R51+
    refines or replaces with concrete in-tree consumer construction.
    `GLWSmallBallShortcut.lean` is currently un-imported anywhere, so
    the +2 sorries are isolated and do not regress consumer build
    state. T2.3 axiom-to-theorem swap **SKIPPED** (premise unverified
    at T1.1). T2.4 Q3.3 stretch **SKIPPED**.
  * **R50-T2.5 build verification + this AXIOM_INVENTORY.md update +
    status doc + push** (`Helpers/PhaseV2R50Status.md` + this entry).
    All 8 critical targets green: `MultivariateGaussianCDF`,
    `MultivariateGaussianPdf`, `PhaseAUpperBound`,
    `MatrixDetDifferentiable`, `GLWLowerProof`, `GLWUpperProof`,
    `«524»` consumer, plus the modified `GLWSmallBallShortcut`. R49
    + R38-R47 milestones preserved.
* **R52 milestone gate trajectory (post-R50):** items at 19, gate
  threshold ≤ 8. Mainline R51-R52 trajectory must contribute ~11
  retirements across 2 rounds = 5.5/round, **infeasible under any
  realistic scope**. R52 gate verdict: **fails decisively under
  hybrid (c)** without major Track C/D/branch-fork contribution. γ
  floor + β R58 extension (BACKGROUND.md confirmed commitment)
  remains the active trajectory: R51 should pivot to either
  (i) Q1a/b/c track consolidation (close one of the 3 named sorries
  in `MultivariateSmallBallUpper.lean:73, :238, :616`), OR
  (ii) γ-floor MGE axiomatization, OR
  (iii) γ-floor `Matrix.det.differentiable` Stub axiomatization.
* **Cumulative T1.1 audit ledger:** 8 distinct misframings caught
  pre-dispatch via T1.1 audit pipeline, including this round's
  semantic mismatch on the GLW determinant shortcut chain. Mismatch
  ledger entry **#16** added (Cowork+Grok shared chain-level
  scope-mismatch on Lemmas 4.1+4.2 → A4/A5 bridge; same family as
  #14 — chain-level vs per-step form). T1.1 pipeline once again
  delivers round-saving value: caught a misframed retirement claim
  at audit stage rather than after writing 110-150 LOC of code that
  would not connect to A4/A5.

See `Helpers/PhaseV2R50Status.md` and
`Helpers/Round50_T1_GLWShortcutAudit.md` for the round status doc +
T1.1 audit.

## Build status (R49 V2 round 11 — Path A axiomatization of Phase 2 body)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone).
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R49 (T1.1 audit `e9f5508`,
  T2.1 axiom replacement `c62b5e4`, T2.2 this entry, T2.3 build + push).
* **Round type:** Variante 1, single round, mainline. Path A switch per
  user directive — mechanical axiomatization of Phase 2 body to free
  3-5 mainline rounds for GLW shortcut + Track C/D parallel work.
* **Net debt change:**
  * Sorries: **12 → 11** (-1, Phase 2 body Stub at
    `MultivariateGaussianCDF.lean:160-313` retired).
  * User-defined axioms: **5 → 6** (+1, Axiom #6 added — see "Axiom #6"
    section below).
  * Items at gate: **17 → 17** (no change; strategic value is freed
    budget for downstream retirements, not item-count change).
* **Total mainline debt:** 6 user-defined axioms + 11 TAG'd sorries =
  17 items.
* **Cumulative R40-R49 retirement rate:** ~0.5 sorry/round (10 rounds
  elapsed since R39; sorry retirements include R44 MGI, R46 sub-gap (a)
  + (c), R49 Phase 2 body via Path A axiomatization). Note: Path A
  axiomatization is a sorry-retirement-via-debt-conversion, NOT a
  closure — the underlying mathematical claim is now load-bearing on
  Axiom #6 instead of being open.
* **Four deliverables this round:**
  * **R49-T1.1 Path γ' breakage re-verification + axiom signature draft**
    (`Helpers/Round49_T1_PathAAxiomatization.md`, 302 lines, commit
    `e9f5508`). Re-verified at HEAD `434a407` that R48-T1.1 misframings
    M1 + M2 still hold:
    * **(M1)** Lean MGI at `MultivariateGaussianPdf.lean:412` is the
      measure-vs-Lebesgue-integral REWRITE identity with no
      `HasFDerivAt` / `DifferentiableAt` content; pdf S-differentiability
      is a separate ~80-150 LOC chain blocked on R40
      `Matrix.det.differentiable` Stub.
    * **(M2)** `multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef`
      at `GaussianParametricAnalysis.lean:168` lives inside a
      `/-! ... -/` docstring code block, NOT a Lean theorem. Path γ' DCT
      chain consumer "Gaussian tail majorant" does not exist as a Lean
      object.
    No new theorems landed between R48 (`434a407`) and R49 mainline that
    unblock Path γ'. Path A axiomatization is the correct decision.
  * **R49-T2.1 Path A axiom replacement** (commit `c62b5e4`).
    `MultivariateGaussianCDF.lean:160-313` Stub deleted; replaced with
    `axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance`
    of identical type signature (verbatim binders + conclusion preserved,
    including `_h_pd` underscore prefix). Anti-mismatch hygiene:
    `lake env lean` clean on the modified file and on the only Lean
    consumer (`PhaseAUpperBound.lean:404`); positional caller unchanged.
  * **R49-T2.2 AXIOM_INVENTORY.md update** (this section + table update +
    Axiom #6 detail entry below).
  * **R49-T2.3 build verification + status doc + push R48+R49 to fork**
    (`Helpers/PhaseV2R49Status.md` + full `lake build` log).
* **R52 milestone gate trajectory:** items at 17, gate threshold ≤ 8.
  Mainline R50-R52 trajectory (post-R49 Path A): GLW shortcut R50-R51
  (~2-3 retirements target) + freed budget redirected to TC3 + TD4
  parallel work. Cumulative items projection: 17 - 5 to 17 - 7 = 10 to
  12 by R52 if GLW shortcut + cross-track contributions land.
  **R52 gate marginal under hybrid (c) target ≤ 8** without further
  axiomatization decisions; Path A switch buys budget but does not by
  itself flip the gate. Track C/Track D contribution cadence determines
  R52 outcome.
* **Cumulative T1.1 audit ledger:** 7 distinct Grok pre-flight
  misframings caught (unchanged from R48 — R49 was a mechanical
  axiomatization round with no Grok dispatch, just T1.1 re-verification
  of R48 audit).

See `Helpers/PhaseV2R49Status.md` and
`Helpers/Round49_T1_PathAAxiomatization.md` for the round status doc +
re-verification audit.

## Build status (R48 V2 round 10 — Path γ' framing audit + T2.1 abort)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone).
* **Branch:** `r46-track-a-mge-posdef` HEAD post-R48-T2.3 (T1.1 audit
  + revision shipped, T2.1 ABORTED per user course correction at
  T+0:50, T2.2 build verification on unchanged code).
* **Net debt change:** 0 sorries retired across R48 (12 → 12).
  **5th consecutive lower-distribution round** on mainline (R44-R48
  all 0 retirements). Round outcome: T1.1 audit caught two
  independent Grok Q3 Path γ' misframings; T2.1 code attempt aborted
  per user directive; substantive deliverable is the T1.1 audit doc.
* **Total mainline debt:** 5 user-defined axioms + 12 TAG'd sorries =
  17 items.
* **Cumulative R40-R48 retirement rate:** ~0.44 sorry/round (was
  ~0.5/round at R47 close); 9 rounds total elapsed since R39.
* **Three deliverables this round:**
  * **R48-T1.1 Path γ' framing verification audit**
    (`Helpers/R48_T1_PathGammaPrimeAudit.md`, ~395 lines after revision
    `d4aa693`). Verified at pin `mathlib4 @ 25ce63313608` that the
    brief's Grok Q3 Path γ' recipe rests on TWO independent
    misframings:
    * **(M1)** Lean MGI
      (`multivariateGaussianOrthantCDF_eq_lebesgue_integral` at
      `MultivariateGaussianPdf.lean:412`) is the integral REWRITE
      (CDF → ∫pdf), NOT a density-differentiability lemma. R44 Full
      body (lines 412-477) is three sequential `rw`s consuming MGE
      Stub via line 466. Grok appears to have conflated Lean MGI
      (integral rewrite) with literature MGI (Maximal Gaussian
      Inequality / generic chaining envelope for `sup_t G_t`). Pdf
      S-differentiability requires the closed-form chain through R40
      `Matrix.det.differentiable` Stub at
      `MatrixDetDifferentiable.lean:149` (~80-150 LOC, NOT 20-30 as
      Q3 claimed; R40 still open).
    * **(M2)** `GaussianParametricAnalysis.lean` (R46-T3.1) exposes
      only re-exports of R46 helpers (lines 103-154); the tail bound
      `multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef`
      lives inside a docstring code block (lines 168-192) labeled
      "R47+ scope, NOT YET LANDED" — it is NOT a Lean theorem. Path
      γ' step (3) DCT chain consumer "Gaussian tail majorant" does
      not exist as a Lean object; landing it as a Full helper is a
      separate ~60-100 LOC sub-round target.
    Combined LOC re-estimate for Path γ' Phase 2 body Full close:
    ~380-700 LOC (vs. Q3 brief estimate ~80-100). The MGE-axiom-
    equivalent treatment from the brief does NOT reduce these costs
    — they sit in chain dependencies independent of MGE.
  * **R48-T2.1 ABORTED** per user course correction at T+0:50. Lean
    Stub body at `MultivariateGaussianCDF.lean:160-313` unchanged
    from R47-T2.2 close (`03699d8`). T1.1 audit retained as the R48
    substantive substitute deliverable.
  * **R48-T2.2 build verification on unchanged code** (this entry).
    All 4 critical build targets remain green; R38-R47 milestones
    preserved. Three R40-era Mathlib piece Stubs unchanged:
    `Matrix.det.differentiable`, MGE Stub, sub-gap (b). MGE-axiom-
    equivalent treatment NOT applied (out of scope per brief).
  * **R48-T2.3 status doc + AXIOM_INVENTORY update** (this section
    + `Helpers/PhaseV2R48Status.md`).
* **R52 milestone gate trajectory:** items at 17, gate threshold ≤ 8.
  Mainline R49-R52 trajectory (post-R48 audit) retires ~2 sorries
  (R40 Stub + Phase 2 body via tail bound + R51 chain composition);
  cumulative items 17 - 2 = 15. **R52 GATE FAILS** without
  compression bundle items (iii) Track D round 3 + (iv) GLW shortcut
  + Track C round 2 contributing ~5-7 retirements jointly. Path A
  switch (axiomatize BTIS at R54) **probability promoted to ~70%**
  for R52 gate decision.
* **Cumulative T1.1 audit ledger: 7 distinct Grok pre-flight
  misframings caught before scope commitment** across R44, R45, R46,
  TC2, R47, R48-M1, R48-M2. Process Q4 ii Local Claude grep audit
  pipeline continues to be the primary defense against scope
  misalignment — R48 demonstrates the pipeline catching TWO
  misframings in a single audit pass.

See `Helpers/PhaseV2R48Status.md` and
`Helpers/R48_T1_PathGammaPrimeAudit.md` for the round status doc +
framing audit.

## Build status (R47 V2 round 9 — MGE three-bridge diagnostic + Phase 2 deferral)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone).
* **Branch:** `r46-track-a-mge-posdef` HEAD `03699d8`.
* **Net debt change:** 0 sorries retired across R47 (12 → 12). Round
  outcome: lower distribution per T1.1 audit prediction. Foundational
  + diagnostic-quality only.
* **Total mainline debt:** 5 user-defined axioms + 12 TAG'd sorries =
  17 items.
* **Cumulative R40-R47 retirement rate:** ~0.5 sorry/round (was
  ~0.43/round at R46 close); 8 rounds total elapsed since R39.
* **Three deliverables this round:**
  * **R47-T1.1 grep audit + framing verification**
    (`Helpers/R47_T1_GrepAuditAndFramingVerification.md`, ~269 lines)
    catches the R44/R45/R46 sub-gap (b) "80-120 LOC" cost estimate
    error. Verified at pin `mathlib4 @ 25ce63313608` that sub-gap (b)
    decomposes into THREE intermediate Mathlib bridges — n-ary
    Pi-withDensity factorization (~80-120 LOC), Map-withDensity
    through measurable equiv (~30-50 LOC), Lebesgue-on-EuclideanSpace
    identification (~20-100 LOC). Revised total: ~150-280 LOC, NOT
    80-120. Also flagged Phase 2 body Full close as blocked on three
    prerequisites (MGE main + `Matrix.det.differentiable` R40 Stub +
    uniform Gaussian-tail integrability).
  * **R47-T2.1 MGE Stub diagnostic-quality enhancement** (commit
    `dfc88bc`). MGE main Stub body updated with the three-bridge
    decomposition + concrete LOC estimates + Mathlib API gap citations
    + R48-R49 closure path. Round-attempt at Bridge (b.A) Full helper
    revealed non-trivial typeclass-inference issues (`SigmaFinite`
    constraint propagation, `lintegral_mul_const` finiteness side-
    conditions); aborted per honest-deferral rules. Net retirement: 0.
  * **R47-T2.2 Phase 2 body deferral diagnostic** (commit `03699d8`).
    Phase 2 body Stub body updated with concrete prerequisite chain
    citing MGE main close dependency, `Matrix.det.differentiable` R40
    Stub, uniform tail bound dependency. R46 helper consumption
    pathways identified explicitly (`posDef_min_eigenvalue_pos` direct
    consumer, `GaussianParametricAnalysis` foundational scaffold,
    `det_CFC_sqrt_eq_sqrt_det` consumed inside MGE main). Net
    retirement: 0.
* **R52 milestone gate trajectory:** items at 17, gate threshold ≤ 8.
  Mainline R48-R52 trajectory retires ~4 sorries (MGE main + det.diff
  + Phase 2 sub-gaps); cumulative items 17 - 4 = 13. R52 GATE FAILS
  without Track C/D parallel contribution. Path A (axiomatize BTIS at
  R54) likelihood promoted to **probable outcome**.
* **Process discipline:** R47 experienced repeated agent-infrastructure
  branch-switching causing ~0.5h overhead. Future rounds should batch
  git operations to maintain branch context across sub-tasks.

See `Helpers/PhaseV2R47Status.md` and
`Helpers/R47_T1_GrepAuditAndFramingVerification.md` for the round
status doc + framing audit.

## Build status (R46 V2 round 8 — MGE sub-gap (a) Full + PosDef min-eigenvalue)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02). 524.lean + all helpers compile.
* **Mathematical content (R46 update):** mid-distribution diagnostic
  enhancement with foundational infrastructure landed. Five
  deliverables, plus (third consecutive) Grok pre-flight misframing
  catch.
  * **R46-T1.1 grep audit + framing verification**
    (`Helpers/R46_T1_GrepAuditAndFramingVerification.md`, ~200 lines).
    Catches Grok R46 pre-flight Q2 misframing: "`Matrix.PosDef.isOpen`"
    in `Matrix n n ℝ` is **mathematically false** because PosDef
    requires `IsHermitian`, which is closed (not open) in the full
    matrix space. Patched to correctly-framed minimum-eigenvalue lower
    bound formulation. Sub-gap (c) constant-Jacobian linear pushforward
    additionally identified as DIRECT application of
    `map_linearMap_addHaar_eq_smul_addHaar` (`EqHaar.lean:234`) — no
    new sub-lemma needed.
  * **R46-T2.1 MGE sub-gap (a) Full close + (c) ApplyDirect.** Two
    new Full theorems in `Helpers/MultivariateGaussianPdf.lean`:
    * `det_CFC_sqrt_eq_sqrt_det` (~30 LOC): `(CFC.sqrt S).det =
      Real.sqrt S.det` for PosSemidef S. Composition of
      `CFC.sqrt_mul_sqrt_self` + `Matrix.det_mul` +
      `Real.sqrt_eq_iff_mul_self_eq`.
    * `det_CFC_sqrt_pos_of_posDef` corollary.
    MGE main body diagnostic refreshed to credit (a) Full + (c)
    ApplyDirect; remaining bottleneck narrowed to sub-gap (b)
    `stdGaussian_eq_lebesgue_withDensity` (~80-120 LOC, deferred to
    R47+).
  * **R46-T2.2 PosDef minimum-eigenvalue helpers (Full).** Two new
    Full theorems in `Helpers/PhaseAUpperBound.lean`:
    * `posDef_min_eigenvalue_pos` (~15 LOC): for PosDef M with
      `[Nonempty n]`, `∃ c > 0, ∀ i, c ≤ eigenvalues i`.
    * `posDef_min_eigenvalue_witness` (~25 LOC): same content with
      constant pinned via `Finset.min'`.
    These are foundational for R47+ Phase 2 body close (uniform
    Gaussian tail majorant on compact PosDef) and for
    local-stability-under-Hermitian-perturbations.
* **Net debt change R45 → R46:** axioms 5 → 5 (unchanged); sorries
  12 → 12 (unchanged — diagnostic-quality progress with foundational
  infrastructure landed). **0 net retirement** (below hybrid (c) target
  of 1.5-2.0/round); R47-R50 must compensate at 1.875-2.5/round to
  recover R52 gate viability.
* **All build targets remain green** (`lake env lean` clean on
  `MultivariateGaussianCDF.lean`, `MultivariateGaussianPdf.lean`,
  `MatrixDetDifferentiable.lean`, `PhaseAUpperBound.lean`,
  `524.lean`); R38 + R39 + R40 + R41 + R42 + R43 + R44 + R45
  milestones preserved.
* **Process Q4 ii continued value:** R46 catches **third consecutive**
  Grok pre-flight misframing. Pattern: Grok reliable for *math
  reasoning* (the WHY) but unreliable for *formal-Mathlib API claims*
  (the WHAT — exact lemma names, exact universe of discourse, exact
  ambient topology). Local Claude grep continues to deliver
  round-saving value at marginal cost.

See `Helpers/PhaseV2R46Status.md` and
`Helpers/R46_T1_GrepAuditAndFramingVerification.md` for the round
status doc + framing audit.

## Build status (R45 V2 round 7 — Phase 2 diagnostic-quality enhancement)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R45 update):** lands per R45-T1.1
  framing-verification audit's mid-distribution prediction
  ("Phase 2 partial — diagnostic enhancement only"). Three deliverables:
  * **R45-T1.1 framing verification audit**
    (`Helpers/R45_T1_FramingVerificationAudit.md`, ~353 lines)
    catches two specific Grok R45 pre-flight misframings:
    * Q1.a (`Matrix.PosSemidef.det_sqrt`) claimed in
      `Mathlib.Analysis.Matrix.Order` — NOT in Mathlib at the
      project pin (0 grep hits). Closure recipe revised to ~30-50
      LOC bridge (Grok said ~20-40).
    * Q3 (Phase 2 dependency) claimed MGI Full directly provides
      `HasFDerivAt` of pdf — partially mis-attributed. MGI gives
      only the rewrite; pdf differentiability requires R40/R41
      stubs + closed-form chain rule.
    Q1.b + Q1.c verified CORRECT. Mathlib API
    `hasFDerivAt_integral_of_dominated_loc_of_lip` confirmed at
    `Mathlib/Analysis/Calculus/ParametricIntegral.lean:164`.
  * **R45-T2.1+T2.2 Phase 2 body diagnostic enhancement.** Replaces
    stale R41/R42 comment block on `MultivariateGaussianCDF.lean:160`
    R35-T2.1 sorry with audit-aligned Path γ skeleton documenting
    (i) MGI rewrite (POST-R44 EXECUTABLE), (ii) diff-under-integral
    Mathlib API target, (iii) integrand pointwise differentiability
    chain (R40 Stub black-box + R41 Full + Mathlib chain rules),
    and (iv) THREE engineering sub-gaps:
    * (A) `Matrix.PosDef.isOpen` — not packaged. ~30-80 LOC.
    * (B) Integrability of `multivariateGaussianPdf S` on
      `orthant x`. ~50-100 LOC.
    * (C) **Load-bearing.** `LipschitzOnWith` with integrable
      Lipschitz envelope. ~150-300 LOC alone.
    Single TAG'd `sorry` preserved at the same site.
  * **MGE Full close stretch (T3.1) NOT attempted** per the brief's
    hard-stop rule (mid-distribution outcome elected over optimistic
    stretch).
* **Net debt change R44 → R45:** axioms 5 → 5 (unchanged); sorries
  12 → 12 (unchanged — diagnostic-quality progress without count
  inflation).
* **All build targets remain green** (`lake env lean` clean on
  `MultivariateGaussianCDF.lean`, `MultivariateGaussianPdf.lean`,
  `MatrixDetDifferentiable.lean`, `PhaseAUpperBound.lean`); R38 +
  R39 + R40 + R41 + R42 + R43 + R44 milestones preserved.
* **R59 ceiling check:** boundary case maintained via Q5 BTIS-merge
  compression option. R45 mid-distribution outcome → 15 remaining
  rounds for pure axiom-free target (R46-R59 with zero buffer at
  R59 boundary). Recommendation for R46: Option C — MGE Full close
  (~180-290 LOC) + Phase 2 sub-gap (A) `Matrix.PosDef.isOpen`
  stretch (~30-80 LOC).

See `Helpers/PhaseV2R45Status.md` and
`Helpers/R45_T1_FramingVerificationAudit.md` for the round status
doc + framing audit.

## Track B status (parallel to R44 Track A — Mathlib re-verification round)

* **Branch:** `track-b-r33cd-gaps` (created from `r33-c-helpers-consolidation`
  at `6783d38`, after Track A's R44-T1.1 + R44-T2.2 commits had landed
  on the parent branch — a non-conflicting interleaving since the two
  tracks modify file-disjoint sets). First parallel-pattern test
  post-R43.
* **Track B contribution:** axioms 5 → 5 (unchanged), sorries
  unchanged (Track A R44-T2.2 already retired the MGI Stub, 13 → 12).
  Three TAG'd sub-Stubs refreshed at the R33-C/D Mathlib-version-skew
  gaps (`Helpers/TwoDimKMTFromOneDim.lean:660`, `:943`, `524.lean:3920`)
  with re-verification stamps confirming the gaps stand at current
  Mathlib HEAD.
* **Calibration data:** brief over-estimated single-round closure
  feasibility for Mathlib-gap sorries (P(Full) actually ~0.05–0.20 per
  sorry, not 0.55–0.65). Apply 0.5× discount for Track C/D briefs.
* See `Helpers/TrackBStatus.md` and
  `Helpers/TrackB_T1_R33cdGapsAudit.md`.

## Build status (R43 V2 round 5 — MGE/MGI signatures + Phase 1A/1B chain rule)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R43 update):** lands per Grok R43 pre-flight
  Q4 verdict (b): signatures + Phase 1A + Phase 1B in a single round.
  * **MGE / MGI signature upgrade.** `multivariateGaussian_eq_lebesgue_withDensity`
    (MGE) + `multivariateGaussianOrthantCDF_eq_lebesgue_integral` (MGI)
    upgraded from R40 `True := by trivial` placeholders to real Lean
    signatures with TAG'd Stub bodies (TAG[R43-T2.1-MGE-pushforward-jacobian-body]
    + TAG[R43-T2.1-MGI-orthant-via-MGE-body]) in
    `Helpers/MultivariateGaussianPdf.lean`.
  * **Phase 1A** (`Sα_path_hasDerivAt`) — Full Lean proof of
    `HasDerivAt (fun α => (1-α) • S_X + α • S_Y) (S_Y - S_X) α` in
    `Helpers/PhaseAUpperBound.lean:245`.
  * **Phase 1B** (`multivariateGaussianOrthantCDF_differentiableAt_along_Sα_path`)
    — Full Lean chain-rule composition giving `DifferentiableAt ℝ` for
    the composite `α ↦ orthantCDF (Σ_path α) x` at `α ∈ (0, 1)` in
    `Helpers/PhaseAUpperBound.lean:297`. No deferred R44 sub-Stub.
  * R43 elects the audit's R44 trajectory: Phase 2 (MGE/MGI body close +
    CDF diff Full body) lands in R44, then Slepian Full body in R45.
* **Net debt change R42 → R43:** axioms 5 → 5 (unchanged); sorries 11 → 13
  (+2 from MGE/MGI signature upgrades — quality upgrade replacing
  uninformative `True` placeholders with TAG'd Stubs carrying real
  mathematical content).
* **All build targets remain green** (`lake env lean` clean on
  `MultivariateGaussianPdf.lean`, `PhaseAUpperBound.lean`,
  `MultivariateGaussianCDF.lean`, `524.lean`).
* **R59 ceiling check:** preserved with 1 round buffer via Grok Q5
  BTIS-merge compression option. R43 mid-distribution outcome → 17
  remaining rounds for pure axiom-free target.

See `Helpers/PhaseV2R43Status.md` and `Helpers/R43_T1_SignatureUpgradeAudit.md`
for the round status doc + audit.

## Build status (R42 V2 round 4 — Slepian diagnostic strengthening, audit-aligned lower outcome)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R42 update):** ships the audit-aligned lower
  outcome. Strengthens the `slepian_comparison_finite` TAG'd Stub
  diagnostic in `Helpers/PhaseAUpperBound.lean:299-372` with explicit
  Mathlib API + failed-tactic citations (5 named missing symbols + 3
  failed tactics), satisfying the R42 brief's 50%-cap clause for
  "concrete sign-analysis diagnostic." Status doc
  `Helpers/PhaseV2R42Status.md` reconciles the round brief's optimistic
  single-turn-Slepian-close target (200-300 LOC per the brief) with the
  load-bearing R41 cold audit's grounded estimate (~1080 LOC across
  R43-R45). R42 elects the audit's R43+ trajectory: MGE/MGI signatures
  → CDF diff body → Slepian body, with R59 ceiling preservation
  (8 rounds slack).
* **Net debt change R41 → R42:** axioms 5 → 5, sorries 11 → 11
  (zero formal-debt change; quality upgrade via diagnostic precision).
* **All build targets remain green** (`lake env lean` clean on
  PhaseAUpperBound + MultivariateGaussianCDF; only expected sorry
  warnings); R38 + R39 + R40 + R41 milestones preserved. See
  `Helpers/PhaseV2R42Status.md` for the round status doc.

## Build status (R41 V2 round 3 — chain composition advance)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R41 update):** chain composition advance for
  Phase A upper Option B. Three deliverables:
  (1) `Matrix.PosDef.inv_hasFDerivAt` Stub→Full close in
  `Helpers/MatrixDetDifferentiable.lean:200-238` (commit `1e30dda`),
  composing `hasFDerivAt_ringInverse` with the global function-equality
  bridge `Matrix.nonsing_inv_eq_ringInverse`. (2)
  `multivariateGaussianOrthantCDF_partial_offdiagonal` (MGP)
  `True := by trivial` → real `∃ d, 0 ≤ d ∧ HasDerivAt …` signature in
  `Helpers/MultivariateGaussianCDF.lean:201`. (3)
  `posDef_convex_combination` helper added (fully proved, no `sorry`)
  in `Helpers/PhaseAUpperBound.lean:182-200`, used in the
  `slepian_comparison_finite` body restructure. New audit
  `Helpers/R41_T1_ChainCompositionAudit.md` documents the refinement
  of Grok R41 pre-flight Q2: chain composition presupposes real
  signatures, not `True` placeholders.
* **All build targets remain green** (Helpers + 524 consumer); R38
  consumer-build-green + R39 + R40 V2 milestones preserved. See
  `Helpers/R41_T1_ChainCompositionAudit.md` for the cold audit and
  `Helpers/PhaseV2R41Status.md` for the round status.

## Build status (R40 V2 round 2 — differentiability infrastructure)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R40 update):** lands the differentiability
  scaffolding required by Phase A upper Option B (Slepian + SF + BTIS
  via covariance interpolation). Three new files:
  `Helpers/MatrixDetDifferentiable.lean` (T2.1 + T2.2 scaffolds),
  `Helpers/MultivariateGaussianPdf.lean` (T2.3 PDF def + bridge sig),
  `Helpers/R40_T1_DifferentiabilityAudit.md` (T1.1 Mathlib re-audit).
  T2.4 closes `sup_continuous_eq_sup_dense` body in
  `Helpers/PhaseAUpperBound.lean` with a real ε–δ density-of-rationals
  proof, retiring the `R35-T2.3-density-mechanical` sorry.
* **All build targets remain green** (Helpers + 524 consumer); R38
  consumer-build-green + R39 V2 milestones preserved. See
  `Helpers/R40_T1_DifferentiabilityAudit.md` for the cold re-audit and
  `Helpers/PhaseV2R40Status.md` for the round status.

## Build status (R39 V2 round 1 — α-tighten / α-redirect)

* **Build infrastructure:** consumer-build-green (preserved from R38
  milestone, 2026-05-02).
* **Mathematical content (R39 update):** R37 cold re-audit revealed the
  3 IsGLWProcess axioms (A6/A7/A8) were unsound as stated (signature
  `Y measurable → IsGLWProcess Y` falsifiable on `Y ≡ 0`). R39
  converted them to `theorem ... := by sorry` with α-tightened
  signatures (now sound modulo {axioms #1, #2, scaling-limit theorem}).
* **All build targets remain green** (Helpers + 524 consumer); R38
  consumer-build-green milestone preserved. See
  `Helpers/R39_T1_AlphaConversionAudit.md` for the cold re-audit and
  `Helpers/PhaseV2R39Status.md` for the round status.

## 9 user-defined axioms (technical debt — must retire)

| # | Axiom | Source round | Provisional retire-path |
|---|---|---|---|
| 1 | `Cp_T_explicit_pointwise_axiom` (D2) | pre-Phase-A | V2 R54-R55 (Komlós explicit constant via decomposition + #2) |
| 2 | `one_dim_KMT_coupling` | pre-Phase-A | V2 R49-R53 (in-scope 1D KMT formalization) |
| 3 | `kmt_aided_gaussian_process` | pre-Phase-A | V2 R49-R53 (derive from #1+#2 + scaling-limit theorem; also closes V2-R39 sorries 7-9) |
| 4 | `gao_li_wellner_small_ball_lower` | R34 | V2 R40-R48 (Slepian + SF + BTIS composition) |
| 5 | `gao_li_wellner_small_ball_upper` | R36 | V2 R40-R48 (parallel to #4) |
| 6 | `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` | R49 (Path A switch) | V2 R57-R59 post-gate (Mathlib pin bump preferred; from-scratch ~150-300 LOC fallback) |
| 7 | `multivariateGaussian_eq_lebesgue_withDensity` | R51 (γ-floor switch) | V2 R57-R59 post-gate (Mathlib pin bump preferred; from-scratch ~150-300 LOC fallback — sub-gap (a) closed R46, (b) + (c) + composition pending) |
| 8 | `Matrix.det.differentiable` | R53 (γ-floor switch) | V2 R57-R59 post-gate (Mathlib pin bump preferred; from-scratch ~100-200 LOC Leibniz-expansion fallback via companion #9 close, retires as a pair) |
| 9 | `Matrix.det.hasFDerivAt` (existential form, companion of #8) | R56 (γ-floor extension) | V2 R57-R59 post-gate (Mathlib pin bump preferred; from-scratch ~100-200 LOC Leibniz-expansion fallback, retires as a pair with #8 in single round) |

All nine are classically correct (see the audit doc + Axiom #6 / #7 /
#8 / #9 detail below for classical-justification chains).

### Axiom #6 detail: `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`

* **Added:** R49 (V2 round 11, 2026-05-02), Path A switch.
* **File:** `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:190`.
* **Lean signature:**
  ```lean
  axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance
      {ι : Type*} [Fintype ι] [DecidableEq ι]
      (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) :
      DifferentiableAt ℝ
        (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀
  ```
  (Section variables `{ι}`, `[Fintype ι]`, `[DecidableEq ι]` are
  auto-bound from the surrounding `namespace
  Erdos524.Helpers.MultivariateGaussianCDF` `variable` block.)
* **Mathematical content (plain English):** for a positive-definite
  covariance matrix `Σ` on `ι`-indexed coordinates and threshold vector
  `x`, the half-space probability
  `F(Σ; x) = ℙ_{Z ∼ 𝒩(0, Σ)} (∀ i, Z i ≤ x i)` is differentiable in `Σ`
  in the entry-wise Fréchet sense at `Σ = S₀.PosDef`. Classical proof:
  Lebesgue density formula `ρ(z; Σ) = (2π)^{-n/2} (det Σ)^{-1/2}
  exp(-z^T Σ^{-1} z / 2)` + differentiation under the integral sign +
  uniform Gaussian-tail Lipschitz envelope on a `PosDef` neighbourhood
  of `S₀`. Reference: Slepian (1962) "The one-sided barrier problem for
  Gaussian noise", Bell System Tech. J. 41:463-501; Tong (1990) "The
  Multivariate Normal Distribution" §5.1.
* **Why axiomatized at R49 (Path A switch):** the R48-T1.1 audit
  (`R48_T1_PathGammaPrimeAudit.md` §2-§3, re-verified at HEAD `434a407`
  in `Round49_T1_PathAAxiomatization.md` §1) caught two independent
  misframings in the Path γ' brief recipe:
  * **(M1)** Lean MGI
    (`multivariateGaussianOrthantCDF_eq_lebesgue_integral` at
    `MultivariateGaussianPdf.lean:412`) is a measure-vs-Lebesgue-integral
    REWRITE identity — its R44 Full body (lines 412-477) is three
    sequential `rw`s with no `HasFDerivAt` / `DifferentiableAt` content.
    Pdf S-differentiability is a separate ~80-150 LOC chain blocked on
    R40 `Matrix.det.differentiable` Stub at
    `MatrixDetDifferentiable.lean:149`.
  * **(M2)** `multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef`
    at `GaussianParametricAnalysis.lean:168` lives INSIDE a `/-! ... -/`
    docstring code block, NOT a Lean theorem. Path γ' DCT chain consumer
    "Gaussian tail majorant" does not exist as a Lean object.

  Path B (continue from-scratch closure) costed at ~400+ LOC across 3-5
  rounds with P(Full)/round ~0.30 — incompatible with the R52 milestone
  gate (items ≤ 8) under the cumulative ~0.5 sorry/round retirement
  rate. Path A axiomatization trades -1 sorry for +1 axiom (item count
  unchanged at gate) and frees 3-5 rounds of mainline budget for GLW
  shortcut (R50-R51) + Track C round 3 + Track D round 4 retirements.
* **Retirement target: R55-R59 (post-gate), two-path sub-plan:**
  1. *Mathlib pin bump (preferred):* monitor Mathlib for landings of
     pdf-differentiability infrastructure for `multivariateGaussianPdf`
     / `multivariateGaussian` density, uniform Gaussian-tail bound on
     `IsCompact ∘ PosDef` neighbourhoods, and `Matrix.det.differentiable`
     (R40 Stub-equivalent). Post-`v4.27` toolchain bump, the axiom
     retires via direct chain composition (~50-100 LOC consumer
     wrapper).
  2. *From-scratch closure (fallback):* build the missing pieces in-tree
     — ~150-300 LOC over 2-3 rounds, anchored on R40 Stub close
     (~30-80 LOC) + tail-bound Full helper (~60-100 LOC) + Phase 2 body
     Full close (~150-300 LOC). This is Path B from the R49 framing,
     executed once R52-gate budget is freed.

  Retirement is **not required for the R52 gate** (gate measures item
  count; +1 axiom / -1 sorry is a wash there). Strategic value of Path
  A is the freed mainline budget for OTHER retirements.
* **Status:** ACTIVE (placeholder, math content provable from the
  classical Lebesgue-density route described above).
* **Consumers (Lean code):**
  * `PhaseAUpperBound.lean:404` —
    `multivariateGaussianOrthantCDF_differentiableAt_along_Sα_path`
    (Phase 1B chain rule composition). Applies the axiom positionally
    with three arguments; signature preserved verbatim so the call site
    is unchanged.

### Axiom #7 detail: `multivariateGaussian_eq_lebesgue_withDensity`

* **Added:** R51 (V2 round 13, 2026-05-02), γ-floor switch (post-R50
  audit-redirect; user-confirmed "γ floor + β R58 extension" trajectory
  per BACKGROUND.md).
* **File:** `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean:248`.
* **Lean signature:**
  ```lean
  axiom multivariateGaussian_eq_lebesgue_withDensity
      {ι : Type*} [Fintype ι] [DecidableEq ι]
      (S : Matrix ι ι ℝ) (_hS : S.PosDef) :
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
        (volume : Measure (EuclideanSpace ℝ ι)).withDensity
          (fun y : EuclideanSpace ℝ ι =>
            ENNReal.ofReal (multivariateGaussianPdf S (fun i => y i)))
  ```
  (Section variables `{ι}`, `[Fintype ι]`, `[DecidableEq ι]` are
  auto-bound from the surrounding `namespace
  Erdos524.Helpers.MultivariateGaussianPdf` `variable` block at line 84.)
* **Mathematical content (plain English):** for a positive-definite
  covariance matrix `S` on `ι`-indexed coordinates, the centered
  multivariate Gaussian measure on `EuclideanSpace ℝ ι` (defined via
  `brownian-motion`'s `multivariateGaussian 0 S` as the pushforward of
  `stdGaussian` by `x ↦ toEuclideanCLM (CFC.sqrt S) x`) is absolutely
  continuous with respect to Lebesgue measure, with Radon–Nikodym
  derivative `multivariateGaussianPdf S` (the explicit
  `(2π)^{-n/2} (det S)^{-1/2} exp(-x^T S^{-1} x / 2)` formula). The PDF
  is evaluated at `fun i => y i`, applying the canonical
  `EuclideanSpace ℝ ι ↔ (ι → ℝ)` coordinate identification at the
  consumer site. Reference: Tong (1990) "The Multivariate Normal
  Distribution" §5.1; Anderson (2003) "An Introduction to Multivariate
  Statistical Analysis" §2.3; Bogachev (2007) "Gaussian Measures"
  Chapter 1.
* **Why axiomatized at R51 (γ-floor switch):** The R44-R47 closure
  diagnostic decomposed the Stub body into three measure-theoretic
  sub-gaps:
  * (a) `det_CFC_sqrt_eq_sqrt_det` for PosDef `S` — **closed R46** as a
    Full sub-lemma in this file (composes `CFC.sqrt_mul_sqrt_self` +
    `Matrix.det_mul` + `Real.sqrt_eq_iff_mul_self_eq`).
  * (b) `stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace ℝ ι` —
    R47 audit decomposed into THREE further Mathlib bridges (n-ary
    `Measure.pi.withDensity` factorization ~80-120 LOC,
    `Measure.map.withDensity` through `MeasurableEquiv` ~30-50 LOC,
    Lebesgue-on-`EuclideanSpace` identification ~20-100 LOC), totalling
    ~150-280 LOC — none packaged at pin `mathlib4 @ 25ce63313608`.
  * (c) Constant-Jacobian linear pushforward — R46 grep audit found
    `map_linearMap_addHaar_eq_smul_addHaar` (Mathlib
    `MeasureTheory/Measure/Lebesgue/EqHaar.lean:234`) as a direct
    application; no separate sub-lemma needed.

  The R52 milestone gate (items ≤ 8) is decisively failing under hybrid
  (c) per the R50 build-status block. The user-confirmed γ-floor + β
  R58 extension trajectory accepts axiomatization of (a)+(b)+(c)
  composition into a single γ-floor axiom to free 3-5 mainline rounds
  for retirement work elsewhere — Q1a/b/c track consolidation,
  Track C/D parallel work, or Matrix.det.differentiable γ-axiomatization
  candidate at R52. Like Axiom #6 (Path A at R49), this trades -1
  sorry for +1 axiom (item count unchanged at gate).
* **Retirement target: R55-R59 (post-gate), two-path sub-plan:**
  1. *Mathlib pin bump (preferred):* monitor Mathlib for landings of
     n-ary `Measure.pi.withDensity` factorization, `Measure.map.withDensity`
     through `MeasurableEquiv`, and `stdGaussian_eq_lebesgue_withDensity`
     on `EuclideanSpace`. Post-`v4.27` toolchain bump may also package
     some of these via the `BrownianMotion.Gaussian` chain. Direct chain
     composition retires this axiom in ~30-80 LOC of consumer wrapper.
  2. *From-scratch closure (fallback):* build the missing pieces
     in-tree over R55-R59 — ~150-300 LOC across 2-3 rounds. Sub-gap (a)
     already closed at R46; (b.A) Pi-withDensity bridge ~80-120 LOC,
     (b.B) MeasurableEquiv pushforward ~30-50 LOC, (b.C) Lebesgue-
     EuclideanSpace identification ~20-100 LOC, composition ~30-50 LOC.

  Retirement is **not required for the R52 gate** (gate measures item
  count; +1 axiom / -1 sorry is a wash there). Strategic value of the
  γ-floor axiomatization is the freed mainline budget for OTHER
  retirements.
* **Status:** ACTIVE (placeholder, math content provable from the
  classical Tong–Anderson Lebesgue-density route; sub-gap (a) already
  closed at R46).
* **Consumers (Lean code):**
  * `Helpers/MultivariateGaussianPdf.lean:466` (post-R51 line number)
    — inside the proof body of
    `multivariateGaussianOrthantCDF_eq_lebesgue_integral`,
    `rw [multivariateGaussian_eq_lebesgue_withDensity S _hS]` converts
    measure-of-orthant to integral-of-pdf-over-orthant. Sole non-comment
    Lean caller; positional arity 2 preserved by the axiom swap.

### Axiom #8 detail: `Matrix.det.differentiable`

* **Added:** R53 (V2 round 15, 2026-05-02), γ-floor switch (post-R52
  audit-redirect; user-confirmed "γ floor + β R58 extension" trajectory
  per BACKGROUND.md, continuing the R49 axiom #6 + R51 axiom #7
  mechanical pattern).
* **File:** `FormalConjectures/ErdosProblems/Helpers/MatrixDetDifferentiable.lean:141`.
* **Lean signature:**
  ```lean
  axiom Matrix.det.differentiable
      {n : Type*} [Fintype n] [DecidableEq n] :
      Differentiable ℝ (fun A : Matrix n n ℝ => A.det)
  ```
  (Typeclass binders bound directly on the axiom; no surrounding
  `variable` block in this section. The axiom lives inside `namespace
  Erdos524.Helpers` with `open Matrix`.)
* **Mathematical content (plain English):** for every finite-index `n`
  with decidable equality and every real `n × n` matrix, the
  determinant function `A ↦ A.det : Matrix n n ℝ → ℝ` is
  Fréchet-differentiable on the entire matrix space. Equivalently, the
  determinant is smooth (in particular C¹) as a function of the entries.
  Reference: Lang (2002) "Algebra" Ch. XIII §5; Hörmander (1990)
  "Analysis of Linear Partial Differential Operators" Ch. I §1. The
  classical proof: determinant is a polynomial in the matrix entries
  via the Leibniz expansion `det A = ∑_{σ ∈ Perm n} sign σ · ∏_i A i (σ
  i)`; polynomials in finitely many real variables are smooth on a
  finite-dimensional real normed space.
* **Why axiomatized at R53 (γ-floor switch):** R40-T2.1 introduced the
  `Matrix.det.differentiable` Stub (line 141-149) along with the
  companion existential form `Matrix.det.hasFDerivAt` (line 124-132),
  both TAG'd `R40-T2.1-det-cofactor-route`. Both were intended as Phase
  A upper Option B infrastructure. The closure path α (cofactor /
  Leibniz expansion + polynomial differentiability + sum/product
  combinator chain) is mathematically clear but requires ~100-200 LOC
  of careful Lean involving:
  * `Matrix.det_apply'` (packaged) for the Leibniz expansion,
  * Per-summand polynomial differentiability via `Matrix.entryLinearMap`
    (packaged) + `Differentiable.prod_finset` + `Differentiable.sum_finset`,
  * Bookkeeping over `Equiv.Perm` for the sign + permutation indexing,
  * Final assembly into the `HasFDerivAt` form, then wrapper
    composition via `HasFDerivAt.differentiableAt.differentiable`.

  R41-R52 attempted no Phase A upper Option B Slepian / SF / BTIS body
  close that consumed this Stub directly, so it has remained
  unconsumed at every gate measurement. The R52 milestone gate is
  decisively failing under hybrid (c); the user-confirmed γ-floor + β
  R58 extension trajectory accepts axiomatization of the wrapper form
  (which downstream consumers will use) to free 1-2 mainline rounds for
  retirement work elsewhere. The companion `Matrix.det.hasFDerivAt`
  Stub remains for now (R54+ candidate for additional γ-floor
  axiomatization if needed).
* **Retirement target: R55-R59 (post-gate), two-path sub-plan:**
  1. *Mathlib pin bump (preferred):* monitor Mathlib for landings of
     `Matrix.det.hasFDerivAt` (likely via `MultilinearMap` or
     `LinearMap` route, or via `Polynomial.contDiff` on the Leibniz
     expansion). Post-`v4.27` toolchain bump may package this directly.
     Wrapper retires as a 2-line consumer:
     `Matrix.det.differentiable := fun M => (Matrix.det.hasFDerivAt
     M).differentiableAt.differentiable`.
  2. *From-scratch closure (fallback):* close the companion
     `Matrix.det.hasFDerivAt` Stub via the cofactor route (~100-200
     LOC) + 2-line wrapper composition. Total ~100-200 LOC over 1-2
     rounds.

  Retirement is **not required for the R52 gate** (gate measures item
  count; +1 axiom / -1 sorry is a wash there). Strategic value of the
  γ-floor axiomatization is the freed mainline budget for OTHER
  retirements R54-R58.
* **Status:** ACTIVE (placeholder, math content provable from the
  classical Leibniz-polynomial route described above).
* **Consumers (Lean code):** **zero Lean call sites at HEAD R53 close**.
  All 6 grep hits for `Matrix.det.differentiable` /
  `Matrix.det.hasFDerivAt` at R53 are docstrings/comments
  (`524.lean:3514`, `Helpers/MultivariateGaussianPdf.lean:242`,
  `Helpers/GLWSmallBallShortcut.lean:220`,
  `Helpers/MultivariateGaussianCDF.lean:46/63/177`). Future consumers
  will appear in the R55+ Slepian / multivariate-CDF differentiability
  assembly phase under the original axiom name.

### Axiom #9 detail: `Matrix.det.hasFDerivAt`

* **Added:** R56 (V2 round 18, 2026-05-02), γ-floor extension switch
  (post-R55 user-confirmed "γ floor + β R58 extension" trajectory per
  BACKGROUND.md, continuing the R49 axiom #6 + R51 axiom #7 + R53 axiom
  #8 mechanical pattern; **4× successful precedent now**).
* **File:** `FormalConjectures/ErdosProblems/Helpers/MatrixDetDifferentiable.lean:179`.
* **Lean signature:**
  ```lean
  axiom Matrix.det.hasFDerivAt
      {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
      ∃ L : Matrix n n ℝ →L[ℝ] ℝ,
        HasFDerivAt (fun A : Matrix n n ℝ => A.det) L M
  ```
  (Typeclass binders bound directly on the axiom, plus the explicit
  point `(M : Matrix n n ℝ)`. No surrounding `variable` block in this
  section. The axiom lives inside `namespace Erdos524.Helpers` with
  `open Matrix`. Strict signature-shape difference vs the wrapper
  axiom #8: this companion form binds an explicit point `M` and asserts
  pointwise existence of the Fréchet derivative `L : Matrix n n ℝ →L[ℝ] ℝ`,
  the strictly stronger statement.)
* **Mathematical content (plain English):** for every finite-index `n`
  with decidable equality, every real `n × n` matrix `M`, the
  determinant function `A ↦ A.det : Matrix n n ℝ → ℝ` is
  Fréchet-differentiable at `M`, with derivative the explicit cofactor /
  adjugate map `H ↦ tr(adj(M) · H) : Matrix n n ℝ →L[ℝ] ℝ`. The
  existential form provides the witness `L`; the wrapper Axiom #8
  recovers via `HasFDerivAt.differentiableAt`.
  Reference: Lang (2002) "Algebra" Ch. XIII §5; Hörmander (1990)
  "Analysis of Linear Partial Differential Operators" Ch. I §1; Magnus
  & Neudecker (1999) "Matrix Differential Calculus" §8.3 for the
  explicit `d(det A) = tr(adj(A) · dA)` derivation. The classical
  proof: determinant is a polynomial in the matrix entries via the
  Leibniz expansion `det A = ∑_{σ ∈ Perm n} sign σ · ∏_i A i (σ i)`;
  polynomials in finitely many real variables are smooth on a
  finite-dimensional real normed space, with the cofactor formula for
  the derivative.
* **Why axiomatized at R56 (γ-floor extension switch):** R40-T2.1
  introduced the companion `Matrix.det.hasFDerivAt` Stub (line 126-134
  pre-R56) along with the `Matrix.det.differentiable` wrapper Stub,
  both TAG'd `R40-T2.1-det-cofactor-route`. R53 axiomatized only the
  wrapper (axiom #8) per R52 user-confirmed audit-redirect; the
  companion existential form was **deliberately preserved** as a Stub
  ("optional R54+ candidate for additional γ-floor axiomatization if
  needed" per `Round53_T1_MatrixDetDifferentiableAxiomatization.md` §1
  row 8). R55 marked the companion axiomatization as priority #1 R56
  candidate per AXIOM_INVENTORY R55 trajectory block.

  R56 closes the companion Stub via the same mechanical pattern as R49
  + R51 + R53 (4× successful precedent now). The closure path α
  (cofactor / Leibniz expansion + polynomial differentiability +
  sum/product combinator chain) requires ~100-200 LOC of careful Lean
  for the body close — same pre-existing diagnostic as R53 axiom #8.
  R41-R55 attempted no Phase A upper Option B Slepian / SF / BTIS body
  close that consumed this companion Stub directly, so it has remained
  unconsumed at every gate measurement. The R52 milestone gate is
  decisively failing under hybrid (c); the user-confirmed γ-floor + β
  R58 extension trajectory accepts axiomatization of the companion
  existential form to free 1-2 mainline rounds for retirement work
  elsewhere (Q1c track full close attempt, additional Mathlib API
  drift fixes, Track C/D parallel work merge).
* **Retirement target: R57-R59 (post-gate), two-path sub-plan:**
  1. *Mathlib pin bump (preferred):* monitor Mathlib for landings of
     `Matrix.det.hasFDerivAt` (likely via `MultilinearMap` or
     `LinearMap` route, or via `Polynomial.contDiff` on the Leibniz
     expansion). Post-`v4.28` toolchain bump may package this directly.
     **Pair retirement bonus**: axioms #8 + #9 retire simultaneously
     when Mathlib packages the existential form, since axiom #8 is a
     2-line consumer:
     ```
     theorem Matrix.det.differentiable :
         Differentiable ℝ (fun A : Matrix n n ℝ => A.det) :=
       fun M => (Matrix.det.hasFDerivAt M).choose_spec.differentiableAt
     ```
     **Net retirement on pin bump: -2 axioms in one move.**
  2. *From-scratch closure (fallback):* close the companion existential
     form via the cofactor route (~100-200 LOC) + 2-line wrapper
     composition for axiom #8. Total ~100-200 LOC over 1-2 rounds for
     both axioms #8 + #9 as a pair, vs ~200-400 LOC if the wrapper had
     to be closed independently (the existential form is the harder
     piece; once it's closed, the wrapper retires immediately).

  Retirement is **not required for the R52 gate** (gate measures item
  count; +1 axiom / -1 sorry is a wash there). Strategic value of the
  γ-floor axiomatization is the freed mainline budget for OTHER
  retirements R57-R59.
* **Status:** ACTIVE (placeholder, math content provable from the
  classical Leibniz-polynomial route described above; companion of
  axiom #8 — the two retire as a pair).
* **Consumers (Lean code):** **zero Lean call sites at HEAD R56 close**
  (same status as axiom #8 at R53 close). All grep hits for
  `Matrix.det.hasFDerivAt` at R56 are docstrings/comments
  (`MatrixDetDifferentiable.lean` self-references at lines 30, 41, 52,
  63, 79+ docstring, 145, 169, 173, plus `.md` audit docs). Future
  consumers will appear in the R57+ Slepian / multivariate-CDF
  differentiability assembly phase under the original axiom name —
  may import either #8 (wrapper) or #9 (existential) depending on
  chain-rule needs.

**R39 retired axioms 6-8** (the 3 IsGLWProcess β-axioms) by α-tighten:
sound tightened signatures requiring KMT-coupling-rate hypothesis;
content deferred to V2 R49-R53 cluster (bundled with axiom #3
retirement). See `Helpers/AxiomFoundationAudit.md` "R39 — V2 round 1"
section.

## 10 TAG'd `sorry` sites (post-R56 — -1 from post-R53 via companion `Matrix.det.hasFDerivAt` γ-floor axiomatization)

(Post-R56 baseline: same 11 sites listed below from post-R42, plus the 2
R50 deferred-paper sub-Stubs added in `GLWSmallBallShortcut.lean`, minus
the MGE Stub at `MultivariateGaussianPdf.lean:248` retired in R51-T2.1
via γ-floor axiomatization (now Axiom #7), minus the
`Matrix.det.differentiable` wrapper Stub at
`MatrixDetDifferentiable.lean:141` retired in R53-T2.1 via γ-floor
axiomatization (now Axiom #8), minus the companion
`Matrix.det.hasFDerivAt` existential-form Stub at
`MatrixDetDifferentiable.lean:126-134` retired in R56-T2.1 via γ-floor
axiomatization (now Axiom #9). Net post-R56 sorries: 11 + 2 - 1 - 1 - 1
= 10.)

* **R56-T2.1 companion `Matrix.det.hasFDerivAt` retirement (γ-floor
  axiomatization, this round):** the existential-form Stub at
  `MatrixDetDifferentiable.lean:126-134` (TAG
  `R40-T2.1-det-cofactor-route`, deliberately preserved at R53) has
  been replaced with **Axiom #9** of identical signature. See
  "Axiom #9 detail" section above. Net debt: -1 sorry, +1 axiom, items
  unchanged at 19. Pair-retirement bonus with Axiom #8: both retire
  simultaneously on Mathlib pin bump or single from-scratch round.

* **R53-T2.1 `Matrix.det.differentiable` retirement (γ-floor
  axiomatization, R53):** the wrapper Stub at
  `MatrixDetDifferentiable.lean:141` (TAG `R40-T2.1-det-cofactor-route`)
  has been replaced with **Axiom #8** of identical signature. See
  "Axiom #8 detail" section above. Net debt: -1 sorry, +1 axiom, items
  unchanged at 19.

* **R51-T2.1 MGE retirement (γ-floor axiomatization, this round):**
  the MGE Stub at `MultivariateGaussianPdf.lean:248`
  (`multivariateGaussian_eq_lebesgue_withDensity`, TAG
  `R43-T2.1-MGE-pushforward-jacobian-body`, signature upgraded R43-T2.1)
  has been replaced with **Axiom #7** of identical signature. See
  "Axiom #7 detail" section above. Net debt: -1 sorry, +1 axiom, items
  unchanged at 19.

* **R50 deferred-paper sub-Stubs** (added in R50-T2.1+T2.2; un-imported
  file, no consumer build impact):
  * `FormalConjectures/ErdosProblems/Helpers/GLWSmallBallShortcut.lean:226`
    (`glw_lemma_4_1_deferred_paper`, Jacobi-style first-order
    determinant expansion along scalar path)
  * `FormalConjectures/ErdosProblems/Helpers/GLWSmallBallShortcut.lean:256`
    (`glw_lemma_4_2_deferred_paper`, existence of structured matrix
    with `per(A) = 1` and `det(A) = 32·m·(240·e⁻³)^m`)

R43 also adds two **fully proved** lemmas (no `sorry`):
  * `Helpers.Sα_path_hasDerivAt` — Phase 1A linear path differentiability.
  * `Helpers.multivariateGaussianOrthantCDF_differentiableAt_along_Sα_path`
    — Phase 1B chain rule composition.

## 11 TAG'd `sorry` sites (post-R42 — pre-R43 baseline)

* **3 R33-C / R33-D Mathlib version-skew gaps** — orthogonal to ENat,
  documented as upstream-Mathlib-pending.
  * `FormalConjectures/ErdosProblems/Helpers/TwoDimKMTFromOneDim.lean:609`
    (R33-C iIndepFun-prod-mathlib-gap)
  * `FormalConjectures/ErdosProblems/Helpers/TwoDimKMTFromOneDim.lean:885`
    (R33-C gaussian-uncorrelated-indep-mathlib-gap)
  * `FormalConjectures/ErdosProblems/524.lean:3913`
    (R33-D form-β-to-fullsum bridge)
* **2 R35 Phase A scaffolds** (orphan-preserved Option (a)) —
  R40-T2.4 retired the `sup_continuous_eq_sup_dense` mechanical
  scaffold (was at line 290); remaining (R41 strengthened diagnostics):
  * `FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean:320`
    (`slepian_comparison_finite`, TAG `R41-T2.2-FTC-via-Stein-and-real-MGP`)
  * `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:290`
    (`multivariateGaussianOrthantCDF_differentiable_wrt_covariance`,
    TAG `R35-T2.1-mathlib-gap-density`)
* **3 V2-R39 IsGLWProcess α-tightened theorems** (axiom→sorry
  conversion with sound signature):
  * `FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean:343`
    (`gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`)
  * `FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean:367`
    (`gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`)
  * `FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:288`
    (`gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`)
* **2 V2-R40 differentiability infrastructure scaffolds** (signature
  + TAG'd Stub with concrete Mathlib API gap diagnostics; R41-T2.2
  closed PosDef.inv_hasFDerivAt Stub→Full):
  * `FormalConjectures/ErdosProblems/Helpers/MatrixDetDifferentiable.lean:132`
    (`Matrix.det.hasFDerivAt`, TAG `R40-T2.1-det-cofactor-route`)
  * `FormalConjectures/ErdosProblems/Helpers/MatrixDetDifferentiable.lean:149`
    (`Matrix.det.differentiable` wrapper, TAG `R40-T2.1-det-cofactor-route`)
  * (`Matrix.PosDef.inv_hasFDerivAt` was the third R40-T2.2 stub;
    closed by R41-T2.2 commit `1e30dda` — now Full body using
    `hasFDerivAt_ringInverse` + `Matrix.nonsing_inv_eq_ringInverse`
    bridge.)
* **1 V2-R41 MGP real-signature upgrade** (added in R41-T2.1):
  * `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:199`
    (`multivariateGaussianOrthantCDF_partial_offdiagonal`,
    TAG `R41-T2.1-bivariate-density-conditional`,
    upgraded from R40 `True := by trivial` to real
    `∃ d, 0 ≤ d ∧ HasDerivAt …` signature with TAG'd Stub body)

**R41 net Δ:** -1 sorry (PosDef.inv_hasFDerivAt closed) +1 sorry (MGP
real-signature upgrade) = 0 net change. Quality upgrade: 1 stub closure
+ 1 real-signature upgrade + `posDef_convex_combination` helper added
(fully proved, no `sorry`).

## ENat duplicate-declaration import collision

Pre-R38 status: blocked the consumer-level build of `524.lean`
(`error: import BrownianMotion.Auxiliary.ENNReal failed,
environment already contains 'ENat.toENNReal_iSup' from
Mathlib.Algebra.Order.Floor.Extended`).

Post-R38 status: **RESOLVED** via a P2 local-patch on the pinned
`brownian-motion` checkout. See
[`FormalConjectures/ErdosProblems/Helpers/R38_T1_ENatDiagnostic.md`](FormalConjectures/ErdosProblems/Helpers/R38_T1_ENatDiagnostic.md)
for the diagnostic, and
[`FormalConjectures/ErdosProblems/Helpers/R38_T2_BrownianMotionENNRealPatch.diff`](FormalConjectures/ErdosProblems/Helpers/R38_T2_BrownianMotionENNRealPatch.diff)
for the patch artifact.

The patch is **not durable across `lake update`**; the durable fix
is the upstream `brownian-motion` commit `4fa8fc0 bump` (which
deletes the duplicate lemma upstream), tied to a Lean v4.27 → v4.28
+ Mathlib bump. Toolchain bump deferred to V2.

## Pinned versions

* Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
* Mathlib: `25ce633136084367f182be00fdff7613ea949d27`
* brownian-motion: `91267abd71bd32e9ef6c10c9359938f24a3e1f38` (with R38 local-patch)
* kolmogorov_extension4: `2c2b44e5525186fbe23b01e6acc76460db616009`
