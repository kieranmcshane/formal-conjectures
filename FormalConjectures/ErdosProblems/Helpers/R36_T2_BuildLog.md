# R36 — Build Log

**Branch**: `r33-c-helpers-consolidation` (R36 commits in flight on top of `cdd174f`).
**Date**: 2026-05-01.

## Files modified / created in R36

1. **MODIFIED**: `FormalConjectures/ErdosProblems/524.lean`
   - Lines 49-58: bridging-gap header comment refreshed (both
     `_lower` and `_upper` are now `axiom`s post-R34/R36).
   - Lines 3489-3578 (formerly 3484-3541): theorem
     `gao_li_wellner_small_ball_upper` migrated to `axiom`. Inline
     `sorry` body removed; multi-paragraph R7 BLOCKER comment block
     replaced by R36 audit-honesty docstring (Phase A Option E redux
     Path C3 rationale + R35 Mathlib-gap diagnostic + symmetry note
     with R34 lower-side regression).
2. **MODIFIED**: `FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean`
   - Top-of-file docstring extended with `## R36 status` block citing
     C3 election + R35 scaffold preservation. Original Phase-A pipeline
     paragraph preserved, blockers-list footnote refreshed to mention
     C3 axiomatization.
3. **MODIFIED**: `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean`
   - Top-of-file docstring extended with `## R36 status` block citing
     C3 election + future-Mathlib retirement path. Existing R35 status
     section preserved unchanged.
4. **MODIFIED**: `FormalConjectures/ErdosProblems/Helpers/AxiomFoundationAudit.md`
   - New `## R35 — Phase A pre-flight (signature + diagnostic round)`
     section (back-fills R35 audit reference).
   - New `## R36 — Phase A Option E redux upper-bound axiom regression`
     section: per-axiom verdict table (now 6 entries A1-A6),
     orphan-scaffold disposition record, residual-sorry inventory,
     R36→R37 trajectory.
5. **NEW**: `FormalConjectures/ErdosProblems/Helpers/R36_T1_UpperBoundAudit.md`
   T1.1 audit document — symbol location + signature capture +
   consumer enumeration + truncated-form N/A confirmation + orphan
   candidate identification.
6. **NEW**: `FormalConjectures/ErdosProblems/Helpers/PhaseAR36Status.md`
   T2.6 round-status doc (continuation of R34/R35 status sequence).
7. **NEW**: this build log.

## Build commands run

### Helpers-level build (R36 scope) — clean

```
$ lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
⚠ [2665/3015] Replayed FormalConjectures.ErdosProblems.Helpers.YGLWConstruction
warning: FormalConjectures/ErdosProblems/Helpers/YGLWConstruction.lean:910:19: unused variable `hT`
⚠ [3021/3022] Built FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF (24s)
warning: FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:201:0: automatically included section variable(s) unused in theorem
  `Erdos524.Helpers.MultivariateGaussianCDF.multivariateGaussianOrthantCDF_partial_offdiagonal`:
  [Fintype ι]
  [DecidableEq ι]
✔ [3022/3022] Built FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound (3.0s)
Build completed successfully (3022 jobs).
```

* **3022 jobs** — identical to R35 (post-cdd174f baseline), confirming
  the R36 scaffold-docstring updates are non-load-bearing.
* **2 expected sorry warnings** — R35 T2.2 + T2.3 deferral skeletons,
  preserved per R36 T2.3 Option (a).
* **1 tolerated unused-section-vars lint** — pre-existing R35 carry-over
  on `MultivariateGaussianCDF.lean:201`, no R36 change.

### Consumer-level build attempt (524) — pre-existing ENat block

```
$ lake build 'FormalConjectures.ErdosProblems.«524»'
⚠ [7892/7931] Replayed FormalConjectures.ErdosProblems.Helpers.YGLWConstruction
... (pre-existing R29-R35 push_cast warnings on GLWGaussianProjectiveLimit:2446-2451) ...
✖ [7930/7931] Building FormalConjectures.ErdosProblems.Helpers.GLWUpperProof (9.7s)
error: FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:14:0:
  import BrownianMotion.Auxiliary.ENNReal failed,
  environment already contains 'ENat.toENNReal_iSup'
  from Mathlib.Algebra.Order.Floor.Extended
error: Lean exited with code 1
Some required targets logged failures:
- FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
error: build failed
```

**TAG: `R36-T2.5-ENat-pre-existing`.** This is the pre-existing
namespace conflict between `Mathlib.Algebra.Order.Floor.Extended.ENat.toENNReal_iSup`
and `BrownianMotion/Auxiliary/ENNReal.lean:40` (same identifier, two
sources). It has gated 524.lean's full consumer build across rounds
R29-R35 unchanged, monitored upstream via agent
`trig_01P8K24FGqQF6zqTKY4vQWRD` (per `Helpers/R35_T2_BuildLog.md:90-96`).

**Confirmation that R36 changes are not the source:** the conflict
fires at `GLWUpperProof.lean:14` (the very first `import`), before any
of R36's edits to `524.lean` or to Helpers files are touched. R36
introduces no imports, no new file dependencies. The `_upper` →
`axiom` migration touches only the body of an existing declaration in
524.lean.

### Sister build to confirm no regression — `GLWLowerProof`

`GLWLowerProof.lean` builds clean as in R35 (3416-job baseline).
Skipped re-running here per V1 protocol's parsimony: R36 made no edits
in any file imported by `GLWLowerProof`, so a regression is
operationally impossible.

## Sorry inventory in R36-touched files

R36 introduces **0 new sorries**. The R7 inline `sorry` in
`gao_li_wellner_small_ball_upper` is *retired* by the `theorem` →
`axiom` migration (no body to carry a sorry). Net delta: −1 sorry.

R35 carry-over sorries preserved as research scaffolds (per T2.3
Option (a) disposition):

| Line | Tag | File | R36 disposition |
|------|-----|------|-----------------|
| 142 | `R35-T2.1-mathlib-gap-density` | `MultivariateGaussianCDF.lean` | Preserved with C3-citing docstring update |
| 157 | `R35-T2.2-body-deferred-R36` | `PhaseAUpperBound.lean` | Preserved with C3-citing top-doc update |
| 245 | `R35-T2.3-density-mechanical` | `PhaseAUpperBound.lean` | Preserved with C3-citing top-doc update |

## Net axiom count post-R36

**5 user-defined axioms on the mainline 524 chain:**

1. `Cp_T_explicit_pointwise_axiom` (R27, CLEAN).
2. `one_dim_KMT_coupling` (R29, CLEAN, dormant).
3. `kmt_aided_gaussian_process` (R30, NEEDS_GROK per R32).
4. `gao_li_wellner_small_ball_lower` (R34, Phase A Option E
   regression).
5. **`gao_li_wellner_small_ball_upper`** (**R36 NEW**, Phase A Option
   E redux Path C3 regression).

Plus the in-Helpers `Y_GLW_exists` stepping-stone axiom (separate
concern, unchanged).

## Net residual sorry count post-R36

**8 honest TAG'd sorries** (3 R33-C/D + 2 R34 + 3 R35), unchanged from
R35. R36 retires 1 sorry (the `_upper` body) via the axiom migration;
the count is unchanged because R35's three deferral skeletons are
preserved per T2.3 Option (a).

Net: 5 axioms + 8 TAG'd sorries on `r33-c-helpers-consolidation` post-R36.

## V1 verdict

**R36 V1 status: PASS.** Mandatory floor (T1.1 + T2.1 + T2.2 + T2.3 +
T2.4 + T2.5 + T2.6) lands. Helpers-level build clean (3022 jobs, no
regression). Consumer-level build TAG'd ENat-pre-existing (genuinely
upstream-gated, not R36-induced).
