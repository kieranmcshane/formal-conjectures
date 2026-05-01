# Phase A — R36 status (single round, branch `r33-c-helpers-consolidation`)

**Phase A upper-side regression round, mechanical mirror of R34.** Per the
post-R35 user-set path decision, R36 executes **Path C3** —
axiomatizing `gao_li_wellner_small_ball_upper` directly to mirror the
R34 lower-side Option E regression. +1 user-defined axiom (5 total
post-R36); Phase A wraps in R37 with §11 limit-law assembly.

## R36 outcomes

### T1.1 — Upper-bound symbol audit (Full)

`Helpers/R36_T1_UpperBoundAudit.md` (~140 lines, 8 sections) covers:

* §1 current declaration state (theorem-with-sorry pre-R36, lines
  3504-3541 of `524.lean`, sister of R34 axiom at 3604).
* §2 verbatim signature capture (existential `(ε₀ : ℝ) (T : ℝ → ℝ)`,
  truncated-form `Set.Icc 0 (T ε)` quantification distinguishing it
  from the lower-side full-half-line shape).
* §3 truncated-companion grep — **0 matches** for
  `_upper_truncated`. T2.2 confirmed N/A on upper side (the truncation
  is intrinsic to the upper bound).
* §4 consumer enumeration — 2 active call-sites (`524.lean:4055,
  4212`), both `Yplus`-branch, both `obtain`-on-existential
  (axiom-vs-theorem invisible at call-sites).
* §5 auxiliary lemmas — `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`
  at `Helpers/GLWUpperProof.lean:281` (sister to R34 lower-side
  carry-over sorries; STILL GATED).
* §6 orphan candidates from R35 — three R35 scaffolds named with
  T2.3 disposition recommendation.
* §7 doc-comment cosmetic-reference list (lines 49, 3470, 7580 of
  524.lean).
* §8 audit verdict: T2.1 mechanical, T2.2 N/A, T2.3 default
  Option (a), T2.5 ENat-blocked-by-design.

### T2.1 — Upper-bound axiom conversion (Full)

`524.lean:3504` migrated from `theorem` to `axiom`. The R7 inline
`sorry` body + multi-paragraph BLOCKER comment block are removed; the
preceding docstring is replaced by the R36 audit-honesty paragraph
documenting:

* Phase A Option E redux Path C3 election.
* R35 pre-flight diagnostic (multivariate-Gaussian-CDF differentiability
  Mathlib gap, three concrete missing pieces named).
* The full Mathlib gap inventory (Karhunen–Loève + Talagrand +
  Slepian + Sudakov-Fernique + Borell-TIS + multivariate-Gaussian
  density formula — six 0%-coverage gaps).
* R35 scaffolds preserved as research artefacts per T2.3 (a).
* Symmetry with R34 lower-side `axiom`.
* Honesty fix carried over from R7 (`Y ≡ 0` falsifies the bare-
  measurability original-axiom form; `IsGLWProcess Y` repairs it).
* Truncated-form intrinsic to the upper bound (no `_truncated`
  companion needed, distinct from the lower side).

Cosmetic doc-comment refresh at `524.lean:49-58` (bridging-gap
header) updated to reflect both `_lower` and `_upper` as user-defined
`axiom`s post-R34/R36.

### T2.2 — Truncated form (N/A on upper side)

Confirmed by grep in T1.1 §3: no `_upper_truncated` companion exists.
The upper bound is intrinsically truncated via the existential
`T : ℝ → ℝ` bound in its output; the lower side needs `_truncated`
because it's stated on the full half-line `u ≥ 0`. T2.2 marked
**N/A** with file evidence per V1 protocol.

### T2.3 — Orphan-scaffold disposition (Full, Option (a) chosen)

**Decision: Option (a) — preserve with updated docstrings.** Cited
explicitly in the round commit message. Three R35 scaffolds preserved:

| Artefact | File | Update |
|----------|------|--------|
| `slepian_comparison_finite` | `Helpers/PhaseAUpperBound.lean` | Top-of-file docstring extended with `## R36 status` block citing C3 + future-Mathlib retirement path |
| `sup_continuous_eq_sup_dense` | `Helpers/PhaseAUpperBound.lean` | (same docstring update) |
| `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` | `Helpers/MultivariateGaussianCDF.lean` | Top-of-file docstring extended with `## R36 status` block citing C3 |

**Rationale for (a) over (b)/(c):** R35's diagnostic work is the
highest-leverage R35 deliverable. Branch-only relegation (option (c))
would force git-log spelunking for future-Mathlib revival; outright
deletion (option (b)) discards the concrete-gap diagnostic that
informed the C3 election in the first place. Cost of (a) is dead code
in mainline (3 TAG'd sorries, all already TAG'd from R35 with
concrete diagnostics — no audit-tool ambiguity).

### T2.4 — `Helpers/AxiomFoundationAudit.md` updated (Full)

Two new top-level sections appended (~115 LOC):

* `## R35 — Phase A pre-flight (signature + diagnostic round)` —
  back-fills R35 audit pointer with 0-axiom-delta status.
* `## R36 — Phase A Option E redux upper-bound axiom regression` —
  per-axiom verdict table (now A1-A6, with A5 R34 + A6 R36 Phase A
  pair marked), orphan-scaffold-disposition record, residual-sorry
  inventory (8 TAG'd, unchanged from R35), R36→R37 trajectory (Phase
  A wraps in R37 with §11 + Scope 3 closure).

### T2.5 — Build verification (Full, ENat-blocked-by-design)

* `lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound`:
  3022 jobs, exit 0, 2 expected R35-T2.2/T2.3 sorry warnings + 1
  tolerated unused-section-vars lint. Identical to R35 baseline.
* `lake build 'FormalConjectures.ErdosProblems.«524»'`: blocks at
  `GLWUpperProof.lean:14` on the pre-existing namespace conflict
  `ENat.toENNReal_iSup` (Mathlib `Algebra.Order.Floor.Extended` ↔
  brownian-motion `BrownianMotion/Auxiliary/ENNReal.lean:40`). TAG
  `R36-T2.5-ENat-pre-existing`. Identical failure mode to R29-R35.
* Verbatim build log in `Helpers/R36_T2_BuildLog.md`.

The consumer-level block is upstream-gated (not R36-induced); the
import that fails is the very first `import` in `GLWUpperProof.lean`,
before any of R36's edits are evaluated. R36 introduces 0 new imports
and 0 new file dependencies.

### T2.6 — Status doc (this file, Full)

This document. R36 round-status, continuation of R34/R35 status
sequence (`PhaseAR34Status.md`, `PhaseAR35Status.md`).

## Net axiom + sorry count post-R36

* **Axioms**: **5 user-defined on mainline** (was 4 post-R34/R35).
  New: `gao_li_wellner_small_ball_upper`. Plus 1 in-Helpers
  (`Y_GLW_exists`). Honest accounting: this is a labelling change, not
  a math regression — the R7 inline sorry was functionally axiomatic
  from R7 onwards.
* **Sorries**: **8 TAG'd** (unchanged from R35 = 3 R33-C/D + 2 R34 +
  3 R35). Net delta: 0 (the `_upper` body sorry retires together with
  the theorem→axiom migration, while R35's three deferral skeletons
  are preserved per T2.3 (a)).

## R37 trajectory (Phase A closure)

R37 = §11 limit-law assembly + Scope 3 closure (1 round projected).

Mechanical content for R37 (preview):

* Locate the §11 limit law statement in `524.lean` (consumer of
  `gao_li_wellner_small_ball_{lower, upper}` via the `obtain` patterns
  at lines 4055/4212/4367/4370 + 4745/4748).
* Verify that with both bounds as `axiom`s, the §11 chain glue
  reduces to a 1-line `obtain` + algebraic combination.
* Capture verbatim build attempt (still expected ENat-blocked at the
  consumer-level pending upstream resolution).
* Update `AxiomFoundationAudit.md` with the §11 / Scope 3 closure
  certification.

If R37 lands the §11 assembly cleanly (irrespective of the
consumer-level ENat block, which is operationally separable from the
mathematical-content closure), Phase A budget closes in 4 rounds total
(R34 + R35 + R36 + R37), matching the original Phase A plan and
absorbing the R35 mid-round path revision without overflow.

## R36 self-grading

Mandatory floor outcomes:

| Outcome | Status | Notes |
|---------|--------|-------|
| T1.1 upper-bound audit | Full | `R36_T1_UpperBoundAudit.md` ~140 LOC, 8 sections |
| T2.1 axiom conversion | Full | `524.lean:3504` migrated, R36 docstring lands, header refresh at 49-58 |
| T2.2 truncated form | N/A (cited) | grep confirms no `_upper_truncated`; intrinsic to upper bound |
| T2.3 orphan disposition | Full | Option (a) chosen, two file docstrings updated, decision in commit |
| T2.4 audit doc | Full | `AxiomFoundationAudit.md` +115 LOC, 6-axiom table + R36 trajectory |
| T2.5 build verification | Full | Helpers clean (3022 jobs); consumer ENat-blocked-by-design with verbatim log |
| T2.6 status doc | Full | this file |
| Round exit ≥ 1.5h | Full | substantive Lean code + 2 audit docs in 1 round |

Joint mandatory floor outcome: 7/7 Full + 1 N/A. No skin-in-the-game
caps triggered.

## Per-prompt Brier check

| Outcome | Predicted P(Full) | Actual | Note |
|---------|-------------------|--------|------|
| T1.1 upper-bound audit | 0.95 | Full | tracking |
| T2.1 axiom conversion | 0.95 | Full | tracking |
| T2.2 truncated derivation | 0.85 (conditional Full) | N/A (cited) | grep showed no upper-truncated companion exists; cited as N/A per V1 protocol |
| T2.3 orphan decision + exec | 0.85 | Full | default Option (a) chosen, decision in commit |
| T2.4 audit doc update | 0.95 | Full | tracking |
| T2.5 build verification | 0.95 | Full | tracking, ENat-pre-existing TAG fires as expected |
| T2.6 status docs | 0.95 | Full | tracking |

R36 is the second round on the Phase A axiom-regression track (after
R34). The R34 precedent meant the upper-side mirror was nearly
mechanical; the only round-specific engineering content was the T2.3
orphan-scaffold disposition (which defaulted to (a) without
controversy).

## Calibration framing post-R36

R29-R36: 10 rounds, mandatory floor land rate 100%. Phase A track:
R34 + R35 + R36 = 3 rounds, on the original Phase A budget of R34-R37
(4 rounds). R37 closes Phase A + Scope 3.

Total user-defined axioms at projected R37 closure: 5 (D2 +
1D KMT + stepping-stone + GLW lower + GLW upper). Plus 3 R33-C/D-tracked
upstream Mathlib gaps (IndepFun reverse + iIndepFun_prod + Ω/Ω×Ω
bridge). Plus R32-flagged IsGLWProcess discharge sorries (separate
concern, both lower and upper sides).

If R37 lands cleanly: **Scope 3 closure at R37** with 5
explicitly-documented user-defined axioms + 3 upstream Mathlib gaps.
Honest audit, no contradictions, all axiomatized content classically
correct (Slepian, Sudakov-Fernique, BTIS, Karhunen-Loève entropy
bounds — all well-known results in the Gaussian-process literature;
the gap is formalization, not mathematics).
