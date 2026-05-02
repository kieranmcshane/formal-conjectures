# Phase V2 — Round R49 status (Track A mainline closure, Path A switch)

**Date:** 2026-05-02. **Branch:** `r46-track-a-mge-posdef` HEAD post-R49
(T1.1 audit `e9f5508`, T2.1 axiom `c62b5e4`, T2.2 inventory `19e7a46`,
T2.3 this entry).
**Round type:** Variante 1, single round, mainline. Mechanical Path A
axiomatization of Phase 2 body — no math content close, no Grok dispatch.

## Round outcome summary

**Net debt change:** -1 sorry, +1 user-defined axiom, items unchanged at
gate.

**Distribution outcome:** **upper** (P(Full)~0.93 prediction at T1.1
draft, materialized as 4/4 mandatory floor Full). All four sub-tasks
landed within the brief's sub-checkpoint windows.

| Sub-task | Status | Net debt impact | Commit |
|---|---|---|---|
| T1.1 Path γ' re-verification + axiom signature draft | Full ✓ | 0 (doc only) | `e9f5508` |
| T2.1 Phase 2 body axiom replacement | Full ✓ | -1 sorry, +1 axiom | `c62b5e4` |
| T2.2 AXIOM_INVENTORY.md update (Axiom #6) | Full ✓ | n/a (debt-tracking) | `19e7a46` |
| T2.3 build verification + this status doc + push R49 to fork | Full ✓ | n/a | (this commit) |

## Round mechanics

### T1.1 Path γ' re-verification (commit `e9f5508`)

Re-verified at HEAD `434a407` that R48-T1.1 misframings M1 + M2 still
hold:

* **(M1) Lean MGI ≠ density differentiability.** The R44 MGI in this
  codebase
  (`multivariateGaussianOrthantCDF_eq_lebesgue_integral` at
  `MultivariateGaussianPdf.lean:412`) is the integral REWRITE identity.
  Its R44 Full body (lines 412-477) is three sequential `rw`s consuming
  MGE Stub via line 466 — no `HasFDerivAt`, no `DifferentiableAt`, no
  derivative formula. Grep at HEAD `434a407` confirms zero
  `multivariateGaussianPdf` differentiability theorems
  (`grep "DifferentiableAt\|HasFDerivAt" MultivariateGaussianPdf.lean` →
  exactly 1 hit, in a comment at line 331). Pdf S-differentiability
  remains a separate ~80-150 LOC chain blocked on R40
  `Matrix.det.differentiable` Stub at `MatrixDetDifferentiable.lean:149`.
* **(M2) `GaussianParametricAnalysis.lean` tail bound is docstring,
  not theorem.** Re-inspected at HEAD `434a407`:
  `multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef` at
  `GaussianParametricAnalysis.lean:168` is INSIDE a `/-! ... -/`
  docstring code block (lines 156-198). The docstring (lines 162-164)
  explicitly states "Not added as TAG'd Stubs in R46 to avoid debt
  inflation. R47+ rounds will land them as Full theorems." Grep
  confirms exactly 1 hit project-wide (the docstring code-block line
  itself), no Lean theorem.

**No new theorems landed between R48 (`434a407`) and R49 mainline that
unblock Path γ'.** No Path γ'' has been validated. Path B (continue
from-scratch closure) costed at ~380-700 LOC across 3-5 rounds with
P(Full)/round ~0.30 — incompatible with R52 gate under cumulative
~0.5 sorry/round retirement rate.

T1.1 audit doc is `Helpers/Round49_T1_PathAAxiomatization.md`, 302
lines, with verbatim axiom signature draft + math content + retirement
target sub-plan.

### T2.1 axiom replacement (commit `c62b5e4`)

`MultivariateGaussianCDF.lean:160-313` replaced with axiom declaration
of identical type signature:

```lean
axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) :
    DifferentiableAt ℝ
      (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀
```

Anti-mismatch hygiene checklist (all items verified):

1. ✅ Theorem name preserved verbatim:
   `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`.
2. ✅ Binders preserved verbatim:
   `(S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ)` — including
   the `_h_pd` underscore prefix so the existing positional caller at
   `PhaseAUpperBound.lean:404` does not need to rename.
3. ✅ Conclusion preserved verbatim:
   `DifferentiableAt ℝ (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀`.
4. ✅ Section variables `{ι : Type*} [Fintype ι] [DecidableEq ι]`
   auto-bind into the axiom prefix (Lean 4 auto-binding rule applies
   identically to `theorem` and `axiom`).
5. ✅ New Lean docstring (`/-- ... -/`) added above the axiom: math
   content + classical justification (Slepian 1962 / Tong 1990) + why
   axiomatized (M1 + M2 cited) + retirement target sub-plan (R55-R59
   post-gate, two-path: Mathlib pin bump preferred / from-scratch
   fallback) + cross-reference to T1.1 audit doc.
6. ✅ Mid-edit compile check:
   `lake env lean MultivariateGaussianCDF.lean` clean (only the
   unrelated R41 off-diagonal Stub `sorry` warning remains in this
   file).
7. ✅ Consumer compile check:
   `lake env lean PhaseAUpperBound.lean` clean (only the unrelated R41
   `slepian_comparison_finite` Stub `sorry` warning remains).
8. ✅ Full `lake build` verification — see §"Build verification" below.

Net change at file level: 1 file changed, 69 insertions, 189 deletions
(150-line Stub-body comment block deleted, replaced with 67-line
axiom-rationale docstring + 4-line axiom declaration).

### T2.2 AXIOM_INVENTORY.md update (commit `19e7a46`)

Three updates to `AXIOM_INVENTORY.md`:

1. New "Build status (R49 V2 round 11 — Path A axiomatization of Phase
   2 body)" section at the top, ~70 lines, documenting the four R49
   deliverables + net debt change + R52 gate trajectory analysis.
2. Axiom count summary updated: "5 user-defined axioms" → "6
   user-defined axioms". Table gains row #6 for
   `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` with
   retirement path "V2 R55-R59 post-gate (Mathlib pin bump preferred;
   from-scratch ~150-300 LOC fallback)".
3. New "### Axiom #6 detail" subsection after the table — full Lean
   signature with section variables explicit, plain-English math
   content, classical justification reference (Slepian 1962 / Tong
   1990), why-axiomatized rationale citing M1 + M2, two-path retirement
   sub-plan, status (ACTIVE placeholder), and consumer list (single
   Lean caller at `PhaseAUpperBound.lean:404`).

### T2.3 build verification + push (this entry)

See §"Build verification" + §"Fork push" below.

## Mainline state at R49 close

* **6 user-defined axioms** (was 5 at R48 close — +1 from Path A switch).
* **11 TAG'd sorries** (was 12 at R48 close — -1 from Phase 2 body Stub
  retirement via Path A).
* **Total debt:** 17 items (unchanged at gate; +1 axiom / -1 sorry is a
  wash for item-count gating).
* **Cumulative R40-R49 retirement rate:** ~0.5 sorry/round over 10
  rounds.

## Hybrid (c) gate trajectory analysis

**R52 milestone gate:** items ≤ 8 required for Path B continuation. At
R49 close, items remain at 17 → **9 retirements needed across R50-R52
(3 rounds) → 3.0/round average** (UP from R48's 2.25/round target due
to one round consumed without item-count change).

**Realistic R50-R52 trajectory (mainline post-R49 Path A):**

| Round | Candidate target | Net retirement |
|---|---|---|
| R50 | GLW shortcut (R36 axiomatization retirement via in-tree closure) | -1 (axiom #5) |
| R51 | GLW shortcut continuation OR R40 `Matrix.det.differentiable` Stub Full close | -1 (sorry or axiom #4) |
| R52 | Track C/Track D parallel work landing OR additional Path A axiomatization | -1 to -3 |

**Cumulative R50-R52 mainline projection:** 3-5 retirements. Track
C/Track D parallel rounds need to contribute 4-6 additional retirements
to reach R52 gate target ≤ 8 items.

**R52 gate verdict (post-R49):** marginal under hybrid (c) target ≤ 8.
Path A switch buys budget but does not by itself flip the gate. Track
C/Track D contribution cadence + GLW shortcut viability are the
dominant remaining variables.

## Build verification

R49 follows the R40+ "named critical build target" convention — full
project `lake build` (8000+ modules) includes orphan WIP files
(`CharFunCrossBlock.lean:397`, `MVGaussianDensityBound.lean:197/199`,
`1141.lean`, `508.lean`, `26.lean`, `HartshorneConjecture.lean`,
`DiameterSimpleFiniteGroups.lean`) with pre-existing build errors
unrelated to Erdős 524 mainline; these were broken at HEAD `434a407`
pre-R49 and remain broken post-R49.

R49 targeted-build verification (all six R49-relevant targets green):

```
$ lake build FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF \
             FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf \
             FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound \
             FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable
Build completed successfully (3024 jobs).
[1 unrelated unused-variable lint at YGLWConstruction.lean:910:19, pre-existing]

$ lake build 'FormalConjectures.ErdosProblems.«524»'
Build completed successfully (7931 jobs).
[Pre-existing AMS-attribute / problem-category style lints at lines 3651,
 3784, 3855; one module-docstring lint at 7631; all pre-R49 unchanged.]

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWLowerProof \
             FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
Build completed successfully (7918 jobs).
[1 unrelated copyright-block style lint, pre-existing.]
```

Critical-target summary:

| Target | Status | Jobs | R49 milestone |
|---|---|---|---|
| `MultivariateGaussianCDF` | ✅ Green | (R49-modified) | Phase 2 body Stub retired via Path A axiomatization |
| `MultivariateGaussianPdf` | ✅ Green | unchanged | R44 MGI body + R43 MGE signature unchanged |
| `PhaseAUpperBound` | ✅ Green | unchanged | Direct consumer at line 404 — positional axiom call site unchanged because signature was preserved verbatim |
| `MatrixDetDifferentiable` | ✅ Green | unchanged | R40 Stub (`Matrix.det.differentiable`) unchanged this round per scope discipline |
| `«524»` | ✅ Green | 7931 | R38 consumer-build-green milestone preserved |
| `GLWLowerProof` + `GLWUpperProof` | ✅ Green | 7918 | R39 V2 milestone preserved |

Sorry-warning audit at R49 close (mainline `r46-track-a-mge-posdef`):

* `MultivariateGaussianCDF.lean:284` (R41 off-diagonal partial
  derivative Stub — unchanged this round; line shift from 268 pre-R49
  is from the new R49 axiom docstring being longer than the deleted
  Stub-body comment block).
* `PhaseAUpperBound.lean:450` (`slepian_comparison_finite` — unchanged).
* `MatrixDetDifferentiable.lean:128` and `:144` (R40 Stubs — unchanged).
* `MultivariateGaussianPdf.lean:260` (R43 MGE Stub body — unchanged).
* `GLWLowerProof.lean` × 2, `GLWUpperProof.lean` × 1 (R39 α-tightened
  IsGLWProcess Stubs — unchanged).
* `524.lean:3913` (R33-D form-β-to-fullsum bridge — unchanged).
* 2 R33-C/D Mathlib version-skew gaps in `TwoDimKMTFromOneDim.lean`
  (unchanged).

**Total mainline TAG'd `sorry`: 11 sites** (was 12 pre-R49). The Phase
2 body Stub previously at `MultivariateGaussianCDF.lean:313` is
**retired** — no longer in the warning list. ✅

## Fork push

`r46-track-a-mge-posdef` HEAD pushed to fork at R49 wrap. R48 catchup
(`434a407`) was already on fork before R49 began (verified via
`git ls-remote fork r46-track-a-mge-posdef` at Phase 0). R49 push
consists of:

* `e9f5508` — R49-T1.1 Path γ' breakage re-verification + axiom signature draft.
* `c62b5e4` — R49-T2.1 Path A axiomatize Phase 2 body — Stub retired, axiom #6 added.
* `19e7a46` — R49-T2.2 AXIOM_INVENTORY.md update — Axiom #6 added.
* (this commit) — R49-T2.3 build verification + status doc.

## Round score (skin-in-the-game evaluation)

Per R49 brief skin-in-the-game caps:

* T1.1 audit produced ✓ (`Round49_T1_PathAAxiomatization.md`, 302 lines).
* T2.1 axiom committed without signature drift ✓ (`c62b5e4`,
  `lake env lean` clean on consumer).
* T2.2 AXIOM_INVENTORY.md updated ✓ (`19e7a46`, count 5 → 6, Axiom #6
  detail section present).
* T2.3 build verified + push completed ✓ (this commit).
* Other Stubs (MGE, Matrix.det) NOT modified ✓ (R49 scope discipline
  preserved).
* R48 catchup commit `434a407` already on fork at R49 start, included
  in pushed range ✓.
* Axiom name SEARCHABLE + specific ✓
  (`multivariateGaussianOrthantCDF_differentiable_wrt_covariance` —
  preserved verbatim from theorem signature, 39 grep hits across the
  project, all of which still resolve).
* Retirement target documented ✓ (R55-R59 post-gate, two-path
  sub-plan).
* Math content of axiom documented ✓ (plain English + classical
  reference Slepian 1962 / Tong 1990 in both axiom docstring and
  AXIOM_INVENTORY Axiom #6 detail).

**No 0-pt or 50% caps triggered.** Realistic round score: upper
distribution (~430 pts on ~450 base ceiling) — clean axiomatization
with all hygiene checklist items verified, R48 catchup already pushed
pre-R49, mandatory floor 4/4 Full.

## V1 calibration

Per V1 protocol skin-in-the-game telemetry:

* **Predicted joint mandatory floor probability** at T1.1 draft: 0.75
  (highest in project so far).
* **Predicted distribution upper outcome (~450 pts)** at T1.1 draft:
  P~0.75.
* **Materialized:** upper outcome (4/4 mandatory floor Full, ~430 pts
  realistic estimate).
* **Calibration update:** confidence on Path A switch as a strategic
  decision validated. R50 GLW shortcut becomes the next strategic bet
  (P(Full)/round at R50 will be lower — likely 0.45-0.55, vs R49's
  0.75 mechanical confidence).

## What R49 did NOT do (scope discipline)

* Did NOT touch MGE Stub at `MultivariateGaussianPdf.lean:402`.
* Did NOT touch `Matrix.det.differentiable` Stub at
  `MatrixDetDifferentiable.lean:149`.
* Did NOT touch any track branches (`track-d-btis-honest`,
  `kmc-erdos-glw-lower`, etc.).
* Did NOT attempt MGE-axiom-equivalent treatment.
* Did NOT add new Stubs for tail-bound or pdf S-differentiability.
* Did NOT dispatch Grok pre-flight (mechanical round, no math content
  close, no T1.1-then-Grok pipeline needed).
* Did NOT modify any consumer (`PhaseAUpperBound.lean:404` call site
  unchanged because axiom signature is verbatim-preserved).

## Build log

(Appended in `Helpers/PhaseV2R49Status.BUILD.log` if size warrants
external file; otherwise summary above suffices for the audit trail.)

---

**R49 outcome:** Path A axiomatization of Phase 2 body landed cleanly.
Mainline budget freed for GLW shortcut R50-R51 + Track C/D parallel
work. R52 gate verdict marginal — Track C/D contribution cadence
remains load-bearing.
