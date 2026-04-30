# R18 Build Status

Per-file `lake build` status for the GLW helper stack at the end of
Round 18 (`r18-finish` branch).

## Verification protocol

Each line below is the verbatim final line of `lake build <target>`
captured against `r18-finish` HEAD. Every helper builds green; the
remaining `sorry` is structurally tagged at conjunct 9 of
`glwGaussianLimit_Y_GLW_existence` and is the sole gating obstruction
for `Y_GLW_exists` axiom retirement.

## Per-file status

| File | Build | Sorries | Notes |
|------|-------|---------|-------|
| `Helpers/GLWGaussianProjectiveLimit.lean` | ✓ | 1 (conjunct 9) | R18 closed conjunct 8 via `exists_glwBrownianModification`; conjuncts 3-7 re-derived by ae-transfer |
| `Helpers/GLWProcess.lean` | ✓ | 0 (transitive sorry from conjunct 9) | `Y_GLW_exists` is a theorem delegating to `glwGaussianLimit_Y_GLW_existence` |
| `Helpers/GLWProcessPredicate.lean` | ✓ | 0 | Imports tightened in R18 (-2) |
| `Helpers/PhaseAUpperBound.lean` | ✓ | (existing R17 stubs for Slepian / Sudakov-Fernique) | Untouched in R18 |

## Build logs

```
$ lake build FormalConjectures.ErdosProblems.Helpers.GLWProcess
Build completed successfully (3408 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit
Build completed successfully (3407 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWProcessPredicate
Build completed successfully (3409 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
Build completed successfully (2667 jobs).
```

## R18 changes

### Phase 1 — Y_GLW_exists witness refactor (T1.1, T1.2, T1.3)

* `exists_glwBrownianModification`: new theorem, applies
  `BrownianMotion.Continuity.KolmogorovChentsov.exists_modification_holder'''`
  to `glwGaussianLimit_isKolmogorovProcess` with the
  `isCoverWithBoundedCoveringNumber_Ico_nnreal` cover. Output is a
  measurable, ae-equal-to-projection, continuous-path modification.
* `glwGaussianLimit_Y_GLW_existence`: existential body refactored to
  use the modification witness `fun u ω ↦ Y' u.toNNReal ω`. Conjuncts
  3-7 re-derived from the original projection-based proofs via
  `Integrable.congr` / `integral_congr_ae` / `Measure.map_congr`.
  Conjunct 8 (continuous paths) closed Full via the modification's
  per-ω continuity composed with `continuous_real_toNNReal`.

### Phase 2 — tail decay (T2.1, T2.2, T2.3)

Not advanced. The Borell-TIS / sup-control infrastructure required to
discharge conjunct 9 is not available in Mathlib at HEAD. The
diagnostic's "elementary route" via finite ε-net + marginal Gaussian
tail stalls because (i) Mathlib has no Gaussian-tail bound (only MGF /
charFun infrastructure), and (ii) the per-ω Hölder constant from
`exists_modification_holder'''` is not a measurable function of ω,
ruling out a uniform sup-bound. See `R19ReadinessDiagnostic.md` for
the prioritized path forward.

### Phase 4 — cleanup (T4.2 Partial)

Imports tightening: -4 explicit imports across two files:

* `GLWGaussianProjectiveLimit.lean`: -2
  (`KolmogorovExtension4.KolmogorovExtension`,
  `Mathlib.Probability.Process.Kolmogorov`).
* `GLWProcessPredicate.lean`: -2
  (`Mathlib.MeasureTheory.Measure.MeasureSpace`,
  `Mathlib.Probability.Distributions.Gaussian.Basic`).

T4.1 (bridge-file dead-code audit on `YGLWFromBrownianMotion.lean`,
3255 LOC) was not attempted in R18 — would require a deeper
unused-symbol scan than fits in the round's budget.

### Phase 5 — documentation (T5.1, T5.2)

This file (T5.1) and `R19ReadinessDiagnostic.md` (T5.2).

## Axiom state

```
$ lean .../check_axioms.lean
'Erdos524.Helpers.Y_GLW_exists' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` is still present, traced to the conjunct-9 stub. R19's
priority-A blocker is to retire it.
