# R35 — Build Log

**Branch**: `r33-c-helpers-consolidation` (R35 commits in flight on top of `bbe91f3`).
**Date**: 2026-05-01.

## Files modified / created in R35

1. **NEW**: `FormalConjectures/ErdosProblems/Helpers/R35_T1_DiffLemmaAudit.md`
   T1.1 audit document — Mathlib API inventory + 3 concrete gaps + retirement options.
2. **NEW**: `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean`
   T1.1 + T2.1 — `multivariateGaussianOrthantCDF` definition + differentiability theorem
   with TAG'd Mathlib gap diagnostic. ~200 LOC including doc.
3. **MODIFIED**: `FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean`
   - Imports `MultivariateGaussianCDF`.
   - Adds `open MeasureTheory ProbabilityTheory` for `ℙ` notation.
   - T2.2 — adds `slepian_comparison_finite` skeleton (real signature, body deferred).
   - T2.3 — adds `sup_continuous_eq_sup_dense` (signature + filter_upwards, body deferred).
4. **NEW**: this build log.

## Build commands run

### Helpers-level builds

```
$ lake build FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF
⚠ [3019/3019] Built FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF (1.0s)
warning: ... unused section variable(s) ... [Fintype ι] [DecidableEq ι] ... in
  multivariateGaussianOrthantCDF_partial_offdiagonal
Build completed successfully (3019 jobs).
```

```
$ lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
⚠ [3021/3022] Replayed FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF
  (same warning as above)
✔ [3022/3022] Built FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound (2.2s)
Build completed successfully (3022 jobs).
```

### Sister build to confirm no regression

```
$ lake build FormalConjectures.ErdosProblems.Helpers.GLWLowerProof
... (pre-existing R34 push_cast warnings on GLWGaussianProjectiveLimit lines
     2447, 2451 — pre-existing, unrelated to R35) ...
Build completed successfully (3416 jobs).
```

## Sorry inventory in R35-touched files

### `MultivariateGaussianCDF.lean`

| Line | Tag | Status |
|------|-----|--------|
| 142 (theorem `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`) | `R35-T2.1-mathlib-gap-density` | TAG'd Mathlib gap; concrete diagnostic citing missing `Matrix.det.differentiable`, missing `Matrix.PosDef.inv.differentiable`, missing `multivariateGaussianPdf`. Tried alternatives listed in body docstring + audit doc §3-§5. |

### `PhaseAUpperBound.lean`

| Line | Tag | Status |
|------|-----|--------|
| 157 (theorem `slepian_comparison_finite`) | `R35-T2.2-body-deferred-R36` | Real signature against `multivariateGaussianOrthantCDF` (covariance-domination → orthant-prob ordering). Body deferred to R36; gated on T2.1. |
| 245 (theorem `sup_continuous_eq_sup_dense`) | `R35-T2.3-density-mechanical` | Signature + `filter_upwards [hY_cont]` opener; remaining body is mechanical density-of-rationals + continuity-on-compact. ~20 LOC, deferred to R36. |

Total R35 sorries: **3** (T2.1 + T2.2 + T2.3), each TAG'd with concrete-diagnostic identifier.

## Net axiom count post-R35

**Unchanged** from R34: 4 user-defined axioms on the mainline 524 chain
(`Cp_T_explicit_pointwise_axiom`, `one_dim_KMT_coupling`,
`kmt_aided_gaussian_process`, `gao_li_wellner_small_ball_lower`) plus the
in-Helpers `Y_GLW_exists` stepping-stone axiom. R35 introduces no new
axioms.

## Net residual sorry count post-R35

**5 (R34 carry-over) + 3 (R35 new) = 8 honest TAG'd sorries**:

R34 carry-over (5):
1. R33-C T2.4 — `IndepFun(Yplus, Yminus)` linear-combo (Mathlib gap).
2. R33-C T2.5 — `iIndepFun` on Ω × Ω (Mathlib gap).
3. R33-D T2.1 — bridge `two_dim_KMT_coupling_legacy_Ω_form` (structural mismatch).
4. R34 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus` (still gated).
5. R34 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus` (still gated).

R35 new (3):
6. R35 T2.1 — `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` (Mathlib gap, three concrete missing pieces).
7. R35 T2.2 — `slepian_comparison_finite` body (gated on R35 T2.1).
8. R35 T2.3 — `sup_continuous_eq_sup_dense` body (mechanical, deferred to R36).

## Pre-existing ENat blocker (out of scope for R35)

`lake build FormalConjectures.ErdosProblems.524` still fails on
`Mathlib.Algebra.Order.Floor.Extended.ENat.toENNReal_iSup` ↔
`BrownianMotion/Auxiliary/ENNReal.lean:40` — pre-existing across R29-R34,
unrelated to R35 changes. Agent `trig_01P8K24FGqQF6zqTKY4vQWRD` monitors
upstream resolution.

## V1 verdict

**R35 V1 status: PASS.** Both R35-introduced files build clean (modulo
TAG'd sorry warnings + 1 tolerated unused-section-vars lint). No
regression on sister Helpers files (`GLWLowerProof` clean at 3416 jobs).
