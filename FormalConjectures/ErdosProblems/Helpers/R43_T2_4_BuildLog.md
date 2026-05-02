# R43 — T2.4 Build Log

**Date**: 2026-05-02 (R43 V2 round 5).
**Branch**: `r33-c-helpers-consolidation`, post-T2.3 commit `0496d40`.

## `lake env lean` output (relevant Phase A files)

### `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean`

```
warning: brownian-motion: repository '...' has local changes
FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean:183:8: warning: declaration uses 'sorry'
FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean:226:8: warning: declaration uses 'sorry'
```

* Line 183 — `multivariateGaussian_eq_lebesgue_withDensity` (MGE),
  TAG[R43-T2.1-MGE-pushforward-jacobian-body]. **NEW R43.**
* Line 226 — `multivariateGaussianOrthantCDF_eq_lebesgue_integral`
  (MGI), TAG[R43-T2.1-MGI-orthant-via-MGE-body]. **NEW R43.**

### `FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean`

```
warning: brownian-motion: repository '...' has local changes
FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean:363:8: warning: declaration uses 'sorry'
```

* Line 363 — `slepian_comparison_finite`,
  TAG[R41-T2.2-FTC-via-Stein-and-real-MGP]. Pre-existing R41 Stub.
* Phase 1A (`Sα_path_hasDerivAt`, ~245) and Phase 1B
  (`multivariateGaussianOrthantCDF_differentiableAt_along_Sα_path`,
  ~297): no sorry (Full Lean).

### `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean`

```
warning: brownian-motion: repository '...' has local changes
FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:160:8: warning: declaration uses 'sorry'
FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean:274:8: warning: declaration uses 'sorry'
```

* Line 160 — `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`,
  TAG[R35-T2.1-mathlib-gap-density]. Pre-existing R35 Stub.
* Line 274 — `multivariateGaussianOrthantCDF_partial_offdiagonal` (MGP),
  TAG[R41-T2.1-bivariate-density-conditional]. Pre-existing R41 Stub.

### `FormalConjectures/ErdosProblems/524.lean`

Build clean. Pre-existing AMS-attribute lint warnings unchanged. The
existing R33-D form-β-to-full-sum bridge sorry @ 3889 unchanged. No new
errors.

## Net debt count (post-R43)

| File | sorry sites | Δ (vs R42) |
|---|---|---|
| `MultivariateGaussianPdf.lean` | 2 (MGE @ 183, MGI @ 226) | +2 (signature upgrades) |
| `PhaseAUpperBound.lean` | 1 (slepian @ 363) | 0 |
| `MultivariateGaussianCDF.lean` | 2 (orthantCDF.diff @ 160, MGP @ 274) | 0 |
| `MatrixDetDifferentiable.lean` | 2 (det.hasFDerivAt + det.differentiable) | 0 |
| `GLWLowerProof.lean` | 2 (Yplus + Yminus IsGLWProcess) | 0 |
| `GLWUpperProof.lean` | 1 (Yplus IsGLWProcess) | 0 |
| `TwoDimKMTFromOneDim.lean` | 2 (R33-C iIndepFun + R33-C gaussian) | 0 |
| `524.lean` | 1 (R33-D form-β bridge) | 0 |
| **Total** | **13** | **+2** |

User-defined axioms: 5 (unchanged from R42).

## Conclusion

All R43 deliverables build clean. Net debt is +2 sorries (13 from 11),
matching the audit prediction (mid-distribution outcome, with Phase 1B
landing Full close — actually the upper-distribution outcome per the
brief's confidence prediction at P~0.30).

R38 + R39 + R40 + R41 + R42 milestones preserved. R59 ceiling check:
17 rounds remaining (R44–R60) for pure-axiom-free target with 1 round
buffer via Q5 BTIS-merge compression.
