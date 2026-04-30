# GLWGaussianProjectiveLimit — kernel-generic projective limit for `K_GLW`

R15 closeout. Documents the construction in
`Helpers/GLWGaussianProjectiveLimit.lean` that retires the `Y_GLW_exists`
axiom in `Helpers/GLWProcess.lean` to a `theorem`.

## Why this file exists

`brownian-motion`'s `gaussianProjectiveFamily`
(`BrownianMotion.Gaussian.ProjectiveLimit:60`) is hardcoded to the
Brownian covariance `brownianCovMatrix(I) = min(s, t)` and cannot be
substituted with `K_GLW`. R14's pivotal finding was that retirement of
the GLW process axiom requires **constructing in parallel**, not
substituting. R15 carries out that parallel construction.

The `IsGLWProcess` predicate (in `GLWProcessPredicate.lean`) imports
`GLWProcess.lean` (where the axiom lives), which means this file —
imported by `GLWProcess.lean` to retire the axiom — must NOT depend on
`GLWProcessPredicate.lean`. Hence the O5 witness is stated in the
9-conjunct existence form instead of as `IsGLWProcess`.

## API map

| ID | Name | Kind | Role |
|----|------|------|------|
| O1 | `glwGaussianProjectiveFamily : Finset NNReal → Measure (· → ℝ)` | def | Multivariate-Gaussian on each finite NNReal grid. |
| O1 | `glwGaussianProjectiveFamily_apply` | simp lemma | Unfolds the def. |
| O1 | `glwMeasurePreserving_equiv_multivariateGaussian` | lemma | EuclideanSpace ↔ projective-family equivalence. |
| O1 | `isGaussian_glwGaussianProjectiveFamily` | instance | Brings `IsFiniteMeasure` into scope for `projectiveLimit`. |
| O2 | `isProjectiveMeasureFamily_glwGaussianProjectiveFamily` | lemma | Projective consistency under `Finset.restrict₂`. |
| O3 | `glwGaussianLimit : Measure (NNReal → ℝ)` | def | Kolmogorov-extension projective-limit measure. |
| O3 | `isProjectiveLimit_glwGaussianLimit` | lemma | Cylindrical-projection lemma. |
| O3 | `IsProbabilityMeasure_glwGaussianLimit` | instance | Probability-measure instance. |
| O3 | `hasLaw_restrict_glwGaussianLimit` | lemma | `I.restrict` is measure-preserving onto the family. |
| O4 | `glwGaussianLimit_isKolmogorovProcess` | theorem (sorry) | Kolmogorov-Chentsov input on the projection. |
| O5 | `glwGaussianLimit_Y_GLW_existence` | theorem (sorry) | 9-conjunct existence witness used by `Y_GLW_exists`. |

## brownian-motion files used

- `BrownianMotion.Gaussian.MultivariateGaussian` — `multivariateGaussian`
  (line 160), `measurePreserving_restrict_multivariateGaussian`
  (line 299), `EuclideanSpace.restrict₂` (line 280).
- `BrownianMotion.Gaussian.ProjectiveLimit` — template for the parallel
  construction.
- `KolmogorovExtension4.KolmogorovExtension` — `projectiveLimit`,
  `IsProjectiveLimit`, `IsProjectiveMeasureFamily`,
  `isProbabilityMeasure_projectiveLimit`.
- `Mathlib.Probability.Process.Kolmogorov` — `IsKolmogorovProcess`
  structure.

## Bridge-file APIs consumed

- `glwCovMatrixNN` (`YGLWFromBrownianMotion.lean:1154`): the K_GLW
  Gram matrix on a Finset NNReal.
- `glwCovMatrixNN_apply` (line 1160): definitional simp lemma.
- `glwCovMatrixNN_PosSemidef` (line 1195): PSD precondition for
  `multivariateGaussian`.
- `glwCovMatrixNN_submatrix` (line 1178): sub-Finset restriction is
  `glwCovMatrixNN J` (`rfl` proof).
- `glwCovMatrixNN_pairwise_diff_quadratic_le_sq` (line 1249): the L²
  Hölder-1 bound, future input for the K-C reduction.
- `K_GLW_processKernel_R14_capstone` (R14 §4.49): the
  `ProcessKernel`-shaped capstone of the bridge file, available for
  the K-C threshold-feasible reformulation in R16.

## Status

- O1, O2, O3: full proofs (sorry-free, build green at 7914/7914 jobs).
- O4: structured-sorry stub. Body details the 3-step recipe to fill
  (variance reduction via `covariance_eval_multivariateGaussian` →
  Hölder-1 input → K-C threshold lift to `q > p` via 4-th moment).
- O5: structured-sorry stub. 9-conjunct projection plan documented.
- O6: theorem `Y_GLW_exists` (`Helpers/GLWProcess.lean`) discharges
  via `glwGaussianLimit_Y_GLW_existence`. Inherits 1 transitive sorry
  from O5; 0 inline sorries; build green.
- O7 (cascade): `lake build FormalConjectures.ErdosProblems.«524»`
  green at 7914/7914 with no errors (only style-linter warnings
  unrelated to this PR).

## R16 work

- **O4 finish** (~30 LOC): reduce
  `∫⁻ ω, edist (ω s) (ω t) ^ p ∂glwGaussianLimit` to
  `K_GLW(s,s) + K_GLW(t,t) - 2 K_GLW(s,t)` via
  `hasLaw_restrict_glwGaussianLimit` + `covariance_eval_multivariateGaussian`,
  then close with `glwCovMatrixNN_pairwise_diff_quadratic_le_sq`.
  Threshold lift to `q > p` requires the Gaussian 4-th-moment recipe
  (`E[X⁴] = 3 E[X²]²`).
- **O5 finish** (~80-120 LOC): apply `IsAEKolmogorovProcess.mk` to O4
  (continuous modification), then individually prove each of the 9
  conjuncts. The integrability/Gaussianity/centeredness/covariance
  conjuncts are direct from `multivariateGaussian` lemmas in
  `MultivariateGaussian.lean`. The continuous-paths conjunct is the
  `IsKolmogorovProcess.continuousModification` output. Tail decay
  uses Borell + Borel-Cantelli (independent ~30 LOC argument).
- **Net axiom retirement**: once O5 is proven sorry-free,
  `#print axioms Y_GLW_exists` will show only `propext / Classical.choice
  / Quot.sound`. The PR is then a true axiom removal.
