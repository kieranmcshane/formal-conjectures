# Mathlib PR draft — Kernel-generic Gaussian projective family

This document drafts the Mathlib (or `brownian-motion`) pull request
that would lift R15+R17's `glwGaussianProjectiveFamily` to a generic
**kernel-parametric** form, displacing the current hardcoded
`brownianCovMatrix` in `brownian-motion/Gaussian/ProjectiveLimit.lean`.

## Motivation

`brownian-motion/Gaussian/ProjectiveLimit.lean` defines:

```lean
def brownianCovMatrix (I : Finset ℝ≥0) : Matrix I I ℝ :=
  Matrix.of fun s t ↦ min s.1 t.1

noncomputable def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (brownianCovMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm
```

This is **hard-coded** to the Brownian covariance `min(s, t)`. Any
other Gaussian process (Ornstein-Uhlenbeck, fractional Brownian motion,
GLW, etc.) requires re-implementing the entire Kolmogorov-extension
chain.

We have an **R15 instance**: GLW. We had to copy-paste the entire
Brownian projective-family construction into
`Helpers/GLWGaussianProjectiveLimit.lean`, with `min(s, t)` replaced
by `K_GLW(s, t)`. This is a smell — we should refactor upstream.

## Proposed API

```lean
-- (1) Kernel signature: a positive-semi-definite kernel on ℝ≥0
structure GaussianKernel where
  kernelMatrix : ∀ (I : Finset ℝ≥0), Matrix I I ℝ
  posSemidef : ∀ I, (kernelMatrix I).PosSemidef
  consistent : ∀ {I J : Finset ℝ≥0} (hJI : J ⊆ I),
    (kernelMatrix I).submatrix
      (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
    kernelMatrix J

-- (2) Kernel-generic projective family
noncomputable def gaussianProjectiveFamilyOfKernel (K : GaussianKernel)
    (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (K.kernelMatrix I)
    |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

-- (3) Kernel-generic projective limit
noncomputable def gaussianLimitOfKernel (K : GaussianKernel) :
    Measure (ℝ≥0 → ℝ) :=
  projectiveLimit (gaussianProjectiveFamilyOfKernel K)
    (isProjectiveMeasureFamily_gaussianProjectiveFamilyOfKernel K)
```

The Brownian case becomes a 1-line specialization:

```lean
def brownianKernel : GaussianKernel where
  kernelMatrix I := Matrix.of fun s t ↦ min s.1 t.1
  posSemidef := posSemidef_brownianCovMatrix
  consistent := brownianCovMatrix_submatrix

example : gaussianLimitOfKernel brownianKernel = gaussianLimit := rfl
```

And the GLW case becomes:

```lean
def glwKernel : GaussianKernel where
  kernelMatrix := Erdos524.Helpers.glwCovMatrixNN
  posSemidef := Erdos524.Helpers.glwCovMatrixNN_PosSemidef
  consistent := Erdos524.Helpers.glwCovMatrixNN_submatrix
```

with `glwGaussianLimit = gaussianLimitOfKernel glwKernel` by `rfl` /
unfold.

## API map (per-symbol comparison)

| Current `brownian-motion`               | Proposed kernel-generic                              |
|-----------------------------------------|------------------------------------------------------|
| `gaussianProjectiveFamily`              | `gaussianProjectiveFamilyOfKernel K`                 |
| `posSemidef_brownianCovMatrix`          | `K.posSemidef`                                       |
| `brownianCovMatrix_submatrix`           | `K.consistent`                                       |
| `measurePreserving_equiv_*`             | `measurePreserving_equiv_*OfKernel K`                |
| `isProjectiveMeasureFamily_*`           | `isProjectiveMeasureFamily_*OfKernel K`              |
| `gaussianLimit`                         | `gaussianLimitOfKernel K`                            |
| `IsProbabilityMeasure_gaussianLimit`    | `IsProbabilityMeasure_gaussianLimitOfKernel K`       |
| `hasLaw_restrict_gaussianLimit`         | `hasLaw_restrict_gaussianLimitOfKernel K`            |
| `integral_gaussianProjectiveFamily`     | `integral_gaussianProjectiveFamilyOfKernel K`        |
| `integral_id_gaussianProjectiveFamily`  | `integral_id_gaussianProjectiveFamilyOfKernel K`     |
| `covariance_eval_gaussianProjectiveFamily` | `covariance_eval_gaussianProjectiveFamilyOfKernel K` |
| `variance_eval_gaussianProjectiveFamily`   | `variance_eval_gaussianProjectiveFamilyOfKernel K`   |
| `hasLaw_eval_gaussianProjectiveFamily`     | `hasLaw_eval_gaussianProjectiveFamilyOfKernel K`     |
| `hasLaw_eval_sub_eval_gaussianProjectiveFamily` | `hasLaw_eval_sub_eval_gaussianProjectiveFamilyOfKernel K` |
| `covariance_eval_gaussianLimit`         | `covariance_eval_gaussianLimitOfKernel K`            |

The covariance value `min s.1 t.1` becomes `K.kernelMatrix I s t` in
each lemma's RHS. For Brownian: equal to `min s.1 t.1` by `rfl`. For
GLW: equal to `K_GLW (s.1) (t.1)` by `rfl`.

## Comparison to `gaussianProjectiveFamily`

The `brownian-motion` package's existing `gaussianProjectiveFamily`
becomes a special case:

```lean
example (I : Finset ℝ≥0) :
    gaussianProjectiveFamily I = gaussianProjectiveFamilyOfKernel brownianKernel I := rfl
```

All downstream `gaussianLimit` consumers (the `IsBrownian`/`IsPreBrownian`
typeclasses, `Brownian`'s continuous modification, etc.) continue to
work unchanged because they reference `gaussianLimit` (which is
re-derived as `gaussianLimitOfKernel brownianKernel`).

## Why this is upstream-worthy

1. **Generality:** any practitioner working with a non-Brownian
   Gaussian process has to redo the entire projective extension
   currently. With the refactor, they supply a kernel and get the
   measure for free.
2. **Discoverability:** `gaussianProjectiveFamilyOfKernel` is a
   conceptually-named primitive that makes the API self-documenting.
3. **Test case:** GLW (this project) is the first non-Brownian
   instance to actually exercise this generality. The PR can cite
   `Helpers/GLWGaussianProjectiveLimit.lean` as the validating
   downstream user.

## Open questions for upstream review

1. Should `GaussianKernel` be a structure or a typeclass? Structure
   feels more honest (the kernel data IS the data), but typeclass
   would let downstream auto-derive instances (e.g., for OU process
   the kernel is `e^{-|s - t|}` and could be auto-inferred).
2. The variable `(0 : EuclideanSpace ℝ I)` for the mean is a hard-
   coded zero. Should we generalize to a kernel-determined mean
   `μ.kernelMean : (I → ℝ)`? For GLW the mean is zero; for affine
   processes it'd be non-zero. **Defer:** keep zero-mean for v1.
3. Generalization to `T ≠ ℝ≥0` (e.g., `T = ℝ` for two-sided
   Brownian, `T = NNReal × NNReal` for fields)? **Defer:** v1 stays
   on `ℝ≥0` to mirror current API exactly.

## R17 outcome posture

**R17 T2.1, T2.2, T2.3:** Stub, Stub, Partial.

**T2.1 + T2.2 (signature lifts):** Not implemented in this round.
The refactor is invasive and would touch the brownian-motion package;
doing it inside `Helpers/GLWGaussianProjectiveLimit.lean` would be a
separate parallel implementation rather than a true upstream lift.
The right path is the PR (T2.3, this document).

**T2.3 (this document):** Partial — fully drafts the PR, including
API map, comparison, and open questions. Length: 100+ lines.

## Cross-references

* `Helpers/GLWGaussianProjectiveLimit.lean` — the GLW instance that
  motivates the lift.
* `brownian-motion/Gaussian/ProjectiveLimit.lean` — the file we'd
  refactor.
* `R18ReadinessDiagnostic.md` — note that this PR is **not** on the
  R18 critical path; the project's own work can proceed without it.
