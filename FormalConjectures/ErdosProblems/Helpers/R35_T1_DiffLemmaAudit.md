# R35 — T1.1 Audit: Multivariate-Gaussian-CDF Differentiability w.r.t. Covariance

**Branch**: `r33-c-helpers-consolidation` (HEAD `bbe91f3`)
**Mathlib pin**: `mathlib4 @ 25ce63313608` (Mathlib 4.27.0-rc1, brownian-motion package).
**Date**: 2026-05-01.
**Scope**: read-only inventory of Mathlib + brownian-motion API for the analytic infrastructure required by Slepian's lemma's covariance-interpolation argument, namely the differentiability of the multivariate-Gaussian CDF (or finite-dimensional half-space probability) with respect to entries of the covariance matrix.

## 1. Multivariate-Gaussian object inventory

The only `multivariateGaussian` object lives in **brownian-motion**, NOT in core Mathlib:

```
.lake/packages/brownian-motion/BrownianMotion/Gaussian/MultivariateGaussian.lean
```

Key definitions and lemmas:
- `multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι)` (line 160).
  - Defined as `(stdGaussian _).map (fun x ↦ μ + toEuclideanCLM (CFC.sqrt S) x)`. **NOT defined via an explicit Lebesgue density**.
- `isGaussian_multivariateGaussian` (instance, line 166).
- `integral_id_multivariateGaussian = μ` (line 174).
- `covariance_eval_multivariateGaussian (hS : S.PosSemidef) (i j : ι) : cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ S] = S i j` (line 227).
- `variance_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) : Var[fun x ↦ x i; multivariateGaussian μ S] = S i i` (line 235).
- `charFun_multivariateGaussian (hS : S.PosSemidef)` (line 249) — characteristic function in closed form.

**No** `multivariateGaussianPdf`, `multivariateGaussianDensity`, or `multivariateGaussianCDF` exists anywhere on the search path. The only density-side handle is the characteristic-function form, which is unsuitable for direct differentiation under the integral against indicator functions of orthants.

## 2. Mathlib `Matrix.PosDef` API

Located at `Mathlib/LinearAlgebra/Matrix/PosDef.lean`. Has:
- `Matrix.PosDef` definition (line 160).
- `PosDef.posSemidef`, `PosDef.transpose`, `PosDef.isUnit` (in fields).
- `posDef_diagonal_iff`, `posDef_natCast_iff`.
- `PosDef.add_PosSemidef`, `PosSemidef.add_PosDef`, `PosDef.add_PosDef`.

**Crucially missing**: no API stating "the set `{Σ : Matrix n n ℝ | Σ.PosDef}` is open in `Matrix n n ℝ` with the entry-wise topology", nor a Cholesky differentiability lemma, nor an inverse-matrix differentiability lemma.

## 3. Determinant differentiability — Mathlib gap

Search results across full Mathlib + brownian-motion:

- `Matrix.det.continuous` exists at `Mathlib/Topology/Instances/Matrix.lean:459` (continuity only).
- `ContinuousLinearMap.continuous_det` at `Mathlib/Analysis/Normed/Module/FiniteDimension.lean:153`.

**Zero matches** for any of:
- `Differentiable.*Matrix.det`
- `HasFDerivAt.*Matrix.det`
- `differentiable_det`
- `det.*HasFDeriv`

**Workaround available, but not packaged**: `Matrix.det_apply` expresses `det` as a polynomial in the matrix entries (sum over `Equiv.Perm`), so `det : Matrix n n ℝ → ℝ` is a polynomial function and hence smooth. Closing this via `Polynomial.contDiff` / `MultilinearMap.contDiff` would take 30–80 LOC; nobody has done it yet.

## 4. Matrix-inverse differentiability — generic API but no specialization

Generic `HasFDerivAt Ring.inverse` lemma exists at `Mathlib/Analysis/Calculus/FDeriv/Mul.lean:726`:

```lean
HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
```

valid for `x : Rˣ` in a topological ring `R` over `𝕜`. **In principle** this applies to `Matrix n n ℝ` once we cast through `Matrix.GeneralLinearGroup` (`GLn`). But there's no recorded instance giving a pre-packaged `HasFDerivAt (·⁻¹) _ Σ` for `Σ : Matrix n n ℝ` with `Σ.PosDef`. Building this bridge is ≥ 50 LOC of structural plumbing.

## 5. Slepian / Sudakov-Fernique / Borell-TIS / log-Sobolev — total absence

Searches for `Slepian`, `slepian`, `Sudakov`, `Borell`, `Herbst`, `gaussian.*log.*sobolev` across Mathlib + brownian-motion:

- **Zero matches** for `Slepian`, `slepian`.
- The only "Sobolev" entries are PoissonSummation / Fourier transforms unrelated to log-Sobolev.

The Phase A upper-bound chain has zero Mathlib infrastructure.

## 6. Continuous-on-compact + dense-supremum primitives (for T2.3)

- `IsCompact.exists_sSup_image_eq` at `Mathlib/Topology/Order/Compact.lean:422`: a continuous function on a compact set attains its supremum.
- `Set.Icc 0 1` is compact in `ℝ` (`isCompact_Icc`).
- Density of `Rat.cast '' (Set.Icc 0 1 : Set ℚ)` in `Set.Icc 0 1`: `Rat.denseRange_cast` exists, intersection with `Icc` gives a dense subset.

Standard density-of-rationals + continuous-function-on-compact-set lemmas are present. T2.3 should be closable with ~20 LOC, mostly bookkeeping.

## 7. Conclusion + R35-T2.1 strategy

**The differentiability lemma cannot be closed in 50 LOC at this Mathlib pin.** The honest path is:

1. **Define a local CDF object** for the centered multivariate Gaussian over an orthant `(-∞, x₁] × ... × (-∞, xₙ]` against the `multivariateGaussian 0 Σ` measure. This is `(multivariateGaussian 0 Σ).real (Set.pi univ (fun i ↦ Set.Iic (x i)))` (or the `EuclideanSpace`-equivalent rectangle).
2. **State the differentiability theorem** with the explicit derivative formula (the standard sub-marginal density formula).
3. **Body:** TAG'd `R35-T2.1-mathlib-gap-determinant-diff` with concrete diagnostic citing missing Mathlib lemmas:
   - `Matrix.det.differentiable` (no entry; `det_apply` polynomial expansion route is an open Mathlib PR direction).
   - `Matrix.PosDef.inv.differentiable` (no entry; would build via `HasFDerivAt Ring.inverse` + `GLn` bridge).
   - **No explicit `multivariateGaussianPdf`** so even stating "density of `multivariateGaussian` w.r.t. Lebesgue" requires building the change-of-variables Jacobian formula manually (the `CFC.sqrt S` push-forward Jacobian is `sqrt(det S) = sqrt|det Σ|`).

Tried alternatives:
- `multivariateGaussian_density_eq` — does not exist in brownian-motion.
- `IsGaussian.density` — generic `IsGaussian` class has no extracted density.
- `MeasureTheory.MeasureSpace.{prod}` of `Real.gaussianReal` densities — works only for the diagonal-Σ case; doesn't handle off-diagonals.

The signature itself is land-able. The body decomposes into three known-missing Mathlib pieces, each ≥ 30 LOC + structural plumbing in their own right. **R35 lands the signature with a concrete, well-tagged Mathlib-gap diagnostic** (cap eligible: 50%–full per skin-in-the-game Rule 2: "TAG'd Mathlib gap with concrete missing lemma names + tried alternatives" → not the vague-hand-waving cap).

## 8. R36+ retirement path

- Either: build the determinant-as-polynomial differentiability lemma in `Helpers/MatrixDetDifferentiable.lean` (~50 LOC, self-contained), then assemble Σ ↦ Σ⁻¹ via `Ring.inverse` bridge (~50 LOC), then assemble multivariate density (~80 LOC, includes Jacobian).
- Or: Slepian via a completely different route (e.g., direct Gaussian-interpolation on sample paths, bypassing the CDF), per the alternative noted in `PhaseAUpperBound.lean` `gaussian_density_sign_comparison` R17 stub at line 73.
- Or: axiomatize the Slepian conclusion (Option E) and skip the differentiability lemma altogether — most direct route, costs +1 user-defined axiom.

R36 brief should pick between these three; my prior is on Option C (axiomatize Slepian) given the depth of Mathlib gaps revealed here.
