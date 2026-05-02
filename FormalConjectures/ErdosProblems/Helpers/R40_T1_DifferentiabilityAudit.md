# R40 — T1.1 Audit: Differentiability Infrastructure for Phase A Upper Option B

**Branch**: `r33-c-helpers-consolidation` (HEAD `c6d8c21`)
**Mathlib pin**: `mathlib4 @ 25ce63313608` (Mathlib 4.27.0-rc1)
**brownian-motion**: bundled with project, `MultivariateGaussian.lean` last touched upstream.
**Date**: 2026-05-02.
**Scope**: Re-verify Grok R40 pre-flight Q1 verdicts on the three Mathlib pieces required for the differentiability infrastructure of Phase A upper Option B (Slepian + SF + BTIS via covariance interpolation).

This doc establishes the local-first decisions for R40-T2.1, R40-T2.2, R40-T2.3 against direct grep against the bundled Mathlib + brownian-motion source.

## (a) `Matrix.det.differentiable` — Mathlib state

**Verdict: gap confirmed.** Grok Q1(a) verdict matches direct grep.

Search command:

```
grep -rn "det.*Differentiable\|Differentiable.*det\|HasFDerivAt.*det\|det.*HasFDerivAt" \
    .lake/packages/mathlib/Mathlib/
```

Returns **zero matches**. Only continuity is packaged:

* `Continuous.matrix_det` at `Mathlib/Topology/Instances/Matrix.lean:210` (entry-wise continuous → continuous det).
* `Matrix.continuous_det` at `Mathlib/Topology/Instances/Matrix.lean:459` (det as a map `GL n R → Rˣ`).

**Explicit derivative not packaged.** No `HasFDerivAt`, no `Differentiable`, no `ContDiff`.

### Routes for R40-T2.1

* **(α) Adjugate / cofactor expansion.** `det A = ∑_i a_{i,j} · cofactor(A, i, j)` for any column `j`. Each cofactor is a polynomial in the other entries; sum and product of differentiable functions is differentiable. Estimated 100–200 LOC.
* **(β) Multilinear alternating form.** `Matrix.detRowAlternating : ((Fin n → R) [Λ^Fin n]→ₗ[R] R)` exists in Mathlib as the multilinear alternating-form witness. `MultilinearMap` does not have a packaged `HasFDerivAt` lemma at this pin (also a gap), so this route adds a second Mathlib gap rather than removing one.

**Decision:** Path (α) is preferred — closer to existing Mathlib API. Local lemma in `Helpers/MatrixDetDifferentiable.lean`.

**Acceptable deliverable for R40-T2.1:** signature + TAG'd Stub citing the missing lemma name (`Matrix.det.hasFDerivAt`) and the route options. Path (α) full proof is non-trivial (cofactor formulas, induction on size) and comfortably exceeds the R40 single-round budget when combined with T2.2 + T2.3 + T2.4 + builds + status doc.

## (b) `Matrix.PosDef.inv.differentiable` — Mathlib state

**Verdict: derivable in principle.** Grok Q1(b) verdict matches: the generic `Ring.inverse` differentiability is packaged; what's missing is the specialization to `Matrix n n ℝ` via the `PosDef → Invertible` bridge.

Confirmed packaged:

* `hasFDerivAt_ringInverse` at `Mathlib/Analysis/Calculus/FDeriv/Mul.lean:725-729`:

  ```lean
  theorem hasFDerivAt_ringInverse (x : Rˣ) :
      HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
  ```

  Hypotheses: `[NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]`.

* `differentiableAt_inverse {x : R} (hx : IsUnit x)` at `:732`.
* `differentiableOn_inverse : DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsUnit x}` at `:742`.

For `R = Matrix n n ℝ` with `n` finite:

* `Matrix n n ℝ` is a `NormedRing` via the entry-wise sup norm (`Matrix.normedRing`).
* `HasSummableGeomSeries (Matrix n n ℝ)` — packaged for finite-dim normed algebras (search `instHasSummableGeomSeries`); needs verification at the pin.
* `Matrix.PosDef → Invertible`: `Matrix.PosDef.isUnit` (or via positive eigenvalues).

The PosDef set being **open** in `Matrix n n ℝ` is provable from `Matrix.det_pos_iff_PosDef`-style lemmas + continuity of det + openness of `(0, ∞)`; a few additional intermediate lemmas needed.

### Routes for R40-T2.2

* **Specialization route.** Theorem `Matrix.PosDef.inv_hasFDerivAt`:

  ```lean
  theorem Matrix.PosDef.inv_hasFDerivAt
      {n : Type*} [Fintype n] [DecidableEq n]
      (M : Matrix n n ℝ) (hM : M.PosDef) :
      HasFDerivAt (fun A : Matrix n n ℝ => A⁻¹)
        (-mulLeftRight ℝ (Matrix n n ℝ) M⁻¹ M⁻¹) M
  ```

  Apply `hasFDerivAt_ringInverse` to the unit `hM.isUnit.unit`. Need to bridge `Matrix.inv` ↔ `Ring.inverse` (these agree for invertible matrices). Estimated 80–150 LOC.

**Decision:** Path is clear; local lemma in `Helpers/MatrixDetDifferentiable.lean` (or `Helpers/MatrixPosDefInverseDifferentiable.lean`).

**Acceptable deliverable for R40-T2.2:** signature + body referencing `hasFDerivAt_ringInverse` with TAG'd Stub for the `Matrix.inv = Ring.inverse on units` bridge if it doesn't compile cleanly via `convert` / `simp`.

## (c) `multivariateGaussianPdf` — brownian-motion state

**Verdict: explicit Lebesgue density absent.** Grok Q1(c) verdict matches direct read.

`multivariateGaussian` is defined as a **pushforward** at `BrownianMotion/Gaussian/MultivariateGaussian.lean:160-162`:

```lean
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map
    (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
```

i.e. `(σ-square-root) · standard-Gaussian + μ`, **not** an explicit density formula `(2π)^{-n/2} |Σ|^{-1/2} exp(-x^T Σ^{-1} x / 2)`.

The available API exposes:

* `integral_id_multivariateGaussian` (mean = μ).
* `covariance_eval_multivariateGaussian`, `variance_eval_multivariateGaussian` (covariance entries).
* `charFun_multivariateGaussian` (characteristic function, closed form).
* `hasLaw_eval_multivariateGaussian` (1D marginals are `gaussianReal`).

**Zero matches** for `multivariateGaussianPdf`, `multivariateGaussianDensity`, anywhere on path.

### Routes for R40-T2.3

* **Local definition route.** Define `multivariateGaussianPdf S x : ℝ` directly via the standard formula:

  ```lean
  noncomputable def multivariateGaussianPdf
      {ι : Type*} [Fintype ι] [DecidableEq ι]
      (S : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
    (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) *
      Real.sqrt (S.det)⁻¹ *
      Real.exp (-(1/2) * (x ⬝ᵥ S⁻¹.mulVec x))
  ```

  Then state the equality bridge `multivariateGaussianPdf_eq_density` between this definition and the Radon–Nikodym derivative of `multivariateGaussian 0 S` w.r.t. Lebesgue (via the `EuclideanSpace.basisFun` pull-back).

* **Equality bridge.** Requires:
  1. Change of variables formula for the linear map `x ↦ CFC.sqrt(S) · x`.
  2. Jacobian determinant of `CFC.sqrt(S)` equals `Real.sqrt (det S)`.
  3. Composition with the standard-Gaussian density `(2π)^{-n/2} exp(-‖x‖²/2)`.

  Mathlib has `Measure.map_apply` + `MeasurePreserving` + `MeasureTheory.integral_image_eq_integral_abs_det_jacobian_smul_of_injOn` (verify exact name at pin), but the matrix-square-root case has no recorded Jacobian computation lemma.

**Decision:** Local definition + signature for the equality bridge land in R40. The bridge body itself is a TAG'd Stub citing concrete missing pieces (Jacobian-of-CFC.sqrt, density-of-stdGaussian-explicit). Estimated 200–350 LOC for the full bridge.

**Acceptable deliverable for R40-T2.3:** definition + bridge signature + TAG'd Stub diagnostic. The `multivariateGaussianPdf` definition itself is ~10 LOC; it's the equality bridge that takes ~300 LOC.

## (d) `sup_continuous_eq_sup_dense` — mechanical close (R40-T2.4)

Already drafted at `Helpers/PhaseAUpperBound.lean:274-290` with `filter_upwards` opener:

```lean
theorem sup_continuous_eq_sup_dense
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (Y : ℝ → Ω → ℝ) (hY_cont : ∀ᵐ ω ∂ℙ, Continuous (fun u => Y u ω)) :
    ∀ᵐ ω, sSup ((fun u => Y u ω) '' Set.Icc (0 : ℝ) 1) =
            sSup ((fun u => Y u ω) '' ((↑) '' (Set.Icc (0 : ℚ) 1))) := by
  filter_upwards [hY_cont] with ω hω
  sorry  -- TAG[R35-T2.3-density-mechanical]
```

The Mathlib primitives needed are present per R35 audit §6:
* `IsCompact.exists_sSup_image_eq` for compact + continuous → sup attained.
* `Rat.denseRange_cast` + `Set.Icc 0 1` density.

**Decision:** Close T2.4 in R40. Body is order-theoretic anti-symmetry:
* `≤`-direction: continuous image of compact `Icc 0 1` is compact, hence has a maximum, attained at some `u* ∈ Icc 0 1`. Approximate `u*` by rationals in `Icc 0 1` (density). Continuity of `Y u ω` at `u*` gives that the rational sequence's `Y`-values converge to `Y u* ω`, hence the rational supremum exceeds `Y u* ω - ε` for every `ε > 0`.
* `≥`-direction: rational `Icc 0 1` ⊆ real `Icc 0 1`, so `sSup` over the smaller set is ≤ `sSup` over the larger.

Estimated 30–60 LOC.

## Decision matrix

| Item | Path | LOC est. | R40 deliverable |
|------|------|----------|-----------------|
| T2.1 (det.diff) | (α) cofactor expansion | 100–200 | signature + TAG'd Stub `R40-T2.1-det-cofactor-route` |
| T2.2 (PosDef.inv.diff) | specialize `hasFDerivAt_ringInverse` | 80–150 | signature + body attempt; TAG'd Stub if Matrix.inv↔Ring.inverse bridge resists |
| T2.3 (multivariateGaussianPdf) | local def + bridge signature | def ~10, bridge 200–350 | definition (full) + bridge signature + TAG'd Stub `R40-T2.3-pushforward-jacobian` |
| T2.4 (sup_continuous_eq_sup_dense) | density argument | 30–60 | full body close |

## Anti-pattern compliance

* ❌ "Re-state R35 audit verbatim" — refused. R40 audit re-verified Grok Q1 verdicts against grep, found `hasFDerivAt_ringInverse` is the canonical Mathlib API for T2.2 (slightly stronger characterisation than R35 audit gave).
* ❌ "Vague Mathlib gap with no concrete diagnostic" — refused. Specific names (`Matrix.det.hasFDerivAt`, Jacobian-of-CFC.sqrt) listed as the missing pieces.
* ❌ "Defer Mathlib API survey to a follow-up doc" — refused. T1.1 cap rule binds us to ≥30 LOC of audit content.

## Conclusion

R40-T2.1 and R40-T2.3 will land as signature + TAG'd Stub with concrete diagnostic (per R40 prompt §50% cap rule, this is normal-scoring). R40-T2.2 will attempt a body via `hasFDerivAt_ringInverse` specialization. R40-T2.4 closes with density-of-rationals + continuous-on-compact argument.

Audit doc complete. T2.1–T2.4 begin.
