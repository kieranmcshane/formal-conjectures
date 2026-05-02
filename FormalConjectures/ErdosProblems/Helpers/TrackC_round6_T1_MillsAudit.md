# Track C round 6 — T1.1 Mills truncation audit

**Round**: TC6
**Date**: 2026-05-02
**Mathlib pin**: `25ce633136`
**Branch**: `track-c-1dkmt`
**Worktree**: `~/Documents/formal-conjectures-track-c`
**Cache state**: `lake-manifest.json` mtime `2026-05-02 16:07`; `.lake/build/` mtime `2026-05-02 17:00` — **fresh** (build newer than manifest, no `lake update` since cache get; `lake exe cache get` skipped).

## Claims Verification Table

| # | Claim | VERIFIED? | Citation | Notes |
|---|-------|-----------|----------|-------|
| 1 | TC5 `gaussianMillsRatioReal_truncation` Stub at line 105 | **YES** | [`FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean:105-120`](FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean#L105) | Exact match: `theorem gaussianMillsRatioReal_truncation {x : ℝ} (_hx : 0 < x) : gaussianMillsRatioReal x ≤ 1 / x`. (Note: BACKGROUND.md predicted absolute path `Helpers/...` — actual is `FormalConjectures/ErdosProblems/Helpers/...`.) |
| 2 | `gaussianPDFReal_pos` available at pin | **YES** | [`Mathlib/Probability/Distributions/Gaussian/Real.lean:62`](.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean#L62) | `lemma gaussianPDFReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x`. With `μ = 0, v = 1` and `(1 : ℝ≥0) ≠ 0`. |
| 3 | `setIntegral` on Ioi monotonicity API | **YES** | [`Mathlib/MeasureTheory/Integral/Bochner/Set.lean:710-714`](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean#L710) | `setIntegral_mono_on (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x) : ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ`. Requires `IntegrableOn f s μ`, `IntegrableOn g s μ` from outer `include hf hg`. `Ioi x` is `MeasurableSet`. |
| 4 | `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` | **YES** | [`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:713`](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L713) | `(hcont : ContinuousWithinAt f (Ici a) a) (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) : ∫ x in Ioi a, f' x = m - f a`. Apply with `f t = -exp(-t²/2)`, `f' t = t * exp(-t²/2)`, `m = 0`. |
| 5 | Stirling explicit form (Robbins 1955) at pin | **NO** | [`Mathlib/Analysis/SpecialFunctions/Stirling.lean:264, 280`](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean#L264) | Mathlib comment explicitly states *"Sharper bounds due to Robbins are available, but are not yet formalised."* Asymptotic-only (`tendsto_stirlingSeq_sqrt_pi`) + lower bound `le_factorial_stirling` + log-form `le_log_factorial_stirling`. **Confirmed Stub-able**. |
| 6 | Real-Beta function at pin | **NO** | [`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60`](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L60) | Only `Complex.betaIntegral (u v : ℂ) : ℂ` at pin. No Real-Beta wrapper. **Confirmed Stub-able**. (Note: file is at `Gamma/Beta.lean`, not standalone `Beta.lean`.) |
| 7 | TC5 `gaussianMillsRatioReal` def preserved | **YES** | [`FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean:79`](FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean#L79) | Line 79 (BACKGROUND.md said line 62 — actually line 79). No regression. Signature `noncomputable def gaussianMillsRatioReal (x : ℝ) : ℝ := (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) / gaussianPDFReal 0 1 x`. |
| 8 | TC5 `gaussianMillsRatioReal_pos` Stub preserved | **YES** | [`FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean:89-96`](FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean#L89) | Untouched by TC6 (TAG[TrackC-Layer3-Mills-positivity]). |
| 9 | TC5 `gaussianMillsRatioReal_antitone` Stub preserved | **YES** | [`FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean:135-147`](FormalConjectures/ErdosProblems/Helpers/GaussianMillsRatio.lean#L135) | Untouched by TC6 (TAG[TrackC-Layer3-Mills-antitone]). Composition: depends on truncation. |
| 10 | Layer 2 + Layer 3 (TC2-TC5) infrastructure preserved | **YES** | [`FormalConjectures/ErdosProblems/Helpers/OneDimKMT.lean`](FormalConjectures/ErdosProblems/Helpers/OneDimKMT.lean) | No regression (TC6 only touches `GaussianMillsRatio.lean`). |

## API summary for T2.1 closure

**Definition unfold**: `gaussianPDFReal 0 1 t = (√(2 * π))⁻¹ * rexp (-t² / 2)` (with `(1 : ℝ≥0) → ℝ` coerced; `2 * π * 1 = 2π`; `(t - 0)² = t²`; `2 * 1 = 2`).

**Mathematical proof outline (TC6 brief)**:
1. Pointwise: `1 ≤ t / x` for `t ∈ Ioi x` (since `0 < x ≤ t`), so `gaussianPDFReal 0 1 t ≤ (t/x) * gaussianPDFReal 0 1 t`.
2. Lift via `setIntegral_mono_on` on `Ioi x` (measurable, both sides integrable on Ioi x).
3. Pull `1/x` constant: `∫ t in Ioi x, (t/x) * φ(t) = (1/x) * ∫ t in Ioi x, t * φ(t)`.
4. Antiderivative: `(d/dt)(-exp(-t²/2)) = t · exp(-t²/2)` (chain rule). Apply `integral_Ioi_of_hasDerivAt_of_tendsto` with `f t = -exp(-t²/2)`, `m = 0`, `f x = -exp(-x²/2)` ⇒ `∫ t in Ioi x, t · exp(-t²/2) = 0 - (-exp(-x²/2)) = exp(-x²/2)`.
5. Multiply through by `(√(2π))⁻¹`: `∫ t in Ioi x, t · gaussianPDFReal 0 1 t = (√(2π))⁻¹ · exp(-x²/2) = gaussianPDFReal 0 1 x`.
6. Therefore: `(numerator of m(x)) ≤ (1/x) · gaussianPDFReal 0 1 x`. Divide both sides by `gaussianPDFReal 0 1 x > 0` to get `m(x) ≤ 1/x`.

**Risk factors**:
- Step 4 antiderivative requires `HasDerivAt` for `t ↦ -exp(-t²/2)` and proof `-exp(-t²/2) → 0 as t → ∞` and `IntegrableOn (fun t => t * exp(-t²/2)) (Ioi x)`. Each is standard Mathlib but cumulative LOC may exceed budget.
- Step 5 algebraic ring manipulation through PDF unfold + factor extraction.
- Coercion `(1 : ℝ≥0) → ℝ = 1` requires `NNReal.coe_one` rewrite or careful unfolding.

**LOC estimate**: 80-120 (upper end of brief's 40-80 range). Decision tree:
- If Mills truncation Full lands ≤ T+2:30 → T2.2 Stirling/Beta sigs.
- If T+2:30 hit without Full → ship TAG'd diagnostic citing exact closure recipe + Mathlib gaps (none material — all APIs present per claims 2-4).

**Mathlib-gap status**: NONE for Mills truncation. All required APIs verified present. Body close is purely a labor question.
