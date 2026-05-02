# Track C round 7 — T1.1 Carter-Pollard assembly audit

**Date:** 2026-05-02.
**Branch / worktree:** `track-c-1dkmt` @ `~/Documents/formal-conjectures-track-c`.
**Pre-TC7 HEAD:** `61073a3` (TC6 closure: Mills truncation Full + Stirling Robbins Stub + Real-Beta Stub).
**Mathlib pin:** `25ce633136084367f182be00fdff7613ea949d27` (unchanged from TC6).
**Cache freshness:** `.lake/build/` mtime `2026-05-02 17:00:13` newer than `lake-manifest.json` mtime `2026-05-02 16:07`. Skip `lake exe cache get`.

## §1. Claims Verification Table (binding, all 10 rows)

| # | Claim | Status | Citation | Notes |
|---|-------|--------|----------|-------|
| 1 | TC6 Mills truncation Full close preserved (commit `61073a3`) | **VERIFIED** | `Helpers/GaussianMillsRatio.lean:201-243` | `gaussianMillsRatioReal_truncation` Full body via FTC-2 + `gaussianTailFirstMomentEq` private helper |
| 2 | TC6 Stirling Robbins Stub at `Helpers/StirlingTwoSided.lean` | **VERIFIED** | `StirlingTwoSided.lean:187-198` | `factorial_le_stirling_robbins` sub-Stub'd (single sorry); brief docstring confirms Mathlib comment "Sharper bounds due to Robbins are available, but are not yet formalised" |
| 3 | TC6 Real-Beta def + Beta-Gamma Stub at `Helpers/RealBeta.lean` | **VERIFIED** | `RealBeta.lean:63-86` | `realBeta` def via `intervalIntegral`; `realBeta_eq_Gamma_ratio` sub-Stub'd (single sorry) |
| 4 | Mathlib `tendsto_stirlingSeq_sqrt_pi` available at pin | **VERIFIED** | `Mathlib/Analysis/SpecialFunctions/Stirling.lean:228` | `theorem tendsto_stirlingSeq_sqrt_pi : Tendsto stirlingSeq atTop (𝓝 (√π))` |
| 5 | Mathlib `Complex.betaIntegral_eq_Gamma_mul_div` available at pin | **VERIFIED** | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:525` | `lemma betaIntegral_eq_Gamma_mul_div (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) : betaIntegral u v = Gamma u * Gamma v / Gamma (u + v)` |
| 6 | TC4 `tusnady_base_polynomial` Path A scaffolding preserved (TC5 universal-constants form) | **VERIFIED** | `OneDimKMT.lean:422-476` | Probability space + Fin.val cast + IsProbabilityMeasure + 2 pushforwards Full; sub-sorry at line 476 = polynomial pointwise bound |
| 7 | TC5 universal constants A=0.6, C=1 + ∀ᵐ form preserved | **VERIFIED** | `OneDimKMT.lean:430-431` | `∀ᵐ ω' ∂μ', |B ω' - (n : ℝ) - Z ω'| ≤ (0.6 : ℝ) + (Z ω') ^ 2 / (n : ℝ)` |
| 8 | Mainline + track-d preserved | **VERIFIED** | `git status --short` clean, no mainline file mutations | Track C work pushed only to `track-c-1dkmt` |
| 9 | `lake exe cache get` cache fresh | **VERIFIED** | `.lake/build` mtime > manifest mtime | Skipped per process Q4 ii cache-freshness rule |
| 10 | Carter-Pollard 2004 polynomial bound proof structure | **VERIFIED — math content** | Carter-Pollard 2004 Thm 1 (Ann. Statist. 32); Bretagnolle-Massart 1989 appendix | Standard literature; per-step polynomial form `|B - n - Z| ≤ A + C · Z²/n` correct (NOT `O(log n)`, anti-#14-regression) |

All 10 rows VERIFIED. No new misframings caught (cumulative ledger remains 8).

## §2. Mathlib API surface for TC7 priorities

### §2.1. T2.1 — Mills `_pos` close (P=0.85, ~15-25 LOC)

Closure recipe:
* `gaussianPDFReal_pos 0 1 x (by norm_num : (1:ℝ≥0) ≠ 0) : 0 < gaussianPDFReal 0 1 x`
  — at `Mathlib/Probability/Distributions/Gaussian/Real.lean:62`.
* `gaussianPDFReal_nonneg μ v x : 0 ≤ gaussianPDFReal μ v x`
  — at `Mathlib/Probability/Distributions/Gaussian/Real.lean:67`.
* `setIntegral_pos_iff_support_of_nonneg_ae` (with support = univ since pdf > 0 everywhere)
  — at `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:594`.
* `Real.volume_Ioi : volume (Ioi a) = ∞` (so positive)
  — at `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean:171`.
* `integrable_gaussianPDFReal 0 1` already used in TC6 truncation — `IntegrableOn` via `.integrableOn`.
* Final: `div_pos (numerator > 0) (denominator > 0)`.

### §2.2. T2.1 — Mills `_antitone` close (P=0.40, ~60-100 LOC)

Closure recipe (derivative argument):
* Define `F : ℝ → ℝ := fun x => ∫ t in Ioi x, gaussianPDFReal 0 1 t`.
* `HasDerivAt F (-gaussianPDFReal 0 1 x) x`: from `integral_Ioi_of_hasDerivAt_of_tendsto` reversed, or `intervalIntegral.integral_hasDerivAt_left` after rewriting `F(x) = ∫_x^∞ φ = 1 - ∫_{-∞}^x φ`. Concretely: use FTC for `Ioi`-integrals from `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean` — already imported in `GaussianMillsRatio.lean`.
  * **Workaround**: Use the identity `F(x) = 1 - G(x)` where `G(x) = ∫ t in Iic x, gaussianPDFReal 0 1 t`. Then `G' = gaussianPDFReal 0 1 x` by FTC for Lebesgue (continuous integrand), and `F' = -G'`.
* `HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x`: via the explicit derivative of `c · exp(-t²/2)` as `c · exp(-t²/2) · (-t)`, identical to `gaussianTailFirstMomentEq`'s `hderivG` chain (already in `GaussianMillsRatio.lean:126-149`, reusable as a private lemma if hoisted).
* Quotient rule `HasDerivAt.div`: `m'(x) = (F'(x) · φ(x) - F(x) · φ'(x)) / φ(x)²`.
* Algebraic simplification: `m'(x) = -1 + x · m(x)`.
* Truncation: `gaussianMillsRatioReal_truncation` (TC6 Full) gives `m(x) ≤ 1/x` for `x > 0`, so `x · m(x) ≤ 1`, so `m'(x) ≤ 0`.
* Lift to monotonicity: `antitoneOn_of_deriv_nonpos convex_Ioi` ...
  — `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:478`.

**Risk:** the FTC for Ioi-integrals applied symmetrically (i.e. `F'(x) = -φ(x)`) requires a clean formulation. Mathlib's `integral_Ioi_of_hasDerivAt_of_tendsto` (used in TC6) is one direction; we need either the other, or to go via `Iic`.

### §2.3. T2.2 — Real-Beta close (P=0.50, ~80-150 LOC)

Closure recipe (real-to-complex bridge):
* `Complex.betaIntegral u v = ∫ x : ℝ in 0..1, (x:ℂ) ^ (u-1) * (1 - (x:ℂ)) ^ (v-1)`
  — at `Beta.lean:60`.
* For `a, b : ℝ` with `a, b > 0`: `Complex.betaIntegral (a:ℂ) (b:ℂ) = ((realBeta a b) : ℂ)` via `IntervalIntegral.integral_ofReal` (or analogous coercion through `(↑·)` linearity of `intervalIntegral`).
  * **Subtle**: the `cpow` and `rpow` integrand correspondence requires `(x:ℝ).toComplex ^ (u-1) = ((x ^ (u.re - 1) : ℝ) : ℂ)` when `u = (a : ℂ)` with `a` real and `x ∈ (0, 1)`. This needs `Complex.ofReal_cpow_of_imp` or explicit `Real.rpow_def`.
* `Complex.betaIntegral_eq_Gamma_mul_div (a:ℂ) (b:ℂ) (ha) (hb) : betaIntegral (a:ℂ) (b:ℂ) = Gamma (a:ℂ) * Gamma (b:ℂ) / Gamma ((a:ℂ) + (b:ℂ))`.
* `Complex.Gamma_ofReal : ∀ (s : ℝ), Gamma ((s:ℂ)) = ((Real.Gamma s) : ℂ)`
  — at `Beta.lean:433` (referenced in proofs).
* Final algebra: equate real parts.

**Risk:** the integrand-coercion step is genuinely fiddly; `Complex.cpow` of a real positive base may not unfold cleanly to `Real.rpow` without a positivity hypothesis on `(x:ℂ).re` and `Complex.cpow_def_of_re_pos` — needs careful Mathlib API hunt mid-implementation.

### §2.4. T2.2 — Stirling Robbins close (P=0.05, ~120-200 LOC)

**Mathlib explicitly comments at `Stirling.lean:264`, `:280`**: "Sharper bounds due to Robbins are available, but are not yet formalised."

Closure path (full Robbins from scratch):
1. Refine `Stirling.stirlingSeq'_antitone` into a quantitative rate via the Robbins log-correction
   `log stirlingSeq n - 1/(12n)` (also antitone in n, by Robbins' classical argument
   bounding the trapezoidal-rule remainder of `∑ log k`).
2. From the quantitative rate, derive `stirlingSeq n ≤ stirlingSeq ∞ · exp(1/(12n)) = √π · exp(1/(12n))`.
3. Unfold `stirlingSeq n = n! / (√(2n) · (n/e)^n)` to get the desired form.

This is ~120-200 LOC of genuine Stirling-series machinery, with a non-trivial trapezoidal-remainder estimate. **TC7 P=0.05 single-round.** Candidate for TC8+ deferral or partial Stub-refinement (e.g. provide signature for the log-correction antitone step).

### §2.5. T2.3 — Carter-Pollard polynomial bound assembly (P=0.20, ~150-300 LOC)

Closure structure (Carter-Pollard 2004 Thm 1):
1. Comonotonic coupling `q_B`, `q_Z` on `Ω' = ℝ` with `μ' = volume.restrict (Ioc 0 1)` — **Full, TC4 Path A retained**.
2. Pointwise bound `|q_B(ω') - n - q_Z(ω')| ≤ 0.6 + (q_Z ω')² / n` for `ω' ∈ Ioo 0 1`:
   * Case (tail): `|q_Z(ω')| ≥ √(2n log(1/min(ω', 1-ω')))` (large deviations of Gaussian quantile).
     Use Mills truncation (TC6 ✅) + Stirling (TC7 partial) for binomial tail.
   * Case (bulk): `|q_Z(ω')| < √(2n log(...))`. Use Stirling Robbins (sharp, TC7 likely Stub) +
     real-Beta moments (TC7 if T2.2 lands).
3. `∀ᵐ` lift on `volume.restrict (Ioc 0 1)`: trivial since the bound is provable for all `ω' ∈ Ioo 0 1`,
   and `Ioc 0 1 \ Ioo 0 1 = {1}` is a null set.

**Composition dependencies on TC7 deliverables:**
| Sub-component | Required for | Available? |
|---|---|---|
| Mills truncation | tail case | ✅ TC6 |
| Mills positivity | tail-bound positivity | TC7 T2.1 priority A |
| Mills antitone | tail-bound monotonicity in scale | TC7 T2.1 priority B |
| Stirling explicit (looser form `factorial_le_stirling`) | binomial-coef bounds | ✅ TC6 (already Full at `StirlingTwoSided.lean:62`) |
| Stirling Robbins | sharp bulk-case bound | TC7 T2.2 (Stub-only realistic) |
| Real-Beta-Gamma | binomial-moment integrals | TC7 T2.2 priority C |

**Realistic TC7 outcome:** if Mills `_pos` lands (P=0.85) + Mills `_antitone` lands (P=0.40) + Real-Beta lands (P=0.50), the tail case of Carter-Pollard becomes provable; the bulk case still blocks on Stirling Robbins. A **partial close** (tail only, with a sub-sub-sorry for the bulk case) is realistic. Full Carter-Pollard close in TC7 has P~0.10.

## §3. Honesty / framing

* **No new misframings.** T1.1 audit confirms all TC6 deliverables intact and brief Mathlib citations correct.
* **Stirling Robbins gap is BINDING.** Mathlib explicitly disclaims sharp Robbins; closing it from scratch is 120-200 LOC of trapezoidal-remainder analysis, well outside a single TC7 budget. T2.2 Robbins Stub will remain with refined diagnostic, NOT Full close.
* **Mills `_antitone` derivative argument is the highest-leverage prelude.** Closing it unblocks the bulk-case scale-monotonicity argument in Carter-Pollard.
* **Carter-Pollard partial close (tail case)** is the realistic T2.3 target if T2.1 + T2.2 partial deliverables land.

## §4. TC7 plan (revised post-audit)

| Sub-task | Target | Priority | P(Full) |
|---|---|---|---|
| T2.1A | `gaussianMillsRatioReal_pos` | High | 0.85 |
| T2.1B | `gaussianMillsRatioReal_antitone` | High | 0.40 |
| T2.2A | `realBeta_eq_Gamma_ratio` | Medium | 0.50 |
| T2.2B | `factorial_le_stirling_robbins` Full | LOW (Mathlib gap binding) | 0.05 |
| T2.3 | Carter-Pollard polynomial pointwise bound | Stretch | 0.10 (Full) / 0.50 (tail-case partial) |
| T2.4 | Build + status doc + push | Mandatory | 0.95 |

**Joint mandatory floor (T1.1 + T2.1 with at least 1 of A/B Full + T2.2 with at least 1 of A/B addressed (close OR refined diagnostic) + T2.4):** ~0.75.

## §5. Sequencing

1. T2.1A first (cheap, high P, unblocks confidence).
2. T2.1B second (derivative chain — moderate cost, high payoff for T2.3).
3. T2.2A third (real-Beta bridge — moderate cost, modest payoff).
4. T2.2B refined diagnostic (Mathlib gap binding; refresh Stub docstring with TC7 evidence).
5. T2.3 if budget remains — attempt tail-case partial close OR ship Carter-Pollard scope diagnostic for TC8.
6. T2.4 build + status + push.
