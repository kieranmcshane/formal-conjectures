# Track C round 8 — T1.1 audit (dual close, Mills antitone + Stirling Robbins)

**Read-only audit, opened TC8 round at HEAD `e82a240` (TC7 closure).**

## Cache state

`lake exe cache get`: completed (7753 files unpacked, no fresh downloads).

## Claims Verification Table

| # | Claim | VERIFIED? | Citation | Notes |
|---|-------|-----------|----------|-------|
| 1 | TC7 Mills `_pos` Full preserved | VERIFIED | `Helpers/GaussianMillsRatio.lean:91-112` | Body ends `exact div_pos hnum_pos hφx_pos`; no sorry |
| 2 | TC7 Mills truncation Full preserved | VERIFIED | `Helpers/GaussianMillsRatio.lean:215-257` | Body uses `gaussianTailFirstMomentEq`; no sorry |
| 3 | TC7 Real-Beta Full preserved | VERIFIED | `Helpers/RealBeta.lean` post-TC7 | Don't touch |
| 4 | Mills `_antitone` Stub at line 272 | VERIFIED | `Helpers/GaussianMillsRatio.lean:272-313` | TC7 wrote 6-step recipe in body comment; sorry at 313 |
| 5 | Stirling Robbins Stub at line 224 | VERIFIED | `Helpers/StirlingTwoSided.lean:224-230` | TC7 wrote 4-step recipe in docstring; sorry at 230 |
| 6 | Mathlib FTC-Ioi adapter | PARTIAL | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:755` (`integral_hasDerivAt_left`) + `Basic.lean:1082` (`integral_Iic_add_Ioi`) | No direct Ioi-derivative lemma; combine `integral_hasDerivAt_left` (interval form) + local splitting via `Ioi u = Ioc u M ⊔ Ioi M` (using `setIntegral_union`) and `HasDerivAt.congr_of_eventuallyEq` |
| 7 | Mathlib `Antitone.of_deriv_nonpos` family | VERIFIED | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:478` (`antitoneOn_of_deriv_nonpos`) | Signature: `Convex ℝ D + ContinuousOn f D + DifferentiableOn ℝ f (interior D) + ∀ x ∈ interior D, deriv f x ≤ 0 → AntitoneOn f D` |
| 8 | Mathlib Wallis product API | VERIFIED but NOT NEEDED | `Mathlib/Analysis/Real/Pi/Wallis.lean` (full `Wallis.W` API) — used by Mathlib's Stirling proof; for Robbins close direct path uses `log_stirlingSeq_diff_hasSum` (`Stirling.lean:76`) so Wallis is bypassed | Better path than route (c): refine Mathlib's `log_stirlingSeq_diff_le_geo_sum` (line 100) with 1/3 factor extraction → exact `1/(12n(n+1))` Robbins bound directly |
| 9 | Mathlib `tendsto_stirlingSeq_sqrt_pi` available | VERIFIED | `Stirling.lean:228` | Used as limit identification in Step 4 of Robbins close |
| 10 | TC4 + TC5 signatures + Layer 2 + Layer 3 infrastructure preserved | VERIFIED | Per `Helpers/TrackCStatus.md` post-TC7 | No regression |

## Mills `_antitone` close — concrete step plan

Per TC7 6-step recipe in `GaussianMillsRatio.lean:274-307`. Refined for TC8 with verified Mathlib API:

**Step A** — `gaussianPDFReal_hasDerivAt`: extract derivative `-x · gaussianPDFReal 0 1 x`
of the standard-Gaussian PDF, hoist from `gaussianTailFirstMomentEq` proof block.

**Step B** — `gaussianTail_hasDerivAt`: prove
`HasDerivAt (fun u => ∫ t in Ioi u, gaussianPDFReal 0 1 t) (-gaussianPDFReal 0 1 x) x`
via local splitting `Ioi u = Ioc u M ⊔ Ioi M` (M := x + 1) for u in nbhd of x:
1. Show `∀ᶠ u in 𝓝 x, ∫ t in Ioi u, φ t = (∫ t in u..M, φ t) + ∫ t in Ioi M, φ t`.
2. Use `integral_hasDerivAt_left` (`FundThmCalculus.lean:755`) on the interval term.
3. The Ioi M term is constant in u; use `HasDerivAt.add_const`.
4. Transfer via `HasDerivAt.congr_of_eventuallyEq`.

**Step C** — Quotient rule: `HasDerivAt.div` with positive denominator
`gaussianPDFReal 0 1 x > 0`, derivative formula `-1 + x · m(x)`.

**Step D** — Sign: from `gaussianMillsRatioReal_truncation` (TC6, gives `m(x) ≤ 1/x`):
`x · m(x) ≤ 1`, hence `m'(x) ≤ 0`.

**Step E** — Lift to `AntitoneOn` via `antitoneOn_of_deriv_nonpos` on
`Set.Ioi 0` (convex by `convex_Ioi 0`). Then specialize to `x ≤ y` both `> 0`.

LOC estimate: ~150-200 LOC.

## Stirling Robbins close — strategy choice

**Route choice**: Bypass Wallis route (c) — Mathlib's Wallis product is consumed
*internally* by `tendsto_stirlingSeq_sqrt_pi`, so a Wallis-derivation-route would
re-prove what Mathlib already gives us. **Better route**: refine the
`log_stirlingSeq_diff` bound with the `1/(2k+3)` factor extracted (Mathlib bounds
it by 1; we extract 1/3) to get the *exact* Robbins bound `1/(12n(n+1))`.

Closure plan:

**Step 1** — `log_stirlingSeq_diff_le_robbins`: prove
`log(stirlingSeq (n+1)) - log(stirlingSeq (n+2)) ≤ 1/(12(n+1)(n+2))`.
Mirror Mathlib's `log_stirlingSeq_diff_le_geo_sum` proof but use bound
`1/(2(k+1)+1) ≤ 1/3` for k ≥ 0 (instead of `≤ 1`). Geometric sum
`(1/3) · q² / (1-q²)` with `q := 1/(2n+3)` gives `(1/3) · 1/((2n+3)² - 1) =
1/(3 · 4(n+1)(n+2)) = 1/(12(n+1)(n+2))`. ~50-80 LOC.

**Step 2** — `robbinsCorr_antitone`: define
`robbinsCorr n := log(stirlingSeq (n+1)) - 1/(12·(n+1))`. Prove
`Monotone robbinsCorr` (i.e. `robbinsCorr n ≤ robbinsCorr (n+1)`) via Step 1:
`log(stirlingSeq (n+2)) - log(stirlingSeq (n+1)) ≥ 1/(12(n+2)) - 1/(12(n+1))
= -1/(12(n+1)(n+2))`, equivalent to Step 1. ~30-50 LOC.

**Step 3** — `robbinsCorr_tendsto`: from `tendsto_stirlingSeq_sqrt_pi`
(`Stirling.lean:228`) and `1/(12·(n+1)) → 0`:
`robbinsCorr → log √π = (1/2) log π`. ~20-30 LOC.

**Step 4** — `robbinsCorr_le_limit`: monotone increasing + tends to limit
implies `robbinsCorr n ≤ (1/2) log π` for all n. Use
`Monotone.tendsto_iSup` or directly: for any n, `robbinsCorr n ≤ robbinsCorr (n+k)`
for all k, taking k → ∞ gives the limit. Or use `Monotone.ge_of_tendsto`. ~20-30 LOC.

**Step 5** — Unfold to factorial form: `log(stirlingSeq (n+1)) ≤ (1/2) log π + 1/(12(n+1))`
⟹ `stirlingSeq (n+1) ≤ √π · exp(1/(12(n+1)))` ⟹
`(n+1)! ≤ √(2(n+1)) · ((n+1)/e)^(n+1) · √π · exp(1/(12(n+1))) =
√(2π(n+1)) · ((n+1)/e)^(n+1) · exp(1/(12(n+1)))`. ~30-50 LOC.

**Step 6** — Specialise from `n+1` indexing to `n ≥ 1`: write target `n` as
`(n-1)+1`, apply Step 5 with `n-1`. ~20-30 LOC.

LOC estimate: ~170-270 LOC. Within `~250-450 LOC` budget.

## Sub-checkpointing

- T+0:30: ✅ T1.1 audit (this doc).
- T+2:00: T2.1 Mills antitone Full or diagnostic.
- T+3:30: T2.2 Stirling Robbins Full or diagnostic.
- T+4:00: T2.3 build + push.
- Hard-stop T+4:30.

## Confidence updates

| Outcome | P(Full) prior | P(Full) posterior |
|---------|---------------|--------------------|
| T1.1 audit | 0.90 | 1.00 (complete) |
| T2.1 Mills `_antitone` Full | 0.40 | 0.50 (recipe verified, all Mathlib lemmas located) |
| T2.2 Stirling Robbins Full | 0.30 | 0.45 (better path than Wallis route — refine Mathlib geo-sum proof with 1/3 factor) |
| T2.3 build + push | 0.95 | 0.95 |

Joint P(both Full): ~0.23 (up from 0.20).
P(at least one Full): ~0.62 (up from 0.55).
