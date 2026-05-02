/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Mills ratio for the standard Gaussian (Track C round 5 infrastructure)

The Mills ratio of the standard Gaussian distribution is the function
`m(x) = (1 - Φ(x)) / φ(x)` where `Φ` is the standard-normal CDF and
`φ` is its density. It is the workhorse of explicit Gaussian-tail
bookkeeping.

Mathlib pin status (`mathlib4 @ 25ce633136`, verified TC5 T1.1):
  * `Real.gaussianPDFReal 0 1` ✅ (`Mathlib/Probability/Distributions/Gaussian/Real.lean:49`),
  * `Real.gaussianCDF` ❌ (not packaged),
  * `Real.gaussianMillsRatio` / `MillsRatio` ❌ (not packaged anywhere
    in `.lake/packages/mathlib/Mathlib/`).

This file provides a *local* `gaussianMillsRatioReal` definition via
the integral form
```
m(x) = (∫ t in Ioi x, gaussianPDFReal 0 1 t) / gaussianPDFReal 0 1 x
```
together with three classical lemmas in TAG'd-Stub form, to be filled
in TC6+ when the polynomial-bound assembly for `tusnady_base_polynomial`
needs them. This avoids the cyclic blocker that the *closure* of the
Tusnády polynomial bound depends on Mills ratio while the Mills ratio
itself was unavailable in pinned Mathlib.

## Lemmas (TC6+ closure targets)

* `gaussianMillsRatioReal_pos`: positivity on `(0, ∞)`.
* `gaussianMillsRatioReal_truncation`: classical bound `m(x) ≤ 1 / x`
  for `x > 0` (Feller Vol. 2 §VII.1; standard proof via the comparison
  `e^{-t²/2} ≤ (t/x) e^{-t²/2}` for `t ≥ x` and explicit integration).
* `gaussianMillsRatioReal_antitone`: monotonicity (the Mills ratio is
  decreasing on `(0, ∞)`; standard proof via derivative analysis or
  direct comparison).

These are the three building blocks Carter–Pollard 2004 use to envelope
the Gaussian tail in the proof of Tusnády's polynomial inequality.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology NNReal

/-- **Standard-Gaussian Mills ratio.**

For a real number `x`, the Mills ratio of the standard Gaussian
distribution `N(0, 1)` is `m(x) = (1 - Φ(x)) / φ(x)`, encoded here
directly as the *integral form*
`(∫ t in Ioi x, gaussianPDFReal 0 1 t) / gaussianPDFReal 0 1 x`.
This is well-defined for all real `x` (positive at every `x ∈ ℝ`
since `gaussianPDFReal 0 1 x > 0` everywhere when variance is `1 ≠ 0`,
and the numerator is the integral of a positive-everywhere measurable
function over a non-empty open set).

The integral form is chosen because pinned Mathlib lacks
`Real.gaussianCDF`; defining Mills via `(1 - Φ) / φ` would require
introducing the CDF first. The integral form is mathematically
equivalent and matches Feller Vol. 2 §VII.1's notation. -/
noncomputable def gaussianMillsRatioReal (x : ℝ) : ℝ :=
  (∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) / gaussianPDFReal 0 1 x

/-- **Positivity of the Mills ratio on `(0, ∞)`.**

For `x > 0`, `gaussianMillsRatioReal x > 0`. Standard fact: numerator
is the integral of `gaussianPDFReal 0 1` (positive everywhere when
variance `1 ≠ 0`) over `Ioi x` (non-empty Lebesgue-positive set), hence
strictly positive; denominator is `gaussianPDFReal 0 1 x > 0`; quotient
of positives is positive. -/
theorem gaussianMillsRatioReal_pos {x : ℝ} (_hx : 0 < x) :
    0 < gaussianMillsRatioReal x := by
  -- TAG[TrackC-Layer3-Mills-positivity]: TC6+ close target.
  -- Closure recipe (~15-25 LOC):
  --   * `setIntegral_pos` on Ioi x with positive integrand
  --     (gaussianPDFReal 0 1 > 0 from Mathlib `gaussianPDFReal_pos`),
  --   * div positivity from `gaussianPDFReal_pos 0 1 x`.
  sorry

/-- **Closed form for the first moment of the standard Gaussian on `(x, ∞)`.**

For all real `x`, `∫ t in Ioi x, t · gaussianPDFReal 0 1 t = gaussianPDFReal 0 1 x`.

Standard fact via FTC-2: the function `t ↦ -gaussianPDFReal 0 1 t` has derivative
`t ↦ t · gaussianPDFReal 0 1 t` and tends to `0` at `+∞`, so by
`integral_Ioi_of_hasDerivAt_of_tendsto`:
`∫ t in Ioi x, t · gaussianPDFReal 0 1 t = 0 - (-gaussianPDFReal 0 1 x) = gaussianPDFReal 0 1 x`. -/
private lemma gaussianTailFirstMomentEq (x : ℝ) :
    ∫ t in Set.Ioi x, t * gaussianPDFReal 0 1 t = gaussianPDFReal 0 1 x := by
  set c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hc_def
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]; positivity
  -- gaussianPDFReal 0 1 t = c * exp(-t^2/2)
  have hpdf_unfold : ∀ t : ℝ, gaussianPDFReal 0 1 t = c * Real.exp (-t ^ 2 / 2) := by
    intro t
    show (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
         Real.exp (-(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) = c * Real.exp (-t ^ 2 / 2)
    rw [hc_def, NNReal.coe_one]
    ring_nf
  -- Antiderivative-friendly form for F
  let G : ℝ → ℝ := fun s => -(c * Real.exp (-s ^ 2 / 2))
  have hF_eq : (fun t => -gaussianPDFReal 0 1 t) = G := by
    funext s; show -gaussianPDFReal 0 1 s = -(c * Real.exp (-s ^ 2 / 2))
    rw [hpdf_unfold s]
  -- HasDerivAt for G
  have hderivG : ∀ t : ℝ, HasDerivAt G (t * gaussianPDFReal 0 1 t) t := by
    intro t
    -- d/dt (s^2) = 2*t at t
    have h_sq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    -- d/dt (-s^2) = -(2*t)
    have h_negsq : HasDerivAt (fun s : ℝ => -s ^ 2) (-(2 * t)) t := h_sq.neg
    -- d/dt (-s^2/2) = -(2*t)/2 = -t
    have h_in : HasDerivAt (fun s : ℝ => -s ^ 2 / 2) (-t) t := by
      have := h_negsq.div_const 2
      have heq : -(2 * t) / 2 = -t := by ring
      rw [heq] at this
      exact this
    -- d/dt exp(-s^2/2) = exp(-t^2/2) * (-t)
    have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2))
        (Real.exp (-t ^ 2 / 2) * (-t)) t := h_in.exp
    -- d/dt (c * exp(-s^2/2)) = c * (exp(-t^2/2) * (-t))
    have h_cexp : HasDerivAt (fun s : ℝ => c * Real.exp (-s ^ 2 / 2))
        (c * (Real.exp (-t ^ 2 / 2) * (-t))) t := h_exp.const_mul c
    -- d/dt G(s) = -(c * (exp(-t^2/2) * (-t))) = c * t * exp(-t^2/2) = t * gaussianPDFReal 0 1 t
    have h_neg : HasDerivAt G (-(c * (Real.exp (-t ^ 2 / 2) * (-t)))) t := h_cexp.neg
    have hderiv_eq : -(c * (Real.exp (-t ^ 2 / 2) * (-t))) = t * gaussianPDFReal 0 1 t := by
      rw [hpdf_unfold t]; ring
    rw [← hderiv_eq]; exact h_neg
  -- G → 0 at +∞
  have hG_tendsto : Tendsto G atTop (nhds 0) := by
    -- exp(-t²/2) → 0
    have hexp_tendsto : Tendsto (fun t : ℝ => Real.exp (-t ^ 2 / 2)) atTop (nhds 0) := by
      -- -t²/2 → -∞ at +∞
      have h_sq_top : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
        tendsto_pow_atTop (by norm_num : 2 ≠ 0)
      -- -t²/2 = (-(1/2)) * t², and (-(1/2)) < 0 so const_mul_atTop_of_neg
      have h_neg_half_sq : Tendsto (fun t : ℝ => -(1 / 2 : ℝ) * t ^ 2) atTop atBot :=
        h_sq_top.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)
      have heq : (fun t : ℝ => -(1 / 2 : ℝ) * t ^ 2) = (fun t : ℝ => -t ^ 2 / 2) := by
        funext t; ring
      rw [heq] at h_neg_half_sq
      exact Real.tendsto_exp_atBot.comp h_neg_half_sq
    have h_c_exp : Tendsto (fun t : ℝ => c * Real.exp (-t ^ 2 / 2)) atTop (nhds (c * 0)) :=
      hexp_tendsto.const_mul c
    have h_neg : Tendsto G atTop (nhds (-(c * 0))) := h_c_exp.neg
    simpa using h_neg
  -- Integrability of t * gaussianPDFReal 0 1 t on Ioi x
  have hint_full : Integrable (fun t : ℝ => t * gaussianPDFReal 0 1 t) := by
    have h1 : Integrable (fun t : ℝ => t * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 : Integrable (fun t : ℝ => c * (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2))) :=
      h1.const_mul c
    apply h2.congr
    filter_upwards with t
    rw [hpdf_unfold t]
    have hexp_eq : Real.exp (-(1 / 2 : ℝ) * t ^ 2) = Real.exp (-t ^ 2 / 2) := by
      congr 1; ring
    rw [hexp_eq]; ring
  have hint : IntegrableOn (fun t : ℝ => t * gaussianPDFReal 0 1 t) (Set.Ioi x) :=
    hint_full.integrableOn
  -- Apply FTC-2 with G as antiderivative
  have hcont : ContinuousWithinAt G (Set.Ici x) x :=
    (hderivG x).continuousAt.continuousWithinAt
  have hres :=
    integral_Ioi_of_hasDerivAt_of_tendsto hcont
      (fun t _ => hderivG t) hint hG_tendsto
  -- hres : ∫ t in Ioi x, t * gaussianPDFReal 0 1 t = 0 - G x
  rw [hres]
  show 0 - G x = gaussianPDFReal 0 1 x
  show 0 - (-(c * Real.exp (-x ^ 2 / 2))) = gaussianPDFReal 0 1 x
  rw [hpdf_unfold x]; ring

/-- **Classical Mills truncation bound.**

For `x > 0`, `gaussianMillsRatioReal x ≤ 1 / x`. Equivalently,
`∫_x^∞ φ(t) dt ≤ φ(x) / x`. Standard Feller-style proof:
`e^{-t²/2} ≤ (t/x) e^{-t²/2}` for `t ≥ x` (since `1 ≤ t/x`),
then `∫_x^∞ (t/x) e^{-t²/2} dt = (1/x) [-e^{-t²/2}]_x^∞ = e^{-x²/2}/x`,
divided through by `√(2π) · φ(x) = e^{-x²/2}` gives the claim. -/
theorem gaussianMillsRatioReal_truncation {x : ℝ} (hx : 0 < x) :
    gaussianMillsRatioReal x ≤ 1 / x := by
  have hφx_pos : 0 < gaussianPDFReal 0 1 x :=
    gaussianPDFReal_pos 0 1 x (by norm_num)
  -- Integrability of pdf and t*pdf on Ioi x
  have hint_φ : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi x) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hint_xφ : IntegrableOn (fun t : ℝ => x * gaussianPDFReal 0 1 t)
      (Set.Ioi x) :=
    hint_φ.const_mul x
  have hint_tφ : IntegrableOn (fun t : ℝ => t * gaussianPDFReal 0 1 t)
      (Set.Ioi x) := by
    have h1 : Integrable (fun t : ℝ => t * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 : Integrable (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2))) := h1.const_mul _
    have hfull : Integrable (fun t : ℝ => t * gaussianPDFReal 0 1 t) := by
      apply h2.congr
      filter_upwards with t
      show (Real.sqrt (2 * Real.pi))⁻¹ * (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) =
           t * gaussianPDFReal 0 1 t
      show (Real.sqrt (2 * Real.pi))⁻¹ * (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) =
           t * ((Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
                Real.exp (-(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))))
      rw [NNReal.coe_one]
      ring_nf
    exact hfull.integrableOn
  -- Pointwise: x * φ t ≤ t * φ t for t ∈ Ioi x
  have hpw : ∀ t ∈ Set.Ioi x, x * gaussianPDFReal 0 1 t ≤ t * gaussianPDFReal 0 1 t := by
    intro t ht
    have ht' : x ≤ t := le_of_lt ht
    exact mul_le_mul_of_nonneg_right ht' (gaussianPDFReal_nonneg 0 1 t)
  -- Lift to integral
  have hmono : ∫ t in Set.Ioi x, x * gaussianPDFReal 0 1 t ≤
               ∫ t in Set.Ioi x, t * gaussianPDFReal 0 1 t :=
    setIntegral_mono_on hint_xφ hint_tφ measurableSet_Ioi hpw
  -- Pull constant + use moment identity
  rw [integral_const_mul, gaussianTailFirstMomentEq] at hmono
  -- hmono : x * (∫ t in Ioi x, gaussianPDFReal 0 1 t) ≤ gaussianPDFReal 0 1 x
  -- Goal: gaussianMillsRatioReal x ≤ 1 / x
  unfold gaussianMillsRatioReal
  rw [div_le_div_iff₀ hφx_pos hx]
  linarith

/-- **Monotonicity of the Mills ratio on `(0, ∞)`.**

For `0 < x ≤ y`, `gaussianMillsRatioReal y ≤ gaussianMillsRatioReal x`.
The Mills ratio is decreasing on `(0, ∞)` — a standard fact used in
Carter–Pollard 2004 §3 to envelope the Gaussian tail in the
binomial-Gaussian-pairing comparison.

Standard proof: differentiate `m(x) · φ(x) = 1 - Φ(x)`; obtain
`m'(x) · φ(x) + m(x) · φ'(x) = -φ(x)`, hence
`m'(x) = -1 - m(x) · (φ'(x) / φ(x)) = -1 + x · m(x)`. Then
`m'(x) ≤ 0` iff `x · m(x) ≤ 1`, which is the truncation bound
above. So monotonicity follows from `gaussianMillsRatioReal_truncation`
plus a sign-of-derivative argument. -/
theorem gaussianMillsRatioReal_antitone {x y : ℝ} (_hx : 0 < x) (_hxy : x ≤ y) :
    gaussianMillsRatioReal y ≤ gaussianMillsRatioReal x := by
  -- TAG[TrackC-Layer3-Mills-antitone]: TC6+ close target.
  -- Closure recipe (~50-80 LOC, depends on truncation closing first):
  --   * derivative formula `m'(x) = x · m(x) - 1` (chain via FTC + product
  --     rule on `m(x) · φ(x) = ∫_x^∞ φ`),
  --   * `gaussianMillsRatioReal_truncation` gives `x · m(x) ≤ 1`, hence
  --     `m'(x) ≤ 0` on Ioi 0,
  --   * `Antitone.of_deriv_nonpos` or analogous to lift derivative-sign
  --     to the function itself.
  -- Composition order: this lemma depends on the truncation bound; close
  -- truncation first, then antitone via derivative argument.
  sorry

end Erdos524.Helpers
