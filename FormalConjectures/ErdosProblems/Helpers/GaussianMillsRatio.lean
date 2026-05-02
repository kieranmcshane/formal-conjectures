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

open MeasureTheory ProbabilityTheory
open scoped Real

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

/-- **Classical Mills truncation bound.**

For `x > 0`, `gaussianMillsRatioReal x ≤ 1 / x`. Equivalently,
`∫_x^∞ φ(t) dt ≤ φ(x) / x`. Standard Feller-style proof:
`e^{-t²/2} ≤ (t/x) e^{-t²/2}` for `t ≥ x` (since `1 ≤ t/x`),
then `∫_x^∞ (t/x) e^{-t²/2} dt = (1/x) [-e^{-t²/2}]_x^∞ = e^{-x²/2}/x`,
divided through by `√(2π) · φ(x) = e^{-x²/2}` gives the claim. -/
theorem gaussianMillsRatioReal_truncation {x : ℝ} (_hx : 0 < x) :
    gaussianMillsRatioReal x ≤ 1 / x := by
  -- TAG[TrackC-Layer3-Mills-truncation]: TC6+ close target.
  -- Closure recipe (~40-60 LOC):
  --   * pointwise `gaussianPDFReal 0 1 t ≤ (t / x) * gaussianPDFReal 0 1 t`
  --     for `t ≥ x` (follows from `1 ≤ t/x` and pdf-nonneg),
  --   * monotonicity of `setIntegral` on `Ioi x` to lift pointwise to
  --     integral inequality,
  --   * exact evaluation of `∫ t in Ioi x, t * exp (-t²/2)` via the
  --     antiderivative `t ↦ -exp(-t²/2)`, requires
  --     `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`
  --     or analogous Mathlib API.
  -- Mathlib pin gap: explicit `setIntegral_exp_neg_sq_div_self_Ioi` not
  -- packaged. Either prove inline (~20-30 LOC) or extract via
  -- `integral_exp_neg_sq` family + change of variables.
  sorry

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
