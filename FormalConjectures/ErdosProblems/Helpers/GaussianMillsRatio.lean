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
of positives is positive. (TC7 T2.1A close.) -/
theorem gaussianMillsRatioReal_pos {x : ℝ} (_hx : 0 < x) :
    0 < gaussianMillsRatioReal x := by
  unfold gaussianMillsRatioReal
  have hφx_pos : 0 < gaussianPDFReal 0 1 x :=
    gaussianPDFReal_pos 0 1 x (by norm_num)
  have hint : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi x) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi x)] gaussianPDFReal 0 1 :=
    Filter.Eventually.of_forall (fun t => gaussianPDFReal_nonneg 0 1 t)
  have hsupp : Function.support (gaussianPDFReal 0 1) = Set.univ := by
    ext t
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (gaussianPDFReal_pos 0 1 t (by norm_num)).ne'
  have hsupp_inter :
      Function.support (gaussianPDFReal 0 1) ∩ Set.Ioi x = Set.Ioi x := by
    rw [hsupp, Set.univ_inter]
  have hvol_Ioi : 0 < volume (Set.Ioi x) := by
    rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
  have hnum_pos : 0 < ∫ t in Set.Ioi x, gaussianPDFReal 0 1 t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hae hint, hsupp_inter]
    exact hvol_Ioi
  exact div_pos hnum_pos hφx_pos

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

/-- **Derivative of the standard-Gaussian PDF.**

For all real `x`, `(d/dx) gaussianPDFReal 0 1 x = -x · gaussianPDFReal 0 1 x`.
Standard fact via the chain rule applied to `c · exp(-x²/2)` with
`c := (√(2π))⁻¹`. (TC8 helper for Mills antitone close.) -/
private lemma gaussianPDFReal_zero_one_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  set c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hc_def
  have hpdf_unfold : ∀ t : ℝ, gaussianPDFReal 0 1 t = c * Real.exp (-t ^ 2 / 2) := by
    intro t
    show (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
         Real.exp (-(t - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) = c * Real.exp (-t ^ 2 / 2)
    rw [hc_def, NNReal.coe_one]
    ring_nf
  have h_sq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h_in : HasDerivAt (fun s : ℝ => -s ^ 2 / 2) (-x) x := by
    have h1 := (h_sq.neg).div_const 2
    have heq2 : -(2 * x) / 2 = -x := by ring
    rw [heq2] at h1
    exact h1
  have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2 / 2))
      (Real.exp (-x ^ 2 / 2) * (-x)) x := h_in.exp
  have h_cexp : HasDerivAt (fun s : ℝ => c * Real.exp (-s ^ 2 / 2))
      (c * (Real.exp (-x ^ 2 / 2) * (-x))) x := h_exp.const_mul c
  have hderiv_eq : c * (Real.exp (-x ^ 2 / 2) * (-x)) = -x * gaussianPDFReal 0 1 x := by
    rw [hpdf_unfold x]; ring
  rw [← hderiv_eq]
  exact h_cexp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => hpdf_unfold t)

/-- **Derivative of the standard-Gaussian tail integral.**

For all real `x`, the function `u ↦ ∫ t in Ioi u, gaussianPDFReal 0 1 t`
has derivative `-gaussianPDFReal 0 1 x` at `x`.

Proof via local splitting: pick `M := x + 1`. For `u` in a neighborhood
of `x` with `u ≤ M`, `Ioi u = Ioc u M ⊔ Ioi M` (disjoint), so
`∫ t in Ioi u, φ t = ∫ t in u..M, φ t + ∫ t in Ioi M, φ t`. The
interval-integral term has derivative `-φ x` at `x` by
`integral_hasDerivAt_left`; the `Ioi M` term is constant in `u`.
Transfer via `HasDerivAt.congr_of_eventuallyEq`. (TC8 helper.) -/
private lemma gaussianTail_hasDerivAt (x : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ t in Set.Ioi u, gaussianPDFReal 0 1 t)
      (-gaussianPDFReal 0 1 x) x := by
  set M : ℝ := x + 1 with hM_def
  have hxM : x < M := by simp [hM_def]
  set φ : ℝ → ℝ := gaussianPDFReal 0 1 with hφ_def
  have hint_φ : Integrable φ := integrable_gaussianPDFReal 0 1
  have hsplit : ∀ u : ℝ, u ≤ M →
      ∫ t in Set.Ioi u, φ t = (∫ t in Set.Ioc u M, φ t) + ∫ t in Set.Ioi M, φ t := by
    intro u huM
    have hdisj : Disjoint (Set.Ioc u M) (Set.Ioi M) := by
      rw [Set.disjoint_left]
      rintro t ⟨_, htM⟩ htM'
      exact absurd htM' (not_lt_of_ge htM)
    have hunion : Set.Ioc u M ∪ Set.Ioi M = Set.Ioi u := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      refine ⟨?_, ?_⟩
      · rintro (⟨h1, _⟩ | h2)
        · exact h1
        · exact lt_of_le_of_lt huM h2
      · intro ht
        by_cases h : t ≤ M
        · left; exact ⟨ht, h⟩
        · right; exact lt_of_not_ge h
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi hint_φ.integrableOn hint_φ.integrableOn
  have hev_uM : ∀ᶠ u in nhds x, u ≤ M := by
    have h1 : Set.Iio M ∈ nhds x := IsOpen.mem_nhds isOpen_Iio hxM
    filter_upwards [h1] with u hu using le_of_lt hu
  have hev : (fun u : ℝ => ∫ t in Set.Ioi u, φ t) =ᶠ[nhds x]
      (fun u : ℝ => (∫ t in u..M, φ t) + ∫ t in Set.Ioi M, φ t) := by
    filter_upwards [hev_uM] with u hu
    rw [hsplit u hu, intervalIntegral.integral_of_le hu]
  have hcont_φ_x : ContinuousAt φ x :=
    (gaussianPDFReal_zero_one_hasDerivAt x).continuousAt
  have hsm_φ : StronglyMeasurableAtFilter φ (𝓝 x) volume :=
    (stronglyMeasurable_gaussianPDFReal 0 1).stronglyMeasurableAtFilter
  have h_int_deriv : HasDerivAt (fun u => ∫ t in u..M, φ t) (-φ x) x :=
    intervalIntegral.integral_hasDerivAt_left
      (hint_φ.intervalIntegrable (a := x) (b := M)) hsm_φ hcont_φ_x
  have h_add : HasDerivAt
      (fun u => (∫ t in u..M, φ t) + ∫ t in Set.Ioi M, φ t)
      (-φ x) x := by
    have := h_int_deriv.add_const (∫ t in Set.Ioi M, φ t)
    simpa using this
  exact h_add.congr_of_eventuallyEq hev

/-- **Derivative of the Mills ratio on `(0, ∞)`.**

For `x > 0`, `(d/dx) gaussianMillsRatioReal x = -1 + x · gaussianMillsRatioReal x`.
Quotient rule applied to `m = F / φ` with `F u := ∫ t in Ioi u, φ t`,
`F'(x) = -φ(x)`, `φ'(x) = -x · φ(x)`, `φ(x) > 0`. (TC8 helper.) -/
private lemma gaussianMillsRatioReal_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt gaussianMillsRatioReal (-1 + x * gaussianMillsRatioReal x) x := by
  have hφ_pos : 0 < gaussianPDFReal 0 1 x := gaussianPDFReal_pos 0 1 x (by norm_num)
  have hφ_ne : gaussianPDFReal 0 1 x ≠ 0 := ne_of_gt hφ_pos
  have h_num := gaussianTail_hasDerivAt x
  have h_den := gaussianPDFReal_zero_one_hasDerivAt x
  have h_div := h_num.div h_den hφ_ne
  -- h_div : HasDerivAt
  --   ((fun u => ∫ t in Set.Ioi u, gaussianPDFReal 0 1 t) / gaussianPDFReal 0 1)
  --   ((-φ x * φ x - F x * (-x * φ x)) / φ x ^ 2) x
  -- Goal: HasDerivAt gaussianMillsRatioReal (-1 + x * gaussianMillsRatioReal x) x
  have hfun_eq :
      (fun u => ∫ t in Set.Ioi u, gaussianPDFReal 0 1 t) / gaussianPDFReal 0 1 =
        gaussianMillsRatioReal := by
    funext u
    rfl
  rw [hfun_eq] at h_div
  -- Now h_div has the right function; reconcile derivative values.
  convert h_div using 1
  -- Show: -1 + x * m(x) = (-φ x * φ x - F x * (-x * φ x)) / (φ x)^2
  unfold gaussianMillsRatioReal
  field_simp
  ring

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
plus a sign-of-derivative argument. (TC8 close via
`antitoneOn_of_deriv_nonpos` on `Ioi 0`.) -/
theorem gaussianMillsRatioReal_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    gaussianMillsRatioReal y ≤ gaussianMillsRatioReal x := by
  have hM_anti : AntitoneOn gaussianMillsRatioReal (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · -- ContinuousOn gaussianMillsRatioReal (Ioi 0)
      intro x₀ hx₀
      exact (gaussianMillsRatioReal_hasDerivAt hx₀).continuousAt.continuousWithinAt
    · -- DifferentiableOn ℝ gaussianMillsRatioReal (interior (Ioi 0))
      rw [interior_Ioi]
      intro x₀ hx₀
      exact (gaussianMillsRatioReal_hasDerivAt hx₀).differentiableAt.differentiableWithinAt
    · -- ∀ x ∈ interior (Ioi 0), deriv gaussianMillsRatioReal x ≤ 0
      rw [interior_Ioi]
      intro x₀ hx₀
      have hx₀' : 0 < x₀ := hx₀
      have h_deriv := gaussianMillsRatioReal_hasDerivAt hx₀'
      rw [h_deriv.deriv]
      have htrunc := gaussianMillsRatioReal_truncation hx₀'
      have hx₀_ne : x₀ ≠ 0 := ne_of_gt hx₀'
      have hmm : x₀ * gaussianMillsRatioReal x₀ ≤ x₀ * (1 / x₀) :=
        mul_le_mul_of_nonneg_left htrunc (le_of_lt hx₀')
      rw [mul_one_div, div_self hx₀_ne] at hmm
      linarith
  exact hM_anti hx (lt_of_lt_of_le hx hxy) hxy

end Erdos524.Helpers
