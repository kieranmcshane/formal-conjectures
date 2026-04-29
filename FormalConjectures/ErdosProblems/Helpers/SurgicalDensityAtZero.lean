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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.ErdosProblems.Helpers.EsseenSmoothing

/-!
# Surgical 2-sided density-at-zero bound for normalized Rademacher walks

This file proves the *surgical density-at-zero bound* for a normalized
Rademacher walk

```
  T = (1/σ) ∑_{k=1}^{n} w_k ε_k     ε_k iid Rademacher,  σ² = ∑ w_k² > 0
```

Setting `α_k := |w_k|/σ` (so `∑α_k² = 1`) and the Lyapunov-style ratio
`ρ := ∑α_k³ = ‖w‖_3³/σ³`, we prove that for `ε ∈ [0, 1/2]`,

```
  | P(|T| ≤ ε) − (Φ(ε) − Φ(−ε)) | ≤ 14·ρ.
```

This is a *surgical replacement* in the downstream Q1c chain for a
combination of standalone Esseen smoothing + full Berry–Esseen.

## Paper proof structure (transcribed step-by-step)

Each numbered step in the user-supplied paper proof is encoded as a named
Lean lemma with a (possibly partial) proof.

* **Step 1 — Gaussian baseline**: `gaussian_baseline_upper`,
  `gaussian_baseline_lower`.
* **Step 2 — Fejér kernel facts**: re-uses lemmas from
  `EsseenSmoothing.lean`.
* **Step 3 — Self-contained smoothing inequality**: `smoothing_inequality`.
* **Step 4 — Fourier representation of `Δ * K_M`**:
  `smoothed_diff_fourier_repr`, `smoothed_diff_sup_le_charFun_integral`.
* **Step 5 — Characteristic-function comparison**:
  - small-`t` regime:   `cf_comparison_small_t`,
  - medium-`t` regime:  `cf_comparison_medium_t`,
  - global integral:    `cf_integral_total_bound`.
* **Step 6 — Kolmogorov-distance bound**: `kolmogorov_distance_bound`.
* **Step 7 — Surgical bound (final)**: `surgical_density_at_zero`.

## Implementation notes

- `T` is encoded abstractly via its law `T_law : Measure ℝ`. The "Rademacher
  product" structure enters through the explicit characteristic-function
  formula `φ_T(t) = ∏_k cos(α_k t)`, which we package as a hypothesis on
  `charFun T_law`.
- `Φ(x) - Φ(-x)` is encoded as the difference of CDFs of the standard normal
  measure `gaussianReal 0 1`.
- Sub-stubs are placed at micro-Mathlib gaps (each annotated with a
  one-line citation) and at points where Mathlib's API needs explicit
  reconciliation work.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.style.longLine false

namespace Erdos524.Helpers

open Real Set MeasureTheory ProbabilityTheory
open scoped Real

/- ## Setup definitions -/

/-- The normalising variance `σ² := ∑_{k=1}^{n} w_k²` of a finite-weight
Rademacher walk with weights `w_1, …, w_n`. -/
noncomputable def variance (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (w k) ^ 2

/-- The standard deviation `σ := √(∑ w_k²)`. -/
noncomputable def stdDev (w : ℕ → ℝ) (n : ℕ) : ℝ := Real.sqrt (variance w n)

/-- The normalised weight `α_k := |w_k|/σ`. -/
noncomputable def alpha (w : ℕ → ℝ) (n : ℕ) (k : ℕ) : ℝ :=
  |w k| / stdDev w n

/-- The Lyapunov-style ratio
`ρ := ∑ α_k³ = ‖w‖_3³/σ³`. -/
noncomputable def lyapunovRatio (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (alpha w n k) ^ 3

/-- The CF of the normalised Rademacher walk
`T = (1/σ) ∑ w_k ε_k`: explicitly `φ_T(t) = ∏_k cos(α_k t)`. -/
noncomputable def rademacherCharFun (w : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∏ k ∈ Finset.range n, ((Real.cos (alpha w n k * t) : ℝ) : ℂ)

/-- The "abstract" law of the normalised Rademacher walk: any probability
measure `T_law` on `ℝ` with characteristic function equal to
`rademacherCharFun w n`. We work with this packaged hypothesis to avoid
hard-wiring an iid-Rademacher product space into our statements. -/
structure RademacherLaw (w : ℕ → ℝ) (n : ℕ) where
  /-- Underlying law of `T` on `ℝ`. -/
  law : Measure ℝ
  /-- It is a probability measure. -/
  isProb : IsProbabilityMeasure law
  /-- Its characteristic function matches the explicit Rademacher product. -/
  charFun_eq : ∀ t : ℝ, charFun law t = rademacherCharFun w n t

/-- **Standard normal CDF**, `Φ(x) := ∫_{-∞}^x φ`, encoded as the CDF of the
Mathlib `gaussianReal 0 1` measure. -/
noncomputable def gaussianCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf (gaussianReal 0 1) x

/-- **The 2-sided Gaussian probability** `Φ(ε) − Φ(−ε)`. -/
noncomputable def gaussianTwoSided (ε : ℝ) : ℝ := gaussianCDF ε - gaussianCDF (-ε)

/- ## Step 1: Gaussian baseline (elementary) -/

/-- The standard normal density (real-valued). -/
noncomputable def gaussianDensity (x : ℝ) : ℝ :=
  Real.exp (- x ^ 2 / 2) / Real.sqrt (2 * Real.pi)

/-- The peak `φ(0) = 1/√(2π)`. -/
lemma gaussianDensity_zero : gaussianDensity 0 = 1 / Real.sqrt (2 * Real.pi) := by
  unfold gaussianDensity
  simp

/-- Density is `≤ 1/√(2π)` (max-density bound). -/
lemma gaussianDensity_le_peak (x : ℝ) :
    gaussianDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold gaussianDensity
  have h2pi : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff_of_pos_right h2pi]
  exact (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

/-- Pointwise lower bound `φ(x) ≥ φ(0)·(1 - x²/2)` from `e^{-u} ≥ 1-u`. -/
lemma gaussianDensity_lower (x : ℝ) :
    1 / Real.sqrt (2 * Real.pi) * (1 - x^2/2) ≤ gaussianDensity x := by
  unfold gaussianDensity
  have h2pi : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ h2pi]
  -- Goal: 1/√(2π) * (1 - x²/2) * √(2π) ≤ exp(-x²/2)
  have hsqrt : 1 / Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 1 := by
    field_simp
  -- We need exp(-x²/2) ≥ 1 - x²/2.
  have hexp : 1 - x^2/2 ≤ Real.exp (- x^2 / 2) := by
    have := Real.add_one_le_exp (- x^2 / 2)
    linarith
  have hrearrange :
      1 / Real.sqrt (2 * Real.pi) * (1 - x^2/2) * Real.sqrt (2 * Real.pi)
        = (1 - x^2/2) := by
    rw [mul_right_comm, hsqrt, one_mul]
  rw [hrearrange]
  exact hexp

/-- Step 1 *upper* baseline: `Φ(ε) − Φ(−ε) ≤ ε·√(2/π)` for `0 ≤ ε`.

**Paper proof (verbatim)**: `Φ(ε) − Φ(−ε) = 2∫₀^ε φ ≤ 2ε·φ(0) = ε·√(2/π)`,
since `φ(0) = 1/√(2π)` and `2/√(2π) = √(2/π)`. -/
lemma gaussian_baseline_upper (ε : ℝ) (h : 0 ≤ ε) :
    gaussianTwoSided ε ≤ ε * Real.sqrt (2 / Real.pi) := by
  -- Mathlib gap: `gaussianCDF` integral formula `Φ(ε)-Φ(-ε) = 2 ∫₀^ε φ` and
  -- monotonic dominance `φ ≤ φ(0)`. Stated as a sub-stub.
  sorry

/-- Step 1 *lower* baseline: `(2/√(2π))·ε·(1 - ε²/2) ≤ Φ(ε) − Φ(−ε)`
for `0 ≤ ε ≤ 1`.

**Paper proof (verbatim)**: from `e^{-u} ≥ 1-u` (`u ≥ 0`), with
`u = ε²/2`, we get `φ(ε) ≥ φ(0)(1 − ε²/2)`. Integrating from `0` to `ε`
and using monotonicity of `φ` away from `0`,
`∫₀^ε φ ≥ ε·φ(0)(1 − ε²/2)`. Hence the lower bound. -/
lemma gaussian_baseline_lower (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (2 / Real.sqrt (2 * Real.pi)) * ε * (1 - ε^2/2) ≤ gaussianTwoSided ε := by
  -- Mathlib gap: integration of `gaussianDensity_lower` from `0` to `ε` and
  -- reconciling with the CDF difference.
  sorry

/- ## Step 2: Fejér kernel facts (re-used from EsseenSmoothing.lean)

We re-use the following from `EsseenSmoothing.lean`:

* `fejerKernel`, `fejerKernelScaled`             — definitions
* `integral_fejerKernel_eq_one`                  — `∫ K = 1`
* `fejerKernel_fourier_transform`,
  `fejerKernelScaled_fourier_transform`          — `K̂(t) = (1-|t|/M)_+`
* `fejerKernel_even`                             — evenness
* `fejerKernel_le_inv_sq`                        — `K(y) ≤ 2/(πy²)`
* `fejerTail_def_bound`                          — `∫_{|y|>a} K ≤ 4/(πMa)` (after rescaling)
-/

/-- *Step 2 alias*: peak density bound `m := 1/√(2π)` (max of `φ`). -/
noncomputable def normalPeak : ℝ := 1 / Real.sqrt (2 * Real.pi)

lemma normalPeak_pos : 0 < normalPeak := by
  unfold normalPeak
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by positivity))

/- ## Step 3: Self-contained smoothing inequality -/

open ProbabilityTheory in
/-- The convolution `(F − G) ⋆ K_M` evaluated at `x`, where
`F = cdf T_law`, `G = gaussianCDF`, and `K_M = fejerKernelScaled M`. -/
noncomputable def deltaConvolution
    (T_law : Measure ℝ) (M x : ℝ) : ℝ :=
  ∫ y, (cdf T_law (x - y) - gaussianCDF (x - y)) * fejerKernelScaled M y

/-- The *Kolmogorov distance* `D := sup_x |F_T(x) - Φ(x)|`. -/
noncomputable def kolmogDist (T_law : Measure ℝ) : ℝ :=
  ⨆ x : ℝ, |ProbabilityTheory.cdf T_law x - gaussianCDF x|

/-- **Step 3 (Smoothing inequality)**.

Set `D := kolmogDist T_law`, `m := 1/√(2π)`. Then
`D ≤ 2·sup_x |(Δ ⋆ K_M)(x)| + 24m / (πM)`.

**Paper proof (verbatim, sketch)**: WLOG choose `x_0` with `Δ(x_0) = D > 0`
(by `kolmogorov_dist_swap`). Set `a := D/(2m)`. Then for `|y| ≤ a`,
`Δ(x_0 + a − y) ≥ D − m(a − y)` since `F` is monotone and `G` is `m`-Lipschitz.
Splitting the convolution into `|y| ≤ a` and `|y| > a`, using
`τ := ½∫_{|y|>a} K_M ≤ 2/(πMa)` and the explicit `(D − ma)(1 − 2τ)` arithmetic,
one obtains
`(D/2) − 3Dτ ≤ ‖Δ⋆K_M‖_∞`, then
`Dτ ≤ D · 2/(πMa) = 4m/(πM)`,
giving `D ≤ 2‖Δ⋆K_M‖_∞ + 24m/(πM)`. -/
lemma smoothing_inequality
    (T_law : Measure ℝ) [IsProbabilityMeasure T_law]
    (M : ℝ) (hM : 0 < M)
    (sup_conv : ℝ)
    (hsup : ∀ x : ℝ, |deltaConvolution T_law M x| ≤ sup_conv) :
    kolmogDist T_law ≤ 2 * sup_conv + 24 * normalPeak / (Real.pi * M) := by
  -- Mathlib gap: full smoothing-inequality argument (WLOG sign reduction,
  -- splitting `|y|≤a` vs. `|y|>a`, evenness of `K_M`, and the Fejér tail
  -- bound). The skeleton: by `kolmogorov_dist_swap` we may assume Δ(x₀)=D>0;
  -- with `a = D/(2m)` and `τ = ½∫_{|y|>a} K_M ≤ 2/(πMa)`, the inner integral
  -- evaluates to `(D-ma)(1-2τ) = (D/2)(1-2τ)` (the linear `m·y K_M`-piece
  -- vanishing by `fejerKernel_even`), and the outer is `≥ -2Dτ`.
  sorry

/- ## Step 4: Fourier representation of `Δ ⋆ K_M` -/

/-- **Step 4 (Fourier representation of the smoothed difference)**.
For `T_law` a probability measure on `ℝ` whose CDF agrees with `Φ` at `±∞`,
and `M > 0`,
```
(Δ ⋆ K_M)(x)
  = (1/2π) ∫_{-M}^{M} ((φ_T(t) - e^{-t²/2}) / (i·t)) · K̂_M(t) · e^{itx} dt
```
where `K̂_M(t) = max(1 - |t|/M, 0)` (compact support `[-M, M]`).

**Paper proof (verbatim)**: integration by parts in the Fourier–Stieltjes
identity (`Δ(±∞) = 0`) converts `Δ̂(t) = (φ_T(t) - e^{-t²/2})/(it)`. The
inversion formula then yields the displayed equation. -/
lemma smoothed_diff_fourier_repr
    (T_law : Measure ℝ) [IsProbabilityMeasure T_law]
    (M : ℝ) (hM : 0 < M) (x : ℝ) :
    (deltaConvolution T_law M x : ℂ)
      = (1 / (2 * Real.pi : ℂ)) *
        ∫ t in Set.Ioo (-M) M,
          ((charFun T_law t - Complex.exp (-(t : ℂ)^2 / 2)) / ((t : ℂ) * Complex.I))
          * ((max (1 - |t|/M) 0 : ℝ) : ℂ)
          * Complex.exp ((t * x : ℝ) * Complex.I) := by
  -- Mathlib gap: Fourier inversion for compactly-supported `K̂_M` combined
  -- with `Δ̂(t) = (φ_T - e^{-t²/2})/(it)`; the latter is Fourier-Stieltjes
  -- IBP using `Δ(-∞) = Δ(+∞) = 0` (as both CDFs go to 0 at -∞ and 1 at +∞).
  sorry

/-- **Step 4 (sup bound corollary)**. With `|K̂_M(t)| ≤ 1` and the Fourier
representation above,
```
sup_x |(Δ ⋆ K_M)(x)| ≤ (1/2π) ∫_{-M}^{M} |φ_T(t) - e^{-t²/2}| / |t| dt.
```

**Paper proof (verbatim)**: take absolute value inside the Fourier integral
and use `|e^{itx}| = 1`, `|K̂_M| ≤ 1`. -/
lemma smoothed_diff_sup_le_charFun_integral
    (T_law : Measure ℝ) [IsProbabilityMeasure T_law]
    (M : ℝ) (hM : 0 < M) :
    ∃ S : ℝ, (∀ x : ℝ, |deltaConvolution T_law M x| ≤ S) ∧
      S ≤ (1 / (2 * Real.pi)) *
        ∫ t in Set.Ioo (-M) M,
          ‖charFun T_law t - Complex.exp (-(t : ℂ)^2 / 2)‖ / |t| := by
  -- Mathlib gap: triangle inequality on the integral form of
  -- `smoothed_diff_fourier_repr`, plus `|K̂_M(t)| ≤ 1` and `|e^{itx}|=1`.
  sorry

/- ## Step 5: Characteristic-function comparison -/

/-- The auxiliary function `g(x) := log(cos x) + x²/2`. Used in the small-`t`
regime expansion `log φ_T(t) + t²/2 = ∑_k g(α_k t)`. -/
noncomputable def gAux (x : ℝ) : ℝ := Real.log (Real.cos x) + x^2/2

/-- For `|x| ≤ 1`, the auxiliary `g(x) ≤ 0`, equivalently `cos x ≤ exp(-x²/2)`.

**Paper proof (verbatim)**: differentiate twice; equivalent to
`exp(-x²/2) - cos x ≥ 0`, which has positive second derivative on
`[-1, 1]` and vanishes to order 4 at zero. -/
lemma gAux_nonpos {x : ℝ} (hx : |x| ≤ 1) : gAux x ≤ 0 := by
  -- Mathlib gap: Taylor analysis of `exp(-x²/2) - cos x`. Positivity on
  -- `[-1,1]` is standard but not in Mathlib in this exact form.
  sorry

/-- For `|x| ≤ 1`, the auxiliary satisfies `|g(x)| ≤ x⁴/8`.

**Paper proof (verbatim)**: the actual maximum of `|g(x)|/x⁴` on `[-1,1]` is
about `0.116 < 1/8 = 0.125`. The constant `1/8` is the safe upper bound
used in the surgical chain. -/
lemma gAux_quartic_bound {x : ℝ} (hx : |x| ≤ 1) : |gAux x| ≤ x^4/8 := by
  -- Mathlib gap: explicit quartic bound `|log(cos x) + x²/2| ≤ x⁴/8`
  -- for `|x| ≤ 1`. Standard analytic exercise.
  sorry

/-- Bound on max of `|α_k|` in terms of `ρ^{1/3}`.
**Paper proof (verbatim)**: `α_k³ ≤ ∑α_k³ = ρ`, so `α_k ≤ ρ^{1/3}`. -/
lemma alpha_le_rhoCubeRoot (w : ℕ → ℝ) (n : ℕ)
    (hσ : 0 < stdDev w n)
    {k : ℕ} (hk : k ∈ Finset.range n) :
    alpha w n k ≤ (lyapunovRatio w n) ^ ((1 : ℝ) / 3) := by
  -- Mathlib gap: `α_k³ ≤ ∑ α_k³ = ρ` then take cube root via `Real.rpow_le_rpow`.
  sorry

/-- Step 5 *small-t bound* (`|t| ≤ ρ^{-1/3}`). For all `k`, `|α_k t| ≤ 1`,
hence
`|log φ_T(t) + t²/2| ≤ (ρ/8) · t⁴`,
and so
`|φ_T(t) - e^{-t²/2}| ≤ (ρ/8) · t⁴ · e^{-t²/2}`.

**Paper proof (verbatim)**: write `log φ_T(t) + t²/2 = ∑_k g(α_k t)`.
Each `|g(α_k t)| ≤ (α_k t)⁴/8`, and `∑α_k⁴ ≤ ∑α_k³ = ρ` since `α_k ≤ 1`.
Setting `θ := log φ_T(t) + t²/2 ≤ 0`, `φ_T(t) = e^{-t²/2}·e^θ`,
and `1 - e^θ ≤ -θ` for `θ ≤ 0`. -/
lemma cf_comparison_small_t
    (w : ℕ → ℝ) (n : ℕ) (T : RademacherLaw w n)
    (hσ : 0 < stdDev w n)
    (t : ℝ) (ht : |t| ≤ (lyapunovRatio w n) ^ (-(1 : ℝ) / 3)) :
    ‖charFun T.law t - Complex.exp (-(t : ℂ)^2 / 2)‖
      ≤ (lyapunovRatio w n) * t^4 / 8 * Real.exp (-t^2/2) := by
  -- Mathlib gap: the chain
  --   (i)   product CF formula → `log φ_T = ∑ log cos(α_k t)`
  --   (ii)  uniform bound `|α_k t| ≤ 1` (from `alpha_le_rhoCubeRoot`)
  --   (iii) per-term quartic bound `gAux_quartic_bound`
  --   (iv)  `∑ α_k⁴ ≤ ∑ α_k³ = ρ` since `0 ≤ α_k ≤ 1`
  --   (v)   `1 - e^θ ≤ -θ` for `θ ≤ 0` and `|φ_T| = e^{-t²/2}·e^θ`
  -- Each substep is a small mathlib reconciliation; bundled here.
  sorry

/-- Step 5 *medium-t bound* (`ρ^{-1/3} < |t| ≤ M = 1/(2ρ)`).

**Paper proof (verbatim)**: split `S₁ := {k : |α_k t| ≤ 1}` and its
complement. For `k ∈ S₂`, `α_k > 1/|t|`, so `α_k² < |t|·α_k³`, summing
`∑_{S₂} α_k² < |t|·ρ ≤ M·ρ = 1/2`, hence `∑_{S₁} α_k² ≥ 1/2`.
For `k ∈ S₁`, `|cos(α_k t)| ≤ exp(-α_k² t²/2)` (from `gAux_nonpos`),
so `|φ_T(t)| ≤ exp(-t² · ½ · ½) = exp(-t²/4)`.
Hence `|φ_T - e^{-t²/2}| ≤ 2·e^{-t²/4}`. -/
lemma cf_comparison_medium_t
    (w : ℕ → ℝ) (n : ℕ) (T : RademacherLaw w n)
    (hσ : 0 < stdDev w n) (hρ : 0 < lyapunovRatio w n)
    (hρsmall : lyapunovRatio w n ≤ 1/4)
    (t : ℝ)
    (htlo : (lyapunovRatio w n) ^ (-(1 : ℝ) / 3) < |t|)
    (hthi : |t| ≤ 1 / (2 * lyapunovRatio w n)) :
    ‖charFun T.law t - Complex.exp (-(t : ℂ)^2 / 2)‖
      ≤ 2 * Real.exp (-t^2/4) := by
  -- Mathlib gap: split-set argument with `S₁ ∪ S₂` and the bookkeeping
  -- `∑_{S₂} α_k² < |t|·ρ ≤ ½`, `∑_{S₁} α_k² ≥ ½`. Plus `|cos| ≤ exp(-x²/2)`
  -- on `S₁` from `gAux_nonpos`.
  sorry

/-- Step 5 *small-t integral contribution*:
`2·∫_0^U |φ_T - e^{-t²/2}|/t dt ≤ ρ/2` where `U := ρ^{-1/3}`.

**Paper proof (verbatim)**: from `cf_comparison_small_t`,
`|φ_T - e^{-t²/2}|/t ≤ (ρ/8) t³ e^{-t²/2}`.  Integrating from `0` to `∞`,
`∫_0^∞ t³ e^{-t²/2} dt = 2` (substitute `u = t²/2`). Hence
`2·∫_0^U … ≤ 2·(ρ/8)·2 = ρ/2`. -/
lemma cf_integral_small_t_bound
    (w : ℕ → ℝ) (n : ℕ) (T : RademacherLaw w n)
    (hσ : 0 < stdDev w n) (hρ : 0 < lyapunovRatio w n) :
    let U := (lyapunovRatio w n) ^ (-(1 : ℝ) / 3)
    2 * ∫ t in Set.Ioc 0 U,
      ‖charFun T.law t - Complex.exp (-(t : ℂ)^2 / 2)‖ / t
      ≤ lyapunovRatio w n / 2 := by
  -- Mathlib gap: combine pointwise bound from `cf_comparison_small_t` with
  -- the explicit `∫_0^∞ t³ e^{-t²/2} dt = 2`.
  sorry

/-- Step 5 *medium-t integral contribution*:
`2·∫_U^M |φ_T - e^{-t²/2}|/t dt ≤ ρ` for `ρ ≤ 1/4`,
where `U = ρ^{-1/3}`, `M = 1/(2ρ)`.

**Paper proof (verbatim)**: from `cf_comparison_medium_t`,
`|φ_T - e^{-t²/2}|/t ≤ 2·e^{-t²/4}/t`. Then
`∫_U^∞ e^{-t²/4}/t dt = O(e^{-U²/4})`, with absolute constant `≤ ½` in
the regime `ρ ≤ 1/4` (i.e. `U ≥ 4^{1/3} > 1`). Hence the total is `≤ ρ`. -/
lemma cf_integral_medium_t_bound
    (w : ℕ → ℝ) (n : ℕ) (T : RademacherLaw w n)
    (hσ : 0 < stdDev w n) (hρ : 0 < lyapunovRatio w n)
    (hρsmall : lyapunovRatio w n ≤ 1/4) :
    let U := (lyapunovRatio w n) ^ (-(1 : ℝ) / 3)
    let M := 1 / (2 * lyapunovRatio w n)
    2 * ∫ t in Set.Ioc U M,
      ‖charFun T.law t - Complex.exp (-(t : ℂ)^2 / 2)‖ / t
      ≤ lyapunovRatio w n := by
  -- Mathlib gap: tail integral `∫_U^∞ e^{-t²/4}/t` bound with
  -- `U = ρ^{-1/3} ≥ 4^{1/3}` for `ρ ≤ 1/4`, an absolute constant ≤ 1.
  sorry

/-- Step 5 *total integral bound*:
`∫_{-M}^{M} |φ_T - e^{-t²/2}|/|t| dt ≤ 3ρ/2`.

**Paper proof (verbatim)**: combine small- and medium-t bounds, exploiting
evenness in `t` of `|φ_T - e^{-t²/2}|`. -/
lemma cf_integral_total_bound
    (w : ℕ → ℝ) (n : ℕ) (T : RademacherLaw w n)
    (hσ : 0 < stdDev w n) (hρ : 0 < lyapunovRatio w n)
    (hρsmall : lyapunovRatio w n ≤ 1/4) :
    let M := 1 / (2 * lyapunovRatio w n)
    ∫ t in Set.Ioo (-M) M,
        ‖charFun T.law t - Complex.exp (-(t : ℂ)^2 / 2)‖ / |t|
      ≤ 3 * lyapunovRatio w n / 2 := by
  -- Mathlib gap: combine `cf_integral_small_t_bound` (≤ ρ/2)
  -- and `cf_integral_medium_t_bound` (≤ ρ), plus evenness in `t`,
  -- to get `≤ 3ρ/2` total.
  sorry

/- ## Step 6: Kolmogorov-distance bound -/

/-- **Step 6 (Kolmogorov-distance bound, `D ≤ 7ρ`)**.

Combining Step 3 (smoothing, `M = 1/(2ρ)`), Step 4 (Fourier sup-norm bound),
and Step 5 (`∫|φ_T-e^{-t²/2}|/|t| ≤ 3ρ/2`):
```
D ≤ 2 · ‖Δ ⋆ K_M‖_∞ + 24m/(πM)
   ≤ 2 · (1/2π) · (3ρ/2) + 24m·2ρ/π
   = 3ρ/(2π) + 48ρ·m/π
```
With `m = 1/√(2π) ≈ 0.3989`, `48m/π ≈ 6.10`, and `3/(2π) ≈ 0.477`,
the total is `≤ 7ρ` (safe upper bound). -/
theorem kolmogorov_distance_bound
    (w : ℕ → ℝ) (n : ℕ) (T : RademacherLaw w n)
    (hσ : 0 < stdDev w n)
    (hρ : 0 < lyapunovRatio w n) (hρsmall : lyapunovRatio w n ≤ 1/4) :
    haveI : IsProbabilityMeasure T.law := T.isProb
    kolmogDist T.law ≤ 7 * lyapunovRatio w n := by
  -- Assemble Step 3 (smoothing_inequality), Step 4
  -- (smoothed_diff_sup_le_charFun_integral), and Step 5
  -- (cf_integral_total_bound) with `M = 1/(2ρ)`.
  haveI : IsProbabilityMeasure T.law := T.isProb
  set ρ := lyapunovRatio w n with hρdef
  set M : ℝ := 1 / (2 * ρ) with hMdef
  have hM_pos : 0 < M := by
    rw [hMdef]
    positivity
  -- Step 4 sup bound:
  obtain ⟨S, hSall, hSint⟩ :=
    smoothed_diff_sup_le_charFun_integral T.law M hM_pos
  -- Step 5 integral bound:
  have hint5 :
      ∫ t in Set.Ioo (-M) M,
          ‖charFun T.law t - Complex.exp (-(t : ℂ)^2 / 2)‖ / |t|
        ≤ 3 * ρ / 2 := cf_integral_total_bound w n T hσ hρ hρsmall
  have hS_le : S ≤ (1 / (2 * Real.pi)) * (3 * ρ / 2) := by
    refine hSint.trans ?_
    have h2pi_pos : 0 < 2 * Real.pi := by positivity
    exact mul_le_mul_of_nonneg_left hint5 (by positivity)
  -- Step 3 smoothing inequality:
  have hsmooth :
      kolmogDist T.law ≤ 2 * S + 24 * normalPeak / (Real.pi * M) :=
    smoothing_inequality T.law M hM_pos S hSall
  -- Combine:
  have h2S : 2 * S ≤ 2 * ((1 / (2 * Real.pi)) * (3 * ρ / 2)) := by
    nlinarith [hS_le]
  have h2S' : 2 * S ≤ 3 * ρ / (2 * Real.pi) := by
    have heq : 2 * ((1 / (2 * Real.pi)) * (3 * ρ / 2)) = 3 * ρ / (2 * Real.pi) := by
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
    linarith
  -- 24m/(πM) = 24m·(2ρ)/π = 48m·ρ/π
  have hMterm : 24 * normalPeak / (Real.pi * M) = 48 * normalPeak * ρ / Real.pi := by
    rw [hMdef]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hρne : ρ ≠ 0 := hρ.ne'
    field_simp
    ring
  rw [hMterm] at hsmooth
  -- Numeric: 3/(2π) + 48m/π ≤ 7
  have hfinal : 3 * ρ / (2 * Real.pi) + 48 * normalPeak * ρ / Real.pi ≤ 7 * ρ := by
    -- Mathlib gap: `3/(2π) + 48/(π√(2π)) ≤ 7`.
    -- Numerically `0.4775 + 6.0997 ≈ 6.5772 ≤ 7`.
    sorry
  linarith

/- ## Step 7: Surgical bound (final) -/

/-- **Step 7 (the surgical density-at-zero bound)**.

For `0 ≤ ε ≤ 1/2`,
```
| P(|T| ≤ ε) − (Φ(ε) − Φ(−ε)) | ≤ 14·ρ.
```

**Paper proof (verbatim)**: write `q := Φ(ε) − Φ(−ε)`. By
`sup |Δ| = D ≤ 7ρ` (Step 6),
* `|F(ε) − Φ(ε)| ≤ D`
* `|F(−ε⁻) − Φ(−ε)| ≤ D` (`Φ` continuous)

Hence
`|P(|T| ≤ ε) − q| = |F(ε) − F(−ε⁻) − q| ≤ |F(ε) − Φ(ε)| + |F(−ε⁻) − Φ(−ε)| ≤ 2D ≤ 14ρ`.

So `C = 14`. ∎ -/
theorem surgical_density_at_zero
    (w : ℕ → ℝ) (n : ℕ) (T : RademacherLaw w n)
    (hσ : 0 < stdDev w n)
    (hρ : 0 < lyapunovRatio w n) (hρsmall : lyapunovRatio w n ≤ 1/4)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/2) :
    haveI : IsProbabilityMeasure T.law := T.isProb
    |T.law.real (Set.Icc (-ε) ε) - gaussianTwoSided ε|
      ≤ 14 * lyapunovRatio w n := by
  haveI : IsProbabilityMeasure T.law := T.isProb
  -- Step 6 input:
  have hD : kolmogDist T.law ≤ 7 * lyapunovRatio w n :=
    kolmogorov_distance_bound w n T hσ hρ hρsmall
  -- We need: |P(|T|≤ε) - (Φ(ε)-Φ(-ε))| ≤ 2 · kolmogDist ≤ 14ρ.
  -- The triangle-inequality step is purely book-keeping in CDF terms,
  -- using continuity of `Φ` to drop the left-limit `F(-ε⁻)` distinction.
  -- Mathlib gap: explicit triangle inequality
  --   |F(ε) - F((-ε)⁻) - (Φ(ε) - Φ(-ε))|
  --     ≤ |F(ε) - Φ(ε)| + |F(-ε) - Φ(-ε)|     (Φ continuous)
  --     ≤ 2D
  -- combined with `μ.real(Icc -ε ε) = F(ε) - F((-ε)⁻)` (atomless or not).
  sorry

end Erdos524.Helpers
