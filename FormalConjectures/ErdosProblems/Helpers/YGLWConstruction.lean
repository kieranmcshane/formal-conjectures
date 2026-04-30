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

import FormalConjectures.ErdosProblems.Helpers.GLWKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Phase 2 / Round 11 — Constructive layer for the GLW process

This file builds the **deterministic-analytic skeleton** of the Wiener-integral
construction `Y_GLW(u) := ∫₀¹ exp(-us) dB(s)` whose existence is asserted by
the `Y_GLW_exists` axiom in `Helpers/GLWProcess.lean`.

## Why a partial layer

Mathlib (as of this round) does **not** ship:
* Brownian motion as a stochastic process (`IsBrownianMotion`),
* the Wiener integral `∫ f dB` against deterministic L² integrands,
* Kolmogorov–Chentsov continuity criterion,
* Borell's Gaussian concentration / supremum tail control.

A *full* retirement of `Y_GLW_exists` would require all four. Until those
arrive, this file provides the **deterministic / analytic content** of the
construction — everything that does NOT involve the probability space — so
that the eventual axiom retirement reduces to plugging in Mathlib's
forthcoming Brownian-motion + Wiener-integral API.

## What this file proves

* `K_GLW_eq_intervalIntegral_exp_neg`: the covariance integral identity
  `K_GLW(u, v) = ∫₀¹ exp(-(u+v)·s) ds` for `u + v > 0`.
* `K_GLW_zero_eq_intervalIntegral`: the same identity at `u = v = 0`
  (the boundary case where both sides equal `1`).
* `K_GLW_eq_integral_glwIntegrand`: `K_GLW(u, v) = ∫₀¹ glwIntegrand u s ·
  glwIntegrand v s ds`, recognising `K_GLW` as the **L²([0,1]) inner
  product** of the integrand family `glwIntegrand u (s) := exp(-u s)`.
* `K_GLW_quadratic_form_nonneg`: positive semi-definiteness of `K_GLW`
  on `[0, ∞)ⁿ`, derived from the Mercer-style integral representation
  `∑ᵢⱼ cᵢ cⱼ K(uᵢ, uⱼ) = ∫₀¹ (∑ᵢ cᵢ exp(-uᵢ s))² ds ≥ 0`.

Each lemma is purely real-analytic — no probability content — and re-uses
Round 10's exponential-integral techniques (`integral_exp_mul_complex`,
`integral_deriv_eq_sub'`).

## Roadmap to full axiom retirement

When Mathlib gains Brownian motion + Wiener integral, the axiom retirement
proceeds:

1. Take `Ω := C([0,∞), ℝ)` with the Wiener measure `ℙ`.
2. Define `Y_GLW u := wienerIntegral (glwIntegrand u)`.
3. Centeredness, integrability, covariance: from the Itô isometry, using
   the lemmas in this file.
4. Joint Gaussianity: every finite linear combination is again a Wiener
   integral, hence Gaussian — `IsGaussian` is closed under L² limits and
   linear maps.
5. Continuous paths: Kolmogorov–Chentsov on the modulus of continuity of
   `u ↦ Y_GLW u` (an L² argument bounding `‖Y_GLW u - Y_GLW v‖_L²` by
   `O(|u - v|^{1/2})`).
6. Tail decay: Borell's inequality on `sup_{u ∈ [T, T+1]} |Y_GLW u|`
   combined with Borel–Cantelli for the integer-indexed envelope.

The deterministic-analytic content of steps 3 and 4 — and most of 5 — lives
in this file.
-/

namespace Erdos524.Helpers
open Real Set MeasureTheory intervalIntegral

/-! ## 1. Covariance integral identity

The defining identity of `K_GLW` as the L²([0,1]) covariance of the
exponential family `s ↦ exp(-u s)`.

We start with the single-variable form `∫₀¹ exp(-c·s) ds` for `c ≠ 0`. -/

/-- The primitive `F_c(s) := exp(-c·s) / (-c)` has derivative `exp(-c·s)`
at every point, for `c ≠ 0`. -/
private theorem hasDerivAt_exp_neg_primitive {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-c * y) / (-c)) (Real.exp (-c * s)) s := by
  have h1 : HasDerivAt (fun y : ℝ => -c * y) (-c) s := by
    simpa using (hasDerivAt_id s).const_mul (-c)
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-c * y))
      (Real.exp (-c * s) * (-c)) s := h1.exp
  have h3 : HasDerivAt (fun y : ℝ => Real.exp (-c * y) / (-c))
      ((Real.exp (-c * s) * (-c)) / (-c)) s := h2.div_const (-c)
  have hsimp : (Real.exp (-c * s) * (-c)) / (-c) = Real.exp (-c * s) := by
    have : (-c : ℝ) ≠ 0 := neg_ne_zero.mpr hc
    field_simp
  rw [hsimp] at h3
  exact h3

/-- For `c ≠ 0`, the interval integral `∫₀¹ exp(-c·s) ds` equals
`(1 - exp(-c))/c`. Application of FTC-2 with the primitive
`F_c(s) := exp(-c·s)/(-c)`. -/
theorem intervalIntegral_exp_neg_mul (c : ℝ) (hc : c ≠ 0) :
    ∫ s in (0 : ℝ)..1, Real.exp (-c * s) = (1 - Real.exp (-c)) / c := by
  have h_cont : Continuous (fun s : ℝ => Real.exp (-c * s)) := by
    have h_inner : Continuous fun s : ℝ => -c * s := by fun_prop
    exact Real.continuous_exp.comp h_inner
  have h_int : IntervalIntegrable (fun s : ℝ => Real.exp (-c * s))
      MeasureTheory.volume 0 1 :=
    h_cont.intervalIntegrable 0 1
  have h_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => Real.exp (-c * y) / (-c))
    (f' := fun s : ℝ => Real.exp (-c * s))
    (a := 0) (b := 1)
    (fun s _ => hasDerivAt_exp_neg_primitive hc s) h_int
  rw [h_eq]
  -- Goal (after beta-reduction): exp(-c·1)/(-c) - exp(-c·0)/(-c) = (1 - exp(-c))/c.
  simp only
  rw [show (-c : ℝ) * (1 : ℝ) = -c from by ring,
      show (-c : ℝ) * (0 : ℝ) = 0 from by ring, Real.exp_zero]
  field_simp
  ring

/-- The covariance integral identity at `u + v > 0`:
`K_GLW(u, v) = ∫₀¹ exp(-(u + v)·s) ds`. -/
theorem K_GLW_eq_intervalIntegral_exp_neg {u v : ℝ} (huv : 0 < u + v) :
    K_GLW u v = ∫ s in (0 : ℝ)..1, Real.exp (-(u + v) * s) := by
  have hne : u + v ≠ 0 := ne_of_gt huv
  rw [K_GLW_def, K_GLW_aux_of_ne _ hne, intervalIntegral_exp_neg_mul (u + v) hne]

/-- The boundary case `u + v = 0`: both sides equal `1`.

Note that the conjunct `0 ≤ u, 0 ≤ v` plus `u + v = 0` forces `u = v = 0`,
so this lemma is most usefully phrased at the origin. -/
theorem K_GLW_zero_eq_intervalIntegral :
    K_GLW (0 : ℝ) 0 = ∫ s in (0 : ℝ)..1, Real.exp (-(0 + 0) * s) := by
  rw [K_GLW_zero]
  -- ∫₀¹ exp(0) ds = ∫₀¹ 1 ds = 1.
  have h_const : (fun s : ℝ => Real.exp (-(0 + 0) * s)) = (fun _ => (1 : ℝ)) := by
    funext s
    rw [show (-(0 + 0) : ℝ) * s = 0 from by ring, Real.exp_zero]
  rw [h_const]
  simp

/-- Combined statement covering both `u + v > 0` and the boundary
`u + v = 0` case (only meaningful when `u = v = 0` if `u, v ≥ 0`). -/
theorem K_GLW_eq_intervalIntegral_of_nonneg {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    K_GLW u v = ∫ s in (0 : ℝ)..1, Real.exp (-(u + v) * s) := by
  rcases eq_or_lt_of_le (add_nonneg hu hv) with hzero | hpos
  · -- u + v = 0, hence u = v = 0.
    have hu0 : u = 0 := le_antisymm (by linarith) hu
    have hv0 : v = 0 := le_antisymm (by linarith) hv
    subst hu0; subst hv0
    exact K_GLW_zero_eq_intervalIntegral
  · exact K_GLW_eq_intervalIntegral_exp_neg hpos

/-! ## 2. K_GLW as L²([0,1]) inner product (Stretch B)

Define the integrand family `glwIntegrand u (s) := exp(-u s)`. Then
`K_GLW(u, v) = ∫₀¹ glwIntegrand u (s) · glwIntegrand v (s) ds`.

This is the **Mercer / RKHS view** of the kernel: `K_GLW` is the kernel
of the integral operator with feature map `u ↦ s ↦ exp(-u s)` on
L²([0,1], λ). It is the deterministic shadow of the Itô isometry
`E[(∫ f dB)(∫ g dB)] = ⟨f, g⟩_{L²([0,1])}`. -/

/-- The integrand family `glwIntegrand u s := exp(-u s)`. The L²([0,1])
feature map for the K_GLW reproducing-kernel structure. -/
noncomputable def glwIntegrand (u s : ℝ) : ℝ := Real.exp (-u * s)

theorem glwIntegrand_def (u s : ℝ) : glwIntegrand u s = Real.exp (-u * s) := rfl

/-- For each fixed `u`, `glwIntegrand u` is continuous in `s`. -/
theorem glwIntegrand_continuous (u : ℝ) : Continuous (glwIntegrand u) := by
  unfold glwIntegrand
  have h_inner : Continuous fun s : ℝ => -u * s := by fun_prop
  exact Real.continuous_exp.comp h_inner

/-- Pointwise product identity: `glwIntegrand u s · glwIntegrand v s =
exp(-(u + v)·s)`, the integrand whose `[0,1]`-integral is `K_GLW(u, v)`. -/
theorem glwIntegrand_mul_eq (u v s : ℝ) :
    glwIntegrand u s * glwIntegrand v s = Real.exp (-(u + v) * s) := by
  unfold glwIntegrand
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Mercer-style identity**: `K_GLW(u, v)` equals the L²([0,1]) inner
product `⟨glwIntegrand u, glwIntegrand v⟩`. This is the deterministic
shadow of the (would-be) Itô isometry `E[Y(u)Y(v)] = ⟨e^{-u·}, e^{-v·}⟩`. -/
theorem K_GLW_eq_integral_glwIntegrand_mul {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    K_GLW u v = ∫ s in (0 : ℝ)..1, glwIntegrand u s * glwIntegrand v s := by
  rw [K_GLW_eq_intervalIntegral_of_nonneg hu hv]
  congr 1
  funext s
  exact (glwIntegrand_mul_eq u v s).symm

/-! ## 3. Positive semi-definiteness of K_GLW

The Mercer-style representation `K_GLW(u, v) = ∫₀¹ φ_u(s) φ_v(s) ds`
immediately yields **positive semi-definiteness**: any quadratic form
`∑ᵢⱼ cᵢ cⱼ K_GLW(uᵢ, uⱼ)` is the integral of a perfect square. -/

/-- The **GLW exponential profile**: `glwExpProfile us cs s := ∑ᵢ cᵢ
exp(-uᵢ s)`. The Mercer feature-vector projected onto the coefficient
direction `c`. -/
noncomputable def glwExpProfile {n : ℕ} (us cs : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin n, cs i * glwIntegrand (us i) s

/-- The exponential profile is continuous in `s`. -/
theorem glwExpProfile_continuous {n : ℕ} (us cs : Fin n → ℝ) :
    Continuous (glwExpProfile us cs) := by
  unfold glwExpProfile
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (glwIntegrand_continuous _)

/-- Quadratic form expansion via `(∑ a)² = ∑∑ aᵢ aⱼ`: the squared
exponential profile equals `∑ᵢⱼ cᵢ cⱼ exp(-(uᵢ + uⱼ)·s)`. -/
theorem glwExpProfile_sq_eq {n : ℕ} (us cs : Fin n → ℝ) (s : ℝ) :
    (glwExpProfile us cs s)^2 =
      ∑ i : Fin n, ∑ j : Fin n,
        cs i * cs j * Real.exp (-(us i + us j) * s) := by
  unfold glwExpProfile
  rw [sq, Finset.sum_mul_sum]
  congr 1
  funext i
  congr 1
  funext j
  rw [show cs i * glwIntegrand (us i) s * (cs j * glwIntegrand (us j) s)
        = cs i * cs j * (glwIntegrand (us i) s * glwIntegrand (us j) s)
      from by ring,
      glwIntegrand_mul_eq]

/-- Integrability of `s ↦ exp(-(uᵢ + uⱼ)·s)` on `[0, 1]`. The integrand
is continuous on the compact interval, so this is automatic. -/
theorem intervalIntegrable_exp_neg_mul (c : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.exp (-c * s)) MeasureTheory.volume 0 1 := by
  have h_cont : Continuous (fun s : ℝ => Real.exp (-c * s)) := by
    have h_inner : Continuous fun s : ℝ => -c * s := by fun_prop
    exact Real.continuous_exp.comp h_inner
  exact h_cont.intervalIntegrable 0 1

/-- The integrand `(i, j) ↦ s ↦ cs i * cs j * exp(-(uᵢ + uⱼ)·s)` is
interval-integrable on `[0, 1]` for each pair `(i, j)`. -/
theorem intervalIntegrable_pair_term {n : ℕ} (us cs : Fin n → ℝ)
    (i j : Fin n) :
    IntervalIntegrable
      (fun s : ℝ => cs i * cs j * Real.exp (-(us i + us j) * s))
      MeasureTheory.volume 0 1 :=
  (intervalIntegrable_exp_neg_mul (us i + us j)).const_mul (cs i * cs j)

/-- Sum-of-pair-terms is interval-integrable on `[0, 1]`. The sum-of-finitely-
many continuous functions is continuous, hence integrable on the compact
interval. -/
theorem intervalIntegrable_sum_pair_terms {n : ℕ} (us cs : Fin n → ℝ)
    (i : Fin n) :
    IntervalIntegrable
      (fun s : ℝ => ∑ j : Fin n, cs i * cs j * Real.exp (-(us i + us j) * s))
      MeasureTheory.volume 0 1 := by
  have h_cont : Continuous
      (fun s : ℝ => ∑ j : Fin n, cs i * cs j * Real.exp (-(us i + us j) * s)) := by
    apply continuous_finset_sum
    intro j _
    have h_inner : Continuous fun s : ℝ => -(us i + us j) * s := by fun_prop
    exact continuous_const.mul (Real.continuous_exp.comp h_inner)
  exact h_cont.intervalIntegrable 0 1

/-- The integral form of the quadratic form: for any nonnegative grid
`us : Fin n → [0, ∞)` and any coefficients `cs`, the quadratic form
`∑ᵢⱼ cᵢ cⱼ K_GLW(uᵢ, uⱼ)` equals `∫₀¹ (glwExpProfile us cs s)² ds`. -/
theorem glwQuadraticForm_eq_integral_sq {n : ℕ} (us cs : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    ∑ i : Fin n, ∑ j : Fin n, cs i * cs j * K_GLW (us i) (us j) =
      ∫ s in (0 : ℝ)..1, (glwExpProfile us cs s)^2 := by
  -- Step 1: rewrite each K_GLW as ∫₀¹ exp(-(uᵢ + uⱼ)·s) ds.
  have h_lhs : (∑ i : Fin n, ∑ j : Fin n, cs i * cs j * K_GLW (us i) (us j)) =
      ∑ i : Fin n, ∑ j : Fin n,
        cs i * cs j * ∫ s in (0 : ℝ)..1, Real.exp (-(us i + us j) * s) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [K_GLW_eq_intervalIntegral_of_nonneg (h_us i) (h_us j)]
  rw [h_lhs]
  -- Step 2: pull constants `cs i * cs j` inside each interval integral.
  have h_pull_const : (∑ i : Fin n, ∑ j : Fin n,
      cs i * cs j * ∫ s in (0 : ℝ)..1, Real.exp (-(us i + us j) * s)) =
      ∑ i : Fin n, ∑ j : Fin n,
        ∫ s in (0 : ℝ)..1, cs i * cs j * Real.exp (-(us i + us j) * s) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
  rw [h_pull_const]
  -- Step 3: exchange the inner ∑ⱼ with ∫ (using interval-integrability of
  -- each pair term).
  have h_exchange_inner : (∑ i : Fin n, ∑ j : Fin n,
      ∫ s in (0 : ℝ)..1, cs i * cs j * Real.exp (-(us i + us j) * s)) =
      ∑ i : Fin n,
        ∫ s in (0 : ℝ)..1,
          ∑ j : Fin n, cs i * cs j * Real.exp (-(us i + us j) * s) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    symm
    exact intervalIntegral.integral_finset_sum (s := Finset.univ)
      (f := fun j s => cs i * cs j * Real.exp (-(us i + us j) * s))
      (fun j _ => intervalIntegrable_pair_term us cs i j)
  rw [h_exchange_inner]
  -- Step 4: exchange the outer ∑ᵢ with ∫.
  rw [show (∑ i : Fin n,
      ∫ s in (0 : ℝ)..1,
        ∑ j : Fin n, cs i * cs j * Real.exp (-(us i + us j) * s)) =
      ∫ s in (0 : ℝ)..1,
        ∑ i : Fin n, ∑ j : Fin n,
          cs i * cs j * Real.exp (-(us i + us j) * s) from
    (intervalIntegral.integral_finset_sum (s := Finset.univ)
      (f := fun i s => ∑ j : Fin n, cs i * cs j * Real.exp (-(us i + us j) * s))
      (fun i _ => intervalIntegrable_sum_pair_terms us cs i)).symm]
  -- Step 5: identify the integrand with `(glwExpProfile us cs s)²`.
  congr 1
  funext s
  rw [glwExpProfile_sq_eq]

/-- **Positive semi-definiteness of K_GLW**: for any nonnegative grid
`us : Fin n → [0, ∞)` and any coefficients `cs`, the quadratic form
`∑ᵢⱼ cᵢ cⱼ K_GLW(uᵢ, uⱼ) ≥ 0`. Direct corollary of the integral-of-square
representation. -/
theorem K_GLW_quadratic_form_nonneg {n : ℕ} (us cs : Fin n → ℝ)
    (h_us : ∀ i, 0 ≤ us i) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, cs i * cs j * K_GLW (us i) (us j) := by
  rw [glwQuadraticForm_eq_integral_sq us cs h_us]
  -- ∫₀¹ f² ≥ 0 since `(0 : ℝ) ≤ (1 : ℝ)` and `f² ≥ 0` pointwise.
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun _ => sq_nonneg _)

/-! ## 4. Marginal L²-norm and tail-decay roadmap

The variance of the eventual `Y_GLW(u)` is `K_GLW(u, u) = (1 - exp(-2u))/(2u)`.
For the tail-decay conjunct of `Y_GLW_exists`, the eventual proof rests
on `K_GLW(u, u) → 0` as `u → ∞`. Both facts are deterministic statements
about the kernel — provable here without any probability machinery. -/

/-- The variance of the (eventual) `Y_GLW(u)`: `K_GLW(u, u) = (1 - exp(-2u))/(2u)`
for `u > 0`. -/
theorem K_GLW_var_eq {u : ℝ} (hu : 0 < u) :
    K_GLW u u = (1 - Real.exp (-(2 * u))) / (2 * u) := by
  have h2u : 0 < u + u := by linarith
  have hne : u + u ≠ 0 := ne_of_gt h2u
  rw [K_GLW_def, K_GLW_aux_of_ne _ hne]
  congr <;> ring

/-- The L²([0,1]) norm of `glwIntegrand u` equals `K_GLW(u, u)`. The
deterministic form of the variance identity: in the eventual
construction, `Var(Y_GLW(u)) = ‖exp(-u·)‖²_{L²([0,1])} = K_GLW(u, u)`. -/
theorem glwIntegrand_L2_norm_sq {u : ℝ} (hu : 0 ≤ u) :
    K_GLW u u = ∫ s in (0 : ℝ)..1, (glwIntegrand u s)^2 := by
  rw [K_GLW_eq_integral_glwIntegrand_mul hu hu]
  congr 1
  funext s
  ring

/-- Pointwise positivity of the variance integrand `(glwIntegrand u s)²`. -/
theorem glwIntegrand_sq_nonneg (u s : ℝ) :
    0 ≤ (glwIntegrand u s)^2 := sq_nonneg _

/-- Variance non-negativity from the integral form (alternative proof to
`K_GLW_pos`, useful when manipulating the integral representation). -/
theorem K_GLW_var_nonneg_from_integral {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ K_GLW u u := by
  rw [glwIntegrand_L2_norm_sq hu]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun s => glwIntegrand_sq_nonneg u s)

/-- Symmetry of `K_GLW` from the Mercer / inner-product form. -/
theorem K_GLW_symm_from_integral {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    K_GLW u v = K_GLW v u := by
  rw [K_GLW_eq_integral_glwIntegrand_mul hu hv,
      K_GLW_eq_integral_glwIntegrand_mul hv hu]
  congr 1
  funext s
  ring

/-! ## 5. Linearity in the coefficient direction

The Mercer representation is bilinear in the underlying coefficients.
The following lemma exposes the linearity that drives the eventual
`Y(au_1 + bu_2)` linear-combination Gaussianity. -/

/-- Linearity of the exponential profile in the coefficient vector. -/
theorem glwExpProfile_smul {n : ℕ} (us cs : Fin n → ℝ) (k : ℝ) (s : ℝ) :
    glwExpProfile us (fun i => k * cs i) s = k * glwExpProfile us cs s := by
  unfold glwExpProfile
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Additivity of the exponential profile in the coefficient vector. -/
theorem glwExpProfile_add {n : ℕ} (us c1 c2 : Fin n → ℝ) (s : ℝ) :
    glwExpProfile us (fun i => c1 i + c2 i) s =
      glwExpProfile us c1 s + glwExpProfile us c2 s := by
  unfold glwExpProfile
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Zero coefficient yields zero profile. -/
theorem glwExpProfile_zero_coeff {n : ℕ} (us : Fin n → ℝ) (s : ℝ) :
    glwExpProfile us 0 s = 0 := by
  unfold glwExpProfile
  simp

/-! ## 6. Cauchy–Schwarz on the L²([0,1]) inner product

The deterministic form of the Cauchy–Schwarz inequality on the K_GLW
covariance: `K_GLW(u, v)² ≤ K_GLW(u, u) · K_GLW(v, v)`. Useful as a
prerequisite for the Anderson-style chain bounds downstream. -/

/-- **Cauchy–Schwarz for K_GLW**: `K_GLW(u, v)² ≤ K_GLW(u, u) · K_GLW(v, v)`
for `u, v ≥ 0`. Specialisation of the L²([0,1]) Cauchy–Schwarz to the
exponential family `s ↦ exp(-u·s)`. Proof via the integral-of-squares
PSD argument applied to the 2-point grid `(u, v)` with coefficient
direction `(c1, c2) = (1, -K_GLW(u,v) / K_GLW(u,u))` (the "best linear
estimator" coefficient).

The straightforward proof uses `K_GLW_quadratic_form_nonneg` with
`n = 2`. For a clean statement we expose this as a separate lemma, but
the proof is left to a future round to keep this file's scope focused on
the Mercer representation and PSD. -/
theorem K_GLW_cauchy_schwarz {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (K_GLW u v)^2 ≤ K_GLW u u * K_GLW v v := by
  -- Apply `K_GLW_quadratic_form_nonneg` to the 2-point grid with
  -- coefficients `(K_GLW v v, -K_GLW u v)`. The resulting quadratic form
  -- is `K_GLW v v · (K_GLW u u · K_GLW v v - (K_GLW u v)²)`. When
  -- `K_GLW v v > 0` (always true for v ≥ 0), divide and rearrange.
  have h_var_v_pos : 0 < K_GLW v v := K_GLW_pos v v hv hv
  have h_var_u_pos : 0 < K_GLW u u := K_GLW_pos u u hu hu
  -- The 2-point Mercer quadratic form with coefficients (a, b):
  -- a² K(u, u) + 2ab K(u, v) + b² K(v, v) ≥ 0.
  -- Choose a = K(v,v), b = -K(u,v); then the form is
  -- K(v,v)² K(u,u) - 2 K(v,v) (K(u,v))² + (K(u,v))² K(v,v)
  --   = K(v,v) · (K(u,u) K(v,v) - (K(u,v))²).
  -- Nonneg + K(v,v) > 0 ⇒ K(u,u) K(v,v) ≥ (K(u,v))².
  set us : Fin 2 → ℝ := ![u, v] with hus
  set cs : Fin 2 → ℝ := ![K_GLW v v, -(K_GLW u v)] with hcs
  have h_us_nn : ∀ i, 0 ≤ us i := by
    intro i
    fin_cases i <;> simp [hus, hu, hv]
  have h_qf := K_GLW_quadratic_form_nonneg us cs h_us_nn
  -- Expand the 2×2 sum.
  have h_expand : (∑ i : Fin 2, ∑ j : Fin 2, cs i * cs j * K_GLW (us i) (us j)) =
      cs 0 * cs 0 * K_GLW (us 0) (us 0) +
      cs 0 * cs 1 * K_GLW (us 0) (us 1) +
      cs 1 * cs 0 * K_GLW (us 1) (us 0) +
      cs 1 * cs 1 * K_GLW (us 1) (us 1) := by
    simp [Fin.sum_univ_two]
    ring
  rw [h_expand] at h_qf
  -- Substitute us 0 = u, us 1 = v, cs 0 = K(v,v), cs 1 = -K(u,v).
  simp only [hus, hcs, Matrix.cons_val_zero, Matrix.cons_val_one] at h_qf
  -- h_qf : 0 ≤ K(v,v) * K(v,v) * K(u,u) + K(v,v) * -K(u,v) * K(u,v) +
  --         -K(u,v) * K(v,v) * K(v,u) + -K(u,v) * -K(u,v) * K(v,v).
  -- Use K_GLW symmetry K(v,u) = K(u,v).
  rw [show K_GLW v u = K_GLW u v from K_GLW_symm v u] at h_qf
  -- Now: 0 ≤ K(v,v)² K(u,u) - K(v,v)(K(u,v))² - (K(u,v))² K(v,v) + (K(u,v))² K(v,v)
  --        = K(v,v)² K(u,u) - K(v,v) (K(u,v))²
  --        = K(v,v) · (K(v,v) K(u,u) - (K(u,v))²).
  have h_simplify : K_GLW v v * K_GLW v v * K_GLW u u +
                    K_GLW v v * -K_GLW u v * K_GLW u v +
                    -K_GLW u v * K_GLW v v * K_GLW u v +
                    -K_GLW u v * -K_GLW u v * K_GLW v v =
                    K_GLW v v * (K_GLW v v * K_GLW u u - (K_GLW u v)^2) := by
    ring
  rw [h_simplify] at h_qf
  -- 0 ≤ K(v,v) * (K(v,v) K(u,u) - K(u,v)²) and K(v,v) > 0 ⇒ inner ≥ 0.
  have h_inner : 0 ≤ K_GLW v v * K_GLW u u - (K_GLW u v)^2 :=
    nonneg_of_mul_nonneg_right h_qf h_var_v_pos
  linarith [h_inner]

/-! ## 6.5. L²([0,1]) distance — Kolmogorov–Chentsov ground floor

The eventual continuous-paths conjunct of `Y_GLW_exists` is proven via
Kolmogorov–Chentsov, which requires the L²(Ω)-Hölder bound on
`Y(u) - Y(v)`. By the (would-be) Itô isometry,
`E[(Y(u) - Y(v))²] = ‖glwIntegrand u - glwIntegrand v‖²_{L²([0,1])}`,
a deterministic quantity. Here we package this L²-distance and reduce
its computation to the kernel.

`‖glwIntegrand u - glwIntegrand v‖²_{L²([0,1])} =
   K_GLW(u, u) - 2 K_GLW(u, v) + K_GLW(v, v)`
which the eventual KC application bounds to deduce continuous paths. -/

/-- Interval-integrability of `(glwIntegrand u s - glwIntegrand v s)²`
on `[0, 1]`. Continuous on the compact interval. -/
theorem intervalIntegrable_glwIntegrand_diff_sq (u v : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => (glwIntegrand u s - glwIntegrand v s)^2)
      MeasureTheory.volume 0 1 := by
  have h_cont : Continuous (fun s : ℝ => (glwIntegrand u s - glwIntegrand v s)^2) := by
    have h1 : Continuous (glwIntegrand u) := glwIntegrand_continuous u
    have h2 : Continuous (glwIntegrand v) := glwIntegrand_continuous v
    exact (h1.sub h2).pow 2
  exact h_cont.intervalIntegrable 0 1

/-- The integrand product `glwIntegrand u s * glwIntegrand v s` is
interval-integrable on `[0, 1]`. -/
theorem intervalIntegrable_glwIntegrand_mul (u v : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => glwIntegrand u s * glwIntegrand v s)
      MeasureTheory.volume 0 1 := by
  have h_cont : Continuous (fun s : ℝ => glwIntegrand u s * glwIntegrand v s) :=
    (glwIntegrand_continuous u).mul (glwIntegrand_continuous v)
  exact h_cont.intervalIntegrable 0 1

/-- Interval-integrability of `(glwIntegrand u s)²` on `[0, 1]`. -/
theorem intervalIntegrable_glwIntegrand_sq (u : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => (glwIntegrand u s)^2) MeasureTheory.volume 0 1 := by
  have : (fun s : ℝ => (glwIntegrand u s)^2) =
         (fun s : ℝ => glwIntegrand u s * glwIntegrand u s) := by
    funext s; ring
  rw [this]
  exact intervalIntegrable_glwIntegrand_mul u u

/-- **The L²([0,1]) distance identity**:
`∫₀¹ (glwIntegrand u s - glwIntegrand v s)² ds =
 K_GLW(u, u) - 2 K_GLW(u, v) + K_GLW(v, v)`.
The deterministic shadow of `E[(Y(u) - Y(v))²]`. -/
theorem L2_distance_glwIntegrand_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ s in (0 : ℝ)..1, (glwIntegrand u s - glwIntegrand v s)^2 =
      K_GLW u u - 2 * K_GLW u v + K_GLW v v := by
  -- Expand the square: (a - b)² = a² - 2 a b + b².
  have h_expand : (fun s : ℝ => (glwIntegrand u s - glwIntegrand v s)^2) =
      fun s : ℝ => (glwIntegrand u s)^2 -
        2 * (glwIntegrand u s * glwIntegrand v s) + (glwIntegrand v s)^2 := by
    funext s; ring
  rw [h_expand]
  -- ∫ (a² - 2 a b + b²) = ∫ a² - 2 ∫ a b + ∫ b².
  have h_uu_int : IntervalIntegrable (fun s : ℝ => (glwIntegrand u s)^2)
      MeasureTheory.volume 0 1 := intervalIntegrable_glwIntegrand_sq u
  have h_vv_int : IntervalIntegrable (fun s : ℝ => (glwIntegrand v s)^2)
      MeasureTheory.volume 0 1 := intervalIntegrable_glwIntegrand_sq v
  have h_uv_int : IntervalIntegrable
      (fun s : ℝ => glwIntegrand u s * glwIntegrand v s)
      MeasureTheory.volume 0 1 := intervalIntegrable_glwIntegrand_mul u v
  have h_2uv_int : IntervalIntegrable
      (fun s : ℝ => 2 * (glwIntegrand u s * glwIntegrand v s))
      MeasureTheory.volume 0 1 := h_uv_int.const_mul 2
  rw [intervalIntegral.integral_add (h_uu_int.sub h_2uv_int) h_vv_int,
      intervalIntegral.integral_sub h_uu_int h_2uv_int,
      intervalIntegral.integral_const_mul]
  -- Identify each piece via the Mercer representation.
  rw [← glwIntegrand_L2_norm_sq hu, ← glwIntegrand_L2_norm_sq hv,
      ← K_GLW_eq_integral_glwIntegrand_mul hu hv]

/-- **L²([0,1]) distance non-negativity**:
`0 ≤ K_GLW(u, u) - 2 K_GLW(u, v) + K_GLW(v, v)`. The deterministic form
of `0 ≤ E[(Y(u) - Y(v))²]`. -/
theorem K_GLW_diff_quadratic_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ K_GLW u u - 2 * K_GLW u v + K_GLW v v := by
  rw [← L2_distance_glwIntegrand_eq hu hv]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun _ => sq_nonneg _)

/-! ## 6.6. Monotonicity & dominance bounds

Two simple but useful deterministic bounds on `K_GLW`:

* the variance `K_GLW(u, u)` is monotonically *decreasing* in `u ≥ 0`,
* the marginal expectation `∫₀¹ glwIntegrand u s ds = K_GLW(u, 0)`
  (an alternative form of the cross-covariance with the constant
  marginal `Y(0)`). -/

/-- The marginal expectation of `glwIntegrand u` on `[0, 1]` equals
`K_GLW(u, 0)`. The deterministic shadow of `E[Y_GLW(u) · Y_GLW(0)] =
K_GLW(u, 0)` (since `Y_GLW(0) ≡ 1` in the L²-completion of the
Wiener-integral feature map). -/
theorem integral_glwIntegrand_eq_K_GLW_zero {u : ℝ} (hu : 0 ≤ u) :
    ∫ s in (0 : ℝ)..1, glwIntegrand u s = K_GLW u 0 := by
  rw [K_GLW_eq_intervalIntegral_of_nonneg hu (le_refl 0)]
  congr 1
  funext s
  unfold glwIntegrand
  congr 1
  ring

/-- `K_GLW` is non-increasing in `u` along the diagonal. For `0 ≤ u ≤ v`,
`K_GLW(v, v) ≤ K_GLW(u, u)`. -/
theorem K_GLW_var_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    K_GLW v v ≤ K_GLW u u := by
  -- Use the integral form: K(u, u) = ∫₀¹ exp(-2us) ds.
  rw [glwIntegrand_L2_norm_sq hu, glwIntegrand_L2_norm_sq (le_trans hu huv)]
  -- ∫₀¹ exp(-2vs)² ds ≤ ∫₀¹ exp(-2us)² ds because exp(-2vs)² ≤ exp(-2us)²
  -- pointwise (for s ≥ 0, u ≤ v ⟹ -2vs ≤ -2us ⟹ exp(-2vs) ≤ exp(-2us)).
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_glwIntegrand_sq v) (intervalIntegrable_glwIntegrand_sq u)
  intro s hs
  have hs_nn : 0 ≤ s := hs.1
  -- Pointwise: (glwIntegrand v s)² ≤ (glwIntegrand u s)².
  unfold glwIntegrand
  have h_exp_pos_v : 0 < Real.exp (-v * s) := Real.exp_pos _
  have h_exp_pos_u : 0 < Real.exp (-u * s) := Real.exp_pos _
  have h_le : Real.exp (-v * s) ≤ Real.exp (-u * s) := by
    apply Real.exp_le_exp.mpr
    have : -v * s ≤ -u * s := by
      have h1 : -v ≤ -u := by linarith
      exact mul_le_mul_of_nonneg_right h1 hs_nn
    exact this
  -- Square preserves order on nonneg reals.
  apply sq_le_sq'
  · linarith [sq_nonneg (Real.exp (-u * s)), h_exp_pos_v, h_exp_pos_u]
  · exact h_le

/-! ## 7. Variance decay roadmap

For the eventual sample-path tail-decay conjunct of `Y_GLW_exists`, the
ground floor is `K_GLW(u, u) → 0` as `u → ∞`. Here we prove the
quantitative bound `K_GLW(u, u) ≤ 1/(2u)` for `u > 0`, which is the
deterministic shadow of `Var(Y_GLW(u)) ≤ 1/(2u)`.

Combined with Borell's inequality (BLOCKER #5), this gives
`P(|Y_GLW(u)| > ε) ≤ 2 exp(-ε² u)` and hence a.s. tail decay via
Borel–Cantelli. The `1/(2u)` ground floor is what we can prove
deterministically. -/

/-- **Variance decay bound** `K_GLW(u, u) ≤ 1/(2u)` for `u > 0`. -/
theorem K_GLW_var_le_recip {u : ℝ} (hu : 0 < u) :
    K_GLW u u ≤ 1 / (2 * u) := by
  rw [K_GLW_var_eq hu]
  have h2u : 0 < 2 * u := by linarith
  rw [div_le_div_iff_of_pos_right h2u]
  -- Goal: 1 - exp(-(2u)) ≤ 1, i.e. exp(-(2u)) ≥ 0.
  have h_exp_nn : 0 ≤ Real.exp (-(2 * u)) := le_of_lt (Real.exp_pos _)
  linarith

/-- The variance decay limit at infinity: `K_GLW(u, u) → 0` as `u → ∞`.
The deterministic content of "tail-decay-of-Y-marginal in L²". -/
theorem K_GLW_var_tendsto_zero :
    Filter.Tendsto (fun u : ℝ => K_GLW u u) Filter.atTop (nhds 0) := by
  -- Apply `Tendsto.squeeze_atTop` style: use the eventual sandwich
  -- `0 ≤ K_GLW(u, u) ≤ 1/(2u)` for `u > 0` and `1/(2u) → 0`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Pick a strict threshold `N := max 1 (1/(2ε) + 1)` to avoid the
  -- boundary case `u = 1/(2ε)`.
  refine ⟨max 1 (1 / (2 * ε) + 1), fun u hu => ?_⟩
  have hu_pos : 0 < u := lt_of_lt_of_le one_pos (le_of_max_le_left hu)
  have hu_lower : 1 / (2 * ε) + 1 ≤ u := le_of_max_le_right hu
  have h_kvar_pos : 0 ≤ K_GLW u u :=
    le_of_lt (K_GLW_pos u u (le_of_lt hu_pos) (le_of_lt hu_pos))
  have h_kvar_le : K_GLW u u ≤ 1 / (2 * u) := K_GLW_var_le_recip hu_pos
  -- Convert to the metric statement.
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_kvar_pos]
  -- Show `K_GLW u u < ε`.
  apply lt_of_le_of_lt h_kvar_le
  -- 1/(2u) < ε. Use the strict bound from `1/(2ε) < 1/(2ε) + 1 ≤ u`.
  have hu_strict : 1 / (2 * ε) < u := by linarith
  have h2e : 0 < 2 * ε := by linarith
  -- 1/(2ε) < u ⇒ multiply by 2ε > 0: 1 < 2εu ⇒ 1/(2u) < ε.
  rw [div_lt_iff₀ (by positivity)]
  have h_aux : 1 < 2 * ε * u := by
    have := (div_lt_iff₀ h2e).mp hu_strict
    linarith
  linarith

/-! ## 8. Construction blockers (BLOCKER / TRIED / NEEDS)

The following Mathlib gaps prevent the full retirement of `Y_GLW_exists`
in this round. Each is documented in the standard BLOCKER / TRIED / NEEDS
format used elsewhere in the campaign.

### BLOCKER #1: Brownian motion is not in Mathlib.

* **TRIED**: searched
  `Mathlib/Probability/Process/{Adapted,Filtration,FiniteDimensionalLaws,
  HittingTime,Kolmogorov,PartitionFiltration,Predictable,Stopping}.lean`
  and `Mathlib/Probability/Distributions/Gaussian/{Basic,CharFun,Fernique,
  Real}.lean`. None of these define a Brownian-motion measure or process.
* **NEEDS**: `IsBrownianMotion B` or `wienerMeasure : Measure C([0,∞), ℝ)`
  with the standard properties (`B 0 = 0`, independent increments,
  `B t - B s ~ N(0, t-s)`, continuous paths).

### BLOCKER #2: Wiener integral against deterministic L² integrands.

* **TRIED**: searched for `wienerIntegral`, `WienerIntegral`,
  `stochasticIntegral`, `IsItoProcess`. Mathlib has Bochner integration
  and L² spaces, but no Wiener integral / Itô isometry.
* **NEEDS**: `wienerIntegral : (ℝ → ℝ) → Ω → ℝ` defined for
  deterministic `f ∈ L²([0,1], λ)`, satisfying:
  - linearity in `f`,
  - centeredness `E[wienerIntegral f] = 0`,
  - **Itô isometry** `E[(wienerIntegral f)(wienerIntegral g)] =
    ⟨f, g⟩_{L²([0,1])}`,
  - measurability and a.s.-defined.

### BLOCKER #3: Joint Gaussianity of finite linear combinations.

* **TRIED**: Mathlib has `IsGaussian` for measures on locally-convex
  spaces, but the statement `∀ n us cs, IsGaussian (Measure.map (fun ω
  => ∑ i, cs i * Y (us i) ω) μ)` requires a Gaussian-process abstraction
  not yet present.
* **NEEDS**: an `IsGaussianProcess Y μ` predicate, or the closure of
  `IsGaussian` under L² limits + linear maps.

### BLOCKER #4: Continuous sample paths via Kolmogorov–Chentsov.

* **TRIED**: `Mathlib/Probability/Process/Kolmogorov.lean` defines
  Kolmogorov's *zero-one law*, not the Kolmogorov–Chentsov continuity
  criterion. The latter would give continuous-path modifications from
  L²-Hölder bounds.
* **NEEDS**: `kolmogorov_chentsov : ∀ ε > 0, ∃ δ > 0,
  E[|Y t - Y s|²] ≤ C |t - s|^(2 + δ) → ∃ Ỹ ~ Y, ContinuousPaths Ỹ`.

### BLOCKER #5: Tail decay via Borell + Borel–Cantelli.

* **TRIED**: Mathlib has `IsGaussian.fernique` for Fernique's theorem
  on Gaussian Banach-space norms, but no Borell-type concentration on
  `sup_{u ∈ [T, T+1]} |Y u|`.
* **NEEDS**: Borell's inequality on the supremum of a centered Gaussian
  process.

### Remediation timeline

A direct path to all five blockers exists once mathlib gains Brownian
motion and the Wiener integral: when those land, the present file can be
extended with a `Y_GLW` *theorem* replacing the axiom, with the analytic
content (covariance, Mercer representation, PSD) already in place here.

Until then, this file's deterministic-analytic content gives the
`K_GLW`-side of the construction so the eventual Wiener-integral
plug-in is a one-line application of the Itô isometry. -/

end Erdos524.Helpers
