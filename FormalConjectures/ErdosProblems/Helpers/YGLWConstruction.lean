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

/-! ## 4. Construction blockers (BLOCKER / TRIED / NEEDS)

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

A direct path to all five blockers exists in mathlib4 PR drafts:
`mathlib4#26145` (Brownian motion via Daniell–Kolmogorov) and the
follow-up `#26167` (Wiener integral). When those merge, the present
file can be extended with a `Y_GLW` *theorem* replacing the axiom.

Until then, this file's deterministic-analytic content gives the
`K_GLW`-side of the construction so the eventual Wiener-integral
plug-in is a one-line application of the Itô isometry. -/

end Erdos524.Helpers
