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

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import FormalConjectures.ErdosProblems.Helpers.BinomialTailBeta

/-!
# Carter–Pollard h-function and cubic Taylor bound (TC11)

Carter, A.V. and Pollard, D. (2004), "Tusnády's inequality revisited,"
*Annals of Statistics* 32(6), 2731–2741. arXiv:math/0508606.

This file implements **§2 eq (8) / §4 first paragraph** of the paper:
the Carter–Pollard h-function and its cubic Taylor upper bound.

  `h(ε, s) := H((1-s)/2; ε) - H(1/2; ε)
            = (1/2)(1+ε) · log(1-s) + (1/2)(1-ε) · log(1+s)`

The closure target is the cubic Taylor bound (paper page 7):

  `∀ ε ∈ [0, 1], ∀ s ∈ [0, 1),  h(ε, s) ≤ ε²/2 - (s + ε)²/2`.

Equivalently `h(ε, s) ≤ -εs - s²/2`.

## Paper typo flag

The paper page 7 prints `h'''(s) = -[6s + 2s² + ε(2 + 6s²)] / (1-s²)³`,
which is a typo for `-[6s + 2s³ + ε(2 + 6s²)]`. This file uses the
**corrected** form
  `h'''(ε, s) = -2 · (3s + s³ + ε(1 + 3s²)) / (1 - s²)³`.
The qualitative claims `h'''(s) ≤ 0` and `h'''(0) = -2ε` (the only ones
used downstream in TC12) are unaffected by the typo.

See `Helpers/TrackC_round11_T1_TaylorAudit.md` for derivation, claims
verification table, and strategy choice (Strategy A: `taylor_mean_remainder_lagrange`).
-/

namespace FormalConjectures.ErdosProblems.Helpers.CarterPollardH

open Real Set

/-- TC12 beta-integral bridge at `p = 1/2`.

This specializes the TC9/TC10 binomial-tail beta identity to the symmetric
binomial tail used in Carter--Pollard §2. A later algebra-only adapter can
rewrite `binomialPolyTail n k (1/2)` as the raw `(1/2)^n * ∑ choose` form
from the paper. -/
theorem bin_tail_beta_integral_half_poly
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Erdos524.Helpers.binomialPolyTail n k (1 / 2 : ℝ) =
      ((n : ℝ) * ((n - 1).choose (k - 1) : ℝ)) *
        Erdos524.Helpers.betaPartialIntegral n k (1 / 2) := by
  simpa using
    (Erdos524.Helpers.binomial_tail_beta_integral n k hk hkn
      (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num))

/-- Carter–Pollard h-function (arXiv:math/0508606 §2 eq (8)).

After cancellation of the constant logs in `H((1-s)/2; ε) - H(1/2; ε)`,
this reduces to
  `h(ε, s) = (1/2)(1+ε) · log(1-s) + (1/2)(1-ε) · log(1+s)`.

The function is concave on `(-1, 1)` and achieves its maximum (=0) at `s = 0`. -/
noncomputable def carterPollardH (ε s : ℝ) : ℝ :=
  (1 / 2) * (1 + ε) * Real.log (1 - s) + (1 / 2) * (1 - ε) * Real.log (1 + s)

@[simp] lemma carterPollardH_zero (ε : ℝ) : carterPollardH ε 0 = 0 := by
  unfold carterPollardH
  simp

/-- First-derivative `HasDerivAt` form at `s ∈ (-1, 1)`.
The "as-built" derivative is `(1/2)(1+ε) · (-1/(1-s)) + (1/2)(1-ε) · (1/(1+s))`,
which equals `-(1+ε)/(2(1-s)) + (1-ε)/(2(1+s))`. -/
lemma carterPollardH_hasDerivAt
    (ε : ℝ) {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    HasDerivAt (carterPollardH ε)
      ((1 / 2) * (1 + ε) * (-1 / (1 - s)) + (1 / 2) * (1 - ε) * (1 / (1 + s))) s := by
  have h1ne : (1 : ℝ) - s ≠ 0 := by linarith
  have h2ne : (1 : ℝ) + s ≠ 0 := by linarith
  have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => (1 : ℝ) + s) 1 s := by
    simpa using (hasDerivAt_id s).const_add 1
  have hlog1 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - s)) s :=
    h1.log h1ne
  have hlog2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s :=
    h2.log h2ne
  have hT1 : HasDerivAt (fun s : ℝ => (1 / 2) * (1 + ε) * Real.log (1 - s))
      ((1 / 2) * (1 + ε) * (-1 / (1 - s))) s := hlog1.const_mul _
  have hT2 : HasDerivAt (fun s : ℝ => (1 / 2) * (1 - ε) * Real.log (1 + s))
      ((1 / 2) * (1 - ε) * (1 / (1 + s))) s := hlog2.const_mul _
  exact hT1.add hT2

/-- `h'(ε, 0) = -ε`. -/
lemma carterPollardH_deriv_zero (ε : ℝ) :
    deriv (carterPollardH ε) 0 = -ε := by
  have h := (carterPollardH_hasDerivAt ε (s := 0) (by norm_num) (by norm_num)).deriv
  simp at h
  linarith [h]

/-! ### First-derivative closed form (`h'`) -/

/-- Closed form for the first derivative of `carterPollardH`:
    `h'(ε, s) = -((1+ε)/2) · (1-s)⁻¹ + ((1-ε)/2) · (1+s)⁻¹`. -/
noncomputable def carterPollardH_d1 (ε s : ℝ) : ℝ :=
  -((1 + ε) / 2) * (1 - s)⁻¹ + ((1 - ε) / 2) * (1 + s)⁻¹

/-- `HasDerivAt (carterPollardH ε) (carterPollardH_d1 ε s) s` for `s ∈ (-1, 1)`. -/
lemma carterPollardH_hasDerivAt_d1
    (ε : ℝ) {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    HasDerivAt (carterPollardH ε) (carterPollardH_d1 ε s) s := by
  have h := carterPollardH_hasDerivAt ε hs1 hs2
  have h1ne : (1 : ℝ) - s ≠ 0 := by linarith
  have h2ne : (1 : ℝ) + s ≠ 0 := by linarith
  refine h.congr_deriv ?_
  unfold carterPollardH_d1
  field_simp

/-! ### Second-derivative closed form (`h''`) -/

/-- Closed form for the second derivative of `carterPollardH`:
    `h''(ε, s) = -(1+ε)/(2(1-s)²) - (1-ε)/(2(1+s)²)`. -/
noncomputable def carterPollardH_d2 (ε s : ℝ) : ℝ :=
  -((1 + ε) / (2 * (1 - s)^2)) - ((1 - ε) / (2 * (1 + s)^2))

/-- `HasDerivAt (carterPollardH_d1 ε) (carterPollardH_d2 ε s) s` for `s ∈ (-1, 1)`. -/
lemma carterPollardH_d1_hasDerivAt
    (ε : ℝ) {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    HasDerivAt (carterPollardH_d1 ε) (carterPollardH_d2 ε s) s := by
  have h1ne : (1 : ℝ) - s ≠ 0 := by linarith
  have h2ne : (1 : ℝ) + s ≠ 0 := by linarith
  have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => (1 : ℝ) + s) 1 s := by
    simpa using (hasDerivAt_id s).const_add 1
  -- (h1.inv h1ne) : HasDerivAt (fun y => (1-y)⁻¹) (-(-1)/(1-s)^2) s
  -- (h2.inv h2ne) : HasDerivAt (fun y => (1+y)⁻¹) (-1/(1+s)^2) s
  have hT1 : HasDerivAt (fun s : ℝ => -((1 + ε) / 2) * (1 - s)⁻¹)
      (-((1 + ε) / 2) * (-(-1) / (1 - s)^2)) s := (h1.inv h1ne).const_mul _
  have hT2 : HasDerivAt (fun s : ℝ => ((1 - ε) / 2) * (1 + s)⁻¹)
      (((1 - ε) / 2) * (-1 / (1 + s)^2)) s := (h2.inv h2ne).const_mul _
  have h := hT1.add hT2
  refine h.congr_deriv ?_
  unfold carterPollardH_d2
  field_simp
  ring

/-! ### Third-derivative closed form (`h'''`)

**Note (paper typo)**: arXiv:math/0508606 page 7 prints
`h'''(s) = -[6s + 2s² + ε(2 + 6s²)] / (1-s²)³`. The correct expression
is `-[6s + 2s³ + ε(2 + 6s²)] = -2(3s + s³ + ε(1 + 3s²))`. The qualitative
claims `h'''(s) ≤ 0` and `h'''(0) = -2ε` are unaffected. -/

/-- Closed form for the third derivative of `carterPollardH`:
    `h'''(ε, s) = -2 · (3s + s³ + ε(1 + 3s²)) / (1 - s²)³`. -/
noncomputable def carterPollardH_d3 (ε s : ℝ) : ℝ :=
  -2 * (3 * s + s^3 + ε * (1 + 3 * s^2)) / (1 - s^2)^3

/-- `HasDerivAt (carterPollardH_d2 ε) (carterPollardH_d3 ε s) s` for `s ∈ (-1, 1)`. -/
lemma carterPollardH_d2_hasDerivAt
    (ε : ℝ) {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    HasDerivAt (carterPollardH_d2 ε) (carterPollardH_d3 ε s) s := by
  have h1ne : (1 : ℝ) - s ≠ 0 := by linarith
  have h2ne : (1 : ℝ) + s ≠ 0 := by linarith
  have h1ne_sq : ((1 : ℝ) - s)^2 ≠ 0 := pow_ne_zero _ h1ne
  have h2ne_sq : ((1 : ℝ) + s)^2 ≠ 0 := pow_ne_zero _ h2ne
  have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => (1 : ℝ) + s) 1 s := by
    simpa using (hasDerivAt_id s).const_add 1
  -- (h1.pow 2) : HasDerivAt (fun y => (1-y)^2) (↑2 * (1-s)^(2-1) * (-1)) s
  -- (h2.pow 2) : HasDerivAt (fun y => (1+y)^2) (↑2 * (1+s)^(2-1) * 1)    s
  -- (... .inv ...) : HasDerivAt (((·)^2)⁻¹) (-((deriv-value)) / ((1∓s)^2)^2) s
  have hT1 : HasDerivAt (fun s : ℝ => -((1 + ε) / 2) * ((1 - s)^2)⁻¹)
      (-((1 + ε) / 2) * (-(↑2 * (1 - s)^(2 - 1) * (-1)) / ((1 - s)^2)^2)) s :=
    ((h1.pow 2).inv h1ne_sq).const_mul _
  have hT2 : HasDerivAt (fun s : ℝ => -((1 - ε) / 2) * ((1 + s)^2)⁻¹)
      (-((1 - ε) / 2) * (-(↑2 * (1 + s)^(2 - 1) * 1) / ((1 + s)^2)^2)) s :=
    ((h2.pow 2).inv h2ne_sq).const_mul _
  -- The function `s ↦ -((1+ε)/2)·((1-s)²)⁻¹ + -((1-ε)/2)·((1+s)²)⁻¹` equals `carterPollardH_d2 ε`.
  -- Reroute the goal through this form via a function equality.
  have hfun : carterPollardH_d2 ε =
      (fun s : ℝ => -((1 + ε) / 2) * ((1 - s)^2)⁻¹ + -((1 - ε) / 2) * ((1 + s)^2)⁻¹) := by
    funext t
    unfold carterPollardH_d2
    field_simp
    ring
  rw [hfun]
  refine (hT1.add hT2).congr_deriv ?_
  unfold carterPollardH_d3
  rw [show (1 - s^2 : ℝ) = (1 - s) * (1 + s) from by ring, mul_pow]
  field_simp
  ring

/-! ### Iterated-derivative closed-form lemmas

We prove `iteratedDeriv n (carterPollardH ε) s = carterPollardH_dn ε s` for
`n ∈ {1, 2, 3}` and `s ∈ (-1, 1)`. The inductive step uses
`Filter.EventuallyEq.deriv_eq` to swap `deriv (...)` for the closed form on
the open neighbourhood `Ioo (-1) 1`. -/

/-- `iteratedDeriv 1 (carterPollardH ε) s = carterPollardH_d1 ε s` on `(-1, 1)`. -/
lemma carterPollardH_iteratedDeriv_one
    (ε : ℝ) {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    iteratedDeriv 1 (carterPollardH ε) s = carterPollardH_d1 ε s := by
  rw [iteratedDeriv_one]
  exact (carterPollardH_hasDerivAt_d1 ε hs1 hs2).deriv

/-- The first derivative of `carterPollardH` agrees with its closed form on
    a neighbourhood of any point in `(-1, 1)`. -/
private lemma deriv_carterPollardH_eventuallyEq
    (ε : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (carterPollardH ε) =ᶠ[nhds s] carterPollardH_d1 ε := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  exact (carterPollardH_hasDerivAt_d1 ε ht.1 ht.2).deriv

/-- `iteratedDeriv 2 (carterPollardH ε) s = carterPollardH_d2 ε s` on `(-1, 1)`. -/
lemma carterPollardH_iteratedDeriv_two
    (ε : ℝ) {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    iteratedDeriv 2 (carterPollardH ε) s = carterPollardH_d2 ε s := by
  have hs : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hs1, hs2⟩
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [(deriv_carterPollardH_eventuallyEq ε hs).deriv_eq]
  exact (carterPollardH_d1_hasDerivAt ε hs1 hs2).deriv

/-- The second derivative of `carterPollardH` agrees with its closed form
    on a neighbourhood of any point in `(-1, 1)`. -/
private lemma iteratedDeriv_two_carterPollardH_eventuallyEq
    (ε : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDeriv 2 (carterPollardH ε) =ᶠ[nhds s] carterPollardH_d2 ε := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  exact carterPollardH_iteratedDeriv_two ε ht.1 ht.2

/-- `iteratedDeriv 3 (carterPollardH ε) s = carterPollardH_d3 ε s` on `(-1, 1)`. -/
lemma carterPollardH_iteratedDeriv_three
    (ε : ℝ) {s : ℝ} (hs1 : -1 < s) (hs2 : s < 1) :
    iteratedDeriv 3 (carterPollardH ε) s = carterPollardH_d3 ε s := by
  have hs : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hs1, hs2⟩
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  rw [(iteratedDeriv_two_carterPollardH_eventuallyEq ε hs).deriv_eq]
  exact (carterPollardH_d2_hasDerivAt ε hs1 hs2).deriv

/-! ### Sign of the third derivative -/

/-- `carterPollardH_d3 ε s ≤ 0` for `s ∈ [0, 1)`, `ε ∈ [0, 1]`.
    Numerator `-2 · (3s + s³ + ε(1 + 3s²)) ≤ 0` since the bracket is
    nonneg; denominator `(1 - s²)³ > 0`. -/
lemma carterPollardH_d3_nonpos
    {ε : ℝ} (hε0 : 0 ≤ ε) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    carterPollardH_d3 ε s ≤ 0 := by
  unfold carterPollardH_d3
  have hbracket : 0 ≤ 3 * s + s^3 + ε * (1 + 3 * s^2) := by
    have h1 : (0 : ℝ) ≤ 3 * s := by positivity
    have h2 : (0 : ℝ) ≤ s^3 := by positivity
    have h3 : (0 : ℝ) ≤ ε * (1 + 3 * s^2) := by positivity
    linarith
  have hnum : -2 * (3 * s + s^3 + ε * (1 + 3 * s^2)) ≤ 0 := by
    have : (0 : ℝ) ≤ 2 * (3 * s + s^3 + ε * (1 + 3 * s^2)) := by linarith
    linarith
  have hden_pos : 0 < (1 - s^2)^3 := by
    have h1ms : 0 < 1 - s^2 := by nlinarith
    positivity
  exact div_nonpos_of_nonpos_of_nonneg hnum hden_pos.le

/-- `iteratedDeriv 3 (carterPollardH ε) s ≤ 0` for `s ∈ [0, 1)`, `ε ∈ [0, 1]`.
    This is the qualitative bound the paper §4 (page 7) uses to drop the cubic
    Taylor remainder. -/
lemma carterPollardH_iteratedDeriv_three_nonpos
    {ε : ℝ} (hε0 : 0 ≤ ε) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    iteratedDeriv 3 (carterPollardH ε) s ≤ 0 := by
  rw [carterPollardH_iteratedDeriv_three ε (by linarith) hs1]
  exact carterPollardH_d3_nonpos hε0 hs0 hs1

/-! ### Smoothness of `carterPollardH` on `(-1, 1)` -/

/-- `carterPollardH ε` is `C^∞` at any point of `(-1, 1)`. -/
lemma carterPollardH_contDiffAt
    (ε : ℝ) {x : ℝ} (hx1 : -1 < x) (hx2 : x < 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (carterPollardH ε) x := by
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith
  have h2 : (1 : ℝ) + x ≠ 0 := by linarith
  have hsub : ContDiffAt ℝ n (fun y : ℝ => (1 : ℝ) - y) x :=
    contDiffAt_const.sub contDiffAt_id
  have hadd : ContDiffAt ℝ n (fun y : ℝ => (1 : ℝ) + y) x :=
    contDiffAt_const.add contDiffAt_id
  have hlog1 : ContDiffAt ℝ n (fun y : ℝ => Real.log (1 - y)) x := hsub.log h1
  have hlog2 : ContDiffAt ℝ n (fun y : ℝ => Real.log (1 + y)) x := hadd.log h2
  have hT1 : ContDiffAt ℝ n (fun y : ℝ => (1 / 2) * (1 + ε) * Real.log (1 - y)) x :=
    contDiffAt_const.mul hlog1
  have hT2 : ContDiffAt ℝ n (fun y : ℝ => (1 / 2) * (1 - ε) * Real.log (1 + y)) x :=
    contDiffAt_const.mul hlog2
  exact hT1.add hT2

/-- `carterPollardH ε` is `ContDiffOn ℝ n` on `Icc 0 s` for any `s < 1`. -/
lemma carterPollardH_contDiffOn_Icc
    (ε : ℝ) {s : ℝ} (hs : s < 1) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (carterPollardH ε) (Set.Icc (0 : ℝ) s) := by
  intro x hx
  have hx1 : -1 < x := by linarith [hx.1]
  have hx2 : x < 1 := by linarith [hx.2]
  exact (carterPollardH_contDiffAt ε hx1 hx2).contDiffWithinAt

/-! ### Cubic Taylor upper bound (closure target) -/

/-- **Carter–Pollard 2004 §4 cubic Taylor bound** (arXiv:math/0508606 page 7).

For `ε ∈ [0, 1]` and `s ∈ [0, 1)`,
  `h(ε, s) ≤ ε²/2 − (s + ε)²/2`.

Equivalently `h(ε, s) ≤ −εs − s²/2`. Proof: Taylor's theorem with Lagrange
remainder at order 2, using `h(0) = 0`, `h'(0) = −ε`, `h''(0) = −1`, and
the third-derivative bound `h'''(t) ≤ 0` to drop the cubic remainder. -/
theorem carterPollardH_taylor_upper_bound
    {ε : ℝ} (hε0 : 0 ≤ ε) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    carterPollardH ε s ≤ ε^2 / 2 - (s + ε)^2 / 2 := by
  -- Boundary case s = 0: both sides are 0.
  rcases eq_or_lt_of_le hs0 with hseq | hspos
  · subst hseq
    have : carterPollardH ε 0 = 0 := carterPollardH_zero ε
    rw [this]
    nlinarith
  -- Main case 0 < s < 1.
  have hUDO : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) s) := uniqueDiffOn_Icc hspos
  have hCD3 : ContDiffOn ℝ 3 (carterPollardH ε) (Set.Icc 0 s) :=
    carterPollardH_contDiffOn_Icc ε hs1
  have hCD2 : ContDiffOn ℝ 2 (carterPollardH ε) (Set.Icc 0 s) :=
    hCD3.of_le (by norm_num)
  have hDiff2 : DifferentiableOn ℝ
      (iteratedDerivWithin 2 (carterPollardH ε) (Set.Icc 0 s)) (Set.Ioo 0 s) := by
    have hWhole := hCD3.differentiableOn_iteratedDerivWithin (m := 2) (by norm_num) hUDO
    exact hWhole.mono Set.Ioo_subset_Icc_self
  obtain ⟨s', hs'mem, hsTaylor⟩ :=
    taylor_mean_remainder_lagrange hspos hCD2 hDiff2
  -- Bridge iteratedDerivWithin n f (Icc 0 s) 0 = iteratedDeriv n f 0 (n = 0, 1, 2).
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) s := Set.left_mem_Icc.mpr hspos.le
  have hb1 : iteratedDerivWithin 1 (carterPollardH ε) (Set.Icc 0 s) 0
      = iteratedDeriv 1 (carterPollardH ε) 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO
      (carterPollardH_contDiffAt ε (by norm_num) (by norm_num : (0 : ℝ) < 1)) hzero_mem
  have hb2 : iteratedDerivWithin 2 (carterPollardH ε) (Set.Icc 0 s) 0
      = iteratedDeriv 2 (carterPollardH ε) 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO
      (carterPollardH_contDiffAt ε (by norm_num) (by norm_num : (0 : ℝ) < 1)) hzero_mem
  -- Compute the Taylor polynomial value.
  have hd1_zero : carterPollardH_d1 ε 0 = -ε := by
    unfold carterPollardH_d1; ring
  have hd2_zero : carterPollardH_d2 ε 0 = -1 := by
    unfold carterPollardH_d2; ring
  have htaylor : taylorWithinEval (carterPollardH ε) 2 (Set.Icc 0 s) 0 s
      = -ε * s - s^2 / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
               iteratedDerivWithin_zero, carterPollardH_zero,
               sub_zero, smul_eq_mul]
    rw [hb1, hb2,
        carterPollardH_iteratedDeriv_one ε (by norm_num) (by norm_num : (0 : ℝ) < 1),
        carterPollardH_iteratedDeriv_two ε (by norm_num) (by norm_num : (0 : ℝ) < 1),
        hd1_zero, hd2_zero]
    simp [Nat.factorial]
    ring
  -- Bridge iteratedDerivWithin 3 f (Icc 0 s) s' = iteratedDeriv 3 f s'.
  have hs'1 : -1 < s' := by linarith [hs'mem.1]
  have hs'2 : s' < 1 := by linarith [hs'mem.2]
  have hb3 : iteratedDerivWithin 3 (carterPollardH ε) (Set.Icc 0 s) s'
      = iteratedDeriv 3 (carterPollardH ε) s' :=
    iteratedDerivWithin_eq_iteratedDeriv hUDO
      (carterPollardH_contDiffAt ε hs'1 hs'2) (Set.Ioo_subset_Icc_self hs'mem)
  -- Bound the remainder.
  have hd3_le : iteratedDeriv 3 (carterPollardH ε) s' ≤ 0 :=
    carterPollardH_iteratedDeriv_three_nonpos hε0 hs'mem.1.le hs'2
  have hs3_pos : 0 ≤ (s - 0)^(2 + 1) := by
    rw [sub_zero]; positivity
  have hfact_pos : (0 : ℝ) < ((2 + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 + 1)
  have hrem_nonpos :
      iteratedDerivWithin 3 (carterPollardH ε) (Set.Icc 0 s) s'
        * (s - 0)^(2 + 1) / ((2 + 1).factorial : ℝ) ≤ 0 := by
    rw [hb3]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg hd3_le hs3_pos
    · exact hfact_pos.le
  have hdiff_nonpos :
      carterPollardH ε s - taylorWithinEval (carterPollardH ε) 2 (Set.Icc 0 s) 0 s ≤ 0 := by
    rw [hsTaylor]; exact hrem_nonpos
  have hf_le : carterPollardH ε s ≤ taylorWithinEval (carterPollardH ε) 2 (Set.Icc 0 s) 0 s := by
    linarith
  rw [htaylor] at hf_le
  have alg : (-ε * s - s^2 / 2 : ℝ) = ε^2 / 2 - (s + ε)^2 / 2 := by ring
  linarith [alg, hf_le]

/-- TC12 pointwise bulk-upper integrand domination.

This is the paper §4 upper-bound payload extracted from
`carterPollardH_taylor_upper_bound`: after subtracting `Nε²/2` from the
exponent, the Carter--Pollard integrand is bounded by the translated
Gaussian kernel. The remaining TC12 work is the interval-integral monotonicity
and Gaussian-tail evaluation step. -/
theorem carterPollardH_exp_bulk_upper_pointwise
    {N ε s : ℝ} (hN0 : 0 ≤ N) (hε0 : 0 ≤ ε) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2) ≤
      Real.exp (-(N * (s + ε) ^ 2) / 2) := by
  have hh := carterPollardH_taylor_upper_bound (ε := ε) hε0 hs0 hs1
  have hmul : N * carterPollardH ε s ≤
      N * (ε ^ 2 / 2 - (s + ε) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hh hN0
  apply Real.exp_le_exp.mpr
  calc
    N * carterPollardH ε s - N * ε ^ 2 / 2
        ≤ N * (ε ^ 2 / 2 - (s + ε) ^ 2 / 2) - N * ε ^ 2 / 2 := by
          linarith
    _ = -(N * (s + ε) ^ 2) / 2 := by ring

/-- TC12 bulk-upper interval domination on compact prefixes `[0, r]`, `r < 1`.

The paper's final bound integrates over `[0, 1]`; this prefix form is the
safe Lean-local version at the current Mathlib pin. It avoids assigning
continuity of `log (1 - s)` at the endpoint `s = 1`, and it is the exact
monotone-integral consequence of `carterPollardH_exp_bulk_upper_pointwise`
needed before the separate improper-limit / Gaussian-tail step. -/
theorem carterPollardH_exp_bulk_upper_interval_prefix
    {N ε r : ℝ} (hN0 : 0 ≤ N) (hε0 : 0 ≤ ε) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ s in (0 : ℝ)..r, Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2) ≤
      ∫ s in (0 : ℝ)..r, Real.exp (-(N * (s + ε) ^ 2) / 2) := by
  let f : ℝ → ℝ := fun s => Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2)
  let g : ℝ → ℝ := fun s => Real.exp (-(N * (s + ε) ^ 2) / 2)
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) r) := by
    dsimp [f]
    have hH : ContinuousOn (carterPollardH ε) (Set.Icc (0 : ℝ) r) :=
      (carterPollardH_contDiffOn_Icc (n := 0) ε hr1).continuousOn
    have hlin : ContinuousOn
        (fun s => N * carterPollardH ε s - N * ε ^ 2 / 2) (Set.Icc (0 : ℝ) r) :=
      (continuousOn_const.mul hH).sub continuousOn_const
    exact continuous_exp.comp_continuousOn hlin
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) r) := by
    dsimp [g]
    have hadd : ContinuousOn (fun s : ℝ => s + ε) (Set.Icc (0 : ℝ) r) :=
      continuousOn_id.add continuousOn_const
    have hsq : ContinuousOn (fun s : ℝ => (s + ε) ^ 2) (Set.Icc (0 : ℝ) r) :=
      hadd.pow 2
    have harg : ContinuousOn (fun s : ℝ => -(N * (s + ε) ^ 2) / 2)
        (Set.Icc (0 : ℝ) r) :=
      ((continuousOn_const.mul hsq).neg).div_const 2
    exact continuous_exp.comp_continuousOn harg
  have hf_int : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) r :=
    (by
      have hf_cont_u : ContinuousOn f (Set.uIcc (0 : ℝ) r) := by
        simpa [Set.uIcc_of_le hr0] using hf_cont
      exact hf_cont_u.intervalIntegrable)
  have hg_int : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) r :=
    (by
      have hg_cont_u : ContinuousOn g (Set.uIcc (0 : ℝ) r) := by
        simpa [Set.uIcc_of_le hr0] using hg_cont
      exact hg_cont_u.intervalIntegrable)
  exact intervalIntegral.integral_mono_on hr0 hf_int hg_int (fun s hs => by
    exact carterPollardH_exp_bulk_upper_pointwise hN0 hε0 hs.1 (lt_of_le_of_lt hs.2 hr1))

/-- TC13 full-interval raw bulk-upper domination.

This is the `[0,1]` version of the TC12 compact-prefix theorem. It deliberately
stops before any Gaussian-tail/CDF evaluation: the right-hand side remains a raw
interval integral. -/
theorem carterPollardH_exp_bulk_upper_full
    {N ε : ℝ} (hN0 : 0 ≤ N) (hε0 : 0 ≤ ε) :
    ∫ s in (0 : ℝ)..1, Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2) ≤
      ∫ s in (0 : ℝ)..1, Real.exp (-(N * (s + ε) ^ 2) / 2) := by
  let f : ℝ → ℝ := fun s => Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2)
  let g : ℝ → ℝ := fun s => Real.exp (-(N * (s + ε) ^ 2) / 2)
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) 1) := by
    dsimp [g]
    have hg_cont_Icc : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
      dsimp [g]
      have hadd : ContinuousOn (fun s : ℝ => s + ε) (Set.Icc (0 : ℝ) 1) :=
        continuousOn_id.add continuousOn_const
      have hsq : ContinuousOn (fun s : ℝ => (s + ε) ^ 2) (Set.Icc (0 : ℝ) 1) :=
        hadd.pow 2
      have harg : ContinuousOn (fun s : ℝ => -(N * (s + ε) ^ 2) / 2)
          (Set.Icc (0 : ℝ) 1) :=
        ((continuousOn_const.mul hsq).neg).div_const 2
      exact continuous_exp.comp_continuousOn harg
    simpa [Set.uIcc_of_le h01] using hg_cont_Icc
  have hg_int : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) 1 :=
    hg_cont.intervalIntegrable
  have hf_cont_Ioo : ContinuousOn f (Set.Ioo (0 : ℝ) 1) := by
    dsimp [f]
    have hH : ContinuousOn (carterPollardH ε) (Set.Ioo (0 : ℝ) 1) := by
      intro s hs
      have hcd : ContDiffAt ℝ 0 (carterPollardH ε) s :=
        carterPollardH_contDiffAt ε (by linarith [hs.1]) hs.2
      exact hcd.continuousAt.continuousWithinAt
    have hlin : ContinuousOn
        (fun s => N * carterPollardH ε s - N * ε ^ 2 / 2) (Set.Ioo (0 : ℝ) 1) :=
      (continuousOn_const.mul hH).sub continuousOn_const
    exact continuous_exp.comp_continuousOn hlin
  have hf_aestronglyMeasurable_Ioo :
      MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hf_cont_Ioo.aestronglyMeasurable measurableSet_Ioo
  have hf_aestronglyMeasurable :
      MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le h01, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact hf_aestronglyMeasurable_Ioo
  have hle_ae :
      (fun s => ‖f s‖) ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)] g := by
    rw [Set.uIoc_of_le h01, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    have hf_nonneg : 0 ≤ f s := by
      dsimp [f]
      exact (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hf_nonneg]
    exact carterPollardH_exp_bulk_upper_pointwise hN0 hε0 hs.1.le hs.2
  have hf_int : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 :=
    IntervalIntegrable.mono_fun' hg_int hf_aestronglyMeasurable hle_ae
  simpa [f, g] using
    (intervalIntegral.integral_mono_on_of_le_Ioo h01 hf_int hg_int (fun s hs => by
      exact carterPollardH_exp_bulk_upper_pointwise hN0 hε0 hs.1.le hs.2))

/-- TC14 raw Gaussian-tail substitution.

This is the direct affine change of variables `t = √N (s + ε)` applied to
the TC13 raw bulk upper bound, followed by enlarging the finite interval to
the one-sided tail. No Gaussian CDF API is used. -/
theorem carterPollardH_exp_bulk_upper_gaussian_tail
    {N ε : ℝ} (hN0 : 0 < N) (hε0 : 0 ≤ ε) :
    ∫ s in (0 : ℝ)..1, Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2) ≤
      (Real.sqrt N)⁻¹ *
        ∫ t in Set.Ioi (Real.sqrt N * ε), Real.exp (-t ^ 2 / 2) := by
  let φ : ℝ → ℝ := fun t => Real.exp (-t ^ 2 / 2)
  let c : ℝ := Real.sqrt N
  have hc_pos : 0 < c := Real.sqrt_pos.2 hN0
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hfull := carterPollardH_exp_bulk_upper_full (N := N) (ε := ε) hN0.le hε0
  have hkernel_eq :
      (∫ s in (0 : ℝ)..1, Real.exp (-(N * (s + ε) ^ 2) / 2)) =
        c⁻¹ * ∫ t in c * ε..c * (1 + ε), φ t := by
    have hfun :
        (fun s : ℝ => Real.exp (-(N * (s + ε) ^ 2) / 2)) =
          (fun s : ℝ => φ (c * s + c * ε)) := by
      funext s
      dsimp [φ, c]
      congr 1
      rw [← mul_add, mul_pow, Real.sq_sqrt hN0.le]
    rw [hfun]
    simpa [φ, c, mul_add, add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_comp_mul_add (f := φ) (a := (0 : ℝ)) (b := 1)
        (c := c) (d := c * ε) hc_ne)
  have hφ_int : MeasureTheory.Integrable φ := by
    have h := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    refine h.congr ?_
    filter_upwards with t
    dsimp [φ]
    congr 1
    ring
  have htail_int : MeasureTheory.IntegrableOn φ (Set.Ioi (c * ε)) := hφ_int.integrableOn
  have htail_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (c * ε))] φ :=
    Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)
  have hfinite_subset_tail :
      Set.Ioc (c * ε) (c * (1 + ε)) ≤ᵐ[MeasureTheory.volume] Set.Ioi (c * ε) :=
    Filter.Eventually.of_forall (fun t ht => ht.1)
  have hfinite_tail :
      ∫ t in c * ε..c * (1 + ε), φ t ≤ ∫ t in Set.Ioi (c * ε), φ t := by
    have hε_le : ε ≤ 1 + ε := by linarith
    have hbounds : c * ε ≤ c * (1 + ε) :=
      mul_le_mul_of_nonneg_left hε_le hc_nonneg
    rw [intervalIntegral.integral_of_le hbounds]
    exact MeasureTheory.setIntegral_mono_set htail_int htail_nonneg hfinite_subset_tail
  calc
    ∫ s in (0 : ℝ)..1, Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2)
        ≤ ∫ s in (0 : ℝ)..1, Real.exp (-(N * (s + ε) ^ 2) / 2) := hfull
    _ = c⁻¹ * ∫ t in c * ε..c * (1 + ε), φ t := hkernel_eq
    _ ≤ c⁻¹ * ∫ t in Set.Ioi (c * ε), φ t :=
      mul_le_mul_of_nonneg_left hfinite_tail (inv_nonneg.mpr hc_nonneg)
    _ = (Real.sqrt N)⁻¹ *
        ∫ t in Set.Ioi (Real.sqrt N * ε), Real.exp (-t ^ 2 / 2) := by
      rfl

end FormalConjectures.ErdosProblems.Helpers.CarterPollardH
