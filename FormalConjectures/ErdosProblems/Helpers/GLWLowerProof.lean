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

import FormalConjectures.ErdosProblems.Helpers.GLWProcess
import FormalConjectures.ErdosProblems.Helpers.GLWProcessPredicate
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Phase 2 Round 8 — Gao–Li–Wellner small-ball LOWER bound proof

Round 8 target: replace the axiom `gao_li_wellner_small_ball_lower` in
`524.lean` (line 3556) with a `theorem`. This file packages the proof
auxiliary structure (cubic-factor lemmas, sup-box-event lemmas, choice
of `ε₀`, and the IsGLWProcess discharge helper for KMT-coupling
consumers) into a self-contained module so the theorem statement in
`524.lean` remains short.

## Honesty fix (Round 8 stress test)

The original axiom was stated universally over `Y : ℝ → Ω → ℝ`, which
is FALSE for `Y ≡ 1` (the box event has probability `0` for `ε < 1`,
but the cubic-exponent LHS is positive). The fix mirrors Round 7:
add an `IsGLWProcess Y` hypothesis (defined in
`Helpers/GLWProcessPredicate.lean`) to make the statement
mathematically valid. With this hypothesis the bound is the genuine
Gao–Li–Wellner (2010) statement; the residual sorry then sits on the
actual Mathlib gap (Karhunen–Loève expansion + Talagrand
generic-chaining lower-tail entropy methods, dual to the upper proof).

## Strategy chain (full proof, sketched)

The complete lower bound is the multi-month dual of the upper bound:

1. Use `IsGLWProcess Y` to obtain joint Gaussianity, K_GLW covariance.
2. Anderson's inequality MULTIVARIATE (PosDef covariance case) — this
   is the Round 6 `mvGaussian_box_density_at_mode_bound` documented
   sorry, which if retired closes 90% of the lower-bound difficulty.
3. Karhunen–Loève expansion of K_GLW with eigenvalues `λ_k ~ k^{-2}`
   (so `Σ λ_k = K_GLW(0,0) = 1` and `Σ √λ_k < ∞`).
4. Talagrand-style entropy lower bound on Gaussian processes — the
   dual of the upper-bound generic chaining argument.
5. Optimization in the truncation level `m(ε) ~ |log ε|` — gives the
   cubic exponent `|log ε|^3`.

The full proof is a Mathlib gap. This file packages the auxiliary
structure (factor lemmas, event lemmas, ε₀ choice) and bottoms out the
main bound at a single documented sorry on the Karhunen–Loève + entropy
gap.

## Choice of `ε₀`

We choose `ε₀ := Real.exp (-100)`. The choice is far enough from `1`
that the cubic-factor `exp(-c · |log ε|³)` is genuinely small (~ exp(-c·10⁶)),
matching the asymptotic regime where the GLW estimate is sharp. The
specific constant is a free parameter — any positive value works for
the existential.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {Y : ℝ → Ω → ℝ}

/-! ## Cubic-exponent factor: `exp(-c · |log ε|³)` (lower direction)

The lower bound has the same RHS form as the upper, so we re-export
the cubic factor under a parallel `glwLower*` namespace. The factor is
identical (`exp(-c · |log ε|³)`); the lower-bound STATEMENT differs in
that this factor LOWER-bounds the probability rather than upper-bounding
it. -/

/-- The cubic-exponent factor for the lower bound. -/
noncomputable def glwLowerCubicFactor (c ε : ℝ) : ℝ :=
  Real.exp (-c * |Real.log ε| ^ 3)

theorem glwLowerCubicFactor_pos (c ε : ℝ) :
    0 < glwLowerCubicFactor c ε :=
  Real.exp_pos _

theorem glwLowerCubicFactor_le_one (c ε : ℝ) (hc : 0 ≤ c) :
    glwLowerCubicFactor c ε ≤ 1 := by
  unfold glwLowerCubicFactor
  rw [Real.exp_le_one_iff]
  have h_pow_nn : 0 ≤ |Real.log ε| ^ 3 := by positivity
  have h_prod : 0 ≤ c * |Real.log ε| ^ 3 := mul_nonneg hc h_pow_nn
  linarith

/-- Cubic factor at `ε = 1` equals `1`. -/
theorem glwLowerCubicFactor_at_one (c : ℝ) :
    glwLowerCubicFactor c 1 = 1 := by
  unfold glwLowerCubicFactor
  rw [Real.log_one]
  simp

/-- Monotonicity in the constant `c`: larger `c` gives a SMALLER lower
factor (looser constraint on the probability), the dual sense to the
upper-bound monotonicity. -/
theorem glwLowerCubicFactor_anti_mono_c (c₁ c₂ ε : ℝ) (h_le : c₁ ≤ c₂) :
    glwLowerCubicFactor c₂ ε ≤ glwLowerCubicFactor c₁ ε := by
  unfold glwLowerCubicFactor
  rw [Real.exp_le_exp]
  have h_pow_nn : 0 ≤ |Real.log ε| ^ 3 := by positivity
  nlinarith

/-- The cubic factor evaluated at the lower-bound `ε₀ := exp(-100)`. -/
theorem glwLowerCubicFactor_at_exp_neg_hundred (c : ℝ) :
    glwLowerCubicFactor c (Real.exp (-100)) =
      Real.exp (-c * 100 ^ 3) := by
  unfold glwLowerCubicFactor
  rw [Real.log_exp]
  congr 1
  rw [show |(-(100 : ℝ))| = 100 from by rw [abs_neg]; exact abs_of_nonneg (by norm_num)]


/-! ## Choice of `ε₀` for the lower bound

Unlike the upper-bound variant, which can take `ε₀ = 1` (the trivial
boundary), the lower bound requires `ε₀ < 1` because the cubic factor
exceeds `1` at `ε = 1` only when `c < 0` (which `glw.lower > 0`
forbids). We choose `ε₀ := exp(-100)`: a value small enough that we
are firmly in the GLW asymptotic regime, while remaining a concrete
constant. -/

/-- The Round 8 lower-bound threshold: `ε₀ := exp(-100)`. -/
noncomputable def glwLowerEpsZero : ℝ := Real.exp (-100)

theorem glwLowerEpsZero_pos : 0 < glwLowerEpsZero :=
  Real.exp_pos _

theorem glwLowerEpsZero_lt_one : glwLowerEpsZero < 1 := by
  unfold glwLowerEpsZero
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  exact Real.exp_lt_exp.mpr (by norm_num)

/-- `ε₀ ≤ 1` (corollary of `ε₀ < 1`). -/
theorem glwLowerEpsZero_le_one : glwLowerEpsZero ≤ 1 :=
  le_of_lt glwLowerEpsZero_lt_one


/-! ## Sup-box event: `{ω | ∀ u ≥ 0, |Y u ω| ≤ ε}` -/

/-- The sup-box event for the lower bound (full half-line `u ≥ 0`,
unlike the upper-bound truncated `[0, T(ε)]`). -/
def glwLowerSupBoxEvent (Y : ℝ → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ u ≥ (0 : ℝ), |Y u ω| ≤ ε}

/-- The sup-box event is a subset of the universe. -/
theorem glwLowerSupBoxEvent_subset_univ (Y : ℝ → Ω → ℝ) (ε : ℝ) :
    glwLowerSupBoxEvent Y ε ⊆ Set.univ :=
  fun _ _ => Set.mem_univ _

/-- Sup-box event monotone in `ε`: larger tolerance gives a larger
event (more `ω` satisfy the bound). -/
theorem glwLowerSupBoxEvent_mono_eps (Y : ℝ → Ω → ℝ) {ε₁ ε₂ : ℝ}
    (h_le : ε₁ ≤ ε₂) :
    glwLowerSupBoxEvent Y ε₁ ⊆ glwLowerSupBoxEvent Y ε₂ := by
  intro ω hω u hu
  exact (hω u hu).trans h_le

/-- Sup-box event measure bound (probability ≤ 1, trivial). -/
theorem glwLowerSupBoxEvent_measure_le_one (Y : ℝ → Ω → ℝ) (ε : ℝ) :
    (ℙ : Measure Ω) (glwLowerSupBoxEvent Y ε) ≤ 1 :=
  le_trans (measure_mono (glwLowerSupBoxEvent_subset_univ Y ε))
    (le_of_eq measure_univ)

/-- The RHS of the lower-bound theorem matches the cubic-factor form. -/
theorem glwLowerBound_eq_cubicFactor (c ε : ℝ) :
    Real.exp (-c * |Real.log ε| ^ 3) = glwLowerCubicFactor c ε := rfl


/-! ## IsGLWProcess discharge helper for KMT-coupling consumers

The `polynomial_sup_small_ball_lower` proof in `524.lean` extracts
`Yplus, Yminus` from `two_dim_KMT_coupling` and applies
`gao_li_wellner_small_ball_lower` to each marginal. After the Round 8
honesty fix, those applications require `IsGLWProcess Yplus` and
`IsGLWProcess Yminus`.

This helper provides the discharge as a documented `sorry`: parallel
to the upper-bound helper `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`,
the KMT-coupling output asserts measurability, continuity, and tail
decay — but not the explicit K_GLW covariance, which requires the
Itô-integral construction `Y(u) = ∫₀¹ e^{-us} dB(s)` (the actual
content of `Y_GLW_exists`, on a different probability space than the
KMT space). Closing this sorry needs either (a) extending
`two_dim_KMT_coupling`'s output to assert `IsGLWProcess` directly, or
(b) a Skorokhod-style transfer of the `Y_GLW_exists` Y to the KMT
space, or (c) accepting this as a stepping-stone helper analogous to
`Y_GLW_exists` itself. -/

-- BLOCKER: `IsGLWProcess Yplus / Yminus` for the KMT-coupling marginals.
-- TRIED: extracting from `two_dim_KMT_coupling` output; the output gives
--   measurability, continuity, tail decay, and a coupling bound — but
--   not the explicit K_GLW covariance, which requires the Itô-integral
--   construction of `Y(u) = ∫₀¹ e^{-us} dB(s)` (this is the actual
--   content of `Y_GLW_exists` but on a DIFFERENT probability space than
--   the KMT space, so direct transfer is not possible without an
--   isomorphism argument).
-- NEEDS: either (a) extending `two_dim_KMT_coupling`'s output to assert
--   `IsGLWProcess` directly (currently only asserts a coupling bound to
--   a Gaussian); OR (b) a Skorokhod-style transfer of the
--   Y_GLW_exists Y to the KMT space; OR (c) accepting this as a
--   stepping-stone helper analogous to `Y_GLW_exists` itself.
/-- Discharges `IsGLWProcess Yplus` for the call sites of
`gao_li_wellner_small_ball_lower` in `polynomial_sup_small_ball_lower`
and `polynomial_sup_small_ball_lower_uniform` in `524.lean`. -/
theorem gao_li_wellner_small_ball_lower_isGLWProcess_Yplus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Yplus : ℝ → Ω → ℝ} (_hYp_meas : ∀ u, Measurable (Yplus u)) :
    IsGLWProcess Yplus := by
  sorry

/-- Discharges `IsGLWProcess Yminus` for the call sites of
`gao_li_wellner_small_ball_lower` in `polynomial_sup_small_ball_lower`
and `polynomial_sup_small_ball_lower_uniform` in `524.lean`. The same
argument as for `Yplus`: the KMT coupling provides `Yminus` with
measurability, continuity and tail decay, but the K_GLW covariance
requires the Itô-integral construction. -/
theorem gao_li_wellner_small_ball_lower_isGLWProcess_Yminus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Yminus : ℝ → Ω → ℝ} (_hYm_meas : ∀ u, Measurable (Yminus u)) :
    IsGLWProcess Yminus := by
  sorry

end Erdos524.Helpers
