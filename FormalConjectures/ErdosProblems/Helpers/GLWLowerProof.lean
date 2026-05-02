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
import FormalConjectures.ErdosProblems.Helpers.RademacherSequence
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
   was the Round 6 `mvGaussian_box_density_at_mode_bound` sorry, which
   was a Mathlib-level gap. **Closed in Round 9** (commit chain
   `kmc-erdos-glw-lower`, see `MVGaussianDensityBound.lean`); the
   density-at-mode bound is now available, leaving the
   Karhunen–Loève + Talagrand-chaining gap as the dominant remaining
   blocker for the full lower bound.
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

/-- Monotonicity in `ε` (for `0 < ε ≤ 1` and `c ≥ 0`): closer-to-1 `ε`
gives a LARGER factor (less decay). Formally: if `0 < ε₁ ≤ ε₂ ≤ 1`,
then `glwLowerCubicFactor c ε₁ ≤ glwLowerCubicFactor c ε₂`.

Reason: for `ε ∈ (0, 1]`, `log ε ≤ 0` so `|log ε| = -log ε`, and
`ε₁ ≤ ε₂` makes `|log ε₁| ≥ |log ε₂|`, so `-c · |log ε₁|³ ≤
-c · |log ε₂|³` (since `c ≥ 0`), and `exp` is monotone. -/
theorem glwLowerCubicFactor_mono_eps_at_le_one
    (c : ℝ) (hc : 0 ≤ c) {ε₁ ε₂ : ℝ}
    (hε₁_pos : 0 < ε₁) (h_le : ε₁ ≤ ε₂) (hε₂_le_one : ε₂ ≤ 1) :
    glwLowerCubicFactor c ε₁ ≤ glwLowerCubicFactor c ε₂ := by
  unfold glwLowerCubicFactor
  rw [Real.exp_le_exp]
  have hlog_ε₁_nonpos : Real.log ε₁ ≤ 0 := by
    apply Real.log_nonpos (le_of_lt hε₁_pos)
    exact h_le.trans hε₂_le_one
  have hε₂_pos : 0 < ε₂ := lt_of_lt_of_le hε₁_pos h_le
  have hlog_ε₂_nonpos : Real.log ε₂ ≤ 0 := Real.log_nonpos (le_of_lt hε₂_pos) hε₂_le_one
  have h_log_le : Real.log ε₁ ≤ Real.log ε₂ :=
    Real.log_le_log hε₁_pos h_le
  have h_abs_le : |Real.log ε₂| ≤ |Real.log ε₁| := by
    rw [abs_of_nonpos hlog_ε₁_nonpos, abs_of_nonpos hlog_ε₂_nonpos]
    linarith
  have h_pow_le : |Real.log ε₂| ^ 3 ≤ |Real.log ε₁| ^ 3 := by
    have h_nn : 0 ≤ |Real.log ε₂| := abs_nonneg _
    exact pow_le_pow_left₀ h_nn h_abs_le 3
  nlinarith [mul_nonneg hc (abs_nonneg (Real.log ε₁) : (0 : ℝ) ≤ |Real.log ε₁|)]

/-- Strict version: for `c > 0` and `0 < ε < 1`, the cubic factor is
strictly less than `1` (the value at `ε = 1`). Used when one needs to
exclude the boundary case in inequalities. -/
theorem glwLowerCubicFactor_lt_one_of_pos
    {c ε : ℝ} (hc : 0 < c) (hε_pos : 0 < ε) (hε_lt_one : ε < 1) :
    glwLowerCubicFactor c ε < 1 := by
  unfold glwLowerCubicFactor
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm, Real.exp_lt_exp]
  have hlog_neg : Real.log ε < 0 := Real.log_neg hε_pos hε_lt_one
  have habs_pos : 0 < |Real.log ε| := abs_pos.mpr (ne_of_lt hlog_neg)
  have hpow_pos : 0 < |Real.log ε| ^ 3 := pow_pos habs_pos 3
  nlinarith


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

/-- Explicit value of `Real.log ε₀` at the chosen lower-bound threshold. -/
theorem glwLowerEpsZero_log : Real.log glwLowerEpsZero = -100 := by
  unfold glwLowerEpsZero
  exact Real.log_exp (-100)

/-- Explicit value of `|Real.log ε₀| = 100`. -/
theorem glwLowerEpsZero_abs_log : |Real.log glwLowerEpsZero| = 100 := by
  rw [glwLowerEpsZero_log]
  rw [abs_neg]
  exact abs_of_nonneg (by norm_num)

/-- The cubic factor evaluated at the chosen `ε₀ := exp(-100)` simplifies
to `exp(-c · 10^6)`. Useful as a sanity check for the asymptotic regime. -/
theorem glwLowerCubicFactor_at_eps_zero (c : ℝ) :
    glwLowerCubicFactor c glwLowerEpsZero = Real.exp (-c * 100 ^ 3) := by
  unfold glwLowerEpsZero
  exact glwLowerCubicFactor_at_exp_neg_hundred c


/-! ## Sup-box event: `{ω | ∀ u ≥ 0, |Y u ω| ≤ ε}` -/

/-- The sup-box event for the lower bound (full half-line `u ≥ 0`,
unlike the upper-bound truncated `[0, T(ε)]`). -/
def glwLowerSupBoxEvent (Y : ℝ → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ u ≥ (0 : ℝ), |Y u ω| ≤ ε}

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The sup-box event is a subset of the universe. -/
theorem glwLowerSupBoxEvent_subset_univ (Y : ℝ → Ω → ℝ) (ε : ℝ) :
    glwLowerSupBoxEvent Y ε ⊆ Set.univ :=
  fun _ _ => Set.mem_univ _

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
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

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Bridge to the truncated event: the full-window sup-box event is a
SUBSET of any truncated `Icc 0 T` event (smaller window means fewer
constraints to satisfy, hence a LARGER event). Useful when lifting a
bound from the truncated event to the full-window one. -/
theorem glwLowerSupBoxEvent_subset_truncated (Y : ℝ → Ω → ℝ) (T ε : ℝ) :
    glwLowerSupBoxEvent Y ε ⊆ {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, |Y u ω| ≤ ε} := by
  intro ω hω u hu
  exact hω u hu.1

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The full-window event equals the intersection of all positive-T
truncated events. The `⊆` direction follows from
`glwLowerSupBoxEvent_subset_truncated`; the reverse direction holds
because every `u ≥ 0` is in `[0, u]`, and `u ∈ [0, ∞)` is dense in
itself. -/
theorem glwLowerSupBoxEvent_eq_iInter_truncated (Y : ℝ → Ω → ℝ) (ε : ℝ) :
    glwLowerSupBoxEvent Y ε =
      ⋂ T : ℝ, {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, |Y u ω| ≤ ε} := by
  ext ω
  refine ⟨fun hω => Set.mem_iInter.mpr (fun T u hu => hω u hu.1), ?_⟩
  intro hω u hu
  exact (Set.mem_iInter.mp hω u) u ⟨hu, le_refl _⟩

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Anti-monotonicity in the `Y`-process for the truncated form: if
`|Y u ω| ≤ |Y' u ω|` pointwise on `[0, T]`, then any `ω` in the
truncated box-event for `Y'` also lies in the one for `Y` (LARGER `Y`
gives a SMALLER event). The full-window analogue would chain over all
`T`, but the truncated form is what bridge lemmas in `polynomial_sup_*`
typically need. -/
theorem truncatedBoxEvent_anti_mono_proc
    {Y Y' : ℝ → Ω → ℝ} {T ε : ℝ}
    (h_dom : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ ω, |Y u ω| ≤ |Y' u ω|) :
    {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, |Y' u ω| ≤ ε} ⊆
      {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, |Y u ω| ≤ ε} := by
  intro ω hω u hu
  exact (h_dom u hu ω).trans (hω u hu)


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

/-! ### R39 V2 cold re-audit migration (axiom → tightened-signature TAG'd sorry)

Per `Helpers/R39_T1_AlphaConversionAudit.md`, the cold re-audit found that
the R37 axiom form `(_hY_meas : ∀ u, Measurable Y) → IsGLWProcess Y` is
**unsound**: the constant-zero process `Y ≡ 0` is measurable but
`IsGLWProcess.cov 0 0 = K_GLW 0 0 = 1` contradicts `∫ 0 · 0 = 0`. R37's
β-needed verdict (Grok-α-recipe inputs absent from the legacy-Ω 13-tuple)
remains correct as far as it goes but missed this signature-level
soundness issue.

R39 elects **α-tighten**: tighten the helper signature to admit only the
call-site context that pins the law of Y uniquely to GLW — specifically,
the Rademacher sequence `a`, the rate-bound `Δ ≤ log(n+1)/√n`, and the
KMT coupling rate `|n^{-1/2} Σ_k a_k(ω) · ker_k(u/n) - Y u ω| ≤ Δ n`. With
these hypotheses the conclusion `IsGLWProcess Y` is sound (1D KMT +
scaling limit theorem pin Y uniquely as the GLW process), and the
counterexample `Y ≡ 0` is excluded (it does not satisfy the KMT bound for
the unscaled partial sums in the limit n → ∞).

R37's axioms are converted from `axiom` to `theorem ... := by sorry` with
TAG[V2-R39-tighten]. This reduces the user-defined-axiom count
8 → 5, recategorizing the 3 IsGLWProcess obligations from "axiom"
(irreducible black box) to "TAG'd sorry" (Mathlib-infra-pending closure).
The remaining proof obligation lives in the R49-R53 V2 cluster (1D KMT
formalization + scaling limit theorem). -/

/-- Discharges `IsGLWProcess Yplus` for the call sites of
`gao_li_wellner_small_ball_lower` in `polynomial_sup_small_ball_lower`
and `polynomial_sup_small_ball_lower_uniform` in `524.lean`.

**R39 V2 status: TAG'd sorry with α-tightened signature.** Sound modulo
{axiom #1 (D2/Komlós), axiom #2 (1D KMT), Mathlib-side scaling-limit
theorem}. Closure scheduled for R49-R53 (V2 1D KMT cluster). See
`Helpers/R39_T1_AlphaConversionAudit.md` for the cold-audit derivation. -/
theorem gao_li_wellner_small_ball_lower_isGLWProcess_Yplus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {a : ℕ → Ω → ℝ} (_ha : Erdos524.IsRademacherSequence a)
    {Δ : ℕ → ℝ}
    (_hΔ_bd : ∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n)
    {Yplus : ℝ → Ω → ℝ}
    (_hYp_meas : ∀ u, Measurable (Yplus u))
    (_hKMT_p : ∀ n : ℕ, 1 ≤ n → ∀ ω : Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n, a k ω * Real.exp (-u * k / n)) -
          Yplus u ω| ≤ Δ n) :
    IsGLWProcess Yplus := by
  -- TAG[V2-R39-tighten-Yplus-lower]: sound modulo {#1, #2, scaling-limit};
  -- closure deferred to R49-R53 (1D KMT formalization cluster).
  sorry

/-- Discharges `IsGLWProcess Yminus` for the call sites of
`gao_li_wellner_small_ball_lower` in `polynomial_sup_small_ball_lower`
and `polynomial_sup_small_ball_lower_uniform` in `524.lean`.

**R39 V2 status: TAG'd sorry with α-tightened signature** — identical
treatment to the `_Yplus` helper above; the only difference is the
KMT-coupling kernel (`(-Real.exp (-u/n))^k` vs `Real.exp (-u·k/n)`),
which is the second component of the legacy-Ω 13-tuple. -/
theorem gao_li_wellner_small_ball_lower_isGLWProcess_Yminus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {a : ℕ → Ω → ℝ} (_ha : Erdos524.IsRademacherSequence a)
    {Δ : ℕ → ℝ}
    (_hΔ_bd : ∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n)
    {Yminus : ℝ → Ω → ℝ}
    (_hYm_meas : ∀ u, Measurable (Yminus u))
    (_hKMT_m : ∀ n : ℕ, 1 ≤ n → ∀ ω : Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n, a k ω * (-Real.exp (-u / n)) ^ k) -
          Yminus u ω| ≤ Δ n) :
    IsGLWProcess Yminus := by
  -- TAG[V2-R39-tighten-Yminus-lower]: sound modulo {#1, #2, scaling-limit};
  -- closure deferred to R49-R53.
  sorry

end Erdos524.Helpers
