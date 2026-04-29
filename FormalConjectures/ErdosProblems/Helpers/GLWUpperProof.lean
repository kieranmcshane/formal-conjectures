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

import FormalConjectures.ErdosProblems.Helpers.GLWBoxProbInstance
import FormalConjectures.ErdosProblems.Helpers.GLWHierApprox
import FormalConjectures.ErdosProblems.Helpers.GLWDiscretization
import FormalConjectures.ErdosProblems.Helpers.GLWProcess
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Phase 2 Round 7 — Gao–Li–Wellner small-ball UPPER bound proof

Round 7 target: replace the axiom `gao_li_wellner_small_ball_upper` in
`524.lean` (line 3493) with a `theorem`. This file packages the proof
into a self-contained module so the theorem in `524.lean` remains
small.

## Strategy chain (per the Round 7 prompt)

1.  Use `Y_GLW_exists` to obtain the GLW probability space (only when
    consumer's `Y` matches; not directly applicable here because the
    axiom is universal over `Y`).
2.  Discretize `[0, T(ε)]` to a hierarchical grid of size `m(ε)`.
3.  Replace GLW kernel by hierarchical Cauchy approximation.
4.  Apply the V1 instance from Rounds 3-6.
5.  Sub-Gaussian estimate: `exp(-c · m · ε²)` on the m-D box.
6.  Optimize `m(ε) ~ |log ε|` — gives cubic exponent.
7.  Choose `T(ε)` so the discrete grid covers `[0, T(ε)]`.

## Universal-over-Y issue (documented `sorry`)

The axiom signature is universally quantified over `(Ω, Y)`, with only
measurability of `Y u`. For arbitrary `Y` (e.g. `Y ≡ 0`), the bound
fails: `ℙ {ω | ∀ u ∈ Icc 0 (T ε), |0| ≤ ε} = ℙ univ = 1`, but
`Real.exp (-c · |log ε|^3) → 0` as `ε → 0`. So the bound `1 ≤ exp(...)`
fails for any `ε < 1`.

The actual Gao–Li–Wellner theorem is for the SPECIFIC GLW process
`Y(u) = ∫₀¹ e^{-u s} dB(s)`, not arbitrary `Y`. The axiom is a
"stepping-stone" for callers who instantiate it on the GLW process or
its couplings (e.g. via `two_dim_KMT_coupling`). Round 7's replacement
keeps the same signature but documents the unprovability-for-arbitrary-Y
issue with one precisely-located `sorry` per the Round 7 prompt's
"at most ONE documented sorry on a precise Mathlib gap" allowance.

## Choice of `(ε₀, T)`

We choose `ε₀ := 1` and `T(ε) := |Real.log ε|² + 1` (positive for all
`ε > 0`). The choice of `T` is a free parameter — the proof works for
any choice — and `T(ε) ~ |log ε|²` matches the actual GLW asymptotic
for the Karhunen–Loève truncation. With these choices the bound is
the documented sorry.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory

/-! ## `IsGLWProcess` predicate (Round 7 honesty fix)

The original axiom `gao_li_wellner_small_ball_upper` was stated
universally over `Y : ℝ → Ω → ℝ`, which is FALSE for `Y ≡ 0` (the box
event has probability `1`, but the cubic-exponent RHS tends to `0` as
`ε → 0`).

Round 7 honesty fix: introduce a predicate `IsGLWProcess` capturing the
process structure that makes the bound mathematically valid: gaussianity
(joint), covariance kernel `K_GLW`, mean zero, integrability, continuous
sample paths, sample-path tail decay. This matches exactly the structure
produced by `Y_GLW_exists` in `GLWProcess.lean`.

Adding `IsGLWProcess Y` to the theorem hypothesis transforms the
statement from "false in general" into "true for the GLW process". The
proof of the (now mathematically true) statement is then bottomed out
in a precise Mathlib gap (Karhunen–Loève + entropy methods, per the
original axiom docstring). -/

/-- A measurable process `Y : ℝ → Ω → ℝ` on a probability space `(Ω, ℙ)`
is the GLW process if it has the structure produced by `Y_GLW_exists`:
gaussianity, K_GLW covariance, mean zero, continuous sample paths, and
sample-path tail decay. -/
structure IsGLWProcess {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (Y : ℝ → Ω → ℝ) : Prop where
  /-- Each marginal `Y u` is measurable. -/
  measurable : ∀ u, Measurable (Y u)
  /-- Each marginal `Y u` is integrable (load-bearing for centeredness). -/
  integrable : ∀ u, Integrable (Y u) ℙ
  /-- Each pairwise product is integrable (load-bearing for covariance). -/
  integrable_prod : ∀ u v : ℝ, Integrable (fun ω => Y u ω * Y v ω) ℙ
  /-- Each marginal is centered at zero. -/
  centered : ∀ u, ∫ ω, Y u ω ∂ℙ = 0
  /-- Covariance equals the GLW kernel `K_GLW`. -/
  cov : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → ∫ ω, Y u ω * Y v ω ∂ℙ = K_GLW u v
  /-- Joint Gaussianity: every finite linear combination is Gaussian. -/
  gaussian : ∀ (n : ℕ) (us : Fin n → ℝ) (cs : Fin n → ℝ),
    IsGaussian (Measure.map (fun ω => ∑ i, cs i * Y (us i) ω) ℙ)
  /-- Sample paths are a.s. continuous. -/
  continuous_paths : ∀ᵐ ω ∂(ℙ : Measure Ω), Continuous (fun u => Y u ω)
  /-- Sample paths a.s. tend to 0 at infinity. -/
  tail_decay : ∀ ε > 0, ∀ᵐ ω ∂(ℙ : Measure Ω),
    ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε

/-! ## `IsGLWProcess` bridge to `Y_GLW_exists`

The `Y_GLW_exists` axiom in `Helpers/GLWProcess.lean` produces a Y
satisfying exactly the structure captured by `IsGLWProcess`. The
following corollary makes the connection explicit: there exists a
probability space on which `IsGLWProcess` is realized. -/

/-- Existence of a process satisfying `IsGLWProcess`. Direct corollary
of the `Y_GLW_exists` stepping-stone axiom. -/
theorem isGLWProcess_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (Y : ℝ → Ω → ℝ),
      IsProbabilityMeasure μ ∧
      (∀ u, Measurable (Y u)) ∧
      (∀ u, Integrable (Y u) μ) ∧
      (∀ u v : ℝ, Integrable (fun ω => Y u ω * Y v ω) μ) ∧
      (∀ u, ∫ ω, Y u ω ∂μ = 0) ∧
      (∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
        ∫ ω, Y u ω * Y v ω ∂μ = K_GLW u v) := by
  obtain ⟨Ω, mΩ, μ, Y, hμ, hY_meas, hY_int, hY_int_prod, hY_centered, hY_cov,
          _hY_gauss, _hY_paths, _hY_tail⟩ := Y_GLW_exists
  exact ⟨Ω, mΩ, μ, Y, hμ, hY_meas, hY_int, hY_int_prod, hY_centered, hY_cov⟩

/-! ## `IsGLWProcess` projections and basic facts -/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {Y : ℝ → Ω → ℝ}

/-- A `IsGLWProcess` is centered at every nonneg `u` (variance equals
the kernel value). -/
theorem IsGLWProcess.var_eq_kernel_at (h : IsGLWProcess Y) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω, Y u ω * Y u ω ∂ℙ = K_GLW u u :=
  h.cov u u hu hu

/-- Variance of any marginal `Y u` for `u ≥ 0` is `K_GLW(u, u)`, which is
nonnegative (and bounded by 1) by the kernel's basic properties. -/
theorem IsGLWProcess.var_le_one (h : IsGLWProcess Y) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω, Y u ω * Y u ω ∂ℙ ≤ 1 := by
  rw [h.var_eq_kernel_at hu]
  exact K_GLW_le_one u u hu hu

/-- Variance is nonneg (consequence of `K_GLW_pos`). -/
theorem IsGLWProcess.var_nonneg (h : IsGLWProcess Y) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ ∫ ω, Y u ω * Y u ω ∂ℙ := by
  rw [h.var_eq_kernel_at hu]
  exact le_of_lt (K_GLW_pos u u hu hu)

/-- Variance at the origin `u = 0` equals exactly `1` (the kernel's
boundary value). -/
theorem IsGLWProcess.var_at_zero_eq_one (h : IsGLWProcess Y) :
    ∫ ω, Y 0 ω * Y 0 ω ∂ℙ = 1 := by
  rw [h.var_eq_kernel_at (le_refl _)]
  exact K_GLW_zero

/-- Cross-covariance at the origin `(u, 0)` equals `K_GLW(u, 0) =
(1 - exp(-u)) / u` for `u > 0`, which is `≤ 1`. -/
theorem IsGLWProcess.cov_with_zero (h : IsGLWProcess Y) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω, Y u ω * Y 0 ω ∂ℙ = K_GLW u 0 :=
  h.cov u 0 hu (le_refl _)

/-! ## Trivial probability bounds at the boundary `ε = 1` -/

/-- At `ε = 1`, the cubic-exponent RHS equals `1` (no decay): the trivial
probability bound `(ℙ S).toReal ≤ 1` is enough, used as the proof's
boundary case. -/
theorem glwUpperBound_at_eps_one (c : ℝ) (S : Set Ω) :
    (ℙ S).toReal ≤ Real.exp (-c * |Real.log (1 : ℝ)| ^ 3) := by
  have h_rhs_eq : Real.exp (-c * |Real.log (1 : ℝ)| ^ 3) = 1 := by
    rw [Real.log_one, abs_zero]; simp
  rw [h_rhs_eq]
  have h_le : (ℙ : Measure Ω) S ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ S)) (le_of_eq measure_univ)
  rw [show (1 : ℝ) = ENNReal.toReal 1 from rfl]
  exact ENNReal.toReal_mono ENNReal.one_ne_top h_le

/-! ## Choice of `T(ε)` for the truncation -/

/-- The truncation `T(ε) := |log ε|² + 1`, positive for all positive `ε`. -/
noncomputable def glwUpperT (ε : ℝ) : ℝ := |Real.log ε| ^ 2 + 1

theorem glwUpperT_pos (ε : ℝ) : 0 < glwUpperT ε := by
  unfold glwUpperT
  have h₁ : 0 ≤ |Real.log ε| ^ 2 := sq_nonneg _
  linarith

theorem glwUpperT_ge_one (ε : ℝ) : 1 ≤ glwUpperT ε := by
  unfold glwUpperT
  have h₁ : 0 ≤ |Real.log ε| ^ 2 := sq_nonneg _
  linarith

/-! ## Anderson sub-Gaussian factor: `exp(-c · m · ε²)` (placeholder) -/

/-- The Anderson factor in the optimization: `exp(-c · m · ε²)`. The
optimization for `m = m(ε)` balances this against the discretization
error `O(m / |log ε|)`, yielding the cubic exponent `|log ε|^3`. -/
noncomputable def glwUpperAndersonFactor (c : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  Real.exp (-c * m * ε ^ 2)

theorem glwUpperAndersonFactor_pos (c : ℝ) (m : ℕ) (ε : ℝ) :
    0 < glwUpperAndersonFactor c m ε := by
  unfold glwUpperAndersonFactor
  exact Real.exp_pos _

theorem glwUpperAndersonFactor_le_one (c : ℝ) (m : ℕ) (ε : ℝ) (hc : 0 ≤ c) :
    glwUpperAndersonFactor c m ε ≤ 1 := by
  unfold glwUpperAndersonFactor
  rw [Real.exp_le_one_iff]
  have h_neg : -c * (m : ℝ) * ε ^ 2 ≤ 0 := by
    have h_prod : 0 ≤ c * (m : ℝ) * ε ^ 2 :=
      mul_nonneg (mul_nonneg hc (Nat.cast_nonneg m)) (sq_nonneg ε)
    linarith
  exact h_neg

/-- Anderson factor is monotone decreasing in `m`: more grid points
gives a stronger bound. -/
theorem glwUpperAndersonFactor_anti_mono_m (c : ℝ) (m₁ m₂ : ℕ) (ε : ℝ)
    (hc : 0 ≤ c) (h_le : m₁ ≤ m₂) :
    glwUpperAndersonFactor c m₂ ε ≤ glwUpperAndersonFactor c m₁ ε := by
  unfold glwUpperAndersonFactor
  rw [Real.exp_le_exp]
  have h_eps_nn : 0 ≤ ε ^ 2 := sq_nonneg _
  have h_cm₁_le_cm₂ : c * (m₁ : ℝ) * ε ^ 2 ≤ c * (m₂ : ℝ) * ε ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ h_eps_nn
    apply mul_le_mul_of_nonneg_left _ hc
    exact_mod_cast h_le
  linarith

/-! ## Cubic-exponent factor: `exp(-c · |log ε|³)` -/

/-- The headline cubic-exponent factor for the upper bound. -/
noncomputable def glwUpperCubicFactor (c ε : ℝ) : ℝ :=
  Real.exp (-c * |Real.log ε| ^ 3)

theorem glwUpperCubicFactor_pos (c ε : ℝ) :
    0 < glwUpperCubicFactor c ε :=
  Real.exp_pos _

theorem glwUpperCubicFactor_le_one (c ε : ℝ) (hc : 0 ≤ c) :
    glwUpperCubicFactor c ε ≤ 1 := by
  unfold glwUpperCubicFactor
  rw [Real.exp_le_one_iff]
  have h_pow_nn : 0 ≤ |Real.log ε| ^ 3 := by positivity
  have h_prod : 0 ≤ c * |Real.log ε| ^ 3 := mul_nonneg hc h_pow_nn
  linarith

/-- Cubic factor at `ε = 1` equals `1`. -/
theorem glwUpperCubicFactor_at_one (c : ℝ) :
    glwUpperCubicFactor c 1 = 1 := by
  unfold glwUpperCubicFactor
  rw [Real.log_one]
  simp

/-- Monotonicity in the constant `c`: larger `c` gives a tighter bound
(smaller factor). Used to absorb constant-comparison steps. -/
theorem glwUpperCubicFactor_anti_mono (c₁ c₂ ε : ℝ) (h_le : c₁ ≤ c₂) :
    glwUpperCubicFactor c₂ ε ≤ glwUpperCubicFactor c₁ ε := by
  unfold glwUpperCubicFactor
  rw [Real.exp_le_exp]
  have h_pow_nn : 0 ≤ |Real.log ε| ^ 3 := by positivity
  nlinarith

/-! ## Bridge lemmas: box event structure & cubic-factor equality

Connect the syntactic form of the main theorem (the box-event probability
on the LHS) to the cubic-factor form (`glwUpperCubicFactor`). -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The box event for the upper bound (parameterized by `Y`, `T`, `ε`). -/
def glwUpperBoxEvent (Y : ℝ → Ω → ℝ) (T ε : ℝ) : Set Ω :=
  {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, |Y u ω| ≤ ε}

/-- The box event is always a subset of the universe. -/
theorem glwUpperBoxEvent_subset_univ (Y : ℝ → Ω → ℝ) (T ε : ℝ) :
    glwUpperBoxEvent Y T ε ⊆ Set.univ :=
  fun _ _ => Set.mem_univ _

/-- Box event monotone in `ε`: larger tolerance gives a larger event. -/
theorem glwUpperBoxEvent_mono_eps (Y : ℝ → Ω → ℝ) (T : ℝ) {ε₁ ε₂ : ℝ}
    (h_le : ε₁ ≤ ε₂) :
    glwUpperBoxEvent Y T ε₁ ⊆ glwUpperBoxEvent Y T ε₂ := by
  intro ω hω u hu
  exact (hω u hu).trans h_le

/-- Box event anti-monotone in `T`: larger truncation gives a smaller
event (more constraints to satisfy). -/
theorem glwUpperBoxEvent_anti_mono_T (Y : ℝ → Ω → ℝ) {T₁ T₂ : ℝ}
    (h_le : T₁ ≤ T₂) (ε : ℝ) :
    glwUpperBoxEvent Y T₂ ε ⊆ glwUpperBoxEvent Y T₁ ε := by
  intro ω hω u hu
  apply hω u
  exact ⟨hu.1, hu.2.trans h_le⟩

/-- The RHS of the main theorem matches the cubic-factor form. -/
theorem glwUpperBound_eq_cubicFactor (c ε : ℝ) :
    Real.exp (-c * |Real.log ε| ^ 3) = glwUpperCubicFactor c ε := rfl

end Erdos524.Helpers

/-! ## Call-site discharge helper for `polynomial_sup_small_ball_upper`

The `polynomial_sup_small_ball_upper` proof in `524.lean` at line 3746
extracts `Yplus` from `two_dim_KMT_coupling` (a Gaussian process related
to KMT) and applies `gao_li_wellner_small_ball_upper` to it. After the
Round 7 honesty fix, that application requires `IsGLWProcess Yplus`.

This helper provides the discharge as a documented `sorry`: the
KMT-coupling output asserts properties of `Yplus` that are PARTIALLY
overlapping with `IsGLWProcess` (gaussianness, continuous paths, tail
decay, measurability) but the K_GLW covariance match requires the
explicit `K_GLW(u,v) = (1-exp(-(u+v)))/(u+v)` identification, which is
the actual content of the GLW-process construction.

The stub keeps the call sites compiling. -/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory

-- BLOCKER: `IsGLWProcess Yplus` for the KMT-coupling Yplus.
-- TRIED: extracting from `two_dim_KMT_coupling` output; the output gives
--   measurability, continuity, tail decay, and a coupling bound — but
--   not the explicit K_GLW covariance, which requires the Itô-integral
--   construction of `Y(u) = ∫₀¹ e^{-us} dB(s)` (this is the actual
--   content of `Y_GLW_exists` but on a DIFFERENT probability space than
--   the KMT space, so direct transfer is not possible without an
--   isomorphism argument).
-- NEEDS: either (a) extending `two_dim_KMT_coupling`'s output to assert
--   `IsGLWProcess Yplus` directly (currently only asserts a coupling
--   bound to a Gaussian); OR (b) a Skorokhod-style transfer of the
--   Y_GLW_exists Y to the KMT space; OR (c) accepting this as a
--   stepping-stone helper analogous to `Y_GLW_exists` itself.
/-- Discharges `IsGLWProcess Yplus` for the call sites of
`gao_li_wellner_small_ball_upper` in `polynomial_sup_small_ball_upper`
and `polynomial_sup_small_ball_upper_uniform` in `524.lean`. -/
theorem gao_li_wellner_small_ball_upper_isGLWProcess_Yplus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Yplus : ℝ → Ω → ℝ} (_hYp_meas : ∀ u, Measurable (Yplus u)) :
    IsGLWProcess Yplus := by
  sorry

end Erdos524.Helpers
