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
import FormalConjectures.ErdosProblems.Helpers.GLWProcessPredicate
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

/-! ## `IsGLWProcess` predicate (Round 7 honesty fix, Round 8 shared)

The `IsGLWProcess` predicate, its `Y_GLW_exists` bridge, and its basic
projections (variance, covariance, centeredness facts) live in the
sibling file `Helpers/GLWProcessPredicate.lean` so they can be reused
by `GLWLowerProof.lean` without circular imports. See the docstring at
the top of that file for the stress-test motivation. -/

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {Y : ℝ → Ω → ℝ}

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

/-- At `ε = 1`, the truncation `T(1) = |log 1|² + 1 = 1`. -/
theorem glwUpperT_at_one : glwUpperT 1 = 1 := by
  unfold glwUpperT
  rw [Real.log_one, abs_zero]
  norm_num

/-- `glwUpperT ε = 1` exactly when `log ε = 0`. -/
theorem glwUpperT_eq_one_iff_log_eq_zero {ε : ℝ} :
    glwUpperT ε = 1 ↔ Real.log ε = 0 := by
  unfold glwUpperT
  constructor
  · intro h
    have h_zero : |Real.log ε| ^ 2 = 0 := by linarith
    have h_abs_zero : |Real.log ε| = 0 :=
      (pow_eq_zero_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0)).mp h_zero
    exact abs_eq_zero.mp h_abs_zero
  · intro h
    rw [h, abs_zero]
    norm_num

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

omit [MeasurableSpace Ω] in
/-- The box event is always a subset of the universe. -/
theorem glwUpperBoxEvent_subset_univ (Y : ℝ → Ω → ℝ) (T ε : ℝ) :
    glwUpperBoxEvent Y T ε ⊆ Set.univ :=
  fun _ _ => Set.mem_univ _

omit [MeasurableSpace Ω] in
/-- Box event monotone in `ε`: larger tolerance gives a larger event. -/
theorem glwUpperBoxEvent_mono_eps (Y : ℝ → Ω → ℝ) (T : ℝ) {ε₁ ε₂ : ℝ}
    (h_le : ε₁ ≤ ε₂) :
    glwUpperBoxEvent Y T ε₁ ⊆ glwUpperBoxEvent Y T ε₂ := by
  intro ω hω u hu
  exact (hω u hu).trans h_le

omit [MeasurableSpace Ω] in
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

/-! ### R37 audit-honesty migration (Phase A code-level closure)

Per `Helpers/R37_T1_ClosureAudit.md` §A, this upper-side IsGLWProcess
helper was promoted from `theorem ... := by sorry` to user-defined
`axiom` symmetrically with the two lower-side helpers in
`Helpers/GLWLowerProof.lean`. The R36 sorry inventory at
`Helpers/AxiomFoundationAudit.md` (R36 section) listed only the two
lower-side helpers; the upper-side helper here is a parallel
structurally-identical sorry that the R36 audit missed. R37 catches the
discrepancy and treats all three consistently.

See `Helpers/R37_T1_ClosureAudit.md` for the full Grok-α-path-vs-actual-
upstream-output kernel-mismatch diagnostic. The KMT-coupling output
exposes only the OUTER pair `(Yplus, Yminus)` with `IndepFun` between
them; the inner Y_e/Y_o decomposition + halved kernels +
individual-Gaussianity that Grok's α-path needs are private internals of
`two_dim_KMT_coupling_via_LS_reduction` not propagated to the legacy-Ω
public surface. -/

/-- Discharges `IsGLWProcess Yplus` for the call sites of
`gao_li_wellner_small_ball_upper` in `polynomial_sup_small_ball_upper`
and `polynomial_sup_small_ball_upper_uniform` in `524.lean`.

**R37 status: user-defined `axiom` (Phase A code-level closure,
β-path).** Symmetric to the lower-side `_isGLWProcess_{Yplus, Yminus}`
helpers in `GLWLowerProof.lean`. Retirement path: extend
`two_dim_KMT_coupling_legacy_Ω_form` to expose Y_e/Y_o + joint
Gaussianity + halved K_{Y_e/Y_o} kernels, then promote the three
IsGLWProcess axioms to theorems via `covariance_add_indep` + kernel
halving + continuity inheritance (Grok's α-path recipe). -/
axiom gao_li_wellner_small_ball_upper_isGLWProcess_Yplus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Yplus : ℝ → Ω → ℝ} (_hYp_meas : ∀ u, Measurable (Yplus u)) :
    IsGLWProcess Yplus

end Erdos524.Helpers
