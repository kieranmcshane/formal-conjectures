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
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Phase 2 Round 8 — Shared `IsGLWProcess` predicate

This file packages the `IsGLWProcess` predicate (introduced in Round 7
to fix the universal-over-`Y` honesty issue in
`gao_li_wellner_small_ball_upper`) as a shared module so it can be
re-used by both the upper and lower-bound proof modules
(`GLWUpperProof.lean` and `GLWLowerProof.lean`) without duplicating
the structure or its basic projections.

## Why a shared file

The Round 7 stress test for the upper-bound axiom showed that the bound
`(ℙ {ω | …}).toReal ≤ exp(-c̄ · |log ε|³)` is FALSE for `Y ≡ 0`
(the LHS is `1`, the RHS tends to `0`). The fix was to add an
`IsGLWProcess Y` hypothesis that captures the actual process structure
the proof relies on (Gaussianity, K_GLW covariance, mean zero,
continuous paths, tail decay).

The Round 8 stress test for the lower-bound axiom shows the SYMMETRIC
issue:

  Case 1 — Y ≡ 0:
    LHS = exp(-c · |log ε|^3) > 0
    RHS = ℙ{∀ u ≥ 0, |0| ≤ ε} = ℙ univ = 1
    Bound: exp(...) ≤ 1. TRUE (trivially, for any ε ≤ 1).

  Case 2 — Y ≡ 1 (or any constant c with 0 < c):
    For ε < c: ℙ{∀ u ≥ 0, c ≤ ε} = 0
    Bound: exp(-c · |log ε|^3) ≤ 0. FALSE.

So the lower-bound axiom is also false for arbitrary measurable `Y`,
and Round 8 fixes the same way: add `IsGLWProcess Y` to the
hypothesis. Sharing the predicate between the two proofs avoids
circular imports (GLWUpperProof and GLWLowerProof are siblings).

## Contents

* `IsGLWProcess` — structure capturing the GLW-process axioms:
  measurability, integrability of marginals and pairwise products,
  centeredness, K_GLW covariance, joint Gaussianity, continuous paths,
  tail decay.
* `isGLWProcess_exists` — bridge to the `Y_GLW_exists` axiom in
  `GLWProcess.lean`: there exists a probability space realizing
  `IsGLWProcess` (modulo the `_hY_gauss / _hY_paths / _hY_tail`
  conjuncts which are present in `Y_GLW_exists` but not extracted
  here for the slim form).
* Projections `IsGLWProcess.var_*`, `IsGLWProcess.cov_*`,
  `IsGLWProcess.centered_at` — basic facts about variance, covariance,
  and centeredness derived from the structure fields and the kernel
  identities `K_GLW_pos`, `K_GLW_le_one`, `K_GLW_zero`, `K_GLW_symm`.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory

/-! ## `IsGLWProcess` predicate

A measurable process `Y : ℝ → Ω → ℝ` on a probability space `(Ω, ℙ)`
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

/-! ## Bridge to `Y_GLW_exists`

The `Y_GLW_exists` axiom in `Helpers/GLWProcess.lean` produces a Y
satisfying exactly the structure captured by `IsGLWProcess`. The
following corollary makes the connection explicit: there exists a
probability space on which `IsGLWProcess` is realized (slim form,
without the gauss/paths/tail conjuncts which would require the
`MeasureSpace` instance to be packaged as a sigma-typed witness). -/

/-- Existence of a process satisfying `IsGLWProcess` (slim form: only
the algebraic conjuncts — measurability, integrability, centeredness,
K_GLW covariance — are extracted). Direct corollary of the
`Y_GLW_exists` stepping-stone axiom. -/
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

/-- **Full witness:** there exist `(Ω, ℙ, Y)` with `Y` satisfying the
full `IsGLWProcess` predicate (all nine conjuncts: measurability,
integrability, integrable-prod, centeredness, K_GLW covariance, joint
Gaussianity, a.s. continuous paths, a.s. tail decay).

This packages the `Y_GLW_exists` axiom into the structured form. It
shows that the Round 8 lower-bound theorem statement (which has
`IsGLWProcess Y` as a hypothesis) is NOT vacuous — there is a concrete
process witnessing the predicate. -/
theorem isGLWProcess_exists_full :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (μ : Measure Ω)
      (_hμ : IsProbabilityMeasure μ),
      letI : MeasureSpace Ω := ⟨μ⟩
      ∃ Y : ℝ → Ω → ℝ, IsGLWProcess Y := by
  obtain ⟨Ω, mΩ, μ, Y, hμ, hY_meas, hY_int, hY_int_prod, hY_centered, hY_cov,
          hY_gauss, hY_paths, hY_tail⟩ := Y_GLW_exists
  refine ⟨Ω, mΩ, μ, hμ, ?_⟩
  letI : MeasureSpace Ω := ⟨μ⟩
  refine ⟨Y, ?_⟩
  exact {
    measurable := hY_meas
    integrable := hY_int
    integrable_prod := hY_int_prod
    centered := hY_centered
    cov := hY_cov
    gaussian := hY_gauss
    continuous_paths := hY_paths
    tail_decay := hY_tail
  }

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

/-- Any `cov[Y u, Y v]` for `u, v ≥ 0` is bounded above by `1` (via
`K_GLW_le_one`). -/
theorem IsGLWProcess.cov_le_one (h : IsGLWProcess Y) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ ω, Y u ω * Y v ω ∂ℙ ≤ 1 := by
  rw [h.cov u v hu hv]
  exact K_GLW_le_one u v hu hv

/-- Any `cov[Y u, Y v]` for `u, v ≥ 0` is positive (via `K_GLW_pos`). -/
theorem IsGLWProcess.cov_pos (h : IsGLWProcess Y) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < ∫ ω, Y u ω * Y v ω ∂ℙ := by
  rw [h.cov u v hu hv]
  exact K_GLW_pos u v hu hv

/-- Covariance is symmetric: `cov[Y u, Y v] = cov[Y v, Y u]` (via
`K_GLW_symm`). -/
theorem IsGLWProcess.cov_symm (h : IsGLWProcess Y) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ ω, Y u ω * Y v ω ∂ℙ = ∫ ω, Y v ω * Y u ω ∂ℙ := by
  rw [h.cov u v hu hv, h.cov v u hv hu, K_GLW_symm]

/-- Centeredness of any nonnegative-argument marginal. -/
theorem IsGLWProcess.centered_at (h : IsGLWProcess Y) (u : ℝ) :
    ∫ ω, Y u ω ∂ℙ = 0 :=
  h.centered u

/-- Variance at the origin is strictly positive (immediate from
`var_at_zero_eq_one`). Used downstream to discharge the `0 < cov`
positivity hypothesis required by Anderson-style bounds when one needs
to invert the covariance at a finite grid containing `0`. -/
theorem IsGLWProcess.var_at_zero_pos (h : IsGLWProcess Y) :
    0 < ∫ ω, Y 0 ω * Y 0 ω ∂ℙ := by
  rw [h.var_at_zero_eq_one]
  exact one_pos

/-- Continuity of the covariance function on the nonneg quadrant: for
`(u, v) ∈ [0, ∞)²`, `(u, v) ↦ ∫ Y u · Y v` is continuous (it equals
`K_GLW(u, v)` there, and `K_GLW` is globally continuous via
`K_GLW_continuous`). Useful for chaining arguments that require the
covariance to be jointly continuous in the indices. -/
theorem IsGLWProcess.cov_continuousOn_nonneg (h : IsGLWProcess Y) :
    ContinuousOn (fun uv : ℝ × ℝ => ∫ ω, Y uv.1 ω * Y uv.2 ω ∂ℙ)
      {uv | 0 ≤ uv.1 ∧ 0 ≤ uv.2} := by
  have hK : ContinuousOn (fun uv : ℝ × ℝ => K_GLW uv.1 uv.2)
      {uv | 0 ≤ uv.1 ∧ 0 ≤ uv.2} := K_GLW_continuous.continuousOn
  refine hK.congr ?_
  intro uv huv
  exact h.cov uv.1 uv.2 huv.1 huv.2

/-! ## Marginal Gaussianity corollaries

The `gaussian` field asserts that every finite linear combination of
the `Y u_i` is Gaussian (a process-level property). Specializing to
single marginals (`n = 1`) and pairs (`n = 2`) gives the marginal and
pair-linear-combination Gaussianity facts that are the load-bearing
prerequisites for Karhunen–Loève / Anderson chain arguments. -/

/-- Each marginal `Y u` is Gaussian (specialization of the `gaussian`
field to `n = 1`, single index `u`, coefficient `1`). -/
theorem IsGLWProcess.gaussian_marginal (h : IsGLWProcess Y) (u : ℝ) :
    IsGaussian (Measure.map (Y u) ℙ) := by
  have hgauss := h.gaussian 1 (fun _ => u) (fun _ => 1)
  -- `hgauss : IsGaussian (Measure.map (fun ω => ∑ i : Fin 1, 1 * Y u ω) ℙ)`.
  -- Rewrite the inner function to `Y u` via `Fin.sum_univ_one` and `one_mul`.
  have h_eq : (fun ω => ∑ i : Fin 1, (1 : ℝ) * Y u ω) = Y u := by
    ext ω
    simp
  rw [h_eq] at hgauss
  exact hgauss

/-- Each affine combination `a · Y u + b · Y v` is Gaussian
(specialization of the `gaussian` field to `n = 2`). The
load-bearing prerequisite for Anderson-style two-dim box bounds on
finite grids of Y-values. -/
theorem IsGLWProcess.gaussian_pair_lc (h : IsGLWProcess Y)
    (u v : ℝ) (a b : ℝ) :
    IsGaussian (Measure.map (fun ω => a * Y u ω + b * Y v ω) ℙ) := by
  have hgauss := h.gaussian 2 ![u, v] ![a, b]
  -- Rewrite ∑ i : Fin 2, ![a, b] i * Y (![u, v] i) ω = a * Y u ω + b * Y v ω
  have h_eq : (fun ω => ∑ i : Fin 2, (![a, b] : Fin 2 → ℝ) i *
              Y ((![u, v] : Fin 2 → ℝ) i) ω) =
              fun ω => a * Y u ω + b * Y v ω := by
    ext ω
    simp [Fin.sum_univ_two]
  rw [h_eq] at hgauss
  exact hgauss

end Erdos524.Helpers
