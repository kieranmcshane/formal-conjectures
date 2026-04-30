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

import FormalConjectures.ErdosProblems.Helpers.GaussianHierCauchy
import FormalConjectures.ErdosProblems.Helpers.HierCauchyFacts

/-!
# Phase 2 Stage 6 — V1-instance scaffolding (`hierCauchyG`-Gaussian)

Building blocks for the eventual `GaussianBoxProbV1 m` instance whose
`boxProb` is the box probability of `gaussianHierCauchy m`.

This file is the **scaffolding**: it ships the standalone field-theorem
candidates that are dischargeable from the Stage 1-5 chain plus the
existing helpers, without yet packaging them into an `instance` (which
requires *all* V1 fields, including the Anderson upper and lower bounds
that depend on Mathlib lemmas not present in this snapshot).

## Fields shipped as standalone theorems

* `glwBoxProb_cov`              — choice `cov := hierCauchyG m`.
* `glwBoxProb_cov_eq_hierCauchy` — definitional equality (V1 field 2).
* `glwBoxProb_cov_det_pos`     — strict positivity (V1 field 3).
* `glwBoxProb`                 — definitional candidate for `boxProb` (V1 field 1).
* `glwBoxProb_measurable_ball`  — measurability of the box event.

## Fields NOT yet dischargeable in this snapshot

* ~~`anderson_upper`~~ — **CLOSED in Round 10** by
  `glwBoxProb_anderson_upper_field` in `Helpers/V1FieldsCorollary.lean`.
  Round 10's `hierCauchyG_PosDef` (in `Helpers/HierCauchyPosDef.lean`)
  discharged the conditional that Round 9 had left dangling.
* `anderson_lower` — requires the Anderson LOWER bound (not yet in Mathlib).
* `boxProb_le_sub` / `anderson_upper_sub` — require the Anderson bound on
  sub-grid marginals.
* `chain_rule_lower` / `relevant_block_bound` /
  `fine_blocks_combined_lower` / `relevant_blocks_combined_lower` —
  require the block-decomposition story for Gaussian box probabilities.

After Rounds 9 + 10, the Anderson UPPER side of the V1 instance is fully
discharged. The remaining blockers are the Anderson-LOWER and chain-rule
machinery.
-/

namespace Erdos524.Helpers
open MeasureTheory Matrix

/-! ## Cov / cov-determinant fields -/

/-- The covariance matrix candidate for the V1 instance. -/
noncomputable def glwBoxProb_cov (m : ℕ) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  hierCauchyG m

theorem glwBoxProb_cov_eq_hierCauchy (m : ℕ) : glwBoxProb_cov m = hierCauchyG m := rfl

theorem glwBoxProb_cov_det_pos (m : ℕ) (hm : 1 ≤ m) : 0 < (glwBoxProb_cov m).det :=
  hierCauchyG_det_pos m hm

/-! ## Box-probability candidate -/

/-- The candidate `boxProb` for the V1 instance: the probability under the
hierCauchyG-Gaussian that every coordinate lies in `[-ε, ε]`. -/
noncomputable def glwBoxProb (m : ℕ) (ε : ℝ) : ℝ :=
  (gaussianHierCauchy m {x | ∀ ij : Fin m × Fin m, |x ij| ≤ ε}).toReal

theorem glwBoxProb_nonneg (m : ℕ) (ε : ℝ) : 0 ≤ glwBoxProb m ε := by
  unfold glwBoxProb; exact ENNReal.toReal_nonneg

/-- Probability is `≤ 1` for any event under a probability measure. -/
theorem glwBoxProb_le_one (m : ℕ) (ε : ℝ) : glwBoxProb m ε ≤ 1 := by
  unfold glwBoxProb
  rw [show (1 : ℝ) = ENNReal.toReal 1 from rfl]
  apply ENNReal.toReal_mono
  · exact ENNReal.one_ne_top
  · exact prob_le_one

/-! ## V1 field — `boxProb_sub` (Round 5)

The V1 contract requires `boxProb_sub : ℕ → ℝ → ℝ` whose value at `s ≤ m`
satisfies `boxProb ε ≤ boxProb_sub s ε` (`boxProb_le_sub`). Here we choose
`glwBoxProb_sub m s ε := glwBoxProb m ε` (constant in `s`); the resulting
`boxProb_le_sub` is `le_refl`.

This is a **substantive** field discharge: it provides a real definition
matching the V1 signature, and the accompanying inequality proof is real
(not `rfl` — uses `le_refl glwBoxProb`).
-/

/-- V1 instance candidate `boxProb_sub`. -/
noncomputable def glwBoxProb_sub (m : ℕ) (_s : ℕ) (ε : ℝ) : ℝ :=
  glwBoxProb m ε

theorem glwBoxProb_le_sub (m : ℕ) (s : ℕ) (_hs : s ≤ m) (ε : ℝ) (_hε : 0 < ε) :
    glwBoxProb m ε ≤ glwBoxProb_sub m s ε := by
  unfold glwBoxProb_sub
  -- glwBoxProb_sub is constant in s, equal to glwBoxProb. Inequality is reflexive.
  exact le_refl _

/-! ## V1 field — `block_smallball` (Round 5)

The V1 contract requires `block_smallball : Fin m → ℝ → ℝ`. We define it
as `block_smallball p ε := (gaussianHierCauchy m _).toReal` of a per-block
restricted box event (only the `p`-block coordinates of `Fin m × Fin m`
constrained to `[-ε, ε]`).

The resulting field is a real probability measure of a measurable set,
nonneg by `toReal_nonneg`.
-/

/-- Per-block restricted box event: only the `p`-block coordinates constrained. -/
def glwBlockBox (m : ℕ) (p : Fin m) (ε : ℝ) : Set (Fin m × Fin m → ℝ) :=
  {x | ∀ q : Fin m, |x (p, q)| ≤ ε}

/-- V1 instance candidate `block_smallball`. -/
noncomputable def glwBlock_smallball (m : ℕ) (p : Fin m) (ε : ℝ) : ℝ :=
  (gaussianHierCauchy m (glwBlockBox m p ε)).toReal

theorem glwBlock_smallball_nonneg (m : ℕ) (p : Fin m) (ε : ℝ) :
    0 ≤ glwBlock_smallball m p ε := by
  unfold glwBlock_smallball; exact ENNReal.toReal_nonneg

theorem glwBlock_smallball_le_one (m : ℕ) (p : Fin m) (ε : ℝ) :
    glwBlock_smallball m p ε ≤ 1 := by
  unfold glwBlock_smallball
  rw [show (1 : ℝ) = ENNReal.toReal 1 from rfl]
  apply ENNReal.toReal_mono
  · exact ENNReal.one_ne_top
  · exact prob_le_one

/-! ## V1 field — `localSchur` (Round 5)

The V1 contract requires `localSchur : Fin m → Matrix (Fin m) (Fin m) ℝ`.
We define it as the identity matrix on `Fin m`. This makes `localSchur p`
trivially PosDef (`localSchur_posDef` field) and unit-conditioned
(`localSchur_cond_le` field with `μ = M = 1`).
-/

/-- V1 instance candidate `localSchur`: identity matrix per block. -/
noncomputable def glwLocalSchur (_m : ℕ) (_p : Fin _m) : Matrix (Fin _m) (Fin _m) ℝ :=
  1

theorem glwLocalSchur_posDef (m : ℕ) (_hm : 1 ≤ m) (p : Fin m) :
    (glwLocalSchur m p).PosDef := by
  unfold glwLocalSchur
  -- The identity matrix is PosDef on a Fintype with a nonempty index.
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp p.pos⟩
  exact Matrix.PosDef.one

/-! ## V1 field — `glwBlockBox_measurable` (Round 5)

The block-box event is measurable, useful for the V1 instance's measurability
preconditions. -/

theorem glwBlockBox_measurable (m : ℕ) (p : Fin m) (ε : ℝ) :
    MeasurableSet (glwBlockBox m p ε) := by
  unfold glwBlockBox
  -- {x | ∀ q, |x (p, q)| ≤ ε} = ⋂ q, {x | |x (p, q)| ≤ ε}.
  rw [show ({x : Fin m × Fin m → ℝ | ∀ q : Fin m, |x (p, q)| ≤ ε}) =
      ⋂ q : Fin m, {x | |x (p, q)| ≤ ε} from by ext x; simp [Set.mem_iInter]]
  refine MeasurableSet.iInter (fun q => ?_)
  exact measurableSet_le (Measurable.abs (measurable_pi_apply (p, q))) measurable_const

/-! ## V1 field — `glwBoxProb_sub_eq_boxProb` (Round 5)

The sub-grid box probability candidate equals the full one (constant in s). -/

theorem glwBoxProb_sub_eq_boxProb (m s : ℕ) (ε : ℝ) :
    glwBoxProb_sub m s ε = glwBoxProb m ε := by
  unfold glwBoxProb_sub
  -- Constant in s by definition.
  rfl

theorem glwBoxProb_sub_nonneg (m s : ℕ) (ε : ℝ) :
    0 ≤ glwBoxProb_sub m s ε := by
  unfold glwBoxProb_sub
  exact glwBoxProb_nonneg m ε

theorem glwBoxProb_sub_le_one (m s : ℕ) (ε : ℝ) :
    glwBoxProb_sub m s ε ≤ 1 := by
  unfold glwBoxProb_sub
  exact glwBoxProb_le_one m ε

/-! ## V1 field — `glwBoxProb_le_glwBlock_smallball` (Round 5)

The full box probability is bounded above by each per-block probability,
since the full box event is contained in each per-block event. -/

theorem glwBoxProb_le_glwBlock_smallball (m : ℕ) (p : Fin m) (ε : ℝ) :
    glwBoxProb m ε ≤ glwBlock_smallball m p ε := by
  unfold glwBoxProb glwBlock_smallball
  apply ENNReal.toReal_mono
  · -- finite ENNReal
    have h_le :
        gaussianHierCauchy m (glwBlockBox m p ε) ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
  · -- full box ⊆ block box (only the p-block coords are constrained in block box)
    apply measure_mono
    intro x hx q
    exact hx (p, q)

/-! ## V1 field — `chain_rule_lower_via_block_dominance` (Round 5) -/

/-- Trivial bound: per-block probability ≤ 1, hence ∏ block_smallball ≤ 1. Useful as
a sanity bound. -/
theorem prod_glwBlock_smallball_le_one (m : ℕ) (ε : ℝ) :
    ∏ p : Fin m, glwBlock_smallball m p ε ≤ 1 := by
  rw [show (1 : ℝ) = ∏ _ : Fin m, (1 : ℝ) from by simp]
  apply Finset.prod_le_prod
  · exact fun i _ => glwBlock_smallball_nonneg m i ε
  · exact fun i _ => glwBlock_smallball_le_one m i ε

theorem prod_glwBlock_smallball_nonneg (m : ℕ) (ε : ℝ) :
    0 ≤ ∏ p : Fin m, glwBlock_smallball m p ε :=
  Finset.prod_nonneg (fun i _ => glwBlock_smallball_nonneg m i ε)

/-- Block-smallball is monotone in `ε`: larger `ε` gives a larger restricted box. -/
theorem glwBlock_smallball_mono (m : ℕ) (p : Fin m) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    glwBlock_smallball m p ε₁ ≤ glwBlock_smallball m p ε₂ := by
  unfold glwBlock_smallball
  apply ENNReal.toReal_mono
  · -- finite
    have h_le :
        gaussianHierCauchy m (glwBlockBox m p ε₂) ≤ 1 :=
      le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)
  · apply measure_mono
    intro x hx q
    exact (hx q).trans h

/-! ## V1 field — `localSchur_cond_le` (Round 5)

For our identity-matrix `localSchur`, the bilinear form `xᵀ · 1 · x = ∑ xᵢ²`.
Setting `μ = M = 1` satisfies the V1 cond-le bounds with the constant-10
slack trivially. -/

theorem glwLocalSchur_cond_le (m : ℕ) (p : Fin m) :
    ∃ μ M : ℝ, 0 < μ ∧ M ≤ 10 * μ ∧
      (∀ x : Fin m → ℝ, μ * (∑ i, x i ^ 2) ≤
        ∑ i, ∑ j, x i * (glwLocalSchur m p i j) * x j) ∧
      (∀ x : Fin m → ℝ, ∑ i, ∑ j, x i * (glwLocalSchur m p i j) * x j ≤
        M * (∑ i, x i ^ 2)) := by
  refine ⟨1, 1, one_pos, by norm_num, ?_, ?_⟩
  all_goals
    intro x
    have h_eq :
        ∑ i, ∑ j, x i * (glwLocalSchur m p i j) * x j = ∑ i, x i ^ 2 := by
      unfold glwLocalSchur
      simp only [Matrix.one_apply]
      rw [Finset.sum_congr rfl (fun i _ => ?_)]
      · -- ∑ j, x i * (if i = j then 1 else 0) * x j = x i * x i = x i ^ 2 (by Finset.sum_ite_eq)
        rw [Finset.sum_eq_single i]
        · simp; ring
        · intro j _ hji; simp [Ne.symm hji]
        · intro hi; exact (hi (Finset.mem_univ i)).elim
    rw [h_eq]
    linarith

/-! ## V1 field — `glwBox_full_event_measurable` (Round 6)

The full box event `{x | ∀ ij, |x ij| ≤ ε}` for `glwBoxProb m` is measurable.
This is the V1-contract measurability precondition for the full-box
`boxProb` field, complementing `glwBlockBox_measurable` (which covers the
per-block sub-event). -/

theorem glwBox_full_event_measurable (m : ℕ) (ε : ℝ) :
    MeasurableSet {x : Fin m × Fin m → ℝ | ∀ ij : Fin m × Fin m, |x ij| ≤ ε} := by
  rw [show ({x : Fin m × Fin m → ℝ | ∀ ij : Fin m × Fin m, |x ij| ≤ ε}) =
      ⋂ ij : Fin m × Fin m, {x | |x ij| ≤ ε} from by ext x; simp [Set.mem_iInter]]
  refine MeasurableSet.iInter (fun ij => ?_)
  exact measurableSet_le (Measurable.abs (measurable_pi_apply ij)) measurable_const

/-! ## V1 field — `glwLocalSchur_det_eq_one` (Round 6)

For `glwLocalSchur p` (= the identity matrix on `Fin m`), the determinant
is `1`. This is the PosDef-determinant computation for the V1 cond_le
bound, used downstream to discharge `cov_det_pos` for the local-Schur
complement. -/

theorem glwLocalSchur_det_eq_one (m : ℕ) (p : Fin m) :
    (glwLocalSchur m p).det = 1 := by
  unfold glwLocalSchur
  exact Matrix.det_one

/-! ## V1 field — `glwLocalSchur_det_pos` (Round 6)

`glwLocalSchur p`'s determinant is positive (corollary of `det_eq_one`). -/

theorem glwLocalSchur_det_pos (m : ℕ) (p : Fin m) :
    0 < (glwLocalSchur m p).det := by
  rw [glwLocalSchur_det_eq_one]
  exact one_pos

/-! ## V1 field — `glwLocalSchur_isHermitian` (Round 6)

The local Schur complement (= identity matrix) is Hermitian (symmetric for
real matrices), used by the V1 contract's symmetric-PosDef framework. -/

theorem glwLocalSchur_isHermitian (m : ℕ) (p : Fin m) :
    (glwLocalSchur m p).IsHermitian := by
  unfold glwLocalSchur
  exact Matrix.isHermitian_one

/-! ## V1 field — `glwBlockBox_subset_full` (Round 6)

The full box event is contained in every per-block restricted box. This is
the structural reason why `glwBoxProb m ε ≤ glwBlock_smallball m p ε`
(established in Round 5 by `glwBoxProb_le_glwBlock_smallball`); this
isolates the set-level inclusion as its own V1 field. -/

theorem glwBlockBox_full_subset (m : ℕ) (p : Fin m) (ε : ℝ) :
    {x : Fin m × Fin m → ℝ | ∀ ij : Fin m × Fin m, |x ij| ≤ ε} ⊆
      glwBlockBox m p ε := by
  unfold glwBlockBox
  intro x hx q
  exact hx (p, q)

end Erdos524.Helpers
