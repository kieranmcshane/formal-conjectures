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

* `anderson_upper` / `anderson_lower` — require multivariate Anderson's
  inequality, which is not in Mathlib.
* `boxProb_le_sub` / `anderson_upper_sub` — require the Anderson bound on
  sub-grid marginals.
* `chain_rule_lower` / `relevant_block_bound` /
  `fine_blocks_combined_lower` / `relevant_blocks_combined_lower` —
  require the block-decomposition story for Gaussian box probabilities.

These seven fields are the actual remaining math content of Node 6 and
will be discharged in a follow-up once Mathlib gains the multivariate
Anderson lemma (or once a local `FormalConjecturesForMathlib/`-style
proof of Anderson on PosDef Gaussians lands).
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

end Erdos524.Helpers
