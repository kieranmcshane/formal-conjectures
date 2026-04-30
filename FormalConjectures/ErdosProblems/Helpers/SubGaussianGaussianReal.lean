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

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian

/-!
# `gaussianReal` is sub-Gaussian (R19 / T2.1 prerequisite)

R19 T1.1 surfaced that Mathlib has all the pieces to package
`gaussianReal 0 v` as a `HasSubgaussianMGF`-instance:

* `Mathlib.Probability.Distributions.Gaussian.Real.mgf_id_gaussianReal`
  gives `mgf id (gaussianReal μ v) t = rexp (μ * t + v * t^2 / 2)`;
* `integrable_exp_mul_gaussianReal` gives the integrability hypothesis;
* `Mathlib.Probability.Moments.SubGaussian.HasSubgaussianMGF` is the
  target predicate, with `mgf_le t : mgf X μ t ≤ exp (c * t^2 / 2)`.

This file is the ~5-LOC bridge identified by R19's API scoping
(`Helpers/R19APIScoping.md`, Claim 1) — closing the marginal-tail
piece of the conjunct-9 proof strategy. The mean-zero hypothesis is
essential: a non-zero `μ` would shift the MGF off the sub-Gaussian
shape `exp(c · t² / 2)`.
-/

namespace ProbabilityTheory

open Real MeasureTheory NNReal

open scoped NNReal

/-- **R19 / T2.1 adapter (Claim 1 of `R19APIScoping.md`).**

Centred real Gaussian with variance `v` is sub-Gaussian with parameter
`v` for the identity test function. -/
theorem hasSubgaussianMGF_id_gaussianReal (v : NNReal) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- **R19 / T2.1: two-sided Chernoff tail for centred real Gaussian.**

Combines `HasSubgaussianMGF.measure_ge_le` (right tail) with
`HasSubgaussianMGF.neg` (left tail via `-id`). -/
lemma gaussianReal_real_abs_ge_le (v : NNReal) {ε : ℝ} (hε : 0 ≤ ε) :
    (gaussianReal 0 v).real {x : ℝ | ε ≤ |x|} ≤ 2 * exp (-ε ^ 2 / (2 * v)) := by
  have hX : HasSubgaussianMGF id v (gaussianReal 0 v) :=
    hasSubgaussianMGF_id_gaussianReal v
  have h_split : {x : ℝ | ε ≤ |x|} ⊆ {x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x} := by
    intro x hx
    rcases abs_choice x with h | h
    · left
      rwa [Set.mem_setOf_eq, h] at hx
    · right
      rwa [Set.mem_setOf_eq, h] at hx
  have h_pos : (gaussianReal 0 v).real {x : ℝ | ε ≤ x} ≤ exp (-ε ^ 2 / (2 * v)) := by
    simpa using hX.measure_ge_le hε
  have hX' : HasSubgaussianMGF (-id) v (gaussianReal 0 v) := hX.neg
  have h_neg : (gaussianReal 0 v).real {x : ℝ | ε ≤ -x} ≤ exp (-ε ^ 2 / (2 * v)) := by
    have h := hX'.measure_ge_le hε
    simpa [Pi.neg_apply] using h
  calc (gaussianReal 0 v).real {x : ℝ | ε ≤ |x|}
      ≤ (gaussianReal 0 v).real ({x | ε ≤ x} ∪ {x | ε ≤ -x}) :=
        measureReal_mono h_split
    _ ≤ (gaussianReal 0 v).real {x | ε ≤ x} +
          (gaussianReal 0 v).real {x | ε ≤ -x} :=
        measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * v)) + exp (-ε ^ 2 / (2 * v)) := by
        gcongr
    _ = 2 * exp (-ε ^ 2 / (2 * v)) := by ring

end ProbabilityTheory
