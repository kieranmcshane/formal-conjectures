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

import FormalConjectures.ErdosProblems.Helpers.SubGaussianGaussianReal
import FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit

/-!
# GLW marginal tail bounds (R19 / T2.1, Path B)

The conjunct-9 tail-decay proof for `glwGaussianLimit_Y_GLW_existence`
needs a quantitative tail bound on `|ω t|` under `glwGaussianLimit`,
suitable for summing over integer points to invoke Borel–Cantelli.

This file packages the marginal piece of Path B from R19 T1.1
(`Helpers/R19APIScoping.md`):

* `hasSubgaussianMGF_eval_glwGaussianLimit t` — the marginal
  evaluation `(· t)` is sub-Gaussian under `glwGaussianLimit` with
  parameter `K_GLW(t, t).toNNReal`.
* `eval_glwGaussianLimit_real_abs_ge_le t hε` — the symmetric
  Chernoff tail
  `glwGaussianLimit.real {ω | ε ≤ |ω t|} ≤ 2 · exp(-ε² / (2 K_GLW(t,t)))`.
* `eval_glwGaussianLimit_real_abs_ge_le_of_pos T_pos` — the same with
  the variance bound `K_GLW(T, T) ≤ 1/(2T)` baked in, giving
  `≤ 2 · exp(-ε² T)` for `T : ℝ` with `T ≥ 1`.
* `summable_marginal_tail` — `∑_{T : ℕ}, 2 · exp(-ε² T) < ∞` for `ε > 0`.

These feed into T2.2 (the sup-tail bound), which still needs the
chaining-via-`finite_set_bound_of_edist_le` argument from T1.1's
Claim 3 — that piece remains an explicit blocker carried into the
conjunct-9 assembly.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

/-! ## Marginal sub-Gaussianness under `glwGaussianLimit` -/

/-- **R19 / T2.1 (Path B step 1).** The coordinate evaluation
`(· t)` is sub-Gaussian under `glwGaussianLimit` with parameter
`K_GLW(t, t).toNNReal`.

Proof: combine the marginal-law identity `glwGaussianLimit.map (· t)
= gaussianReal 0 K_GLW(t,t).toNNReal` (`hasLaw_eval_glwGaussianLimit`)
with the gaussianReal sub-Gaussian adapter
`hasSubgaussianMGF_id_gaussianReal` and `HasSubgaussianMGF.id_map_iff`. -/
lemma hasSubgaussianMGF_eval_glwGaussianLimit (t : NNReal) :
    HasSubgaussianMGF (fun ω : NNReal → ℝ ↦ ω t)
      (K_GLW (t : ℝ) (t : ℝ)).toNNReal glwGaussianLimit := by
  have hL := hasLaw_eval_glwGaussianLimit (t := t)
  have h_meas : AEMeasurable (fun ω : NNReal → ℝ ↦ ω t) glwGaussianLimit :=
    hL.aemeasurable
  have h_id : HasSubgaussianMGF id (K_GLW (t : ℝ) (t : ℝ)).toNNReal
      ((glwGaussianLimit).map (fun ω : NNReal → ℝ ↦ ω t)) := by
    rw [hL.map_eq]
    exact hasSubgaussianMGF_id_gaussianReal _
  exact (HasSubgaussianMGF.id_map_iff h_meas).mp h_id

/-- **R19 / T2.1 (Path B step 2).** Two-sided Chernoff tail for the
marginal `(· t)`. -/
lemma eval_glwGaussianLimit_real_abs_ge_le (t : NNReal) {ε : ℝ} (hε : 0 ≤ ε) :
    glwGaussianLimit.real {ω : NNReal → ℝ | ε ≤ |ω t|} ≤
      2 * exp (-ε ^ 2 / (2 * (K_GLW (t : ℝ) (t : ℝ)).toNNReal)) := by
  -- Push the gaussianReal two-sided tail through the marginal law.
  have hL := hasLaw_eval_glwGaussianLimit (t := t)
  have h_set : {ω : NNReal → ℝ | ε ≤ |ω t|} =
      (fun ω : NNReal → ℝ ↦ ω t) ⁻¹' {x : ℝ | ε ≤ |x|} := rfl
  rw [h_set]
  have h_map : (gaussianReal 0 (K_GLW (t : ℝ) (t : ℝ)).toNNReal).real
      {x : ℝ | ε ≤ |x|} ≤ 2 * exp (-ε ^ 2 / (2 * (K_GLW (t : ℝ) (t : ℝ)).toNNReal)) :=
    gaussianReal_real_abs_ge_le _ hε
  have h_meas_set : MeasurableSet {x : ℝ | ε ≤ |x|} :=
    measurableSet_le measurable_const measurable_id.norm
  -- Convert via the law.
  have h_map_real :
      (Measure.map (fun ω : NNReal → ℝ ↦ ω t) glwGaussianLimit).real
        {x : ℝ | ε ≤ |x|} =
      glwGaussianLimit.real
        ((fun ω : NNReal → ℝ ↦ ω t) ⁻¹' {x : ℝ | ε ≤ |x|}) := by
    rw [Measure.real, Measure.map_apply_of_aemeasurable hL.aemeasurable h_meas_set]
    rfl
  rw [hL.map_eq] at h_map_real
  rw [← h_map_real]
  exact h_map

/-! ## Variance bound at integer points -/

/-- **R19 / T2.1 (Path B step 3).** For `T ≥ 1`, the variance bound
`K_GLW(T, T) ≤ 1/(2T)` (`K_GLW_var_le_recip`) collapses the marginal
tail to `≤ 2 · exp(-ε² T)`. The hypothesis `T ≥ 1` keeps both `K_GLW`
and `1/(2T)` strictly positive. -/
lemma eval_glwGaussianLimit_real_abs_ge_le_of_pos {T : ℝ} (hT : 1 ≤ T)
    {ε : ℝ} (hε : 0 ≤ ε) :
    glwGaussianLimit.real {ω : NNReal → ℝ | ε ≤ |ω T.toNNReal|} ≤
      2 * exp (-ε ^ 2 * T) := by
  have hT_pos : 0 < T := by linarith
  have h_T_toNNReal : ((T.toNNReal : NNReal) : ℝ) = T := Real.coe_toNNReal _ hT_pos.le
  -- Variance bound K_GLW(T, T) ≤ 1/(2T).
  have h_var_le : K_GLW T T ≤ 1 / (2 * T) := K_GLW_var_le_recip hT_pos
  have h_var_pos : 0 < K_GLW T T := K_GLW_pos T T hT_pos.le hT_pos.le
  -- The marginal tail bound at `t = T.toNNReal`.
  have h_marg :=
    eval_glwGaussianLimit_real_abs_ge_le (t := T.toNNReal) (ε := ε) hε
  rw [h_T_toNNReal] at h_marg
  -- Bound `(K_GLW T T).toNNReal : ℝ` by `K_GLW T T` (which it equals
  -- on the nonneg side) and use `K_GLW T T > 0` for the substitution.
  have h_coe : ((K_GLW T T).toNNReal : ℝ) = K_GLW T T :=
    Real.coe_toNNReal _ h_var_pos.le
  rw [h_coe] at h_marg
  -- Now monotonicity of `exp` in the negative ε² / (2 K_GLW T T):
  -- K_GLW ≤ 1/(2T) ⇒ 2 · K_GLW ≤ 1/T ⇒ 1/(2 · K_GLW) ≥ T
  -- ⇒ -ε²/(2 · K_GLW) ≤ -ε² · T ⇒ exp ≤ exp.
  have h_two_kvar_pos : 0 < 2 * K_GLW T T := by linarith
  have h_two_T_pos : 0 < 2 * T := by linarith
  -- Multiply through `K_GLW T T ≤ 1 / (2 T)` by `2 T > 0` to get
  -- `K_GLW T T * (2 * T) ≤ 1`.
  have h_kvar2T_le : K_GLW T T * (2 * T) ≤ 1 :=
    (le_div_iff₀ (by linarith : (0:ℝ) < 2 * T)).mp h_var_le
  have h_eps_sq_nn : 0 ≤ ε ^ 2 := sq_nonneg _
  -- Step: ε² · T ≤ ε² / (2 · K_GLW T T)  (when 2 · K_GLW T T > 0).
  have h_recip_le : ε ^ 2 * T ≤ ε ^ 2 / (2 * K_GLW T T) := by
    rw [le_div_iff₀ h_two_kvar_pos]
    -- Goal: ε² · T · (2 · K_GLW T T) ≤ ε²
    -- From h_kvar2T_le: K_GLW T T · (2 · T) ≤ 1, so multiply by ε² ≥ 0.
    nlinarith [h_kvar2T_le, h_eps_sq_nn, hT_pos.le, h_var_pos.le]
  have h_neg_le : -(ε ^ 2 / (2 * K_GLW T T)) ≤ -(ε ^ 2 * T) := neg_le_neg h_recip_le
  -- Substitute -ε²/(2 K_GLW) = -(ε²/(2 K_GLW))
  have h_div_eq : -ε ^ 2 / (2 * K_GLW T T) = -(ε ^ 2 / (2 * K_GLW T T)) := by
    rw [neg_div]
  rw [h_div_eq] at h_marg
  have h_exp_mono : exp (-(ε ^ 2 / (2 * K_GLW T T))) ≤ exp (-(ε ^ 2 * T)) :=
    Real.exp_le_exp.mpr h_neg_le
  have h_neg_exp_eq : exp (-(ε ^ 2 * T)) = exp (-ε ^ 2 * T) := by ring_nf
  calc glwGaussianLimit.real {ω : NNReal → ℝ | ε ≤ |ω T.toNNReal|}
      ≤ 2 * exp (-(ε ^ 2 / (2 * K_GLW T T))) := h_marg
    _ ≤ 2 * exp (-(ε ^ 2 * T)) := by gcongr
    _ = 2 * exp (-ε ^ 2 * T) := by rw [h_neg_exp_eq]

/-! ## Summability over integer points -/

/-- **R19 / T2.1 (Path B step 4).** For `ε > 0`, the geometric series
`∑_{T : ℕ}, 2 · exp(-ε² T)` converges. -/
lemma summable_marginal_tail {ε : ℝ} (hε : 0 < ε) :
    Summable (fun T : ℕ => 2 * exp (-ε ^ 2 * (T : ℝ))) := by
  have h_eps_sq_pos : 0 < ε ^ 2 := by positivity
  have h_exp_lt : exp (-ε ^ 2) < 1 := by
    rw [show (1 : ℝ) = exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h_exp_nn : 0 ≤ exp (-ε ^ 2) := (Real.exp_pos _).le
  -- The series is `∑ T, 2 * (exp(-ε²))^T`, geometric with ratio < 1.
  have h_eq : (fun T : ℕ => 2 * exp (-ε ^ 2 * (T : ℝ))) =
              (fun T : ℕ => 2 * (exp (-ε ^ 2)) ^ T) := by
    funext T
    rw [← Real.exp_nat_mul, mul_comm (-ε ^ 2) (T : ℝ)]
  rw [h_eq]
  exact (summable_geometric_of_lt_one h_exp_nn h_exp_lt).mul_left _

end Erdos524.Helpers
