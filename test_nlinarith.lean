import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

lemma test (L : ℝ) (hL3_ge : 1000000 ≤ L^3) : -(1/50000 : ℝ) * L^3 ≤ -(1/200000 : ℝ) * L^3 - 1 := by
  linarith

lemma test2 : (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := by
  have : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  -- how to deduce inverse
  exact inv_le_inv₀ (by positivity) this |>.mpr this
