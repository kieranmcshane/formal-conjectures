import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Real

def c₃_node3 : ℝ := 10

theorem schur_chain_scalar_arithmetic (m : ℕ) (_hm : 1 ≤ m) :
    Real.exp (-(c₃_node3 * (m : ℝ))) ≤ (2 / 3 : ℝ) ^ m * ((1 : ℝ) / 4 ^ m) := by
  unfold c₃_node3
  have h_pow_pos : 0 < (2 / 3 : ℝ) ^ m * (1 / 4 ^ m) := by positivity
  have h_rhs_eq : (2 / 3 : ℝ) ^ m * (1 / 4 ^ m) = (1 / 6 : ℝ) ^ m := by
    have : (1 / 4 : ℝ) ^ m = (1 ^ m) / 4 ^ m := by ring
    have h_prod : (2 / 3 : ℝ) * (1 / 4) = 1 / 6 := by norm_num
    rw [← mul_pow]
    rw [h_prod]
  rw [h_rhs_eq]
  have h_lhs_eq : Real.exp (-(10 * (m : ℝ))) = (Real.exp (-10)) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h_lhs_eq]
  have h_base_le : Real.exp (-10) ≤ 1 / 6 := by
    have : Real.exp 10 ≥ 6 := by
      calc Real.exp 10
          ≥ 1 + 10 := Real.add_one_le_exp 10
        _ ≥ 6 := by norm_num
    have h1 : Real.exp (-10) = (Real.exp 10)⁻¹ := by
      rw [Real.exp_neg]
    rw [h1]
    exact inv_le_inv₀ (by norm_num) this |>.mpr this
  have h_base_nn : 0 ≤ Real.exp (-10) := by positivity
  exact pow_le_pow_left₀ h_base_nn h_base_le m
