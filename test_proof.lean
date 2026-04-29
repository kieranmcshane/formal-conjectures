import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Real

def cUpper_node3 : ℝ := 1 / 200000
def cLower_node3 : ℝ := 1 / 100000
noncomputable def ε₀_node3 : ℝ := Real.exp (-100)

theorem my_bound (L : ℝ) (h100 : 100 ≤ L) :
    -2 * cLower_node3 * L^3 ≤ -cUpper_node3 * L^3 + Real.log (1 / 2 : ℝ) := by
  have h_log : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [h_log]
  have h_log_le : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have h1 : cLower_node3 = 1 / 100000 := by unfold cLower_node3; norm_num
  have h2 : cUpper_node3 = 1 / 200000 := by unfold cUpper_node3; norm_num
  have hL3_ge : (1000000 : ℝ) ≤ L^3 := by
    have h_cube : (100 : ℝ) ^ 3 ≤ L ^ 3 := by
      have h100_nn : (0 : ℝ) ≤ 100 := by norm_num
      exact pow_le_pow_left₀ h100_nn h100 3
    have h_val : (100 : ℝ) ^ 3 = 1000000 := by norm_num
    rw [h_val] at h_cube
    exact h_cube
  rw [h1, h2]
  linarith
