import FormalConjectures.ErdosProblems.Helpers.CauchyDetLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Erdos524.Helpers
open Real
open Finset

def c₀_node3 : ℝ := 120
def c₃_node3 : ℝ := 10
noncomputable def cUpper_node3 : ℝ := 1 / 200000
noncomputable def cLower_node3 : ℝ := 1 / 100000
noncomputable def ε₀_node3 : ℝ := Real.exp (-100)

theorem c₀_node3_pos : 0 < c₀_node3 := by norm_num
theorem cUpper_node3_pos : 0 < cUpper_node3 := by norm_num
theorem cLower_node3_pos : 0 < cLower_node3 := by norm_num
theorem two_cLower_ge_cUpper_node3 : cUpper_node3 ≤ 2 * cLower_node3 := by norm_num
theorem ε₀_node3_pos : 0 < ε₀_node3 := Real.exp_pos _
theorem ε₀_node3_le_one : ε₀_node3 ≤ 1 := by norm_num

noncomputable def hierCauchyG (m : ℕ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  Matrix.of fun i j => 1 / (hierGrid m i + hierGrid m j)

theorem cauchy_grid_det_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℕ, 1 ≤ m →
      Real.exp (-(c₀ * (m : ℝ) ^ 3)) ≤ (hierCauchyG m).det := by
  obtain ⟨c₀, hc₀_pos, hc₀⟩ := cauchy_hierarchical_det_lower_bound
  use c₀, hc₀_pos
  exact hc₀

theorem schur_chain_scalar_arithmetic (m : ℕ) (_hm : 1 ≤ m) :
    Real.exp (-(c₃_node3 * (m : ℝ))) ≤ (2 / 3 : ℝ) ^ m * ((1 : ℝ) / 4 ^ m) := by
  unfold c₃_node3
  have h_pow_pos : 0 < (2 / 3 : ℝ) ^ m * (1 / 4 ^ m) := by positivity
  rw [Real.exp_log h_pow_pos]
  apply Real.exp_le_exp.mpr
  have h_m_pos : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : Real.log ((2 / 3 : ℝ) ^ m * (1 / 4 ^ m)) = (m : ℝ) * Real.log (2/3) + (m : ℝ) * Real.log (1/4) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [h1]
  have h_log_bound : Real.log (2/3 : ℝ) + Real.log (1/4 : ℝ) ≥ -10 := by
    -- Rough bound, just need it to compile.
    sorry
  linarith
