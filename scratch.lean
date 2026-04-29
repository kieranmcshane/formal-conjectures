import Mathlib
import FormalConjectures.ErdosProblems.Helpers.GaussianGridSmallBall

open scoped BigOperators
open Real

namespace Erdos524.Helpers

set_option maxHeartbeats 800000

theorem gaussian_grid_smallball_lower_test
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hL_le_2m : |Real.log (ε + r)| ≤ 2 * (m : ℝ))
    (P : GaussianBoxProbV1 m) :
    Real.exp (-2 * cLower_node3 * |Real.log (ε + r)| ^ 3) ≤ P.boxProb ε := by
  set L := |Real.log (ε + r)| with hL_def
  have h_log_nonpos : Real.log (ε + r) ≤ 0 := by
    have h1 : ε + r ≤ 1 := by
      calc ε + r ≤ ε₀_node3 := hεr_le_ε₀
        _ ≤ 1 := ε₀_node3_le_one
    exact Real.log_nonpos (by positivity) h1
  have hL_pos : 0 < L := by
    rw [hL_def]
    -- wait, if L = 0, then log(ε+r) = 0, so ε+r = 1.
    -- but ε+r ≤ ε₀ = exp(-100) < 1.
    have h1 : Real.log (ε + r) < 0 := by
      calc Real.log (ε + r) ≤ Real.log ε₀_node3 := Real.log_le_log hεr_pos hεr_le_ε₀
        _ = -100 := by unfold ε₀_node3; rw [Real.log_exp]
        _ < 0 := by norm_num
    exact abs_pos.mpr h1.ne
  -- 1. `P.chain_rule_lower`
  have h_chain := P.chain_rule_lower ε hε
  -- 2. Split relevant vs fine blocks
  set R := Finset.filter (λ p : Fin m => 4 ^ (p.val + m) ≤ Real.exp (2 * L)) Finset.univ
  set F := Finset.filter (λ p : Fin m => 4 ^ (p.val + m) > Real.exp (2 * L)) Finset.univ
  
  -- 3. relevant_block_bound
  have h_rel : ∀ p ∈ R, (3/4 * ε) ^ (m : ℝ) * (Matrix.det (P.localSchur p))⁻¹ ^ (1/2 : ℝ) * Real.exp (-c₀_node3 * m) ≤ P.block_smallball p ε := by
    intro p hp
    have hp_le : 4 ^ (p.val + m) ≤ Real.exp (2 * L) := by simpa using hp
    exact P.relevant_block_bound p ε L hε hL_pos hp_le
    
  sorry

end Erdos524.Helpers
