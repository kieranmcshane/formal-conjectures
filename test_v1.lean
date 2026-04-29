import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset
open Real

def cUpper_node3 : ℝ := 1 / 200000
def cLower_node3 : ℝ := 1 / 100000

theorem two_cLower_ge_cUpper_node3 : cUpper_node3 ≤ 2 * cLower_node3 := by
  unfold cUpper_node3 cLower_node3; norm_num

structure GaussianBoxProbV1 (m : ℕ) where
  boxProb : ℝ → ℝ
  block_smallball : Fin m → ℝ → ℝ
  chain_rule_lower : ∀ ε, 0 < ε →
    (∏ p, block_smallball p ε) ≤ boxProb ε
  relevant_block_bound : ∀ p ε L, 0 < ε → 0 < L →
    4 ^ (p.val + m) ≤ Real.exp (2 * L) →
    Real.exp (-cUpper_node3 * L^3 / m) ≤ block_smallball p ε
  fine_blocks_combined_lower : ∀ ε L, 0 < ε → 0 < L →
    (1/2 : ℝ) ≤ ∏ p ∈ Finset.univ.filter (λ p ↦ (4 : ℝ) ^ (p.val + m) > Real.exp (2 * L)),
                       block_smallball p ε

theorem lower_bound_test
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hL_pos : 0 < |Real.log (ε + r)|)
    (hL_le_2m : |Real.log (ε + r)| ≤ 2 * (m : ℝ))
    (P : GaussianBoxProbV1 m) :
    Real.exp (-2 * cLower_node3 * |Real.log (ε + r)| ^ 3) ≤ P.boxProb ε := by
  set L := |Real.log (ε + r)| with hL_def
  have h_chain := P.chain_rule_lower ε hε
  set R := Finset.univ.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L))
  set F := Finset.univ.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) > Real.exp (2 * L))

  have h_split : ∏ p, P.block_smallball p ε = (∏ p ∈ R, P.block_smallball p ε) * (∏ p ∈ F, P.block_smallball p ε) := by
    have h_union : R ∪ F = Finset.univ := by
      ext p
      rw [mem_union, mem_filter, mem_filter, mem_univ]
      by_cases h : (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L)
      · exact Or.inl ⟨trivial, h⟩
      · push_neg at h; exact Or.inr ⟨trivial, h⟩
    have h_disj : Disjoint R F := by
      rw [disjoint_left]
      intro a ha hb
      rw [mem_filter] at ha hb
      linarith [ha.2, hb.2]
    rw [← prod_union h_disj, h_union]

  have h_rel_prod : (∏ p ∈ R, Real.exp (-cUpper_node3 * L^3 / m)) ≤ ∏ p ∈ R, P.block_smallball p ε := by
    apply prod_le_prod
    · intro p hp
      exact le_trans (Real.exp_pos _).le (P.relevant_block_bound p ε L hε hL_pos (mem_filter.mp hp).2)
    · intro p hp
      exact P.relevant_block_bound p ε L hε hL_pos (mem_filter.mp hp).2

  have h_rel_val : ∏ p ∈ R, Real.exp (-cUpper_node3 * L^3 / m) = Real.exp (-cUpper_node3 * L^3 / m * R.card) := by
    rw [prod_const]
    have : Real.exp (-cUpper_node3 * L ^ 3 / ↑m) ^ R.card = Real.exp (-cUpper_node3 * L ^ 3 / ↑m * ↑R.card) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    exact this

  have h_fine : (1/2 : ℝ) ≤ ∏ p ∈ F, P.block_smallball p ε := P.fine_blocks_combined_lower ε L hε hL_pos

  have h_R_card_le_m : (R.card : ℝ) ≤ (m : ℝ) := by
    exact Nat.cast_le.mpr (card_le_univ _)

  have h_exp_mono : Real.exp (-cUpper_node3 * L^3) ≤ Real.exp (-cUpper_node3 * L^3 / m * R.card) := by
    apply Real.exp_le_exp.mpr
    have h_m_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    rw [div_mul_eq_mul_div]
    have : -cUpper_node3 * L ^ 3 ≤ -cUpper_node3 * L ^ 3 * ↑R.card / ↑m ↔
           -cUpper_node3 * L ^ 3 * ↑m ≤ -cUpper_node3 * L ^ 3 * ↑R.card := by
      exact le_div_iff₀ h_m_pos
    rw [this]
    have h_c_L_nn : 0 ≤ cUpper_node3 * L^3 := by positivity
    nlinarith

  have h_combine : Real.exp (-cUpper_node3 * L^3) * (1/2 : ℝ) ≤ (∏ p ∈ R, P.block_smallball p ε) * (∏ p ∈ F, P.block_smallball p ε) := by
    apply mul_le_mul
    · rw [← h_rel_val] at h_exp_mono
      exact le_trans h_exp_mono h_rel_prod
    · exact h_fine
    · norm_num
    · exact le_trans (Real.exp_pos _).le (le_trans h_exp_mono h_rel_prod)

  have h_half_le : Real.exp (-2 * cLower_node3 * L^3) ≤ Real.exp (-cUpper_node3 * L^3) * (1 / 2 : ℝ) := sorry

  sorry
