import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Real

structure GaussianBoxProbV1 (m : ℕ) where
  block_smallball : Fin m → ℝ → ℝ
  localSchur : Fin m → Matrix (Fin m) (Fin m) ℝ
  localSchur_posDef : ∀ p, localSchur p |>.PosDef
  relevant_block_bound : ∀ p ε L, 0 < ε → 0 < L →
    4 ^ (p.val + m) ≤ Real.exp (2 * L) →
    block_smallball p ε ≥
      (3/4 * ε) ^ (m : ℝ) *
      (Matrix.det (localSchur p))⁻¹ ^ (1/2 : ℝ) *
      Real.exp (-120 * m)

theorem test
    (m : ℕ) (ε r : ℝ) (hε : 0 < ε)
    (P : GaussianBoxProbV1 m)
    (L : ℝ) (hL_pos : 0 < L) : True := by
  set R := Finset.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L)) Finset.univ
  set F := Finset.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) > Real.exp (2 * L)) Finset.univ

  have h_split : ∏ p, P.block_smallball p ε = (∏ p ∈ R, P.block_smallball p ε) * (∏ p ∈ F, P.block_smallball p ε) := by
    have h_union : R ∪ F = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_or_lt _ _
    have h_disj : Disjoint R F := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      subst hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      linarith
    rw [← Finset.prod_union h_disj, h_union]

  have h_rel_prod : (∏ p ∈ R, (3/4 * ε) ^ (m : ℝ) * (Matrix.det (P.localSchur p))⁻¹ ^ (1/2 : ℝ) * Real.exp (-120 * m)) ≤ ∏ p ∈ R, P.block_smallball p ε := by
    apply Finset.prod_le_prod
    · intro p _hp
      have h_det_pos : 0 < Matrix.det (P.localSchur p) :=
        Matrix.PosDef.det_pos (P.localSchur_posDef p)
      positivity
    · intro p hp
      have hp_le : (4 : ℝ) ^ (p.val + m) ≤ Real.exp (2 * L) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp
      exact P.relevant_block_bound p ε L hε hL_pos hp_le

  trivial
