import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
open Finset

theorem disjoint_filter (m : ℕ) (L : ℝ) :
  Disjoint
    (Finset.univ.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) ≤ L))
    (Finset.univ.filter (λ p : Fin m => (4 : ℝ) ^ (p.val + m) > L)) := by
  rw [disjoint_left]
  intro a ha hb
  rw [mem_filter] at ha hb
  linarith [ha.2, hb.2]
