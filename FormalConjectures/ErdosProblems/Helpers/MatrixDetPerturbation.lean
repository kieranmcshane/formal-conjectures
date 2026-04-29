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

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Entrywise determinant perturbation bound

If two `n × n` real matrices `A, B` have entries within `δ` of each other and
both have entries bounded by `M` in absolute value, then their determinants
differ by at most `(card n) * (card n)! * δ * M^((card n) - 1)`.

This is the matrix-side prerequisite for Phase 2 / Node 6 of the Erdős 524
formalisation: it bridges the entrywise closeness of `K_GLW_matrix m` and
`hierCauchyG m` (proved in `GLWHierApprox.lean`) to closeness of their
determinants, which is what the V1-instance Anderson bounds consume.

The proof goes through the Leibniz expansion `Matrix.det_apply'` and a
telescoping-product bound on `|∏ a_i - ∏ b_i|`. It uses only the entrywise
sup norm — no operator norm or PosDef assumptions are needed.

The natural target file for this lemma is
`FormalConjecturesForMathlib/Matrix/EntrywiseDetPerturbation.lean`; it is
parked here under `FormalConjectures/ErdosProblems/Helpers/` for in-project
use during Phase 2 and can be moved + namespaced once Phase 2 closes.
-/

namespace Erdos524.Helpers
open Finset Matrix

/-! ## Telescoping product bound -/

/-- Telescoping bound: if every `|a i - b i| ≤ δ` and every `|a i|, |b i| ≤ M`
on `s`, then `|∏ s, a - ∏ s, b| ≤ s.card * δ * M^(s.card - 1)`. -/
lemma abs_prod_sub_prod_le {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α → ℝ) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (ha_bd : ∀ i ∈ s, |a i| ≤ M)
    (hb_bd : ∀ i ∈ s, |b i| ≤ M)
    (h_close : ∀ i ∈ s, |a i - b i| ≤ δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * δ * M ^ (s.card - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x t hxt ih =>
    -- Specialise hypotheses to `t`.
    have ha_bd_t : ∀ i ∈ t, |a i| ≤ M := fun i hi =>
      ha_bd i (Finset.mem_insert_of_mem hi)
    have hb_bd_t : ∀ i ∈ t, |b i| ≤ M := fun i hi =>
      hb_bd i (Finset.mem_insert_of_mem hi)
    have h_close_t : ∀ i ∈ t, |a i - b i| ≤ δ := fun i hi =>
      h_close i (Finset.mem_insert_of_mem hi)
    have ha_x : |a x| ≤ M := ha_bd x (Finset.mem_insert_self x t)
    have hb_x : |b x| ≤ M := hb_bd x (Finset.mem_insert_self x t)
    have h_close_x : |a x - b x| ≤ δ := h_close x (Finset.mem_insert_self x t)
    have ih' := ih ha_bd_t hb_bd_t h_close_t
    -- Algebraic split.
    rw [Finset.prod_insert hxt, Finset.prod_insert hxt]
    have h_split :
        a x * ∏ i ∈ t, a i - b x * ∏ i ∈ t, b i =
          a x * (∏ i ∈ t, a i - ∏ i ∈ t, b i) +
            (a x - b x) * ∏ i ∈ t, b i := by ring
    rw [h_split]
    -- Triangle inequality.
    have h_tri :
        |a x * (∏ i ∈ t, a i - ∏ i ∈ t, b i) + (a x - b x) * ∏ i ∈ t, b i| ≤
          |a x| * |∏ i ∈ t, a i - ∏ i ∈ t, b i| +
            |a x - b x| * |∏ i ∈ t, b i| := by
      calc |a x * (∏ i ∈ t, a i - ∏ i ∈ t, b i) + (a x - b x) * ∏ i ∈ t, b i|
          ≤ |a x * (∏ i ∈ t, a i - ∏ i ∈ t, b i)| +
              |(a x - b x) * ∏ i ∈ t, b i| := abs_add_le _ _
        _ = |a x| * |∏ i ∈ t, a i - ∏ i ∈ t, b i| +
              |a x - b x| * |∏ i ∈ t, b i| := by
              rw [abs_mul, abs_mul]
    refine h_tri.trans ?_
    -- Bound each piece. First piece: |a x| * |Δ_prod| ≤ M * (t.card · δ · M^(t.card - 1)).
    have h_M_nn : 0 ≤ M := hM
    have h_prod_b_le_M_pow_card : |∏ i ∈ t, b i| ≤ M ^ t.card := by
      calc |∏ i ∈ t, b i|
          = ∏ i ∈ t, |b i| := Finset.abs_prod _ _
        _ ≤ ∏ i ∈ t, M :=
              Finset.prod_le_prod (fun i _ => abs_nonneg _) hb_bd_t
        _ = M ^ t.card := by simp
    have h_first :
        |a x| * |∏ i ∈ t, a i - ∏ i ∈ t, b i| ≤
          M * (t.card * δ * M ^ (t.card - 1)) := by
      have h_diff_nn : 0 ≤ |∏ i ∈ t, a i - ∏ i ∈ t, b i| := abs_nonneg _
      have h_rhs_nn : 0 ≤ t.card * δ * M ^ (t.card - 1) := by
        have : 0 ≤ M ^ (t.card - 1) := pow_nonneg hM _
        positivity
      exact mul_le_mul ha_x ih' h_diff_nn hM
    have h_second :
        |a x - b x| * |∏ i ∈ t, b i| ≤ δ * M ^ t.card := by
      have h_prod_b_nn : 0 ≤ |∏ i ∈ t, b i| := abs_nonneg _
      have h_pow_nn : 0 ≤ M ^ t.card := pow_nonneg hM _
      exact mul_le_mul h_close_x h_prod_b_le_M_pow_card h_prod_b_nn hδ
    -- Combine and simplify.
    have h_sum : M * (t.card * δ * M ^ (t.card - 1)) + δ * M ^ t.card ≤
        (insert x t).card * δ * M ^ ((insert x t).card - 1) := by
      have h_card : (insert x t).card = t.card + 1 := Finset.card_insert_of_notMem hxt
      rw [h_card]
      simp only [Nat.add_sub_cancel]
      -- Goal: M * (↑t.card * δ * M^(t.card - 1)) + δ * M^t.card ≤ (↑t.card + 1) * δ * M^t.card
      by_cases ht : t.card = 0
      · -- t.card = 0 means M * (0 · δ · M^?) + δ * M^0 ≤ 1 · δ · M^0 ⇒ 0 + δ ≤ δ. ✓
        rw [ht]
        simp
      · -- t.card ≥ 1: equality LHS = RHS = M · K · δ · (n + 1) where K = M^(t.card-1).
        have h_card_pos : 0 < t.card := Nat.pos_of_ne_zero ht
        have h_pow_succ : M ^ t.card = M * M ^ (t.card - 1) := by
          conv_lhs => rw [show t.card = (t.card - 1) + 1 from
            (Nat.sub_add_cancel h_card_pos).symm]
          rw [pow_succ]; ring
        have h_eq :
            M * (↑t.card * δ * M ^ (t.card - 1)) + δ * M ^ t.card =
              (↑t.card + 1) * δ * M ^ t.card := by
          rw [h_pow_succ]; ring
        push_cast
        linarith [h_eq]
    linarith [h_first, h_second, h_sum]

/-! ## Determinant perturbation -/

/-- Entrywise sup-norm bound on absolute determinant difference.
For `n × n` real matrices `A, B` with entries in `[-M, M]` and entrywise
discrepancy at most `δ`, the determinants satisfy
`|A.det - B.det| ≤ (card n) * (card n)! * δ * M^((card n) - 1)`. -/
theorem abs_det_sub_det_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hA_bd : ∀ i j, |A i j| ≤ M)
    (hB_bd : ∀ i j, |B i j| ≤ M)
    (h_close : ∀ i j, |A i j - B i j| ≤ δ) :
    |A.det - B.det| ≤
      (Fintype.card n) * (Fintype.card n).factorial *
        δ * M ^ ((Fintype.card n) - 1) := by
  -- Leibniz expansion.
  rw [Matrix.det_apply', Matrix.det_apply']
  -- Difference of sums = sum of differences (per σ).
  rw [← Finset.sum_sub_distrib]
  -- Rewrite each summand σ as σ.sign • (∏ A_σ - ∏ B_σ).
  have h_eq_per_perm : ∀ σ : Equiv.Perm n,
      ↑(Equiv.Perm.sign σ) * ∏ i, A (σ i) i -
        ↑(Equiv.Perm.sign σ) * ∏ i, B (σ i) i =
      ↑(Equiv.Perm.sign σ) * (∏ i, A (σ i) i - ∏ i, B (σ i) i) := by
    intro σ
    ring
  rw [Finset.sum_congr rfl (fun σ _ => h_eq_per_perm σ)]
  -- |sum| ≤ sum of |·|
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Per σ: |σ.sign| · |∏ A_σ - ∏ B_σ| ≤ 1 · n · δ · M^(n-1).
  have h_per_perm : ∀ σ : Equiv.Perm n,
      |↑(Equiv.Perm.sign σ) * (∏ i, A (σ i) i - ∏ i, B (σ i) i)| ≤
      (Fintype.card n) * δ * M ^ ((Fintype.card n) - 1) := by
    intro σ
    rw [abs_mul]
    have h_sign_abs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      · rw [h]
        norm_num
    rw [h_sign_abs, one_mul]
    -- Reduce ∏ over univ to ∏ over Finset.univ : Finset n
    have h_prod_a : ∏ i, A (σ i) i = ∏ i ∈ (Finset.univ : Finset n), A (σ i) i := rfl
    have h_prod_b : ∏ i, B (σ i) i = ∏ i ∈ (Finset.univ : Finset n), B (σ i) i := rfl
    rw [h_prod_a, h_prod_b]
    have ha_bd_perm : ∀ i ∈ (Finset.univ : Finset n), |A (σ i) i| ≤ M :=
      fun i _ => hA_bd (σ i) i
    have hb_bd_perm : ∀ i ∈ (Finset.univ : Finset n), |B (σ i) i| ≤ M :=
      fun i _ => hB_bd (σ i) i
    have h_close_perm : ∀ i ∈ (Finset.univ : Finset n), |A (σ i) i - B (σ i) i| ≤ δ :=
      fun i _ => h_close (σ i) i
    have h_lemma := abs_prod_sub_prod_le (Finset.univ : Finset n)
      (fun i => A (σ i) i) (fun i => B (σ i) i) M δ hM hδ
      ha_bd_perm hb_bd_perm h_close_perm
    have h_card : (Finset.univ : Finset n).card = Fintype.card n :=
      Finset.card_univ
    rw [h_card] at h_lemma
    exact h_lemma
  -- Sum over permutations.
  refine (Finset.sum_le_sum (fun σ _ => h_per_perm σ)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
  -- Goal: (Fintype.card n)! • (n · δ · M^(n-1)) ≤ n · n! · δ · M^(n-1)
  have h_smul : ∀ (k : ℕ) (x : ℝ), k • x = (k : ℝ) * x := fun k x => by
    rw [nsmul_eq_mul]
  rw [h_smul]
  -- Both sides are `(card n)! · card n · δ · M^(card n - 1)`; just rearrange order.
  ring_nf
  exact le_refl _

end Erdos524.Helpers
