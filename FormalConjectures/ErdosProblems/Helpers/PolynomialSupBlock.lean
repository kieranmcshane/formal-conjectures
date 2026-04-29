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

import FormalConjectures.Util.ProblemImports

/-!
# Block-truncated polynomial sup norm (helper for Erdős 524)

For a random sequence of coefficients `a : ℕ → Ω → ℝ` and a finite block
`I ⊆ ℕ`, the block-truncated polynomial supremum on `[-1, 1]` is
```
polynomialSupBlock a I ω := ⨆ x ∈ Set.Icc (-1) 1, |∑ k ∈ I, a k ω * x^k|.
```
The global supremum `supNorm a n ω` in `524.lean` is the special case
`I = Finset.Icc 1 n`.

This file provides:
1. The definition `polynomialSupBlock`.
2. `polynomialSupBlock_bddAbove`: for each fixed `ω`, the set
   `{|∑_{k∈I} a k ω · x^k| : x ∈ [-1, 1]}` is bounded above by
   `∑_{k∈I} |a k ω|` (a polynomial restricted to a compact set).
3. `polynomialSupBlock_le_sum_abs`: the same bound applied to the sup.
4. Bridge: `polynomialSupBlock_eq_supNorm`-style identity connecting to
   `supNorm` when `I = Finset.Icc 1 n`.

We intentionally do NOT prove full measurability of `polynomialSupBlock` here;
that requires the same sup-continuity argument used for `supNorm` itself, and
is not yet pinned to a Mathlib API. A narrow residual sorry for measurability
is left with a precise label. -/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524
namespace Helpers

open MeasureTheory Finset
open scoped Topology

/-- The block-truncated polynomial sup norm on `[-1, 1]`:
`⨆_{x ∈ [-1, 1]} |∑_{k ∈ I} a k ω x^k|`. -/
noncomputable def polynomialSupBlock {Ω : Type*} (a : ℕ → Ω → ℝ)
    (I : Finset ℕ) (ω : Ω) : ℝ :=
  ⨆ x ∈ Set.Icc (-1 : ℝ) 1, |∑ k ∈ I, a k ω * x ^ k|

/-- For each `ω`, the polynomial `x ↦ |∑_{k∈I} a k ω x^k|` is bounded above on
`[-1, 1]` by `∑_{k∈I} |a k ω|`.

Key inputs: `|a_k · x^k| ≤ |a_k|` when `x ∈ [-1, 1]`, then sum. -/
lemma polynomialSupBlock_abs_le_sum_abs
    {Ω : Type*} (a : ℕ → Ω → ℝ) (I : Finset ℕ) (ω : Ω)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |∑ k ∈ I, a k ω * x ^ k| ≤ ∑ k ∈ I, |a k ω| := by
  have habsx : |x| ≤ 1 := by
    rcases hx with ⟨hx1, hx2⟩; rw [abs_le]; exact ⟨hx1, hx2⟩
  calc |∑ k ∈ I, a k ω * x ^ k|
      ≤ ∑ k ∈ I, |a k ω * x ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ I, |a k ω| * |x ^ k| := by
        refine Finset.sum_congr rfl (fun k _ => ?_); exact abs_mul _ _
    _ ≤ ∑ k ∈ I, |a k ω| * 1 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hxk : |x ^ k| ≤ 1 := by
          rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) habsx
        exact mul_le_mul_of_nonneg_left hxk (abs_nonneg _)
    _ = ∑ k ∈ I, |a k ω| := by simp

/-- The image of the absolute-value polynomial on `[-1, 1]` is bounded above. -/
lemma polynomialSupBlock_image_bddAbove
    {Ω : Type*} (a : ℕ → Ω → ℝ) (I : Finset ℕ) (ω : Ω) :
    BddAbove ((fun x : ℝ => |∑ k ∈ I, a k ω * x ^ k|) '' Set.Icc (-1) 1) := by
  refine ⟨∑ k ∈ I, |a k ω|, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact polynomialSupBlock_abs_le_sum_abs a I ω hx

/-- The block-truncated polynomial sup norm is bounded above by the sum of
absolute coefficient values. -/
lemma polynomialSupBlock_le_sum_abs
    {Ω : Type*} (a : ℕ → Ω → ℝ) (I : Finset ℕ) (ω : Ω) :
    polynomialSupBlock a I ω ≤ ∑ k ∈ I, |a k ω| := by
  unfold polynomialSupBlock
  -- Bound on the outer sup: need BddAbove of outer range.
  refine ciSup_le fun x => ?_
  rcases em (x ∈ Set.Icc (-1 : ℝ) 1) with hx | hx
  · haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
    refine ciSup_le fun _ => ?_
    exact polynomialSupBlock_abs_le_sum_abs a I ω hx
  · have hempty : ¬(x ∈ Set.Icc (-1 : ℝ) 1) := hx
    simp [hempty]
    exact Finset.sum_nonneg (fun k _ => abs_nonneg _)

/-- Bridge to `supNorm` in 524.lean: for `I = Finset.Icc 1 n`, the block-truncated
sup norm matches the full `supNorm` (up to unfolding definitions).

We do not import 524.lean here (circular), so we state this as an `rfl`-style
identity in terms of the underlying `⨆` expression. -/
lemma polynomialSupBlock_eq_iSup_abs_poly
    {Ω : Type*} (a : ℕ → Ω → ℝ) (I : Finset ℕ) (ω : Ω) :
    polynomialSupBlock a I ω =
      ⨆ x ∈ Set.Icc (-1 : ℝ) 1, |∑ k ∈ I, a k ω * x ^ k| := rfl

/-- When the block is `Finset.Icc 1 n`, the block supremum has the same shape
as the `randomPoly`-based `supNorm` of 524.lean. -/
lemma polynomialSupBlock_Icc_eq
    {Ω : Type*} (a : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    polynomialSupBlock a (Finset.Icc 1 n) ω =
      ⨆ x ∈ Set.Icc (-1 : ℝ) 1, |∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k| := rfl

/-- Nonnegativity of the block-truncated sup norm.

Uses the base point `x = 0 ∈ [-1, 1]` where the inner expression is `|0| = 0`
(when `I` doesn't contain `0`) or `|a_0 ω|` (when `0 ∈ I`), which is ≥ 0.
More generally, the outer `⨆` over `x ∈ Icc (-1) 1` of nonneg-image is ≥ 0. -/
lemma polynomialSupBlock_nonneg
    {Ω : Type*} (a : ℕ → Ω → ℝ) (I : Finset ℕ) (ω : Ω) :
    (0 : ℝ) ≤ polynomialSupBlock a I ω := by
  -- Use `0 ∈ Icc (-1) 1` and the fact that the inner value at 0 is nonneg,
  -- combined with `le_ciSup` (outer) applied at `x = 0`.
  unfold polynomialSupBlock
  -- Introduce BddAbove for outer sup.
  have hbdd_outer : BddAbove (Set.range fun y =>
      ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ I, a k ω * y ^ k|) := by
    refine ⟨∑ k ∈ I, |a k ω|, ?_⟩
    rintro z ⟨y, rfl⟩
    rcases em (y ∈ Set.Icc (-1 : ℝ) 1) with hy | hy
    · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
      exact ciSup_le fun _ => polynomialSupBlock_abs_le_sum_abs a I ω hy
    · have : ¬(y ∈ Set.Icc (-1 : ℝ) 1) := hy
      simp [this]
      exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  -- At y = 0: outer indicator inner sup is |∑_{k∈I} a_k ω · 0^k|. For `k ≥ 1`,
  -- `0^k = 0`. For `k = 0`, `0^0 = 1`. The absolute value is ≥ 0 regardless.
  have h0mem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  haveI : Nonempty ((0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) := ⟨h0mem⟩
  have hinner_nonneg : (0 : ℝ) ≤ |∑ k ∈ I, a k ω * (0 : ℝ) ^ k| := abs_nonneg _
  have hinner_bddAbove :
      BddAbove (Set.range fun _ : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 =>
        |∑ k ∈ I, a k ω * (0 : ℝ) ^ k|) := by
    refine ⟨|∑ k ∈ I, a k ω * (0 : ℝ) ^ k|, ?_⟩
    rintro z ⟨_, rfl⟩; exact le_refl _
  -- ⨆ indicator at y = 0 is the inner absolute value.
  have hat_zero : (⨆ (_ : (0:ℝ) ∈ Set.Icc (-1 : ℝ) 1),
      |∑ k ∈ I, a k ω * (0 : ℝ) ^ k|) =
      |∑ k ∈ I, a k ω * (0 : ℝ) ^ k| := by
    exact ciSup_const
  calc (0 : ℝ)
      ≤ |∑ k ∈ I, a k ω * (0 : ℝ) ^ k| := hinner_nonneg
    _ = ⨆ (_ : (0:ℝ) ∈ Set.Icc (-1 : ℝ) 1),
          |∑ k ∈ I, a k ω * (0 : ℝ) ^ k| := hat_zero.symm
    _ ≤ ⨆ x, ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ I, a k ω * x ^ k| :=
        le_ciSup hbdd_outer (0 : ℝ)

/-- Measurability of `ω ↦ polynomialSupBlock a I ω` (with each `a k` measurable).

The sup over `[-1,1]` coincides with the sup over the countable dense subset
`ℚ ∩ [-1,1]` (by continuity of the polynomial in `x`), and the latter is a
countable biSup of measurable functions, hence measurable. -/
lemma polynomialSupBlock_measurable
    {Ω : Type*} [MeasurableSpace Ω] (a : ℕ → Ω → ℝ)
    (hmeas : ∀ k, Measurable (a k)) (I : Finset ℕ) :
    Measurable (fun ω => polynomialSupBlock a I ω) := by
  classical
  -- Countable dense subset of Icc (-1) 1: rationals (as reals) in [-1,1].
  set D : Set ℝ := (Set.range ((↑) : ℚ → ℝ)) ∩ Set.Icc (-1 : ℝ) 1 with hD_def
  have hD_count : D.Countable :=
    (Set.countable_range _).mono Set.inter_subset_left
  have hD_sub_Icc : D ⊆ Set.Icc (-1 : ℝ) 1 := Set.inter_subset_right
  -- Abbreviation: f x ω = |∑ k ∈ I, a k ω * x^k|.
  set f : ℝ → Ω → ℝ := fun x ω => |∑ k ∈ I, a k ω * x ^ k| with hf_def
  -- Measurability in ω, for each x.
  have hf_meas : ∀ x, Measurable (f x) := fun x => by
    refine Measurable.abs ?_
    exact Finset.measurable_sum _ (fun k _ => (hmeas k).mul_const _)
  -- Continuity in x, for each ω.
  have hf_cont : ∀ ω, Continuous (fun x : ℝ => f x ω) := fun ω => by
    refine Continuous.abs ?_
    exact continuous_finset_sum _
      (fun k _ => continuous_const.mul (continuous_id.pow k))
  -- Range of f x (over x ∈ Icc) is bounded above (pointwise in ω).
  have hbdd_range : ∀ ω,
      BddAbove ((fun x : ℝ => f x ω) '' Set.Icc (-1 : ℝ) 1) :=
    polynomialSupBlock_image_bddAbove a I
  -- Auxiliary: boundedness of outer iSup range for Icc and D.
  have hbdd_outer_Icc : ∀ ω, BddAbove (Set.range fun z =>
      ⨆ (_ : z ∈ Set.Icc (-1 : ℝ) 1), f z ω) := fun ω => by
    refine ⟨∑ k ∈ I, |a k ω|, ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
    · haveI : Nonempty (z ∈ Set.Icc (-1 : ℝ) 1) := ⟨hz⟩
      exact ciSup_le fun _ => polynomialSupBlock_abs_le_sum_abs a I ω hz
    · have : (⨆ (_ : z ∈ Set.Icc (-1 : ℝ) 1), f z ω) ≤ 0 := by
        have : (Set.range fun (_ : z ∈ Set.Icc (-1 : ℝ) 1) => f z ω) = ∅ :=
          Set.range_eq_empty_iff.mpr ⟨hz⟩
        simp [iSup, this]
      exact this.trans (Finset.sum_nonneg (fun k _ => abs_nonneg _))
  have hbdd_outer_D : ∀ ω, BddAbove (Set.range fun z =>
      ⨆ (_ : z ∈ D), f z ω) := fun ω => by
    refine ⟨∑ k ∈ I, |a k ω|, ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ D
    · haveI : Nonempty (z ∈ D) := ⟨hz⟩
      exact ciSup_le fun _ =>
        polynomialSupBlock_abs_le_sum_abs a I ω (hD_sub_Icc hz)
    · have : (⨆ (_ : z ∈ D), f z ω) ≤ 0 := by
        have : (Set.range fun (_ : z ∈ D) => f z ω) = ∅ :=
          Set.range_eq_empty_iff.mpr ⟨hz⟩
        simp [iSup, this]
      exact this.trans (Finset.sum_nonneg (fun k _ => abs_nonneg _))
  -- Key equality (pointwise in ω): sup over Icc = sup over D.
  have hSup_eq : ∀ ω,
      polynomialSupBlock a I ω = ⨆ x ∈ D, f x ω := by
    intro ω
    unfold polynomialSupBlock
    apply le_antisymm
    · -- LHS (sup over Icc) ≤ RHS (sup over D): density + continuity.
      refine ciSup_le fun x => ?_
      by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
      · haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
        refine ciSup_le fun _ => ?_
        -- f x ω ≤ ⨆ z ∈ D, f z ω via sequential approximation.
        -- Strategy: pick q_n ∈ D with (q_n : ℝ) → x, then f q_n ω → f x ω
        -- (continuity), and each f q_n ω ≤ ⨆ z ∈ D, f z ω.
        -- We use `le_of_tendsto`: if a_n → ℓ and ∀ n, a_n ≤ M, then ℓ ≤ M.
        -- Construct the sequence using Rat.denseRange_cast.
        have hx_ge : (-1 : ℝ) ≤ x := hx.1
        have hx_le : x ≤ (1 : ℝ) := hx.2
        -- Pick rationals q_n converging to x with each (q_n : ℝ) ∈ [-1, 1].
        -- For each n, choose q_n with |q_n - x| < 1/(n+1) and q_n ∈ [-1, 1].
        -- We use the "clamp" construction: if a rational near x is chosen, and
        -- we clamp to [-1,1], it stays rational and converges.
        have hseq : ∃ q : ℕ → ℚ, (∀ n, (-1 : ℝ) ≤ (q n : ℝ) ∧ (q n : ℝ) ≤ 1) ∧
            Filter.Tendsto (fun n => ((q n : ℝ))) Filter.atTop (𝓝 x) := by
          have : ∀ n : ℕ, ∃ q : ℚ, (-1 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧
              |(q : ℝ) - x| < 1 / (n + 1 : ℝ) := by
            intro n
            have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
            have hle : (max (-1 : ℝ) (x - 1 / (n + 1 : ℝ))) <
                (min (1 : ℝ) (x + 1 / (n + 1 : ℝ))) := by
              apply max_lt
              · exact lt_min (by linarith) (by linarith)
              · exact lt_min (by linarith) (by linarith)
            obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hle
            refine ⟨q, ?_, ?_, ?_⟩
            · exact le_of_lt ((le_max_left _ _).trans_lt hq1)
            · exact le_of_lt (hq2.trans_le (min_le_left _ _))
            · rw [abs_sub_lt_iff]; refine ⟨?_, ?_⟩
              · have := hq2.trans_le (min_le_right _ _); linarith
              · have := (le_max_right _ _).trans_lt hq1; linarith
          choose q hq_ge hq_le hq_close using this
          refine ⟨q, fun n => ⟨hq_ge n, hq_le n⟩, ?_⟩
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
          refine ⟨N, fun n hn => ?_⟩
          have : |(q n : ℝ) - x| < 1 / (n + 1 : ℝ) := hq_close n
          have hmono : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
            apply one_div_le_one_div_of_le
            · exact_mod_cast Nat.succ_pos N
            · exact_mod_cast Nat.succ_le_succ hn
          have hbd : 1 / (N + 1 : ℝ) < ε := hN
          rw [Real.dist_eq]
          linarith
        obtain ⟨q, hq_mem, hq_lim⟩ := hseq
        -- Each (q n : ℝ) is in D.
        have hqD : ∀ n, (q n : ℝ) ∈ D := fun n =>
          ⟨⟨q n, rfl⟩, hq_mem n⟩
        -- f (q n) ω → f x ω by continuity.
        have hfq_tendsto : Filter.Tendsto (fun n => f (q n : ℝ) ω) Filter.atTop
            (𝓝 (f x ω)) := ((hf_cont ω).tendsto x).comp hq_lim
        -- Each f (q n) ω ≤ ⨆ z ∈ D, f z ω.
        have hfq_le : ∀ n, f (q n : ℝ) ω ≤ ⨆ z ∈ D, f z ω := by
          intro n
          haveI : Nonempty ((q n : ℝ) ∈ D) := ⟨hqD n⟩
          calc f (q n : ℝ) ω
              = ⨆ (_ : (q n : ℝ) ∈ D), f (q n : ℝ) ω := (ciSup_const).symm
            _ ≤ ⨆ z ∈ D, f z ω := le_ciSup (hbdd_outer_D ω) _
        -- Conclude: f x ω ≤ ⨆ z ∈ D, f z ω.
        exact le_of_tendsto_of_frequently hfq_tendsto (.of_forall hfq_le)
      · -- x ∉ Icc: inner iSup is ≤ 0 ≤ RHS (since f ≥ 0 on D, nonempty).
        have : (⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1), f x ω) ≤ 0 := by
          have : (Set.range fun (_ : x ∈ Set.Icc (-1 : ℝ) 1) => f x ω) = ∅ :=
            Set.range_eq_empty_iff.mpr ⟨hx⟩
          simp [iSup, this]
        refine this.trans ?_
        -- 0 ≤ ⨆ z ∈ D, f z ω. Use that 0 ∈ D (as ↑(0 : ℚ) = 0).
        have h0D : (0 : ℝ) ∈ D := ⟨⟨0, by norm_num⟩, by constructor <;> norm_num⟩
        haveI : Nonempty ((0 : ℝ) ∈ D) := ⟨h0D⟩
        calc (0 : ℝ)
            ≤ f 0 ω := abs_nonneg _
          _ = ⨆ (_ : (0 : ℝ) ∈ D), f 0 ω := (ciSup_const).symm
          _ ≤ ⨆ z ∈ D, f z ω := le_ciSup (hbdd_outer_D ω) 0
    · -- RHS ≤ LHS: sup over D ≤ sup over Icc (since D ⊆ Icc).
      refine ciSup_le fun x => ?_
      by_cases hx : x ∈ D
      · haveI : Nonempty (x ∈ D) := ⟨hx⟩
        refine ciSup_le fun _ => ?_
        have hx_Icc : x ∈ Set.Icc (-1 : ℝ) 1 := hD_sub_Icc hx
        haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx_Icc⟩
        calc f x ω = ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1), f x ω := (ciSup_const).symm
          _ ≤ ⨆ z ∈ Set.Icc (-1 : ℝ) 1, f z ω := le_ciSup (hbdd_outer_Icc ω) x
      · have : (⨆ (_ : x ∈ D), f x ω) ≤ 0 := by
          have : (Set.range fun (_ : x ∈ D) => f x ω) = ∅ :=
            Set.range_eq_empty_iff.mpr ⟨hx⟩
          simp [iSup, this]
        refine this.trans ?_
        -- 0 ≤ ⨆ z ∈ Icc, f z ω via z = 0.
        have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
        haveI : Nonempty ((0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) := ⟨h0⟩
        calc (0 : ℝ)
            ≤ f 0 ω := abs_nonneg _
          _ = ⨆ (_ : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1), f 0 ω := (ciSup_const).symm
          _ ≤ ⨆ z ∈ Set.Icc (-1 : ℝ) 1, f z ω := le_ciSup (hbdd_outer_Icc ω) 0
  -- Conclude measurability via the countable biSup.
  have heq : (fun ω => polynomialSupBlock a I ω) = fun ω => ⨆ x ∈ D, f x ω := by
    funext ω; exact hSup_eq ω
  rw [heq]
  exact Measurable.biSup D hD_count (fun x _ => hf_meas x)

/-- **Triangle inequality for `polynomialSupBlock`** over disjoint unions.

If `I` and `J` are disjoint finite index sets, the polynomial sup norm over
`I ∪ J` is bounded by the sum of the block sup norms over `I` and `J`:
`polynomialSupBlock a (I ∪ J) ω ≤ polynomialSupBlock a I ω + polynomialSupBlock a J ω`.

Proof outline. For any `x ∈ [-1, 1]`,
  `∑_{k ∈ I ∪ J} a k ω · x^k = ∑_{k ∈ I} a k ω · x^k + ∑_{k ∈ J} a k ω · x^k`
(by `Finset.sum_union` with `Disjoint I J`), so the absolute value is bounded
by the sum of absolute values, each of which is bounded by the respective
block sup (at this fixed `x`). Taking the sup over `x` then gives the result. -/
lemma polynomialSupBlock_union_le
    {Ω : Type*} (a : ℕ → Ω → ℝ) {I J : Finset ℕ} (hdisj : Disjoint I J) (ω : Ω) :
    polynomialSupBlock a (I ∪ J) ω ≤
      polynomialSupBlock a I ω + polynomialSupBlock a J ω := by
  -- Pointwise triangle bound at each x ∈ Icc (-1) 1.
  have hpt : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |∑ k ∈ (I ∪ J), a k ω * x ^ k| ≤
        polynomialSupBlock a I ω + polynomialSupBlock a J ω := by
    intro x hx
    rw [Finset.sum_union hdisj]
    have h1 : |∑ k ∈ I, a k ω * x ^ k + ∑ k ∈ J, a k ω * x ^ k| ≤
        |∑ k ∈ I, a k ω * x ^ k| + |∑ k ∈ J, a k ω * x ^ k| := abs_add_le _ _
    -- Each inner term is ≤ the respective polynomialSupBlock.
    have hI_le : |∑ k ∈ I, a k ω * x ^ k| ≤ polynomialSupBlock a I ω := by
      unfold polynomialSupBlock
      haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
      -- le_ciSup to pass to the outer sup.
      have hbdd : BddAbove (Set.range fun y =>
          ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ I, a k ω * y ^ k|) := by
        refine ⟨∑ k ∈ I, |a k ω|, ?_⟩
        rintro _ ⟨y, rfl⟩
        by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
        · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
          exact ciSup_le fun _ => polynomialSupBlock_abs_le_sum_abs a I ω hy
        · have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ I, a k ω * y ^ k|) ≤ 0 := by
            have : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) =>
                |∑ k ∈ I, a k ω * y ^ k|) = ∅ :=
              Set.range_eq_empty_iff.mpr ⟨hy⟩
            simp [iSup, this]
          exact this.trans (Finset.sum_nonneg (fun k _ => abs_nonneg _))
      calc |∑ k ∈ I, a k ω * x ^ k|
          = ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ I, a k ω * x ^ k| := (ciSup_const).symm
        _ ≤ ⨆ y, ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ I, a k ω * y ^ k| :=
            le_ciSup hbdd x
    have hJ_le : |∑ k ∈ J, a k ω * x ^ k| ≤ polynomialSupBlock a J ω := by
      unfold polynomialSupBlock
      haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
      have hbdd : BddAbove (Set.range fun y =>
          ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ J, a k ω * y ^ k|) := by
        refine ⟨∑ k ∈ J, |a k ω|, ?_⟩
        rintro _ ⟨y, rfl⟩
        by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
        · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
          exact ciSup_le fun _ => polynomialSupBlock_abs_le_sum_abs a J ω hy
        · have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ J, a k ω * y ^ k|) ≤ 0 := by
            have : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) =>
                |∑ k ∈ J, a k ω * y ^ k|) = ∅ :=
              Set.range_eq_empty_iff.mpr ⟨hy⟩
            simp [iSup, this]
          exact this.trans (Finset.sum_nonneg (fun k _ => abs_nonneg _))
      calc |∑ k ∈ J, a k ω * x ^ k|
          = ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ J, a k ω * x ^ k| := (ciSup_const).symm
        _ ≤ ⨆ y, ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), |∑ k ∈ J, a k ω * y ^ k| :=
            le_ciSup hbdd x
    linarith
  -- Now pass to the outer sup.
  unfold polynomialSupBlock
  refine ciSup_le fun x => ?_
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
    exact ciSup_le fun _ => hpt x hx
  · have hempty : (Set.range fun (_ : x ∈ Set.Icc (-1 : ℝ) 1) =>
        |∑ k ∈ (I ∪ J), a k ω * x ^ k|) = ∅ :=
      Set.range_eq_empty_iff.mpr ⟨hx⟩
    have hle0 : (⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
        |∑ k ∈ (I ∪ J), a k ω * x ^ k|) ≤ 0 := by
      simp [iSup, hempty]
    have hInn : 0 ≤ polynomialSupBlock a I ω := polynomialSupBlock_nonneg a I ω
    have hJnn : 0 ≤ polynomialSupBlock a J ω := polynomialSupBlock_nonneg a J ω
    have hsum_nn : 0 ≤ polynomialSupBlock a I ω + polynomialSupBlock a J ω := by linarith
    -- Unfold the RHS polynomialSupBlock to match the goal.
    show (⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
        |∑ k ∈ (I ∪ J), a k ω * x ^ k|) ≤
        polynomialSupBlock a I ω + polynomialSupBlock a J ω
    linarith

/-- **Icc-split triangle** for the polynomial sup norm. For `m ≤ n`,
`polynomialSupBlock a (Finset.Icc 1 n) ω
  ≤ polynomialSupBlock a (Finset.Icc 1 m) ω
  + polynomialSupBlock a (Finset.Icc (m+1) n) ω`.
This is the special case of `polynomialSupBlock_union_le` applied to the
disjoint decomposition `Icc 1 n = Icc 1 m ∪ Icc (m+1) n` when `m ≤ n`. -/
lemma polynomialSupBlock_Icc_split
    {Ω : Type*} (a : ℕ → Ω → ℝ) {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    polynomialSupBlock a (Finset.Icc 1 n) ω ≤
      polynomialSupBlock a (Finset.Icc 1 m) ω +
        polynomialSupBlock a (Finset.Icc (m + 1) n) ω := by
  have hsplit : Finset.Icc 1 n = Finset.Icc 1 m ∪ Finset.Icc (m + 1) n := by
    ext j; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) n) := by
    simp only [Finset.disjoint_left, Finset.mem_Icc]; omega
  calc polynomialSupBlock a (Finset.Icc 1 n) ω
      = polynomialSupBlock a (Finset.Icc 1 m ∪ Finset.Icc (m + 1) n) ω := by rw [hsplit]
    _ ≤ polynomialSupBlock a (Finset.Icc 1 m) ω +
          polynomialSupBlock a (Finset.Icc (m + 1) n) ω :=
          polynomialSupBlock_union_le a hdisj ω

/-- **Reverse Icc-split triangle** for the polynomial sup norm. For `m ≤ n`,
`polynomialSupBlock a (Finset.Icc (m+1) n) ω
  ≤ polynomialSupBlock a (Finset.Icc 1 n) ω
  + polynomialSupBlock a (Finset.Icc 1 m) ω`.

This is the dual direction to `polynomialSupBlock_Icc_split`: at each `x`,
`∑_{k ∈ Icc (m+1) n} = ∑_{k ∈ Icc 1 n} - ∑_{k ∈ Icc 1 m}`, so
`|∑_{k ∈ Icc (m+1) n}| ≤ |∑_{k ∈ Icc 1 n}| + |∑_{k ∈ Icc 1 m}|`, and each
term is bounded by its respective block sup (at this fixed `x`). Taking the
sup over `x` gives the result. Used in the sandwich step of the Chojecki
sparse-upper-envelope argument (H6). -/
lemma polynomialSupBlock_Icc_sub_le
    {Ω : Type*} (a : ℕ → Ω → ℝ) {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    polynomialSupBlock a (Finset.Icc (m + 1) n) ω ≤
      polynomialSupBlock a (Finset.Icc 1 n) ω +
        polynomialSupBlock a (Finset.Icc 1 m) ω := by
  have hsplit : Finset.Icc 1 n = Finset.Icc 1 m ∪ Finset.Icc (m + 1) n := by
    ext j; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) n) := by
    simp only [Finset.disjoint_left, Finset.mem_Icc]; omega
  -- Pointwise bound at every x ∈ [-1, 1]:
  -- `|∑ Icc (m+1) n| = |∑ Icc 1 n - ∑ Icc 1 m| ≤ |∑ Icc 1 n| + |∑ Icc 1 m|`,
  -- and each bound is ≤ the corresponding polynomialSupBlock.
  have hpt : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |∑ k ∈ Finset.Icc (m + 1) n, a k ω * x ^ k| ≤
        polynomialSupBlock a (Finset.Icc 1 n) ω +
          polynomialSupBlock a (Finset.Icc 1 m) ω := by
    intro x hx
    have hsum_split : ∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k =
        (∑ k ∈ Finset.Icc 1 m, a k ω * x ^ k) +
          (∑ k ∈ Finset.Icc (m + 1) n, a k ω * x ^ k) := by
      rw [hsplit, Finset.sum_union hdisj]
    -- Rearrange: block_sum = full_sum - old_sum.
    have hblock_eq : ∑ k ∈ Finset.Icc (m + 1) n, a k ω * x ^ k =
        (∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k) -
          (∑ k ∈ Finset.Icc 1 m, a k ω * x ^ k) := by
      linarith [hsum_split]
    rw [hblock_eq]
    have habs_sub : |(∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k) -
        (∑ k ∈ Finset.Icc 1 m, a k ω * x ^ k)| ≤
        |∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k| +
          |∑ k ∈ Finset.Icc 1 m, a k ω * x ^ k| := abs_sub _ _
    have hN_le : |∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k| ≤
        polynomialSupBlock a (Finset.Icc 1 n) ω := by
      unfold polynomialSupBlock
      haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
      have hbdd : BddAbove (Set.range fun y =>
          ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
            |∑ k ∈ Finset.Icc 1 n, a k ω * y ^ k|) := by
        refine ⟨∑ k ∈ Finset.Icc 1 n, |a k ω|, ?_⟩
        rintro _ ⟨y, rfl⟩
        by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
        · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
          exact ciSup_le fun _ =>
            polynomialSupBlock_abs_le_sum_abs a (Finset.Icc 1 n) ω hy
        · have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 n, a k ω * y ^ k|) ≤ 0 := by
            have : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) =>
                |∑ k ∈ Finset.Icc 1 n, a k ω * y ^ k|) = ∅ :=
              Set.range_eq_empty_iff.mpr ⟨hy⟩
            simp [iSup, this]
          exact this.trans (Finset.sum_nonneg (fun k _ => abs_nonneg _))
      calc |∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k|
          = ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 n, a k ω * x ^ k| := (ciSup_const).symm
        _ ≤ ⨆ y, ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 n, a k ω * y ^ k| := le_ciSup hbdd x
    have hM_le : |∑ k ∈ Finset.Icc 1 m, a k ω * x ^ k| ≤
        polynomialSupBlock a (Finset.Icc 1 m) ω := by
      unfold polynomialSupBlock
      haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
      have hbdd : BddAbove (Set.range fun y =>
          ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
            |∑ k ∈ Finset.Icc 1 m, a k ω * y ^ k|) := by
        refine ⟨∑ k ∈ Finset.Icc 1 m, |a k ω|, ?_⟩
        rintro _ ⟨y, rfl⟩
        by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
        · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
          exact ciSup_le fun _ =>
            polynomialSupBlock_abs_le_sum_abs a (Finset.Icc 1 m) ω hy
        · have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 m, a k ω * y ^ k|) ≤ 0 := by
            have : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) =>
                |∑ k ∈ Finset.Icc 1 m, a k ω * y ^ k|) = ∅ :=
              Set.range_eq_empty_iff.mpr ⟨hy⟩
            simp [iSup, this]
          exact this.trans (Finset.sum_nonneg (fun k _ => abs_nonneg _))
      calc |∑ k ∈ Finset.Icc 1 m, a k ω * x ^ k|
          = ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 m, a k ω * x ^ k| := (ciSup_const).symm
        _ ≤ ⨆ y, ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 m, a k ω * y ^ k| := le_ciSup hbdd x
    linarith
  -- Pass to the outer sup.
  unfold polynomialSupBlock
  refine ciSup_le fun x => ?_
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
    exact ciSup_le fun _ => hpt x hx
  · have hempty : (Set.range fun (_ : x ∈ Set.Icc (-1 : ℝ) 1) =>
        |∑ k ∈ Finset.Icc (m + 1) n, a k ω * x ^ k|) = ∅ :=
      Set.range_eq_empty_iff.mpr ⟨hx⟩
    have hle0 : (⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
        |∑ k ∈ Finset.Icc (m + 1) n, a k ω * x ^ k|) ≤ 0 := by
      simp [iSup, hempty]
    have hN_nn : 0 ≤ polynomialSupBlock a (Finset.Icc 1 n) ω :=
      polynomialSupBlock_nonneg a _ ω
    have hM_nn : 0 ≤ polynomialSupBlock a (Finset.Icc 1 m) ω :=
      polynomialSupBlock_nonneg a _ ω
    show (⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
        |∑ k ∈ Finset.Icc (m + 1) n, a k ω * x ^ k|) ≤
        polynomialSupBlock a (Finset.Icc 1 n) ω +
          polynomialSupBlock a (Finset.Icc 1 m) ω
    linarith

/-- **Shifted block bound**: the polynomial sup norm over the shifted block
`Icc (m₀ + 1) (m₀ + N)` is bounded above by the polynomial sup norm of the
reindexed coefficient sequence `b_j := a (m₀ + j)` over `Icc 1 N`.

*Mathematically.* For `x ∈ [-1, 1]`, reindexing `k = m₀ + j`:
`∑_{k ∈ Icc (m₀+1) (m₀+N)} a k ω · x^k = x^{m₀} · ∑_{j ∈ Icc 1 N} a (m₀+j) ω · x^j`,
and `|x^{m₀}| = |x|^{m₀} ≤ 1` on `[-1, 1]`. Passing to the sup in `x` gives
the result.

This bridges to `supNorm` in `524.lean` via `polynomialSupBlock_Icc_eq`:
`polynomialSupBlock (fun j ω => a (m₀ + j) ω) (Icc 1 N) ω
  = supNorm (fun j ω => a (m₀ + j) ω) N ω`. -/
lemma polynomialSupBlock_shift_Icc_le
    {Ω : Type*} (a : ℕ → Ω → ℝ) (m₀ N : ℕ) (ω : Ω) :
    polynomialSupBlock a (Finset.Icc (m₀ + 1) (m₀ + N)) ω ≤
      polynomialSupBlock (fun j ω => a (m₀ + j) ω) (Finset.Icc 1 N) ω := by
  classical
  -- Abbreviation for the shifted sequence.
  set b : ℕ → Ω → ℝ := fun j ω => a (m₀ + j) ω with hb_def
  -- Step 1: reindex the block sum via `Icc 1 N`.
  have himage : (Finset.Icc 1 N).image (fun j => m₀ + j) =
      Finset.Icc (m₀ + 1) (m₀ + N) :=
    Finset.image_add_left_Icc 1 N m₀
  have hinj : Set.InjOn (fun j : ℕ => m₀ + j) (Finset.Icc 1 N : Set ℕ) := by
    intro i _ j _ hij
    exact Nat.add_left_cancel hij
  -- Pointwise reindex identity.
  have hreindex : ∀ (x : ℝ),
      ∑ k ∈ Finset.Icc (m₀ + 1) (m₀ + N), a k ω * x ^ k =
        ∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ (m₀ + j) := by
    intro x
    have := Finset.sum_image (s := Finset.Icc 1 N)
      (g := fun j : ℕ => m₀ + j)
      (f := fun k => a k ω * x ^ k) hinj
    -- this: ∑ x ∈ (Icc 1 N).image (m₀ + ·), (fun k => a k ω * x^k) x
    --       = ∑ x ∈ Icc 1 N, (fun k => a k ω * x^k) (m₀ + x)
    rw [himage] at this
    exact this
  -- Factor x^{m₀}: `∑_j a (m₀+j) ω · x^(m₀+j) = x^{m₀} · ∑_j a (m₀+j) ω · x^j`.
  have hfactor : ∀ (x : ℝ),
      ∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ (m₀ + j) =
        x ^ m₀ * ∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ j := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add]; ring
  -- Step 2: pointwise bound at each `x ∈ [-1, 1]`.
  have hpt : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |∑ k ∈ Finset.Icc (m₀ + 1) (m₀ + N), a k ω * x ^ k| ≤
        polynomialSupBlock b (Finset.Icc 1 N) ω := by
    intro x hx
    have habsx : |x| ≤ 1 := by
      rcases hx with ⟨hx1, hx2⟩; rw [abs_le]; exact ⟨hx1, hx2⟩
    have hxm_le : |x ^ m₀| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) habsx
    have hxm_nn : 0 ≤ |x ^ m₀| := abs_nonneg _
    -- Rewrite via reindex + factorization.
    rw [hreindex x, hfactor x]
    rw [abs_mul]
    -- Inner |∑ j ∈ Icc 1 N, a (m₀+j) ω · x^j| ≤ polynomialSupBlock b (Icc 1 N) ω.
    have hinner_le : |∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ j| ≤
        polynomialSupBlock b (Finset.Icc 1 N) ω := by
      unfold polynomialSupBlock
      haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
      have hbdd : BddAbove (Set.range fun y =>
          ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
            |∑ k ∈ Finset.Icc 1 N, b k ω * y ^ k|) := by
        refine ⟨∑ k ∈ Finset.Icc 1 N, |b k ω|, ?_⟩
        rintro _ ⟨y, rfl⟩
        by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
        · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
          exact ciSup_le fun _ =>
            polynomialSupBlock_abs_le_sum_abs b (Finset.Icc 1 N) ω hy
        · have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 N, b k ω * y ^ k|) ≤ 0 := by
            have : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) =>
                |∑ k ∈ Finset.Icc 1 N, b k ω * y ^ k|) = ∅ :=
              Set.range_eq_empty_iff.mpr ⟨hy⟩
            simp [iSup, this]
          exact this.trans (Finset.sum_nonneg (fun k _ => abs_nonneg _))
      -- `b k ω = a (m₀ + k) ω` definitionally, so the two sums agree.
      have heq : |∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ j| =
          |∑ k ∈ Finset.Icc 1 N, b k ω * x ^ k| := rfl
      rw [heq]
      calc |∑ k ∈ Finset.Icc 1 N, b k ω * x ^ k|
          = ⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 N, b k ω * x ^ k| := (ciSup_const).symm
        _ ≤ ⨆ y, ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1),
              |∑ k ∈ Finset.Icc 1 N, b k ω * y ^ k| := le_ciSup hbdd x
    have hinner_nn : 0 ≤ |∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ j| :=
      abs_nonneg _
    -- |x^{m₀}| * |inner| ≤ 1 * |inner| ≤ polynomialSupBlock b (Icc 1 N) ω.
    calc |x ^ m₀| * |∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ j|
        ≤ 1 * |∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ j| :=
          mul_le_mul_of_nonneg_right hxm_le hinner_nn
      _ = |∑ j ∈ Finset.Icc 1 N, a (m₀ + j) ω * x ^ j| := one_mul _
      _ ≤ polynomialSupBlock b (Finset.Icc 1 N) ω := hinner_le
  -- Step 3: pass to the outer sup.
  unfold polynomialSupBlock
  refine ciSup_le fun x => ?_
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · haveI : Nonempty (x ∈ Set.Icc (-1 : ℝ) 1) := ⟨hx⟩
    exact ciSup_le fun _ => hpt x hx
  · have hempty : (Set.range fun (_ : x ∈ Set.Icc (-1 : ℝ) 1) =>
        |∑ k ∈ Finset.Icc (m₀ + 1) (m₀ + N), a k ω * x ^ k|) = ∅ :=
      Set.range_eq_empty_iff.mpr ⟨hx⟩
    have hle0 : (⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
        |∑ k ∈ Finset.Icc (m₀ + 1) (m₀ + N), a k ω * x ^ k|) ≤ 0 := by
      simp [iSup, hempty]
    have hRHS_nn : 0 ≤ polynomialSupBlock b (Finset.Icc 1 N) ω :=
      polynomialSupBlock_nonneg b _ ω
    show (⨆ (_ : x ∈ Set.Icc (-1 : ℝ) 1),
        |∑ k ∈ Finset.Icc (m₀ + 1) (m₀ + N), a k ω * x ^ k|) ≤
        polynomialSupBlock b (Finset.Icc 1 N) ω
    linarith

end Helpers
end Erdos524
