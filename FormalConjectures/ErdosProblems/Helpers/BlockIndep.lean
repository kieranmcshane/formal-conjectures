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

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Kernel.IndepFun
import FormalConjectures.ErdosProblems.Helpers.PolynomialSupBlock
import FormalConjectures.ErdosProblems.Helpers.IndepSetBridge

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

/-!
# Independence of disjoint-block sums (helper for Erdős 524)

If `(a k : Ω → ℝ)` are mutually independent measurable random variables and
`(I k : Finset ℕ)` is a pairwise-disjoint family of finset blocks, then the
block sums `S k ω := ∑ j ∈ I k, a j ω` are mutually independent.

The proof reduces `iIndepFun` of the block sums to the measure factorisation
criterion `iIndepFun_iff_measure_inter_preimage_eq_mul`, then inducts on the
finite index set. The inductive step is powered by the two-block independence
lemma `ProbabilityTheory.iIndepFun.indepFun_finset`, applied to the separating
pair `(I k₀, t.biUnion I)`, which is disjoint because the blocks are pairwise
disjoint.
-/

namespace Erdos524
namespace Helpers

open MeasureTheory ProbabilityTheory Finset
open scoped Topology

section BlockSums

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]

/-- For a measurable family `a : ℕ → Ω → ℝ` and a finite index block `J`,
the block sum `ω ↦ ∑ j ∈ J, a j ω` is measurable. -/
lemma measurable_blockSum (a : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (a k))
    (J : Finset ℕ) : Measurable (fun ω => ∑ j ∈ J, a j ω) :=
  Finset.measurable_sum J (fun j _ => hmeas j)

/-- **Main result: independence of disjoint-block sums.**
If `(a k)` are mutually independent measurable random variables and `I` is a
pairwise-disjoint family of finite index blocks, then the block sums
`S k ω := ∑ j ∈ I k, a j ω` are mutually independent. -/
theorem iIndepFun_block_sums
    (a : ℕ → Ω → ℝ)
    (ha : ProbabilityTheory.iIndepFun a μ)
    (hmeas : ∀ k, Measurable (a k))
    (I : ℕ → Finset ℕ) (hI : Pairwise (fun i j => Disjoint (I i) (I j))) :
    ProbabilityTheory.iIndepFun (fun k ω => ∑ j ∈ I k, a j ω) μ := by
  classical
  -- Abbreviate the block-sum random variable.
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ I k, a j ω with hS_def
  have hS_meas : ∀ k, Measurable (S k) :=
    fun k => measurable_blockSum a hmeas (I k)
  -- We use the measure-factorisation characterisation and induct on `s`.
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s E hE
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert k₀ t hk₀ ih =>
      -- Blocks `I k₀` and `t.biUnion I` are disjoint thanks to pairwise
      -- disjointness of `I`.
      have hdisj : Disjoint (I k₀) (t.biUnion I) := by
        rw [Finset.disjoint_biUnion_right]
        intro k hk
        have hk_ne : k₀ ≠ k := fun h => hk₀ (h ▸ hk)
        exact hI hk_ne
      -- Tuple-level 2-block independence from `iIndepFun.indepFun_finset`.
      have htuple :
          IndepFun (fun ω (j : ↥(I k₀)) => a (j : ℕ) ω)
                   (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω) μ :=
        ha.indepFun_finset (I k₀) (t.biUnion I) hdisj hmeas
      -- `F` sums a `(I k₀)`-indexed tuple.
      let F : (↥(I k₀) → ℝ) → ℝ := fun x => ∑ j ∈ (I k₀).attach, x j
      have hF_meas : Measurable F := by
        refine Finset.measurable_sum _ (fun j _ => ?_)
        exact measurable_pi_apply j
      -- For each `k : ℕ`, `restrictSum k` picks out the `I k` part of a
      -- `t.biUnion I`-indexed tuple (using `0` for components outside `I k`).
      let restrictSum : ℕ → (↥(t.biUnion I) → ℝ) → ℝ :=
        fun k x =>
          ∑ j ∈ (t.biUnion I).attach, if (j : ℕ) ∈ I k then x j else 0
      have hrestrictSum_meas : ∀ k, Measurable (restrictSum k) := by
        intro k
        refine Finset.measurable_sum _ (fun j _ => ?_)
        by_cases hj : (j : ℕ) ∈ I k
        · simp only [hj, if_true]; exact measurable_pi_apply j
        · simp only [hj, if_false]; exact measurable_const
      -- Package remaining block sums into a `↥t`-indexed tuple.
      let G : (↥(t.biUnion I) → ℝ) → (↥t → ℝ) :=
        fun x k => restrictSum (k : ℕ) x
      have hG_meas : Measurable G := by
        refine measurable_pi_iff.mpr ?_
        intro k
        exact hrestrictSum_meas (k : ℕ)
      -- `S k₀ = F ∘ tuple_{I k₀}`.
      have hS₀_eq : S k₀ = F ∘ (fun ω (j : ↥(I k₀)) => a (j : ℕ) ω) := by
        funext ω
        simp only [Function.comp, F, S]
        exact (Finset.sum_attach (I k₀) (fun j => a j ω)).symm
      -- For `k ∈ t`, `S k = restrictSum k ∘ tuple_{t.biUnion I}`.
      have hSk_eq : ∀ k ∈ t, S k =
          (restrictSum k) ∘ (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω) := by
        intro k hk
        funext ω
        simp only [Function.comp, restrictSum, S]
        have hsub : I k ⊆ t.biUnion I := Finset.subset_biUnion_of_mem I hk
        -- Rewrite RHS from attach sum to sum over `t.biUnion I`.
        rw [Finset.sum_attach (t.biUnion I)
          (fun j => if j ∈ I k then a j ω else 0)]
        -- `∑ j ∈ t.biUnion I, if j ∈ I k then a j ω else 0
        --  = ∑ j ∈ (t.biUnion I) with j ∈ I k, a j ω`.
        rw [← Finset.sum_filter]
        -- `(t.biUnion I) with j ∈ I k = I k` since `I k ⊆ t.biUnion I`.
        have hfilter : ((t.biUnion I).filter (fun j => j ∈ I k)) = I k := by
          ext j
          simp only [Finset.mem_filter]
          refine ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
        rw [hfilter]
      -- Independence of `S k₀` and `G ∘ tuple_{t.biUnion I}`.
      have hindep_new :
          IndepFun (S k₀)
            (G ∘ (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω)) μ := by
        have hcomp := htuple.comp hF_meas hG_meas
        rw [hS₀_eq]; exact hcomp
      -- Preimages on the `t`-side.
      have hE_k₀ : MeasurableSet (E k₀) :=
        hE k₀ (Finset.mem_insert_self _ _)
      have hE_t : ∀ k ∈ t, MeasurableSet (E k) :=
        fun k hk => hE k (Finset.mem_insert_of_mem hk)
      let C : Set (↥t → ℝ) := { y | ∀ k : ↥t, y k ∈ E (k : ℕ) }
      have hC_meas : MeasurableSet C := by
        have heq : C = ⋂ k : ↥t, {y : ↥t → ℝ | y k ∈ E (k : ℕ)} := by
          ext y; simp [C]
        rw [heq]
        refine MeasurableSet.iInter (fun k => ?_)
        exact (measurable_pi_apply k) (hE_t (k : ℕ) k.2)
      -- Identify the "remaining" intersection with the preimage of `C`.
      have hB_eq :
          (⋂ k ∈ t, S k ⁻¹' E k)
            = (G ∘ (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω)) ⁻¹' C := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_preimage, Function.comp, C,
          Set.mem_setOf_eq]
        refine ⟨fun h k => ?_, fun h k hk => ?_⟩
        · have hS_eq := hSk_eq (k : ℕ) k.2
          have := h (k : ℕ) k.2
          -- `S k ω ∈ E k` ↔ `G (tuple ω) k ∈ E k`
          have hgoal : G (fun j : ↥(t.biUnion I) => a (j : ℕ) ω) k
              = S (k : ℕ) ω := by
            simp only [G]
            have := congrFun hS_eq ω
            simp only [Function.comp] at this
            exact this.symm
          rw [hgoal]; exact this
        · have hS_eq := hSk_eq k hk
          have := h ⟨k, hk⟩
          have hgoal : S k ω = G (fun j : ↥(t.biUnion I) => a (j : ℕ) ω) ⟨k, hk⟩ := by
            have := congrFun hS_eq ω
            simp only [Function.comp] at this
            exact this
          rw [hgoal]; exact this
      -- Unfold the insert intersection and product.
      have hinter :
          (⋂ k ∈ insert k₀ t, S k ⁻¹' E k)
            = (S k₀ ⁻¹' E k₀) ∩ (⋂ k ∈ t, S k ⁻¹' E k) := by
        rw [Finset.set_biInter_insert]
      rw [hinter, Finset.prod_insert hk₀]
      -- Independence: `μ(A ∩ B) = μ A * μ B`.
      have hprod :
          μ ((S k₀ ⁻¹' E k₀) ∩ (⋂ k ∈ t, S k ⁻¹' E k))
            = μ (S k₀ ⁻¹' E k₀) * μ (⋂ k ∈ t, S k ⁻¹' E k) := by
        rw [hB_eq]
        exact hindep_new.measure_inter_preimage_eq_mul (s := E k₀) (t := C)
          hE_k₀ hC_meas
      rw [hprod]
      -- Apply the induction hypothesis.
      rw [ih (fun k hk => hE k (Finset.mem_insert_of_mem hk))]

end BlockSums

section BlockPolynomialSup

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]

/-- Tuple-indexed polynomial sup norm: for a coefficient tuple `x : J → ℝ`,
`polyTupleSup J x := ⨆_{y ∈ [-1, 1]} |∑_{j ∈ J.attach} x j · y^(j : ℕ)|`. -/
private noncomputable def polyTupleSup (J : Finset ℕ) (x : ↥J → ℝ) : ℝ :=
  ⨆ y ∈ Set.Icc (-1 : ℝ) 1, |∑ j ∈ J.attach, x j * y ^ (j : ℕ)|

/-- Pointwise identity: `polynomialSupBlock a J ω = polyTupleSup J (fun j => a j ω)`. -/
private lemma polynomialSupBlock_eq_polyTupleSup
    (a : ℕ → Ω → ℝ) (J : Finset ℕ) (ω : Ω) :
    polynomialSupBlock a J ω = polyTupleSup J (fun j : ↥J => a (j : ℕ) ω) := by
  unfold polynomialSupBlock polyTupleSup
  have hsum : ∀ y : ℝ,
      (∑ k ∈ J, a k ω * y ^ k)
        = ∑ j ∈ J.attach, (fun j : ↥J => a (j : ℕ) ω) j * y ^ ((j : ↥J) : ℕ) := by
    intro y
    exact (Finset.sum_attach J (fun k => a k ω * y ^ k)).symm
  simp_rw [hsum]

/-- `polyTupleSup J` is measurable as a function of the coefficient tuple.
Same rationals-density argument as `polynomialSupBlock_measurable`. -/
private lemma polyTupleSup_measurable (J : Finset ℕ) :
    Measurable (polyTupleSup J) := by
  classical
  -- Countable dense subset D = ℚ ∩ [-1, 1] in ℝ.
  set D : Set ℝ := (Set.range ((↑) : ℚ → ℝ)) ∩ Set.Icc (-1 : ℝ) 1 with hD_def
  have hD_count : D.Countable :=
    (Set.countable_range _).mono Set.inter_subset_left
  have hD_sub_Icc : D ⊆ Set.Icc (-1 : ℝ) 1 := Set.inter_subset_right
  -- Abbreviation: f y x = |∑ j ∈ J.attach, x j * y^(j : ℕ)|.
  set f : ℝ → (↥J → ℝ) → ℝ :=
    fun y x => |∑ j ∈ J.attach, x j * y ^ (j : ℕ)| with hf_def
  -- Measurability in x, for each y.
  have hf_meas : ∀ y, Measurable (f y) := fun y => by
    refine Measurable.abs ?_
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact (measurable_pi_apply j).mul_const _
  -- Continuity in y, for each x.
  have hf_cont : ∀ x, Continuous (fun y : ℝ => f y x) := fun x => by
    refine Continuous.abs ?_
    exact continuous_finset_sum _
      (fun j _ => continuous_const.mul (continuous_id.pow _))
  -- Pointwise bound: for y ∈ Icc (-1) 1, |∑ j, x j · y^(j:ℕ)| ≤ ∑ j, |x j|.
  have habs_le : ∀ (x : ↥J → ℝ) {y : ℝ}, y ∈ Set.Icc (-1 : ℝ) 1 →
      |∑ j ∈ J.attach, x j * y ^ (j : ℕ)| ≤ ∑ j ∈ J.attach, |x j| := by
    intro x y hy
    have habsy : |y| ≤ 1 := by
      rcases hy with ⟨hy1, hy2⟩; rw [abs_le]; exact ⟨hy1, hy2⟩
    calc |∑ j ∈ J.attach, x j * y ^ (j : ℕ)|
        ≤ ∑ j ∈ J.attach, |x j * y ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ J.attach, |x j| * |y ^ (j : ℕ)| := by
          refine Finset.sum_congr rfl (fun j _ => ?_); exact abs_mul _ _
      _ ≤ ∑ j ∈ J.attach, |x j| * 1 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have hyk : |y ^ (j : ℕ)| ≤ 1 := by
            rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) habsy
          exact mul_le_mul_of_nonneg_left hyk (abs_nonneg _)
      _ = ∑ j ∈ J.attach, |x j| := by simp
  -- BddAbove of outer iSup range for Icc.
  have hbdd_outer_Icc : ∀ x, BddAbove (Set.range fun z =>
      ⨆ (_ : z ∈ Set.Icc (-1 : ℝ) 1), f z x) := fun x => by
    refine ⟨∑ j ∈ J.attach, |x j|, ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
    · haveI : Nonempty (z ∈ Set.Icc (-1 : ℝ) 1) := ⟨hz⟩
      exact ciSup_le fun _ => habs_le x hz
    · have : (⨆ (_ : z ∈ Set.Icc (-1 : ℝ) 1), f z x) ≤ 0 := by
        have : (Set.range fun (_ : z ∈ Set.Icc (-1 : ℝ) 1) => f z x) = ∅ :=
          Set.range_eq_empty_iff.mpr ⟨hz⟩
        simp [iSup, this]
      exact this.trans (Finset.sum_nonneg (fun j _ => abs_nonneg _))
  -- BddAbove of outer iSup range for D.
  have hbdd_outer_D : ∀ x, BddAbove (Set.range fun z =>
      ⨆ (_ : z ∈ D), f z x) := fun x => by
    refine ⟨∑ j ∈ J.attach, |x j|, ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ D
    · haveI : Nonempty (z ∈ D) := ⟨hz⟩
      exact ciSup_le fun _ => habs_le x (hD_sub_Icc hz)
    · have : (⨆ (_ : z ∈ D), f z x) ≤ 0 := by
        have : (Set.range fun (_ : z ∈ D) => f z x) = ∅ :=
          Set.range_eq_empty_iff.mpr ⟨hz⟩
        simp [iSup, this]
      exact this.trans (Finset.sum_nonneg (fun j _ => abs_nonneg _))
  -- Key equality: sup over Icc = sup over D (by density + continuity).
  have hSup_eq : ∀ x, polyTupleSup J x = ⨆ y ∈ D, f y x := by
    intro x
    unfold polyTupleSup
    apply le_antisymm
    · -- LHS (sup over Icc) ≤ RHS (sup over D).
      refine ciSup_le fun y => ?_
      by_cases hy : y ∈ Set.Icc (-1 : ℝ) 1
      · haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy⟩
        refine ciSup_le fun _ => ?_
        have hy_ge : (-1 : ℝ) ≤ y := hy.1
        have hy_le : y ≤ (1 : ℝ) := hy.2
        -- Pick rationals q_n → y with (q_n : ℝ) ∈ [-1, 1].
        have hseq : ∃ q : ℕ → ℚ,
            (∀ n, (-1 : ℝ) ≤ (q n : ℝ) ∧ (q n : ℝ) ≤ 1) ∧
            Filter.Tendsto (fun n => ((q n : ℝ))) Filter.atTop (𝓝 y) := by
          have : ∀ n : ℕ, ∃ q : ℚ, (-1 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1 ∧
              |(q : ℝ) - y| < 1 / (n + 1 : ℝ) := by
            intro n
            have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
            have hle : (max (-1 : ℝ) (y - 1 / (n + 1 : ℝ))) <
                (min (1 : ℝ) (y + 1 / (n + 1 : ℝ))) := by
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
          have : |(q n : ℝ) - y| < 1 / (n + 1 : ℝ) := hq_close n
          have hmono : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
            apply one_div_le_one_div_of_le
            · exact_mod_cast Nat.succ_pos N
            · exact_mod_cast Nat.succ_le_succ hn
          have hbd : 1 / (N + 1 : ℝ) < ε := hN
          rw [Real.dist_eq]
          linarith
        obtain ⟨q, hq_mem, hq_lim⟩ := hseq
        have hqD : ∀ n, (q n : ℝ) ∈ D := fun n =>
          ⟨⟨q n, rfl⟩, hq_mem n⟩
        have hfq_tendsto : Filter.Tendsto (fun n => f (q n : ℝ) x) Filter.atTop
            (𝓝 (f y x)) := ((hf_cont x).tendsto y).comp hq_lim
        have hfq_le : ∀ n, f (q n : ℝ) x ≤ ⨆ z ∈ D, f z x := by
          intro n
          haveI : Nonempty ((q n : ℝ) ∈ D) := ⟨hqD n⟩
          calc f (q n : ℝ) x
              = ⨆ (_ : (q n : ℝ) ∈ D), f (q n : ℝ) x := (ciSup_const).symm
            _ ≤ ⨆ z ∈ D, f z x := le_ciSup (hbdd_outer_D x) _
        exact le_of_tendsto_of_frequently hfq_tendsto (.of_forall hfq_le)
      · have : (⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), f y x) ≤ 0 := by
          have : (Set.range fun (_ : y ∈ Set.Icc (-1 : ℝ) 1) => f y x) = ∅ :=
            Set.range_eq_empty_iff.mpr ⟨hy⟩
          simp [iSup, this]
        refine this.trans ?_
        have h0D : (0 : ℝ) ∈ D := ⟨⟨0, by norm_num⟩, by constructor <;> norm_num⟩
        haveI : Nonempty ((0 : ℝ) ∈ D) := ⟨h0D⟩
        calc (0 : ℝ)
            ≤ f 0 x := abs_nonneg _
          _ = ⨆ (_ : (0 : ℝ) ∈ D), f 0 x := (ciSup_const).symm
          _ ≤ ⨆ z ∈ D, f z x := le_ciSup (hbdd_outer_D x) 0
    · -- RHS ≤ LHS.
      refine ciSup_le fun y => ?_
      by_cases hy : y ∈ D
      · haveI : Nonempty (y ∈ D) := ⟨hy⟩
        refine ciSup_le fun _ => ?_
        have hy_Icc : y ∈ Set.Icc (-1 : ℝ) 1 := hD_sub_Icc hy
        haveI : Nonempty (y ∈ Set.Icc (-1 : ℝ) 1) := ⟨hy_Icc⟩
        calc f y x = ⨆ (_ : y ∈ Set.Icc (-1 : ℝ) 1), f y x := (ciSup_const).symm
          _ ≤ ⨆ z ∈ Set.Icc (-1 : ℝ) 1, f z x := le_ciSup (hbdd_outer_Icc x) y
      · have : (⨆ (_ : y ∈ D), f y x) ≤ 0 := by
          have : (Set.range fun (_ : y ∈ D) => f y x) = ∅ :=
            Set.range_eq_empty_iff.mpr ⟨hy⟩
          simp [iSup, this]
        refine this.trans ?_
        have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
        haveI : Nonempty ((0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1) := ⟨h0⟩
        calc (0 : ℝ)
            ≤ f 0 x := abs_nonneg _
          _ = ⨆ (_ : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1), f 0 x := (ciSup_const).symm
          _ ≤ ⨆ z ∈ Set.Icc (-1 : ℝ) 1, f z x := le_ciSup (hbdd_outer_Icc x) 0
  -- Conclude: polyTupleSup J is a countable biSup of measurable functions.
  have heq : polyTupleSup J = fun x => ⨆ y ∈ D, f y x := by
    funext x; exact hSup_eq x
  rw [heq]
  exact Measurable.biSup D hD_count (fun y _ => hf_meas y)

/-- **Independence of disjoint-block polynomial sups.**
If `(a k)` are mutually independent measurable random variables and `I` is a
pairwise-disjoint family of finite index blocks, then the block polynomial
suprema `ω ↦ polynomialSupBlock a (I k) ω` are mutually independent. -/
theorem iIndepFun_polynomialSupBlock
    (a : ℕ → Ω → ℝ)
    (ha : ProbabilityTheory.iIndepFun a μ)
    (hmeas : ∀ k, Measurable (a k))
    (I : ℕ → Finset ℕ) (hI : Pairwise (fun i j => Disjoint (I i) (I j))) :
    ProbabilityTheory.iIndepFun
      (fun k ω => polynomialSupBlock a (I k) ω) μ := by
  classical
  set S : ℕ → Ω → ℝ := fun k ω => polynomialSupBlock a (I k) ω with hS_def
  have hS_meas : ∀ k, Measurable (S k) :=
    fun k => polynomialSupBlock_measurable a hmeas (I k)
  -- Measure-factorisation characterisation + induction on `s`.
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s E hE
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert k₀ t hk₀ ih =>
      have hdisj : Disjoint (I k₀) (t.biUnion I) := by
        rw [Finset.disjoint_biUnion_right]
        intro k hk
        have hk_ne : k₀ ≠ k := fun h => hk₀ (h ▸ hk)
        exact hI hk_ne
      -- Tuple-level 2-block independence.
      have htuple :
          IndepFun (fun ω (j : ↥(I k₀)) => a (j : ℕ) ω)
                   (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω) μ :=
        ha.indepFun_finset (I k₀) (t.biUnion I) hdisj hmeas
      -- `F` takes a `(I k₀)`-indexed tuple to its polynomial sup.
      let F : (↥(I k₀) → ℝ) → ℝ := polyTupleSup (I k₀)
      have hF_meas : Measurable F := polyTupleSup_measurable (I k₀)
      -- `restrictSup k` computes `polynomialSupBlock` for block `I k` from a
      -- `t.biUnion I`-indexed tuple (by restricting to `I k` with zero padding).
      let restrictSup : ℕ → (↥(t.biUnion I) → ℝ) → ℝ :=
        fun k x => polyTupleSup (I k)
          (fun j : ↥(I k) =>
            if hj : (j : ℕ) ∈ t.biUnion I then x ⟨(j : ℕ), hj⟩ else 0)
      have hrestrictSup_meas : ∀ k, Measurable (restrictSup k) := by
        intro k
        refine (polyTupleSup_measurable (I k)).comp ?_
        refine measurable_pi_iff.mpr ?_
        intro j
        by_cases hj : (j : ℕ) ∈ t.biUnion I
        · simp only [hj, dif_pos]
          exact measurable_pi_apply _
        · simp only [hj, dif_neg, not_false_iff]
          exact measurable_const
      -- Package remaining polynomial sups into a `↥t`-indexed tuple.
      let G : (↥(t.biUnion I) → ℝ) → (↥t → ℝ) :=
        fun x k => restrictSup (k : ℕ) x
      have hG_meas : Measurable G := by
        refine measurable_pi_iff.mpr ?_
        intro k
        exact hrestrictSup_meas (k : ℕ)
      -- `S k₀ = F ∘ tuple_{I k₀}`.
      have hS₀_eq : S k₀ = F ∘ (fun ω (j : ↥(I k₀)) => a (j : ℕ) ω) := by
        funext ω
        simp only [Function.comp, F, S]
        exact polynomialSupBlock_eq_polyTupleSup a (I k₀) ω
      -- For `k ∈ t`, `S k = restrictSup k ∘ tuple_{t.biUnion I}`.
      have hSk_eq : ∀ k ∈ t, S k =
          (restrictSup k) ∘ (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω) := by
        intro k hk
        funext ω
        simp only [Function.comp, restrictSup, S]
        have hsub : I k ⊆ t.biUnion I := Finset.subset_biUnion_of_mem I hk
        -- Rewrite RHS using that every `j ∈ I k` has `(j : ℕ) ∈ t.biUnion I`.
        have hrewrite :
            (fun j : ↥(I k) =>
              if hj : (j : ℕ) ∈ t.biUnion I then
                (fun j' : ↥(t.biUnion I) => a (j' : ℕ) ω) ⟨(j : ℕ), hj⟩
              else 0) =
            (fun j : ↥(I k) => a (j : ℕ) ω) := by
          funext j
          have hj_mem : (j : ℕ) ∈ t.biUnion I := hsub j.2
          simp only [hj_mem, dif_pos]
        rw [hrewrite]
        exact polynomialSupBlock_eq_polyTupleSup a (I k) ω
      -- Independence of `S k₀` and `G ∘ tuple_{t.biUnion I}`.
      have hindep_new :
          IndepFun (S k₀)
            (G ∘ (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω)) μ := by
        have hcomp := htuple.comp hF_meas hG_meas
        rw [hS₀_eq]; exact hcomp
      have hE_k₀ : MeasurableSet (E k₀) :=
        hE k₀ (Finset.mem_insert_self _ _)
      have hE_t : ∀ k ∈ t, MeasurableSet (E k) :=
        fun k hk => hE k (Finset.mem_insert_of_mem hk)
      let C : Set (↥t → ℝ) := { y | ∀ k : ↥t, y k ∈ E (k : ℕ) }
      have hC_meas : MeasurableSet C := by
        have heq : C = ⋂ k : ↥t, {y : ↥t → ℝ | y k ∈ E (k : ℕ)} := by
          ext y; simp [C]
        rw [heq]
        refine MeasurableSet.iInter (fun k => ?_)
        exact (measurable_pi_apply k) (hE_t (k : ℕ) k.2)
      have hB_eq :
          (⋂ k ∈ t, S k ⁻¹' E k)
            = (G ∘ (fun ω (j : ↥(t.biUnion I)) => a (j : ℕ) ω)) ⁻¹' C := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_preimage, Function.comp, C,
          Set.mem_setOf_eq]
        refine ⟨fun h k => ?_, fun h k hk => ?_⟩
        · have hS_eq := hSk_eq (k : ℕ) k.2
          have := h (k : ℕ) k.2
          have hgoal : G (fun j : ↥(t.biUnion I) => a (j : ℕ) ω) k
              = S (k : ℕ) ω := by
            simp only [G]
            have := congrFun hS_eq ω
            simp only [Function.comp] at this
            exact this.symm
          rw [hgoal]; exact this
        · have hS_eq := hSk_eq k hk
          have := h ⟨k, hk⟩
          have hgoal : S k ω = G (fun j : ↥(t.biUnion I) => a (j : ℕ) ω) ⟨k, hk⟩ := by
            have := congrFun hS_eq ω
            simp only [Function.comp] at this
            exact this
          rw [hgoal]; exact this
      have hinter :
          (⋂ k ∈ insert k₀ t, S k ⁻¹' E k)
            = (S k₀ ⁻¹' E k₀) ∩ (⋂ k ∈ t, S k ⁻¹' E k) := by
        rw [Finset.set_biInter_insert]
      rw [hinter, Finset.prod_insert hk₀]
      have hprod :
          μ ((S k₀ ⁻¹' E k₀) ∩ (⋂ k ∈ t, S k ⁻¹' E k))
            = μ (S k₀ ⁻¹' E k₀) * μ (⋂ k ∈ t, S k ⁻¹' E k) := by
        rw [hB_eq]
        exact hindep_new.measure_inter_preimage_eq_mul (s := E k₀) (t := C)
          hE_k₀ hC_meas
      rw [hprod]
      rw [ih (fun k hk => hE k (Finset.mem_insert_of_mem hk))]

/-- **Independence of `polynomialSupBlock` level events across disjoint blocks.**

Given mutually independent measurable random variables `(a k)` and a
pairwise-disjoint family of finite blocks `I : ℕ → Finset ℕ`, the events
`{ω | polynomialSupBlock a (I m) ω ≤ c m}` are mutually independent (as sets).

This is the `iIndepSet`-level companion to `iIndepFun_polynomialSupBlock`; the
caller typically supplies `ha.indep` and `ha.measurable` from an
`IsRademacherSequence` hypothesis. -/
theorem iIndepSet_polynomialSupBlock_events
    (a : ℕ → Ω → ℝ)
    (ha : ProbabilityTheory.iIndepFun a μ)
    (hmeas : ∀ k, Measurable (a k))
    (I : ℕ → Finset ℕ) (hI : Pairwise (fun i j => Disjoint (I i) (I j)))
    (c : ℕ → ℝ) :
    ProbabilityTheory.iIndepSet
      (fun m : ℕ => {ω | polynomialSupBlock a (I m) ω ≤ c m}) μ := by
  have hindep_fun :
      ProbabilityTheory.iIndepFun
        (fun m ω => polynomialSupBlock a (I m) ω) μ :=
    iIndepFun_polynomialSupBlock a ha hmeas I hI
  have hmeas_m : ∀ m, Measurable (fun ω => polynomialSupBlock a (I m) ω) :=
    fun m => polynomialSupBlock_measurable a hmeas (I m)
  have hevent_eq : (fun m : ℕ =>
      {ω | polynomialSupBlock a (I m) ω ≤ c m}) =
      (fun m : ℕ =>
        (fun ω => polynomialSupBlock a (I m) ω) ⁻¹' Set.Iic (c m)) := by
    funext m
    ext ω
    simp [Set.Iic]
  rw [hevent_eq]
  exact iIndepSet_preimage_of_iIndepFun hindep_fun hmeas_m
    (A := fun m => Set.Iic (c m)) (fun _ => measurableSet_Iic)

end BlockPolynomialSup

end Helpers
end Erdos524
