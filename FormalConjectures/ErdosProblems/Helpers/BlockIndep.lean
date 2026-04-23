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

end Helpers
end Erdos524
