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

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Polynomial

/-!
# Endpoint reparametrization (helper for Erdős 524, Chojecki Theorem 18)

Chojecki's proof of Theorem 18 ("sparse-subsequence lower envelope") opens with
the reparametrization `x = ± e^{-u/n}`, which converts the sup-norm on
`[-1, 1]` of the random polynomial `P_n(ω)(x) = ∑_{k=1}^{n} a_k(ω) x^k` into
a supremum over `u ≥ 0` of two random processes
`Z_n^±(u) := ∑_{k=1}^{n} (±1)^k a_k(ω) e^{-u k / n}`.

This file formalizes the purely analytic content of that step: for any finite
coefficient sequence and any degree `n ≥ 1`,
```
sup_{x ∈ [-1, 1]} |∑ a_k x^k|
  = max (sup_{u ≥ 0} |∑ a_k e^{-u k / n}|)
        (sup_{u ≥ 0} |∑ a_k (-1)^k e^{-u k / n}|).
```

The math is elementary. Three ingredients:

1. **Image**: `u ↦ e^{-u/n}` is a continuous, strictly decreasing bijection
   `[0, ∞) → (0, 1]`.
2. **Continuity + density**: the polynomial `P(x) = ∑ a_k x^k` is continuous,
   hence its sup over `(0, 1]` equals its sup over `[0, 1]` (Mathlib's
   compact-sup theorems).
3. **Symmetry**: `sup_{[-1, 1]} |P| = max(sup_{[-1, 0]} |P|, sup_{[0, 1]} |P|)`,
   and `sup_{[-1, 0]} |P(x)| = sup_{y ∈ [0, 1]} |P(-y)|`, with
   `P(-y) = ∑ a_k (-1)^k y^k`.

Note on conventions. We use the range `Finset.Icc 1 n`, matching the
`randomPoly` definition in `FormalConjectures/ErdosProblems/524.lean`. The
associated `supNorm` is defined with a `⨆ x ∈ Set.Icc (-1) 1` there.
-/

namespace Erdos524
namespace Helpers

open Set Real

section EndpointReparametrization

variable (a : ℕ → ℝ) (n : ℕ)

/-- The one-sided random polynomial evaluated at a real point,
`P(x) = ∑_{k=1}^{n} a_k x^k`. This is a purely deterministic (coefficient-only)
version of `Erdos524.randomPoly`, avoiding the probability-space parameter. -/
noncomputable def poly (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 n, a k * x ^ k

/-- The "right-endpoint" reparametrization process
`Z^+_n(u) := ∑_{k=1}^{n} a_k · e^{-u k / n}`. -/
noncomputable def Zplus (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, a k * Real.exp (-(u * k) / n)

/-- The "left-endpoint" reparametrization process
`Z^-_n(u) := ∑_{k=1}^{n} a_k · (-1)^k · e^{-u k / n}`. -/
noncomputable def Zminus (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, a k * (-1 : ℝ) ^ k * Real.exp (-(u * k) / n)

/-- Polynomial continuity: `P` is continuous on `ℝ`. -/
theorem poly_continuous : Continuous (poly a n) := by
  unfold poly
  refine continuous_finset_sum _ (fun k _ => ?_)
  exact continuous_const.mul (continuous_id.pow k)

/-- `|P|` is continuous. -/
theorem abs_poly_continuous : Continuous (fun x => |poly a n x|) :=
  (poly_continuous a n).abs

/-- Image of `[0, ∞)` under `u ↦ e^{-u/n}` is `(0, 1]`, for `n ≥ 1`. -/
theorem image_exp_neg_div_n (hn : 1 ≤ n) :
    (fun u : ℝ => Real.exp (-u / n)) '' (Set.Ici (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨u, hu, rfl⟩
    have hu0 : 0 ≤ u := hu
    refine ⟨Real.exp_pos _, ?_⟩
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact le_of_lt hnpos
  · rintro y ⟨hypos, hyle⟩
    refine ⟨-(n : ℝ) * Real.log y, ?_, ?_⟩
    · show (0 : ℝ) ≤ -(n : ℝ) * Real.log y
      have hly : Real.log y ≤ 0 := Real.log_nonpos (le_of_lt hypos) hyle
      have hnn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
      nlinarith
    · show Real.exp (-(-(n : ℝ) * Real.log y) / n) = y
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have heq : -(-(n : ℝ) * Real.log y) / n = Real.log y := by field_simp
      rw [heq]
      exact Real.exp_log hypos

/-- Key exponent identity: `exp(-(u*k)/n) = exp(-u/n)^k`. -/
theorem exp_neg_div_pow (u : ℝ) (k : ℕ) (hn : 1 ≤ n) :
    Real.exp (-(u * (k : ℝ)) / n) = Real.exp (-u / n) ^ k := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp

/-- Link: `Z^+(u) = P(e^{-u/n})`. Uses `exp(-u*k/n) = (exp(-u/n))^k`. -/
theorem Zplus_eq_poly_exp (u : ℝ) (hn : 1 ≤ n) :
    Zplus a n u = poly a n (Real.exp (-u / n)) := by
  unfold Zplus poly
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [exp_neg_div_pow n u k hn]

/-- Link: `Z^-(u) = P(-e^{-u/n})`. -/
theorem Zminus_eq_poly_neg_exp (u : ℝ) (hn : 1 ≤ n) :
    Zminus a n u = poly a n (-(Real.exp (-u / n))) := by
  unfold Zminus poly
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [exp_neg_div_pow n u k hn, neg_pow]
  ring

/-- Value at `0`: `P(0) = 0` since the sum starts at `k = 1`. -/
theorem poly_at_zero : poly a n 0 = 0 := by
  unfold poly
  apply Finset.sum_eq_zero
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have : (0 : ℝ) ^ k = 0 := zero_pow (Nat.one_le_iff_ne_zero.mp hk1)
  rw [this]; ring

/-! ### Boundedness helpers

`|P|` is continuous, hence bounded on any compact set. We package this into
small helper lemmas that provide the `BddAbove` side-conditions required by
Mathlib's conditional-sup API (`csSup_image`, `csSup_union`, etc.). -/

/-- `|P|` is bounded above on any closed interval `[c, d]`. -/
private theorem bddAbove_abs_poly_image_Icc (c d : ℝ) :
    BddAbove ((fun x => |poly a n x|) '' Set.Icc c d) :=
  isCompact_Icc.bddAbove_image (abs_poly_continuous a n).continuousOn

/-- `|P(-·)|` is bounded above on any closed interval `[c, d]`. -/
private theorem bddAbove_abs_poly_neg_image_Icc (c d : ℝ) :
    BddAbove ((fun x => |poly a n (-x)|) '' Set.Icc c d) := by
  have hcont : Continuous (fun x => |poly a n (-x)|) :=
    (abs_poly_continuous a n).comp continuous_neg
  exact isCompact_Icc.bddAbove_image hcont.continuousOn

/-- `|P|` is bounded above on `Ioc c d ⊂ Icc c d`. -/
private theorem bddAbove_abs_poly_image_Ioc (c d : ℝ) :
    BddAbove ((fun x => |poly a n x|) '' Set.Ioc c d) :=
  (bddAbove_abs_poly_image_Icc a n c d).mono (Set.image_mono Set.Ioc_subset_Icc_self)

/-- `|P(-·)|` is bounded above on `Ioc c d ⊂ Icc c d`. -/
private theorem bddAbove_abs_poly_neg_image_Ioc (c d : ℝ) :
    BddAbove ((fun x => |poly a n (-x)|) '' Set.Ioc c d) :=
  (bddAbove_abs_poly_neg_image_Icc a n c d).mono
    (Set.image_mono Set.Ioc_subset_Icc_self)

/-- The range of `|Z^+|` on `Ici 0` equals `|P|` on `Ioc 0 1`, hence bounded. -/
private theorem bddAbove_abs_Zplus_image_Ici (hn : 1 ≤ n) :
    BddAbove ((fun u => |Zplus a n u|) '' Set.Ici (0 : ℝ)) := by
  obtain ⟨M, hM⟩ := bddAbove_abs_poly_image_Ioc a n 0 1
  refine ⟨M, ?_⟩
  rintro v ⟨u, hu, rfl⟩
  apply hM
  refine ⟨Real.exp (-u / n), ?_, ?_⟩
  · have himg := image_exp_neg_div_n n hn
    have : Real.exp (-u / n) ∈ Set.Ioc (0 : ℝ) 1 := by
      rw [← himg]
      exact ⟨u, hu, rfl⟩
    exact this
  · show |poly a n (Real.exp (-u / n))| = |Zplus a n u|
    rw [Zplus_eq_poly_exp a n u hn]

/-- Mirror: range of `|Z^-|` on `Ici 0` equals `|P(-·)|` on `Ioc 0 1`. -/
private theorem bddAbove_abs_Zminus_image_Ici (hn : 1 ≤ n) :
    BddAbove ((fun u => |Zminus a n u|) '' Set.Ici (0 : ℝ)) := by
  obtain ⟨M, hM⟩ := bddAbove_abs_poly_neg_image_Ioc a n 0 1
  refine ⟨M, ?_⟩
  rintro v ⟨u, hu, rfl⟩
  apply hM
  refine ⟨Real.exp (-u / n), ?_, ?_⟩
  · have himg := image_exp_neg_div_n n hn
    have : Real.exp (-u / n) ∈ Set.Ioc (0 : ℝ) 1 := by
      rw [← himg]
      exact ⟨u, hu, rfl⟩
    exact this
  · show |poly a n (-(Real.exp (-u / n)))| = |Zminus a n u|
    rw [Zminus_eq_poly_neg_exp a n u hn]

/-! ### Translation between `⨆ x ∈ s, f x` and `sSup (f '' s)`

Mathlib provides `csSup_image` (in `ConditionallyCompleteLattice.Indexed`) for
this translation. We specialise it to our nonneg-continuous situation where
the side condition `sSup ∅ ≤ ⨆ i : s, f i` is automatic (in ℝ, `sSup ∅ = 0`,
and `|P|` is nonneg, so any nonempty bi-iSup is ≥ 0). -/

/-- Common lemma: convert `⨆ x ∈ s, g x` into `sSup (g '' s)` when `g` is
bounded above on `s` and `s` is nonempty, using `csSup_image`.

The two `BddAbove` facts (on the range over subtype vs the image) are
equivalent via `Set.image_eq_range`. -/
private theorem biSup_eq_sSup_image_of_bddAbove {g : ℝ → ℝ} {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddAbove (g '' s)) (hnonneg : ∀ x ∈ s, 0 ≤ g x) :
    (⨆ x ∈ s, g x) = sSup (g '' s) := by
  have hbdd' : BddAbove (Set.range fun i : s => g i) := by
    rw [show (Set.range fun i : s => g i) = g '' s from (Set.image_eq_range g s).symm]
    exact hbdd
  have hne_sub : Nonempty s := hne.to_subtype
  have hne' : sSup (∅ : Set ℝ) ≤ ⨆ i : s, g i := by
    rw [Real.sSup_empty]
    obtain ⟨x, hx⟩ := hne
    exact le_ciSup_of_le hbdd' ⟨x, hx⟩ (hnonneg x hx)
  exact (csSup_image hne hbdd' hne').symm

private theorem biSup_Icc_abs_poly_eq (c d : ℝ) (hcd : c ≤ d) :
    (⨆ x ∈ Set.Icc c d, |poly a n x|)
      = sSup ((fun x => |poly a n x|) '' Set.Icc c d) :=
  biSup_eq_sSup_image_of_bddAbove (Set.nonempty_Icc.mpr hcd)
    (bddAbove_abs_poly_image_Icc a n c d) (fun _ _ => abs_nonneg _)

private theorem biSup_Ioc_abs_poly_eq (c d : ℝ) (hcd : c < d) :
    (⨆ x ∈ Set.Ioc c d, |poly a n x|)
      = sSup ((fun x => |poly a n x|) '' Set.Ioc c d) :=
  biSup_eq_sSup_image_of_bddAbove (Set.nonempty_Ioc.mpr hcd)
    (bddAbove_abs_poly_image_Ioc a n c d) (fun _ _ => abs_nonneg _)

private theorem biSup_Ioc_abs_poly_neg_eq (c d : ℝ) (hcd : c < d) :
    (⨆ x ∈ Set.Ioc c d, |poly a n (-x)|)
      = sSup ((fun x => |poly a n (-x)|) '' Set.Ioc c d) :=
  biSup_eq_sSup_image_of_bddAbove (Set.nonempty_Ioc.mpr hcd)
    (bddAbove_abs_poly_neg_image_Ioc a n c d) (fun _ _ => abs_nonneg _)

private theorem biSup_Icc_abs_poly_neg_eq (c d : ℝ) (hcd : c ≤ d) :
    (⨆ x ∈ Set.Icc c d, |poly a n (-x)|)
      = sSup ((fun x => |poly a n (-x)|) '' Set.Icc c d) :=
  biSup_eq_sSup_image_of_bddAbove (Set.nonempty_Icc.mpr hcd)
    (bddAbove_abs_poly_neg_image_Icc a n c d) (fun _ _ => abs_nonneg _)

private theorem biSup_Ici_abs_Zplus_eq (hn : 1 ≤ n) :
    (⨆ u ∈ Set.Ici (0 : ℝ), |Zplus a n u|)
      = sSup ((fun u => |Zplus a n u|) '' Set.Ici (0 : ℝ)) :=
  biSup_eq_sSup_image_of_bddAbove ⟨0, Set.left_mem_Ici⟩
    (bddAbove_abs_Zplus_image_Ici a n hn) (fun _ _ => abs_nonneg _)

private theorem biSup_Ici_abs_Zminus_eq (hn : 1 ≤ n) :
    (⨆ u ∈ Set.Ici (0 : ℝ), |Zminus a n u|)
      = sSup ((fun u => |Zminus a n u|) '' Set.Ici (0 : ℝ)) :=
  biSup_eq_sSup_image_of_bddAbove ⟨0, Set.left_mem_Ici⟩
    (bddAbove_abs_Zminus_image_Ici a n hn) (fun _ _ => abs_nonneg _)

/-! ### The six main lemmas -/

/-- Splitting: `sup over [-1,1] = max (sup over [-1,0]) (sup over [0,1])`.
Reduces to `csSup_union` applied to `Icc (-1) 0 ∪ Icc 0 1 = Icc (-1) 1`. -/
theorem sup_Icc_split :
    (⨆ x ∈ Set.Icc (-1 : ℝ) 1, |poly a n x|)
      = max (⨆ x ∈ Set.Icc (-1 : ℝ) 0, |poly a n x|)
            (⨆ x ∈ Set.Icc (0 : ℝ) 1, |poly a n x|) := by
  rw [biSup_Icc_abs_poly_eq a n (-1) 1 (by norm_num),
      biSup_Icc_abs_poly_eq a n (-1) 0 (by norm_num),
      biSup_Icc_abs_poly_eq a n 0 1 (by norm_num)]
  have hunion : Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 0 ∪ Set.Icc 0 1 :=
    (Set.Icc_union_Icc_eq_Icc (by norm_num : (-1 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) ≤ 1)).symm
  rw [hunion, Set.image_union]
  exact csSup_union
    (bddAbove_abs_poly_image_Icc a n (-1) 0)
    ((Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 0)).image _)
    (bddAbove_abs_poly_image_Icc a n 0 1)
    ((Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _)

/-- Symmetry: `sup_{[-1, 0]} |P(x)| = sup_{[0, 1]} |P(-y)|`. -/
theorem sup_Icc_neg_eq :
    (⨆ x ∈ Set.Icc (-1 : ℝ) 0, |poly a n x|)
      = ⨆ y ∈ Set.Icc (0 : ℝ) 1, |poly a n (-y)| := by
  rw [biSup_Icc_abs_poly_eq a n (-1) 0 (by norm_num),
      biSup_Icc_abs_poly_neg_eq a n 0 1 (by norm_num)]
  congr 1
  -- Show (fun x => |poly a n x|) '' Icc (-1) 0 = (fun y => |poly a n (-y)|) '' Icc 0 1
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨-x, ?_, ?_⟩
    · exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
    · simp [neg_neg]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-y, ?_, ?_⟩
    · exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    · rfl

/-- The analytic crux: `sup over Ioc 0 1 = sup over Icc 0 1`. -/
theorem sup_Ioc_eq_sup_Icc_of_poly :
    (⨆ x ∈ Set.Ioc (0 : ℝ) 1, |poly a n x|)
      = ⨆ x ∈ Set.Icc (0 : ℝ) 1, |poly a n x| := by
  rw [biSup_Ioc_abs_poly_eq a n 0 1 (by norm_num),
      biSup_Icc_abs_poly_eq a n 0 1 (by norm_num)]
  -- `Icc 0 1 = insert 0 (Ioc 0 1)`, so image becomes {|P 0|} ∪ (|P| '' Ioc 0 1).
  have hsplit : Set.Icc (0 : ℝ) 1 = insert 0 (Set.Ioc 0 1) := by
    ext x
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · left; exact h.symm
      · right; exact ⟨h, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨le_refl _, by norm_num⟩
      · exact ⟨le_of_lt h1, h2⟩
  rw [hsplit, Set.image_insert_eq]
  have habs0 : |poly a n 0| = 0 := by rw [poly_at_zero]; simp
  rw [habs0]
  -- Now show sSup (insert 0 S) = sSup S when S is nonempty, bounded above, and 0 is a lower bound
  have hne : ((fun x => |poly a n x|) '' Set.Ioc (0 : ℝ) 1).Nonempty := by
    refine ⟨|poly a n 1|, 1, ?_, rfl⟩
    exact ⟨by norm_num, le_refl _⟩
  have hbdd : BddAbove ((fun x => |poly a n x|) '' Set.Ioc (0 : ℝ) 1) :=
    bddAbove_abs_poly_image_Ioc a n 0 1
  -- sSup (insert 0 S) = sSup ({0} ∪ S) = max 0 (sSup S) = sSup S
  have h0_le : 0 ≤ sSup ((fun x => |poly a n x|) '' Set.Ioc (0 : ℝ) 1) := by
    obtain ⟨v, hv⟩ := hne
    have : v ≤ sSup ((fun x => |poly a n x|) '' Set.Ioc (0 : ℝ) 1) :=
      le_csSup hbdd hv
    obtain ⟨x, _, rfl⟩ := hv
    linarith [abs_nonneg (poly a n x)]
  rw [Set.insert_eq, csSup_union
      (by exact ⟨0, by rintro _ rfl; rfl⟩ : BddAbove ({0} : Set ℝ))
      (Set.singleton_nonempty _) hbdd hne]
  rw [show sSup ({0} : Set ℝ) = 0 from csSup_singleton _]
  exact (max_eq_right h0_le).symm

/-- Mirror: `sup over Ioc 0 1` of `|P(-y)|` equals sup over `Icc 0 1` of `|P(-y)|`. -/
theorem sup_Ioc_eq_sup_Icc_of_poly_neg :
    (⨆ x ∈ Set.Ioc (0 : ℝ) 1, |poly a n (-x)|)
      = ⨆ x ∈ Set.Icc (0 : ℝ) 1, |poly a n (-x)| := by
  rw [biSup_Ioc_abs_poly_neg_eq a n 0 1 (by norm_num),
      biSup_Icc_abs_poly_neg_eq a n 0 1 (by norm_num)]
  have hsplit : Set.Icc (0 : ℝ) 1 = insert 0 (Set.Ioc 0 1) := by
    ext x
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · left; exact h.symm
      · right; exact ⟨h, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨le_refl _, by norm_num⟩
      · exact ⟨le_of_lt h1, h2⟩
  rw [hsplit, Set.image_insert_eq]
  have habs0 : |poly a n (-0)| = 0 := by rw [neg_zero, poly_at_zero]; simp
  rw [habs0]
  have hne : ((fun x => |poly a n (-x)|) '' Set.Ioc (0 : ℝ) 1).Nonempty := by
    refine ⟨|poly a n (-1)|, 1, ?_, rfl⟩
    exact ⟨by norm_num, le_refl _⟩
  have hbdd : BddAbove ((fun x => |poly a n (-x)|) '' Set.Ioc (0 : ℝ) 1) :=
    bddAbove_abs_poly_neg_image_Ioc a n 0 1
  have h0_le : 0 ≤ sSup ((fun x => |poly a n (-x)|) '' Set.Ioc (0 : ℝ) 1) := by
    obtain ⟨v, hv⟩ := hne
    have : v ≤ sSup ((fun x => |poly a n (-x)|) '' Set.Ioc (0 : ℝ) 1) :=
      le_csSup hbdd hv
    obtain ⟨x, _, rfl⟩ := hv
    linarith [abs_nonneg (poly a n (-x))]
  rw [Set.insert_eq, csSup_union
      (by exact ⟨0, by rintro _ rfl; rfl⟩ : BddAbove ({0} : Set ℝ))
      (Set.singleton_nonempty _) hbdd hne]
  rw [show sSup ({0} : Set ℝ) = 0 from csSup_singleton _]
  exact (max_eq_right h0_le).symm

/-- Reindexing: `⨆ u ∈ Ici 0, |Z^+(u)| = ⨆ x ∈ Ioc 0 1, |P(x)|`. -/
theorem sup_Zplus_eq_sup_poly_Ioc (hn : 1 ≤ n) :
    (⨆ u ∈ Set.Ici (0 : ℝ), |Zplus a n u|)
      = ⨆ x ∈ Set.Ioc (0 : ℝ) 1, |poly a n x| := by
  rw [biSup_Ici_abs_Zplus_eq a n hn,
      biSup_Ioc_abs_poly_eq a n 0 1 (by norm_num)]
  -- Show: (|Zplus| '' Ici 0) = (|poly| '' Ioc 0 1)
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Real.exp (-u / n), ?_, ?_⟩
    · have himg := image_exp_neg_div_n n hn
      rw [← himg]; exact ⟨u, hu, rfl⟩
    · show |poly a n (Real.exp (-u / n))| = |Zplus a n u|
      rw [Zplus_eq_poly_exp a n u hn]
  · rintro ⟨x, hx, rfl⟩
    -- hx : x ∈ Ioc 0 1, so x ∈ (exp(-·/n) '' Ici 0)
    have himg := image_exp_neg_div_n n hn
    have : x ∈ (fun u : ℝ => Real.exp (-u / n)) '' Set.Ici (0 : ℝ) := by
      rw [himg]; exact hx
    obtain ⟨u, hu, heq⟩ := this
    refine ⟨u, hu, ?_⟩
    show |Zplus a n u| = |poly a n x|
    rw [Zplus_eq_poly_exp a n u hn]
    have heq' : Real.exp (-u / n) = x := heq
    rw [heq']

/-- Mirror reindexing: `⨆ u ∈ Ici 0, |Z^-(u)| = ⨆ x ∈ Ioc 0 1, |P(-x)|`. -/
theorem sup_Zminus_eq_sup_poly_neg_Ioc (hn : 1 ≤ n) :
    (⨆ u ∈ Set.Ici (0 : ℝ), |Zminus a n u|)
      = ⨆ x ∈ Set.Ioc (0 : ℝ) 1, |poly a n (-x)| := by
  rw [biSup_Ici_abs_Zminus_eq a n hn,
      biSup_Ioc_abs_poly_neg_eq a n 0 1 (by norm_num)]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Real.exp (-u / n), ?_, ?_⟩
    · have himg := image_exp_neg_div_n n hn
      rw [← himg]; exact ⟨u, hu, rfl⟩
    · show |poly a n (-Real.exp (-u / n))| = |Zminus a n u|
      rw [Zminus_eq_poly_neg_exp a n u hn]
  · rintro ⟨x, hx, rfl⟩
    have himg := image_exp_neg_div_n n hn
    have : x ∈ (fun u : ℝ => Real.exp (-u / n)) '' Set.Ici (0 : ℝ) := by
      rw [himg]; exact hx
    obtain ⟨u, hu, heq⟩ := this
    refine ⟨u, hu, ?_⟩
    show |Zminus a n u| = |poly a n (-x)|
    rw [Zminus_eq_poly_neg_exp a n u hn]
    have heq' : Real.exp (-u / n) = x := heq
    rw [heq']

/-- The **endpoint reparametrization** lemma (Chojecki, Theorem 18). For any
coefficient sequence `a : ℕ → ℝ` and any `n ≥ 1`,
`sup_{x ∈ [-1, 1]} |∑_{k=1}^n a_k x^k|
  = max (sup_{u ≥ 0} |Z^+_n(u)|) (sup_{u ≥ 0} |Z^-_n(u)|)`. -/
theorem endpoint_reparametrization (hn : 1 ≤ n) :
    (⨆ x ∈ Set.Icc (-1 : ℝ) 1, |poly a n x|)
      = max (⨆ u ∈ Set.Ici (0 : ℝ), |Zplus a n u|)
            (⨆ u ∈ Set.Ici (0 : ℝ), |Zminus a n u|) := by
  rw [sup_Zplus_eq_sup_poly_Ioc a n hn, sup_Zminus_eq_sup_poly_neg_Ioc a n hn,
      sup_Ioc_eq_sup_Icc_of_poly a n, sup_Ioc_eq_sup_Icc_of_poly_neg a n,
      sup_Icc_split a n, sup_Icc_neg_eq a n, max_comm]

end EndpointReparametrization

end Helpers
end Erdos524
