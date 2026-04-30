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

import FormalConjectures.ErdosProblems.Helpers.GaussianBoxBounds
import FormalConjectures.ErdosProblems.Helpers.MVGaussianRotation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Phase 2 Round 6 / Round 9 — Multivariate Gaussian density-at-mode small-ball bound

For an `n × n` symmetric positive-definite real matrix `M`, the multivariate
Gaussian on `n → ℝ` with covariance `M`,
`mvGaussianFromPosDef M = Measure.map (mulVec L) standardMVGaussian`,
where `L = realMatrixSqrt M`, satisfies the Anderson-style density-at-mode
upper bound on a symmetric anisotropic box `∏ᵢ [-εᵢ, εᵢ]`:

  `ℙ[X ∈ B] ≤ (∏ᵢ 2 εᵢ) · (2π)^(-n/2) · (det M)^(-1/2)`.

The proof outline (textbook Anderson):

1.  Density of the MV Gaussian at `x = 0` (the mode) is
    `(2π)^(-n/2) · (det M)^(-1/2)`, since the exponential factor
    `exp(-xᵀ M⁻¹ x / 2)` evaluated at zero is `1`.
2.  For all `x ∈ B`, `xᵀ M⁻¹ x ≥ 0` (since `M⁻¹` is PosDef), so the
    exponential factor is `≤ 1`, hence `p_X(x) ≤ p_X(0)`.
3.  Integrate the pointwise bound over `B`:
    `ℙ[X ∈ B] = ∫_B p_X(x) dx ≤ p_X(0) · vol(B) = p_X(0) · ∏ᵢ 2εᵢ`.

This file:

* Proves the **standard MV Gaussian** anisotropic-box bound (cov = `1`)
  fully, no `sorry`. This is the supporting lemma of Target A.

* Proves the **general PosDef** version (Round 9) by composing change of
  variables, the Jacobian formula, the standard MV uniform density bound,
  and the box volume — all closed with the new `lintegral_fintype_prod_eq_prod`
  Tonelli lemma added in this file (Mathlib gap: ENNReal analogue of
  `MeasureTheory.integral_fintype_prod_eq_prod`).

* Specialises the PosDef version to `M = 1` (provable from the standard
  MV bound — no `sorry`).

The standard MV bound is itself the key input the V1 instance needs for
its `anderson_upper` field on the diagonal-covariance reduction.

## Round 9 contributions (Mathlib-PR-ready)

The Round 9 closure of this file introduced four lemmas that fill genuine
Mathlib gaps:

* `lintegral_fin_nat_prod_eq_prod_aux` — Tonelli for ENNReal integrands
  on `Measure.pi μ` indexed by `Fin n`.
* `lintegral_fintype_prod_eq_prod` — Fintype-indexed counterpart.
* `setLIntegral_fintype_prod_pi_eq_prod` — rectangle-restricted form.
* `pi_withDensity_eq_withDensity_pi` — `Measure.pi` / `withDensity`
  commutation.

These are the ENNReal analogues of `MeasureTheory.integral_fintype_prod_eq_prod`
(which Mathlib provides only for real-valued integrals) and are
independently useful outside this codebase.
-/

namespace Erdos524.Helpers
open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {n : Type*} [Fintype n]

/-! ## Anisotropic box event = product of intervals -/

set_option linter.unusedSectionVars false in
/-- The anisotropic symmetric box `{x | ∀ i, |x i| ≤ ε i}` is exactly the
product of intervals `Set.pi univ (fun i => Set.Icc (-ε i) (ε i))`. -/
theorem anisotropic_box_event_eq_pi (ε : n → ℝ) :
    {x : n → ℝ | ∀ i, |x i| ≤ ε i} =
      Set.pi Set.univ (fun i => Set.Icc (-ε i) (ε i)) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies, abs_le]

/-! ## Anisotropic box probability factorises as a product of 1-D probabilities -/

theorem standardMVGaussian_anisotropic_box_eq_prod (ε : n → ℝ) :
    standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε i} =
      ∏ i, gaussianReal 0 1 (Set.Icc (-ε i) (ε i)) := by
  rw [anisotropic_box_event_eq_pi]
  unfold standardMVGaussian
  exact Measure.pi_pi (fun _ => gaussianReal 0 1) _

/-! ## Each 1-D box probability is finite -/

theorem gaussianReal_Icc_finite (a b : ℝ) :
    gaussianReal 0 1 (Set.Icc a b) ≠ ⊤ := by
  have h_le : gaussianReal 0 1 (Set.Icc a b) ≤ 1 :=
    le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
  exact ne_of_lt (lt_of_le_of_lt h_le ENNReal.one_lt_top)

/-! ## Each 1-D box probability is nonneg as `toReal` -/

theorem gaussianReal_Icc_toReal_nonneg (a b : ℝ) :
    (0 : ℝ) ≤ (gaussianReal 0 1 (Set.Icc a b)).toReal :=
  ENNReal.toReal_nonneg

/-! ## Per-coordinate 1-D bound: `(gaussianReal 0 1 (Icc (-εᵢ) εᵢ)).toReal ≤ 2εᵢ · (√(2π))⁻¹` -/

theorem gaussianReal_Icc_neg_le_aniso (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1 (Set.Icc (-ε) ε)).toReal ≤ 2 * ε * (Real.sqrt (2 * Real.pi))⁻¹ :=
  one_d_box_bound_uniform ε hε

/-! ## Anisotropic Anderson-upper for `standardMVGaussian` (no `sorry`)

Headline theorem of this file in the cov = `1` case: for any anisotropic
symmetric box, the box probability is at most `(∏ᵢ 2εᵢ) · (√(2π))⁻¹^n`. -/

theorem standardMVGaussian_anisotropic_box_density_at_mode_bound
    (ε : n → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    (standardMVGaussian n {x : n → ℝ | ∀ i, |x i| ≤ ε i}).toReal ≤
      (∏ i, 2 * ε i) * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  -- Factor the box probability as a product of 1-D box probabilities.
  rw [standardMVGaussian_anisotropic_box_eq_prod]
  -- toReal of finite product = product of toReal.
  rw [ENNReal.toReal_prod]
  -- Bound each 1-D factor by `2εᵢ · (√(2π))⁻¹`.
  have h_per_factor :
      ∀ i, (gaussianReal 0 1 (Set.Icc (-ε i) (ε i))).toReal ≤
           2 * ε i * (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro i; exact gaussianReal_Icc_neg_le_aniso (ε i) (hε i)
  have h_prod_le :
      ∏ i, (gaussianReal 0 1 (Set.Icc (-ε i) (ε i))).toReal ≤
        ∏ i, (2 * ε i * (Real.sqrt (2 * Real.pi))⁻¹) := by
    apply Finset.prod_le_prod (fun i _ => gaussianReal_Icc_toReal_nonneg _ _)
      (fun i _ => h_per_factor i)
  refine h_prod_le.trans ?_
  -- Split `∏ (2εᵢ · c) = (∏ 2εᵢ) · c^n`.
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-! ## Reciprocal-square-root form: `(√(2π))⁻¹^n` is positive -/

theorem inv_sqrt_two_pi_pow_pos (n : ℕ) :
    0 < (Real.sqrt (2 * Real.pi))⁻¹ ^ n := by
  apply pow_pos
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem inv_sqrt_two_pi_pow_nonneg (n : ℕ) :
    0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ ^ n :=
  le_of_lt (inv_sqrt_two_pi_pow_pos n)

/-! ## Determinant of a PosDef matrix is positive — convenience wrappers -/

theorem sqrt_det_pos_of_posDef [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) : 0 < Real.sqrt M.det :=
  Real.sqrt_pos.mpr hM.det_pos

theorem sqrt_det_nonneg_of_posDef [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) : 0 ≤ Real.sqrt M.det :=
  le_of_lt (sqrt_det_pos_of_posDef hM)

/-! ## Round 9 — Convenience: `c • 1` is PosDef for `c > 0`

A small constructor lemma: scalar multiples of the identity by a positive
constant are PosDef. This is a clean Mathlib-style derived lemma reusing
`Matrix.PosDef.diagonal`. Useful for the scalar-covariance V1 instance
(the `c • 1` Gaussian) and any other consumer that wants to instantiate
`mvGaussian_box_density_at_mode_bound` at a scalar covariance.
-/

theorem smul_one_PosDef [DecidableEq n] {c : ℝ} (hc : 0 < c) :
    (c • (1 : Matrix n n ℝ)).PosDef := by
  rw [show (c • (1 : Matrix n n ℝ)) = Matrix.diagonal (fun _ : n => c) from ?_]
  · exact Matrix.PosDef.diagonal (fun _ => hc)
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq]
    · simp [Matrix.smul_apply, hij]

/-! ## Round 9 — Determinant of the symmetric square root

For a PosDef matrix `M`, the symmetric square root `realMatrixSqrt M` (= `CFC.sqrt M`)
has determinant `Real.sqrt (det M)`. This follows from
`Matrix.PosSemidef.det_sqrt` (Mathlib `Analysis/Matrix/Order.lean`), specialised
to the field `ℝ`: `RCLike.sqrt` of a real argument is `Real.sqrt`.
-/

theorem realMatrixSqrt_det [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    (realMatrixSqrt M).det = Real.sqrt M.det := by
  unfold realMatrixSqrt
  rw [hM.det_sqrt]
  exact RCLike.sqrt_real

theorem realMatrixSqrt_det_pos [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    0 < (realMatrixSqrt M).det := by
  rw [realMatrixSqrt_det hM.posSemidef]
  exact Real.sqrt_pos.mpr hM.det_pos

theorem realMatrixSqrt_det_ne_zero [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    (realMatrixSqrt M).det ≠ 0 :=
  ne_of_gt (realMatrixSqrt_det_pos hM)

/-- The symmetric square root of a PosDef matrix is invertible (over ℝ a field). -/
theorem realMatrixSqrt_isUnit [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    IsUnit (realMatrixSqrt M) :=
  Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_iff_ne_zero.mpr (realMatrixSqrt_det_ne_zero hM))

/-! ## Round 9 — Volume of the linear preimage under `mulVec L`

For an invertible matrix `L : Matrix n n ℝ`, the Lebesgue volume of the
linear preimage `L.mulVec ⁻¹' S` equals `|det L|⁻¹ * volume S`. This is the
Jacobian formula for the change-of-variables `y = L⁻¹ x`, packaged from
Mathlib's `Real.map_matrix_volume_pi_eq_smul_volume_pi`.
-/

theorem volume_mulVec_preimage [DecidableEq n]
    {L : Matrix n n ℝ} (hL : L.det ≠ 0) {S : Set (n → ℝ)} (hS : MeasurableSet S) :
    volume (L.mulVec ⁻¹' S) = ENNReal.ofReal (|L.det|⁻¹) * volume S := by
  have h_meas : Measurable L.mulVec := mulVec_measurable L
  have h_map : Measure.map L.mulVec (volume : Measure (n → ℝ)) =
      ENNReal.ofReal (|L.det|⁻¹) • volume := by
    have := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
    simpa [Matrix.toLin'_apply'] using this
  calc volume (L.mulVec ⁻¹' S)
      = (Measure.map L.mulVec volume) S := (Measure.map_apply h_meas hS).symm
    _ = (ENNReal.ofReal (|L.det|⁻¹) • volume) S := by rw [h_map]
    _ = ENNReal.ofReal (|L.det|⁻¹) * volume S := by
        rw [Measure.smul_apply, smul_eq_mul]

/-- Specialised to `realMatrixSqrt M` for PosDef `M`: the preimage volume is
`(√det M)⁻¹` times the original volume (using `det L > 0` to drop the
absolute value). -/
theorem volume_realMatrixSqrt_mulVec_preimage [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) {S : Set (n → ℝ)} (hS : MeasurableSet S) :
    volume ((realMatrixSqrt M).mulVec ⁻¹' S) =
      ENNReal.ofReal ((Real.sqrt M.det)⁻¹) * volume S := by
  rw [volume_mulVec_preimage (realMatrixSqrt_det_ne_zero hM) hS]
  congr 2
  rw [realMatrixSqrt_det hM.posSemidef, abs_of_pos (Real.sqrt_pos.mpr hM.det_pos)]

/-! ## Round 9 — Change-of-variables identity for `mvGaussianFromPosDef`

For any measurable set `S`, the box probability under `mvGaussianFromPosDef M`
is the standard MV measure of the preimage parallelepiped under
`(realMatrixSqrt M).mulVec`. This is the pushforward identity in operational
form. -/

theorem mvGaussianFromPosDef_apply_eq [DecidableEq n]
    (M : Matrix n n ℝ) {S : Set (n → ℝ)} (hS : MeasurableSet S) :
    mvGaussianFromPosDef M S =
      standardMVGaussian n ((realMatrixSqrt M).mulVec ⁻¹' S) := by
  unfold mvGaussianFromPosDef mvGaussianFromMatrix
  rw [Measure.map_apply (mulVec_measurable _) hS]

/-- The anisotropic symmetric box `{x | ∀ i, |x i| ≤ ε i}` is measurable
(it equals a product of closed intervals). -/
theorem anisotropic_box_measurable (ε : n → ℝ) :
    MeasurableSet {x : n → ℝ | ∀ i, |x i| ≤ ε i} := by
  rw [anisotropic_box_event_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- Specialised change-of-variables for the anisotropic box. -/
theorem mvGaussianFromPosDef_box_apply_eq [DecidableEq n]
    (M : Matrix n n ℝ) (ε : n → ℝ) :
    mvGaussianFromPosDef M {x : n → ℝ | ∀ i, |x i| ≤ ε i} =
      standardMVGaussian n
        ((realMatrixSqrt M).mulVec ⁻¹' {x : n → ℝ | ∀ i, |x i| ≤ ε i}) :=
  mvGaussianFromPosDef_apply_eq M (anisotropic_box_measurable ε)

/-! ## Round 9 — Tonelli for product measures (Fin n)

The lintegral version of Mathlib's `integral_fintype_prod_eq_prod`: for
σ-finite measures, the integral of a product of single-coordinate functions
factorises as a product of single-coordinate integrals. Proved by induction
on the number of factors using `lintegral_prod_mul` and the
`measurePreserving_piFinSuccAbove` equivalence.

This is a genuine new content lemma (no analogue in current Mathlib for
ENNReal-valued integrands) and is the key technical input for the
standardMVGaussian uniform density bound below. -/

theorem lintegral_fin_nat_prod_eq_prod_aux {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ENNReal} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const]
    rw [Measure.pi_univ]
    simp
  | succ n n_ih =>
    have hm := (MeasureTheory.measurePreserving_piFinSuccAbove μ 0).symm
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [hm.lintegral_map_equiv]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (f := fun i => f (Fin.succ i)) (fun i => hf _)]
          rw [← lintegral_prod_mul (hf 0).aemeasurable
                (Measurable.aemeasurable (by fun_prop))]
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → E i → ENNReal} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (MeasureTheory.measurePreserving_piCongrLeft _ e).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod_aux (μ := fun i => μ (e i))
    (f := fun i => f (e i)) (fun i => hf _)

/-- Rectangle-restricted version of `lintegral_fintype_prod_eq_prod`: integrating
a product of single-coordinate functions over a measurable rectangle factorises
as a product of single-coordinate integrals over the corresponding factor sets.
Useful corollary derived from the unrestricted Tonelli lemma above. -/
theorem setLIntegral_fintype_prod_pi_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → E i → ENNReal} (hf : ∀ i, Measurable (f i))
    {s : (i : ι) → Set (E i)} (hs : ∀ i, MeasurableSet (s i)) :
    ∫⁻ x : (i : ι) → E i in Set.univ.pi s, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x in s i, f i x ∂(μ i) := by
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  -- Express indicator of rectangle as product of factor indicators.
  have h_eq : ∀ x : (i : ι) → E i,
      (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by
        by_contra hall
        push_neg at hall
        exact hx (fun i _ => hall i)
      obtain ⟨i, hi⟩ := this
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [Set.indicator_of_notMem hi]
  simp_rw [h_eq]
  rw [lintegral_fintype_prod_eq_prod (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i)]

/-! ## Round 9 — pi/withDensity commutation lemma

Direct corollary of `setLIntegral_fintype_prod_pi_eq_prod`: the product
measure of `withDensity`-modified factors equals the product measure
`withDensity`-modified by the product density. Another genuine Mathlib
gap (no analogue in current Mathlib for ENNReal density factorisations).
-/

theorem pi_withDensity_eq_withDensity_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {μ : (i : ι) → Measure (α i)}
    [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → α i → ENNReal} (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
      setLIntegral_fintype_prod_pi_eq_prod hf hs]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]

/-! ## Round 9 — Standard MV Gaussian uniform density-at-mode bound

For any measurable set `K ⊆ n → ℝ`, the standard MV Gaussian satisfies the
uniform density-at-mode bound

  `standardMVGaussian K ≤ ((√(2π))⁻¹)^n · volume K`,

since the standard MV density `∏ᵢ gaussianPDF 0 1 (xᵢ)` is bounded
pointwise by `((√(2π))⁻¹)^n` (each 1-D Gaussian density has its maximum
`(√(2π))⁻¹` at the mode `0`).

The remaining gap is the equality
`standardMVGaussian = volume.withDensity (∏ᵢ gaussianPDF 0 1)`,
which would follow from the missing pi/withDensity commutation lemma in
Mathlib. We package it as a single, narrowly-scoped sub-lemma below; the
rest of the Round 9 chain depends only on this. -/

/-- The product density `x ↦ ∏ᵢ gaussianPDF 0 1 (xᵢ)` is measurable. -/
theorem measurable_prod_gaussianPDF :
    Measurable (fun (x : n → ℝ) => ∏ i, gaussianPDF 0 1 (x i)) := by
  refine Finset.measurable_prod _ (fun i _ => ?_)
  exact (measurable_gaussianPDF _ _).comp (measurable_pi_apply i)

/-- The product density is bounded pointwise by `(√(2π))⁻¹^n`, since each 1-D
Gaussian PDF achieves its maximum `(√(2π))⁻¹` at the mode `0`. -/
theorem prod_gaussianPDF_le (x : n → ℝ) :
    ∏ i, gaussianPDF 0 1 (x i) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) := by
  have h_factor : ∀ y : ℝ, gaussianPDF 0 1 y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro y
    rw [gaussianPDF, gaussianPDFReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have h_exp_le : Real.exp (-(y - 0) ^ 2 / (2 * (1 : ℝ≥0))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have h_sq_nn : 0 ≤ (y - 0) ^ 2 := by positivity
      have h_two_v_pos : (0 : ℝ) < 2 * (1 : ℝ≥0) := by norm_num
      have h_div_nn : 0 ≤ (y - 0) ^ 2 / (2 * (1 : ℝ≥0)) :=
        div_nonneg h_sq_nn (le_of_lt h_two_v_pos)
      have h_neg : -(y - 0) ^ 2 / (2 * (1 : ℝ≥0)) =
                    -((y - 0) ^ 2 / (2 * (1 : ℝ≥0))) := by ring
      rw [h_neg]
      linarith
    have h_inv_sqrt_nn : 0 ≤ (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ := by positivity
    calc (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ *
          Real.exp (-(y - 0) ^ 2 / (2 * (1 : ℝ≥0)))
        ≤ (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le h_inv_sqrt_nn
      _ = (Real.sqrt (2 * Real.pi))⁻¹ := by
          simp [NNReal.coe_one, mul_one]
  calc ∏ i, gaussianPDF 0 1 (x i)
      ≤ ∏ i, ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ :=
        Finset.prod_le_prod' (fun i _ => h_factor (x i))
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card n := by
        rw [Finset.prod_const, Finset.card_univ]
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) := by
        rw [← ENNReal.ofReal_pow (by positivity)]

/-- The standard MV Gaussian, expressed as a `withDensity` of Lebesgue volume
with the explicit product density. -/
theorem standardMVGaussian_eq_withDensity :
    standardMVGaussian n =
      (volume : Measure (n → ℝ)).withDensity
        (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  unfold standardMVGaussian
  refine Measure.pi_eq (μ := fun _ : n => gaussianReal 0 1) fun s hs => ?_
  -- LHS on rectangle: ∫⁻ x in univ.pi s, ∏ pdf(x_i) ∂volume.
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), MeasureTheory.volume_pi,
      setLIntegral_fintype_prod_pi_eq_prod
        (μ := fun _ : n => (volume : Measure ℝ))
        (fun _ => measurable_gaussianPDF _ _) hs]
  -- Each factor: ∫⁻ y in s i, pdf y ∂volume = gaussianReal 0 1 (s i).
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply _ one_ne_zero (s i)).symm

/-- Round 9 sub-lemma. The standard multivariate Gaussian uniform density
bound: for any measurable set `K ⊆ n → ℝ`,
`standardMVGaussian n K ≤ ((√(2π))⁻¹)^n · volume K`. -/
theorem standardMVGaussian_le_volume_smul (K : Set (n → ℝ)) (hK : MeasurableSet K) :
    standardMVGaussian n K ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) * volume K := by
  rw [standardMVGaussian_eq_withDensity, withDensity_apply _ hK]
  calc ∫⁻ x in K, ∏ i, gaussianPDF 0 1 (x i) ∂volume
      ≤ ∫⁻ _ in K, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) ∂volume := by
        apply MeasureTheory.setLIntegral_mono measurable_const
        intro x _
        exact prod_gaussianPDF_le x
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) * volume K := by
        rw [setLIntegral_const]

/-! ## Round 9 — Volume of the anisotropic symmetric box

The Lebesgue volume of the box `B = ∏ᵢ [-εᵢ, εᵢ]` is `∏ᵢ ENNReal.ofReal (2εᵢ)`,
via `Real.volume_Icc` per factor and `Measure.volume_pi_pi`.
-/

theorem volume_anisotropic_box (ε : n → ℝ) :
    volume {x : n → ℝ | ∀ i, |x i| ≤ ε i} = ∏ i, ENNReal.ofReal (2 * ε i) := by
  rw [anisotropic_box_event_eq_pi, MeasureTheory.volume_pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.volume_Icc, show ε i - (-ε i) = 2 * ε i by ring]

theorem volume_anisotropic_box_lt_top (ε : n → ℝ) :
    volume {x : n → ℝ | ∀ i, |x i| ≤ ε i} < ⊤ := by
  rw [anisotropic_box_event_eq_pi, MeasureTheory.volume_pi_pi]
  exact ENNReal.prod_lt_top fun i _ => by simp [Real.volume_Icc]

/-! ## Round 9 — Headline theorem (PosDef Anderson box bound)

The general PosDef multivariate Gaussian Anderson-upper / density-at-mode
small-ball bound for an anisotropic symmetric box. The proof composes:

* `mvGaussianFromPosDef_box_apply_eq` (change of variables);
* `standardMVGaussian_le_volume_smul` (uniform density bound, fully proven);
* `volume_realMatrixSqrt_mulVec_preimage` (Jacobian);
* `volume_anisotropic_box` (box volume).
-/

/-- General PosDef multivariate Gaussian Anderson-upper / density-at-mode
small-ball bound for an anisotropic symmetric box. -/
theorem mvGaussian_box_density_at_mode_bound [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) (ε : n → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    ((mvGaussianFromPosDef M) {x : n → ℝ | ∀ i, |x i| ≤ ε i}).toReal ≤
      (∏ i, 2 * ε i) * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n /
        Real.sqrt M.det := by
  set B : Set (n → ℝ) := {x : n → ℝ | ∀ i, |x i| ≤ ε i} with hB
  set L : Matrix n n ℝ := realMatrixSqrt M with hL
  have hB_meas : MeasurableSet B := anisotropic_box_measurable ε
  have hpre_meas : MeasurableSet (L.mulVec ⁻¹' B) :=
    (mulVec_measurable L) hB_meas
  -- Step 1: pushforward identity: P(X ∈ B) = stdMV(L⁻¹ B).
  have h_eq_push : (mvGaussianFromPosDef M) B = standardMVGaussian n (L.mulVec ⁻¹' B) :=
    mvGaussianFromPosDef_apply_eq M hB_meas
  -- Step 2: uniform density bound on stdMV applied to L⁻¹ B.
  have h_unif :
      standardMVGaussian n (L.mulVec ⁻¹' B) ≤
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) *
          volume (L.mulVec ⁻¹' B) :=
    standardMVGaussian_le_volume_smul (L.mulVec ⁻¹' B) hpre_meas
  -- Step 3: volume of L⁻¹ B = (√det M)⁻¹ · volume B.
  have h_vol_pre : volume (L.mulVec ⁻¹' B) =
      ENNReal.ofReal ((Real.sqrt M.det)⁻¹) * volume B :=
    volume_realMatrixSqrt_mulVec_preimage hM hB_meas
  -- Step 4: volume B = ∏ ENNReal.ofReal (2 ε i).
  have h_vol_box : volume B = ∏ i, ENNReal.ofReal (2 * ε i) :=
    volume_anisotropic_box ε
  -- Step 5: assemble the ENNReal bound.
  have h_ENNReal :
      (mvGaussianFromPosDef M) B ≤
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) *
          (ENNReal.ofReal ((Real.sqrt M.det)⁻¹) *
            ∏ i, ENNReal.ofReal (2 * ε i)) := by
    calc (mvGaussianFromPosDef M) B
        = standardMVGaussian n (L.mulVec ⁻¹' B) := h_eq_push
      _ ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) *
            volume (L.mulVec ⁻¹' B) := h_unif
      _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) *
            (ENNReal.ofReal ((Real.sqrt M.det)⁻¹) * volume B) := by rw [h_vol_pre]
      _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) *
            (ENNReal.ofReal ((Real.sqrt M.det)⁻¹) *
              ∏ i, ENNReal.ofReal (2 * ε i)) := by rw [h_vol_box]
  -- Step 6: convert ENNReal bound to ℝ bound via toReal monotonicity.
  have h_finite : (mvGaussianFromPosDef M) B ≠ ⊤ := by
    have : IsProbabilityMeasure (mvGaussianFromPosDef M) := inferInstance
    exact (measure_lt_top (mvGaussianFromPosDef M) B).ne
  have h_eps_nn : ∀ i, 0 ≤ 2 * ε i := fun i => mul_nonneg (by norm_num) (hε i)
  have h_inv_pi_nn : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have h_pow_nn : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by positivity
  have h_inv_det_nn : 0 ≤ (Real.sqrt M.det)⁻¹ := by positivity
  have h_prod_nn : 0 ≤ ∏ i, 2 * ε i := Finset.prod_nonneg fun i _ => h_eps_nn i
  -- The RHS ENNReal value equals ENNReal.ofReal of the real RHS.
  have h_RHS_eq :
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n) *
          (ENNReal.ofReal ((Real.sqrt M.det)⁻¹) *
            ∏ i, ENNReal.ofReal (2 * ε i)) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n *
        ((Real.sqrt M.det)⁻¹ * (∏ i, 2 * ε i))) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => h_eps_nn i),
        ← ENNReal.ofReal_mul h_inv_det_nn, ← ENNReal.ofReal_mul h_pow_nn]
  rw [h_RHS_eq] at h_ENNReal
  have h_RHS_real_nn :
      0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n *
        ((Real.sqrt M.det)⁻¹ * (∏ i, 2 * ε i)) := by
    exact mul_nonneg h_pow_nn (mul_nonneg h_inv_det_nn h_prod_nn)
  have h_toReal_mono :
      ((mvGaussianFromPosDef M) B).toReal ≤
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n *
          ((Real.sqrt M.det)⁻¹ * (∏ i, 2 * ε i)) :=
    ENNReal.toReal_le_of_le_ofReal h_RHS_real_nn h_ENNReal
  -- Final algebra: rearrange to the headline form `* / √det M`.
  refine h_toReal_mono.trans (le_of_eq ?_)
  field_simp

/-! ## Round 9 — Power-form corollary of the headline theorem

The same bound expressed in the `(2π)^(-n/2)` form (via
`Real.sqrt_eq_rpow`), matching how the V1 instance / anderson_upper field
naturally reads it. -/

theorem mvGaussian_box_density_at_mode_bound_rpow [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) (ε : n → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    ((mvGaussianFromPosDef M) {x : n → ℝ | ∀ i, |x i| ≤ ε i}).toReal ≤
      (∏ i, 2 * ε i) *
        (2 * Real.pi) ^ (-(Fintype.card n : ℝ) / 2) *
        (Real.sqrt M.det)⁻¹ := by
  have h_two_pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h := mvGaussian_box_density_at_mode_bound hM ε hε
  have h_pow_eq : (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n =
      (2 * Real.pi) ^ (-(Fintype.card n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h_two_pi_nn,
        ← Real.rpow_natCast ((2 * Real.pi) ^ (-(1 / (2 : ℝ)))) (Fintype.card n),
        ← Real.rpow_mul h_two_pi_nn]
    congr 1
    ring
  rw [h_pow_eq] at h
  rw [div_eq_mul_inv] at h
  exact h

/-! ## Round 9 — Isotropic-ε consumer corollary

The form actually consumed by `GaussianBoxProb.anderson_upper` (in
`Helpers/GaussianGridSmallBall.lean`): a single radius `ε > 0` rather than an
anisotropic vector `(εᵢ)`. Specialise the headline theorem to all `εᵢ = ε`. -/

theorem mvGaussian_isotropic_box_density_at_mode_bound [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) {ε : ℝ} (hε : 0 ≤ ε) :
    ((mvGaussianFromPosDef M) {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card n * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n /
        Real.sqrt M.det := by
  have h_eps_nn : ∀ _ : n, (0 : ℝ) ≤ ε := fun _ => hε
  have h := mvGaussian_box_density_at_mode_bound hM (fun _ : n => ε) h_eps_nn
  simpa [Finset.prod_const, Finset.card_univ] using h

/-- Equivalent reformulation of `mvGaussian_isotropic_box_density_at_mode_bound`
in the `(2π)^(-n/2)` form, matching the `anderson_upper` field shape of
`GaussianBoxProb` exactly. -/
theorem mvGaussian_isotropic_box_density_at_mode_bound_rpow [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) {ε : ℝ} (hε : 0 ≤ ε) :
    ((mvGaussianFromPosDef M) {x : n → ℝ | ∀ i, |x i| ≤ ε}).toReal ≤
      (2 * ε) ^ Fintype.card n *
        (2 * Real.pi) ^ (-(Fintype.card n : ℝ) / 2) *
        (Real.sqrt M.det)⁻¹ := by
  have h_two_pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h := mvGaussian_isotropic_box_density_at_mode_bound hM hε
  -- Rewrite the `(√(2π))⁻¹ ^ n` form into `(2π)^(-n/2)` form via `sqrt_eq_rpow`.
  have h_pow_eq : (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n =
      (2 * Real.pi) ^ (-(Fintype.card n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h_two_pi_nn,
        ← Real.rpow_natCast ((2 * Real.pi) ^ (-(1 / (2 : ℝ)))) (Fintype.card n),
        ← Real.rpow_mul h_two_pi_nn]
    congr 1
    ring
  rw [h_pow_eq] at h
  rw [div_eq_mul_inv] at h
  exact h

/-! ## Identity-covariance specialisation (provable from the standard MV bound) -/

/-- Specialisation of the PosDef bound to `M = 1`, where `det 1 = 1`. -/
theorem mvGaussian_box_density_at_mode_bound_one [DecidableEq n]
    (ε : n → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    ((mvGaussianFromPosDef (1 : Matrix n n ℝ))
        {x : n → ℝ | ∀ i, |x i| ≤ ε i}).toReal ≤
      (∏ i, 2 * ε i) * (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n := by
  -- `mvGaussianFromPosDef 1 = standardMVGaussian` (Round 4).
  rw [mvGaussianFromPosDef_one_eq]
  exact standardMVGaussian_anisotropic_box_density_at_mode_bound ε hε

/-! ## Round 9 — Consumer-facing API summary

Round 9 delivers the following consumer entry points (all sorry-free):

| Form                                                            | Theorem                                            |
| --------------------------------------------------------------- | -------------------------------------------------- |
| anisotropic, `(√(2π))⁻¹^n` form (headline)                      | `mvGaussian_box_density_at_mode_bound`             |
| anisotropic, `(2π)^(-n/2)` form                                 | `mvGaussian_box_density_at_mode_bound_rpow`        |
| isotropic ε, `(√(2π))⁻¹^n` form                                 | `mvGaussian_isotropic_box_density_at_mode_bound`   |
| isotropic ε, `(2π)^(-n/2)` form (V1 instance shape)             | `mvGaussian_isotropic_box_density_at_mode_bound_rpow` |
| identity covariance specialisation                              | `mvGaussian_box_density_at_mode_bound_one`         |

PosDef constructors:

| Statement                                                       | Theorem               |
| --------------------------------------------------------------- | --------------------- |
| `(c • (1 : Matrix n n ℝ)).PosDef` for `c > 0`                   | `smul_one_PosDef`     |

Mathlib-PR-ready Tonelli / pi-density lemmas:

| Statement                                                       | Theorem                                       |
| --------------------------------------------------------------- | --------------------------------------------- |
| `∫⁻ ∏ f_i (x_i) ∂ Measure.pi μ = ∏ ∫⁻ f_i ∂ μ_i` (Fin n)        | `lintegral_fin_nat_prod_eq_prod_aux`          |
| Same, Fintype version                                           | `lintegral_fintype_prod_eq_prod`              |
| Rectangle-restricted form                                       | `setLIntegral_fintype_prod_pi_eq_prod`        |
| `Measure.pi (μ.withDensity f) = (Measure.pi μ).withDensity (∏ f)` | `pi_withDensity_eq_withDensity_pi`        |

The Round 9 closure used the last four to reduce the Round 6 sorry on
`mvGaussian_box_density_at_mode_bound` from Mathlib-gap status to a fully
proven theorem.
-/

end Erdos524.Helpers
