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
# Two-scale cosine-product cross-block swap inequality (helper for Erdős 524)

A finite-`n`, axiom-free, real-valued cosine-product inequality bounding the
deviation of a joint cosine product from its product of marginals when the
arguments come from two scales `δ₁, δ₂ > 0`. This is the keystone "Lindeberg
swap with kernel decay" lemma — replaces KMT/Brownian coupling for the
Erdős 524 upper-bound axiom retirement (`gao_li_wellner_small_ball_upper`).

The bound `|t₁||t₂|/(2√(δ₁δ₂))` is sharp at `δ₁ = δ₂` and provides the
geometric-mean cross-covariance scaling needed for iterated multi-block
small-ball bounds.

Proof: telescoping product inequality + cos addition formula + |sin x|≤|x|
+ right-Riemann sum bound on monotone-decreasing exp + AM-GM. No probability
machinery required at this layer.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace Erdos524.Helpers

open Real Finset MeasureTheory

/-- Telescoping product inequality: if all factors are bounded by 1 in absolute
value, then `|∏ uᵢ - ∏ vᵢ| ≤ ∑ |uᵢ - vᵢ|`. -/
lemma abs_prod_sub_prod_le_sum_abs_sub
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (u v : ι → ℝ)
    (hu : ∀ i ∈ s, |u i| ≤ 1) (hv : ∀ i ∈ s, |v i| ≤ 1) :
    |∏ i ∈ s, u i - ∏ i ∈ s, v i| ≤ ∑ i ∈ s, |u i - v i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have hu' : ∀ i ∈ s, |u i| ≤ 1 := fun i hi => hu i (mem_insert_of_mem hi)
    have hv' : ∀ i ∈ s, |v i| ≤ 1 := fun i hi => hv i (mem_insert_of_mem hi)
    have hua : |u a| ≤ 1 := hu a (mem_insert_self a s)
    rw [prod_insert has, prod_insert has, sum_insert has]
    set P := ∏ i ∈ s, u i with hP
    set Q := ∏ i ∈ s, v i with hQ_def
    have key : u a * P - v a * Q = u a * (P - Q) + (u a - v a) * Q := by ring
    rw [key]
    have hQ : |Q| ≤ 1 := by
      simp only [Q, abs_prod]
      exact prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hv' i hi)
    calc |u a * (P - Q) + (u a - v a) * Q|
        ≤ |u a * (P - Q)| + |(u a - v a) * Q| := abs_add_le _ _
      _ = |u a| * |P - Q| + |u a - v a| * |Q| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |P - Q| + |u a - v a| * 1 := by
          gcongr
      _ = |P - Q| + |u a - v a| := by ring
      _ ≤ (∑ i ∈ s, |u i - v i|) + |u a - v a| := by
          gcongr
          exact ih hu' hv'
      _ = |u a - v a| + ∑ i ∈ s, |u i - v i| := by ring

/-- Per-factor bound: `|cos(θ + ψ) - cos θ · cos ψ| ≤ |θ| · |ψ|`. -/
lemma abs_cos_add_sub_cos_mul_cos_le (θ ψ : ℝ) :
    |Real.cos (θ + ψ) - Real.cos θ * Real.cos ψ| ≤ |θ| * |ψ| := by
  rw [Real.cos_add,
      show Real.cos θ * Real.cos ψ - Real.sin θ * Real.sin ψ - Real.cos θ * Real.cos ψ
        = -(Real.sin θ * Real.sin ψ) by ring,
      abs_neg, abs_mul]
  exact mul_le_mul Real.abs_sin_le_abs Real.abs_sin_le_abs (abs_nonneg _) (abs_nonneg _)

/-- Riemann sum bound: `(1/n) Σ_{k<n} exp(-c(k+1)/n) ≤ 1/c`. The function
`u ↦ exp(-c·u/n)` is antitone on `[0,n]` with antiderivative
`u ↦ -(n/c)·exp(-c·u/n)`. -/
lemma sum_exp_neg_div_le_inv (n : ℕ) (hn : 0 < n) {c : ℝ} (hc : 0 < c) :
    (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        Real.exp (-(c * ((k : ℝ) + 1) / n)) ≤ c⁻¹ := by
  let f : ℝ → ℝ := fun u => Real.exp (-(c * u / n))
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc
  -- Antitone on [0, n]
  have hf_anti : AntitoneOn f (Set.Icc (0 : ℝ) ((0 : ℝ) + n)) := by
    intro x _ y _ hxy
    simp only [f]
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ hn_pos.le
    exact mul_le_mul_of_nonneg_left hxy hc.le
  -- Antiderivative F(u) = -(n/c) * exp(-c*u/n), so F'(u) = exp(-c*u/n)
  let F : ℝ → ℝ := fun u => -((n : ℝ) / c) * Real.exp (-(c * u / n))
  have hF_deriv : ∀ x : ℝ, HasDerivAt F (f x) x := by
    intro x
    have h1 : HasDerivAt (fun u => -(c * u / n)) (-(c / n)) x := by
      have hd1 : HasDerivAt (fun u : ℝ => c * u) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have hd2 : HasDerivAt (fun u : ℝ => c * u / n) (c / n) x := by
        have := hd1.div_const (n : ℝ)
        simpa [mul_div_assoc] using this
      exact hd2.neg
    have h2 : HasDerivAt (fun u => Real.exp (-(c * u / n)))
        (Real.exp (-(c * x / n)) * (-(c / n))) x :=
      Real.hasDerivAt_exp _ |>.comp x h1
    have h3 : HasDerivAt F
        (-((n : ℝ) / c) * (Real.exp (-(c * x / n)) * (-(c / n)))) x :=
      h2.const_mul (-((n : ℝ) / c))
    convert h3 using 1
    field_simp
    ring
  -- f is continuous
  have hf_cont : Continuous f :=
    Real.continuous_exp.comp (by continuity)
  -- Apply AntitoneOn.sum_le_integral
  have hsum_le : (∑ i ∈ Finset.range n, f ((0 : ℝ) + ((i + 1 : ℕ) : ℝ)))
      ≤ ∫ x in (0 : ℝ)..(0 + (n : ℝ)), f x :=
    hf_anti.sum_le_integral (a := n) (x₀ := (0 : ℝ))
  -- Compute the integral via the FTC
  have hint_eq : ∫ x in (0 : ℝ)..((n : ℝ)), f x = F n - F 0 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := F) (f' := f) (a := 0) (b := (n : ℝ))
      (fun x _ => hF_deriv x) (hf_cont.intervalIntegrable 0 n)
    simpa using this
  -- F n - F 0 = (n/c) * (1 - exp(-c))
  have hFn : F (n : ℝ) = -((n : ℝ) / c) * Real.exp (-c) := by
    show -((n : ℝ) / c) * Real.exp (-(c * (n : ℝ) / n)) = -((n : ℝ) / c) * Real.exp (-c)
    congr 2
    field_simp
  have hF0 : F 0 = -((n : ℝ) / c) := by
    show -((n : ℝ) / c) * Real.exp (-(c * 0 / n)) = -((n : ℝ) / c)
    simp
  have hint_val : ∫ x in (0 : ℝ)..((n : ℝ)), f x = (n / c) * (1 - Real.exp (-c)) := by
    rw [hint_eq, hFn, hF0]; ring
  have hexp_le : 1 - Real.exp (-c) ≤ 1 := by linarith [Real.exp_nonneg (-c)]
  -- The sum we want, equating cast forms
  have hsum_form : (∑ i ∈ Finset.range n, f ((0 : ℝ) + ((i + 1 : ℕ) : ℝ)))
      = ∑ k ∈ Finset.range n, Real.exp (-(c * ((k : ℝ) + 1) / n)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [f, zero_add, Nat.cast_add, Nat.cast_one]
  have h0n : (0 : ℝ) + (n : ℝ) = (n : ℝ) := by ring
  rw [h0n] at hsum_le
  rw [hsum_form] at hsum_le
  -- Combine: sum ≤ ∫ = (n/c)*(1-exp(-c)) ≤ n/c
  have hfinal : ∑ k ∈ Finset.range n, Real.exp (-(c * ((k : ℝ) + 1) / n))
      ≤ (n : ℝ) / c := by
    calc ∑ k ∈ Finset.range n, Real.exp (-(c * ((k : ℝ) + 1) / n))
        ≤ ∫ x in (0 : ℝ)..((n : ℝ)), f x := hsum_le
      _ = (n / c) * (1 - Real.exp (-c)) := hint_val
      _ ≤ (n / c) * 1 := by
          apply mul_le_mul_of_nonneg_left hexp_le
          exact div_nonneg hn_pos.le hc.le
      _ = (n : ℝ) / c := by ring
  have hinv_nn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
  calc (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, Real.exp (-(c * ((k : ℝ) + 1) / n))
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) / c) := mul_le_mul_of_nonneg_left hfinal hinv_nn
    _ = c⁻¹ := by field_simp

/-- Two-scale cosine-product cross-block swap inequality.

For `n ≥ 1`, `δ₁, δ₂ > 0`, and `t₁, t₂ ∈ ℝ`, with `θₖ = (√n)⁻¹·t₁·exp(-δ₁k/n)`
and `ψₖ = (√n)⁻¹·t₂·exp(-δ₂k/n)`,
`|∏cos(θₖ+ψₖ) - (∏cos θₖ)(∏cos ψₖ)| ≤ |t₁|·|t₂| / (2√(δ₁δ₂))`. -/
theorem abs_cosProd_two_scale_swap
    (n : ℕ) (hn : 0 < n) {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (t₁ t₂ : ℝ) :
    |∏ k ∈ Finset.Icc 1 n, Real.cos
        ((Real.sqrt n)⁻¹ *
          (t₁ * Real.exp (-(δ₁ * k / n)) + t₂ * Real.exp (-(δ₂ * k / n))))
     - (∏ k ∈ Finset.Icc 1 n, Real.cos
          ((Real.sqrt n)⁻¹ * (t₁ * Real.exp (-(δ₁ * k / n)))))
       * (∏ k ∈ Finset.Icc 1 n, Real.cos
          ((Real.sqrt n)⁻¹ * (t₂ * Real.exp (-(δ₂ * k / n)))))|
    ≤ |t₁| * |t₂| / (2 * Real.sqrt (δ₁ * δ₂)) := by
  -- Step 1: combine the two product factors on the RHS into one product,
  -- via the rewrite cos α · cos β with α := (√n)⁻¹ t₁ exp(-δ₁k/n) etc.
  -- Define θₖ and ψₖ as functions of k : ℕ.
  set θ : ℕ → ℝ := fun k => (Real.sqrt n)⁻¹ * (t₁ * Real.exp (-(δ₁ * k / n))) with hθ
  set ψ : ℕ → ℝ := fun k => (Real.sqrt n)⁻¹ * (t₂ * Real.exp (-(δ₂ * k / n))) with hψ
  have hθψ_sum : ∀ k : ℕ,
      (Real.sqrt n)⁻¹ * (t₁ * Real.exp (-(δ₁ * k / n)) + t₂ * Real.exp (-(δ₂ * k / n)))
      = θ k + ψ k := by
    intro k; simp only [θ, ψ]; ring
  -- Rewrite all three products
  conv_lhs => rw [show
    (fun k : ℕ => Real.cos ((Real.sqrt ↑n)⁻¹ *
          (t₁ * Real.exp (-(δ₁ * ↑k / ↑n)) + t₂ * Real.exp (-(δ₂ * ↑k / ↑n))))) =
    (fun k : ℕ => Real.cos (θ k + ψ k)) from
      funext (fun k => by rw [hθψ_sum])]
  -- The two marginal products use cos (θ k) and cos (ψ k)
  have hLHS_eq : (∏ k ∈ Finset.Icc 1 n, Real.cos
        ((Real.sqrt ↑n)⁻¹ * (t₁ * Real.exp (-(δ₁ * ↑k / ↑n))))) =
      ∏ k ∈ Finset.Icc 1 n, Real.cos (θ k) := by
    apply Finset.prod_congr rfl; intro k _; rfl
  have hRHS_eq : (∏ k ∈ Finset.Icc 1 n, Real.cos
        ((Real.sqrt ↑n)⁻¹ * (t₂ * Real.exp (-(δ₂ * ↑k / ↑n))))) =
      ∏ k ∈ Finset.Icc 1 n, Real.cos (ψ k) := by
    apply Finset.prod_congr rfl; intro k _; rfl
  rw [hLHS_eq, hRHS_eq]
  -- Combine the two marginal products into ∏ cos θ · cos ψ
  rw [← Finset.prod_mul_distrib]
  -- Apply telescoping
  set u : ℕ → ℝ := fun k => Real.cos (θ k + ψ k) with hu_def
  set v : ℕ → ℝ := fun k => Real.cos (θ k) * Real.cos (ψ k) with hv_def
  have hu_bd : ∀ i ∈ Finset.Icc 1 n, |u i| ≤ 1 := fun i _ => Real.abs_cos_le_one _
  have hv_bd : ∀ i ∈ Finset.Icc 1 n, |v i| ≤ 1 := by
    intro i _
    simp only [v, abs_mul]
    calc |Real.cos (θ i)| * |Real.cos (ψ i)|
        ≤ 1 * 1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = 1 := by ring
  have htel : |∏ i ∈ Finset.Icc 1 n, u i - ∏ i ∈ Finset.Icc 1 n, v i|
      ≤ ∑ i ∈ Finset.Icc 1 n, |u i - v i| :=
    abs_prod_sub_prod_le_sum_abs_sub _ u v hu_bd hv_bd
  -- Per-factor bound: |u i - v i| ≤ |θ i| · |ψ i|
  have hpf : ∀ i ∈ Finset.Icc 1 n, |u i - v i| ≤ |θ i| * |ψ i| := by
    intro i _
    simp only [u, v]
    exact abs_cos_add_sub_cos_mul_cos_le (θ i) (ψ i)
  have hsum_le : ∑ i ∈ Finset.Icc 1 n, |u i - v i|
      ≤ ∑ i ∈ Finset.Icc 1 n, |θ i| * |ψ i| :=
    Finset.sum_le_sum hpf
  -- Compute |θ i| · |ψ i| = |t₁| |t₂|/n · exp(-(δ₁+δ₂) i / n)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrtn_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrtn_pos
  have hsqrtn_sq : Real.sqrt n * Real.sqrt n = n :=
    Real.mul_self_sqrt hn_pos.le
  have hθψ_abs : ∀ k : ℕ,
      |θ k| * |ψ k| = |t₁| * |t₂| / n *
        Real.exp (-((δ₁ + δ₂) * (k : ℝ) / n)) := by
    intro k
    have h1 : |(Real.sqrt n)⁻¹| = (Real.sqrt n)⁻¹ :=
      abs_of_pos (inv_pos.mpr hsqrtn_pos)
    have h2 : |Real.exp (-(δ₁ * (k : ℝ) / n))| = Real.exp (-(δ₁ * (k : ℝ) / n)) :=
      abs_of_pos (Real.exp_pos _)
    have h3 : |Real.exp (-(δ₂ * (k : ℝ) / n))| = Real.exp (-(δ₂ * (k : ℝ) / n)) :=
      abs_of_pos (Real.exp_pos _)
    have hθk : |θ k| = (Real.sqrt n)⁻¹ * |t₁| * Real.exp (-(δ₁ * (k : ℝ) / n)) := by
      simp only [θ, abs_mul, h1, h2]; ring
    have hψk : |ψ k| = (Real.sqrt n)⁻¹ * |t₂| * Real.exp (-(δ₂ * (k : ℝ) / n)) := by
      simp only [ψ, abs_mul, h1, h3]; ring
    rw [hθk, hψk]
    have hexp_add : Real.exp (-(δ₁ * (k : ℝ) / n)) * Real.exp (-(δ₂ * (k : ℝ) / n))
        = Real.exp (-((δ₁ + δ₂) * (k : ℝ) / n)) := by
      rw [← Real.exp_add]
      congr 1; ring
    have hinv_sq : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
      rw [← mul_inv, hsqrtn_sq]
    calc (Real.sqrt n)⁻¹ * |t₁| * Real.exp (-(δ₁ * (k : ℝ) / n)) *
          ((Real.sqrt n)⁻¹ * |t₂| * Real.exp (-(δ₂ * (k : ℝ) / n)))
        = ((Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹) * (|t₁| * |t₂|) *
          (Real.exp (-(δ₁ * (k : ℝ) / n)) * Real.exp (-(δ₂ * (k : ℝ) / n))) := by ring
      _ = (n : ℝ)⁻¹ * (|t₁| * |t₂|) * Real.exp (-((δ₁ + δ₂) * (k : ℝ) / n)) := by
          rw [hinv_sq, hexp_add]
      _ = |t₁| * |t₂| / n * Real.exp (-((δ₁ + δ₂) * (k : ℝ) / n)) := by
          rw [div_eq_inv_mul]; ring
  -- Sum bound: ∑ |θ i| |ψ i| = (|t₁||t₂|/n) ∑ exp(-(δ₁+δ₂) i / n)
  have hreidx : ∑ i ∈ Finset.Icc 1 n, |θ i| * |ψ i|
      = ∑ k ∈ Finset.range n, |t₁| * |t₂| / n *
          Real.exp (-((δ₁ + δ₂) * ((k : ℝ) + 1) / n)) := by
    -- reindex i ↔ k+1
    rw [show (Finset.Icc 1 n) = (Finset.range n).image (· + 1) from ?_]
    · rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k _
        rw [hθψ_abs (k + 1)]
        push_cast; ring
      · intro a _ b _ h; exact Nat.add_right_cancel h
    · ext m; simp [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨m - 1, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩; omega
  -- Pull out the constant factor
  have hsum_eq : ∑ k ∈ Finset.range n, |t₁| * |t₂| / n *
        Real.exp (-((δ₁ + δ₂) * ((k : ℝ) + 1) / n))
      = |t₁| * |t₂| * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            Real.exp (-((δ₁ + δ₂) * ((k : ℝ) + 1) / n))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [div_eq_inv_mul]; ring
  -- Apply the Riemann bound with c = δ₁ + δ₂ > 0
  have hsum_riemann : ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        Real.exp (-((δ₁ + δ₂) * ((k : ℝ) + 1) / n)))
      ≤ (δ₁ + δ₂)⁻¹ :=
    sum_exp_neg_div_le_inv n hn (by linarith : (0 : ℝ) < δ₁ + δ₂)
  -- AM-GM step: 1/(δ₁+δ₂) ≤ 1/(2√(δ₁δ₂))
  have hsqrtδ₁_pos : 0 < Real.sqrt δ₁ := Real.sqrt_pos.mpr hδ₁
  have hsqrtδ₂_pos : 0 < Real.sqrt δ₂ := Real.sqrt_pos.mpr hδ₂
  have hsqrtδ₁_sq : Real.sqrt δ₁ * Real.sqrt δ₁ = δ₁ := Real.mul_self_sqrt hδ₁.le
  have hsqrtδ₂_sq : Real.sqrt δ₂ * Real.sqrt δ₂ = δ₂ := Real.mul_self_sqrt hδ₂.le
  have hAMGM : 2 * Real.sqrt (δ₁ * δ₂) ≤ δ₁ + δ₂ := by
    have h := two_mul_le_add_sq (Real.sqrt δ₁) (Real.sqrt δ₂)
    rw [Real.sqrt_mul hδ₁.le]
    have hsq1 : (Real.sqrt δ₁) ^ 2 = δ₁ := Real.sq_sqrt hδ₁.le
    have hsq2 : (Real.sqrt δ₂) ^ 2 = δ₂ := Real.sq_sqrt hδ₂.le
    rw [hsq1, hsq2] at h
    linarith
  have h2sqrt_pos : 0 < 2 * Real.sqrt (δ₁ * δ₂) := by
    apply mul_pos two_pos
    exact Real.sqrt_pos.mpr (mul_pos hδ₁ hδ₂)
  have hδsum_pos : 0 < δ₁ + δ₂ := by linarith
  have hinv_le : (δ₁ + δ₂)⁻¹ ≤ (2 * Real.sqrt (δ₁ * δ₂))⁻¹ :=
    one_div (δ₁ + δ₂) ▸ one_div (2 * Real.sqrt (δ₁ * δ₂)) ▸
      one_div_le_one_div_of_le h2sqrt_pos hAMGM
  -- |t₁| * |t₂| ≥ 0
  have ht_nn : 0 ≤ |t₁| * |t₂| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- Chain everything together
  calc |∏ i ∈ Finset.Icc 1 n, u i - ∏ i ∈ Finset.Icc 1 n, v i|
      ≤ ∑ i ∈ Finset.Icc 1 n, |u i - v i| := htel
    _ ≤ ∑ i ∈ Finset.Icc 1 n, |θ i| * |ψ i| := hsum_le
    _ = ∑ k ∈ Finset.range n, |t₁| * |t₂| / n *
            Real.exp (-((δ₁ + δ₂) * ((k : ℝ) + 1) / n)) := hreidx
    _ = |t₁| * |t₂| * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            Real.exp (-((δ₁ + δ₂) * ((k : ℝ) + 1) / n))) := hsum_eq
    _ ≤ |t₁| * |t₂| * (δ₁ + δ₂)⁻¹ := by
        apply mul_le_mul_of_nonneg_left hsum_riemann ht_nn
    _ ≤ |t₁| * |t₂| * (2 * Real.sqrt (δ₁ * δ₂))⁻¹ := by
        apply mul_le_mul_of_nonneg_left hinv_le ht_nn
    _ = |t₁| * |t₂| / (2 * Real.sqrt (δ₁ * δ₂)) := by
        rw [mul_inv_eq_iff_eq_mul₀ (ne_of_gt h2sqrt_pos)]
        field_simp

/-- M-block per-factor inequality: for a finite family of arguments `θ : ι → ℝ`
indexed over `S : Finset ι`,
`|cos(∑_{p∈S} θ_p) − ∏_{p∈S} cos θ_p| ≤ ∑_{(p,q)∈S.offDiag} (1/2)·|θ_p|·|θ_q|`.
The factor `1/2` accounts for each unordered pair being counted twice. -/
lemma abs_cos_sum_sub_prod_cos_le_sum_offDiag
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (θ : ι → ℝ) :
    |Real.cos (∑ p ∈ S, θ p) - ∏ p ∈ S, Real.cos (θ p)|
      ≤ ∑ pq ∈ S.offDiag, (1/2 : ℝ) * |θ pq.1| * |θ pq.2| := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S has ih =>
    rw [Finset.sum_insert has, Finset.prod_insert has]
    set sumS : ℝ := ∑ p ∈ S, θ p with hsumS
    set prodS : ℝ := ∏ p ∈ S, Real.cos (θ p) with hprodS
    -- Decompose: cos(θ_a + Σ) - cos θ_a · Π
    --   = [cos(θ_a + Σ) - cos θ_a · cos Σ] + cos θ_a · [cos Σ - Π]
    --   = -sin θ_a · sin Σ + cos θ_a · [cos Σ - Π]
    have hkey : Real.cos (θ a + sumS) - Real.cos (θ a) * prodS
        = -(Real.sin (θ a) * Real.sin sumS) + Real.cos (θ a) * (Real.cos sumS - prodS) := by
      rw [Real.cos_add]; ring
    rw [hkey]
    -- Triangle inequality
    have hbound1 :
        |-(Real.sin (θ a) * Real.sin sumS) + Real.cos (θ a) * (Real.cos sumS - prodS)|
        ≤ |Real.sin (θ a) * Real.sin sumS|
          + |Real.cos (θ a) * (Real.cos sumS - prodS)| := by
      calc |-(Real.sin (θ a) * Real.sin sumS) + Real.cos (θ a) * (Real.cos sumS - prodS)|
          ≤ |-(Real.sin (θ a) * Real.sin sumS)|
              + |Real.cos (θ a) * (Real.cos sumS - prodS)| :=
            abs_add_le _ _
        _ = |Real.sin (θ a) * Real.sin sumS|
              + |Real.cos (θ a) * (Real.cos sumS - prodS)| := by
            rw [abs_neg]
    -- Bound first term: |sin θ_a · sin sumS| ≤ |θ_a| · |sumS| ≤ |θ_a| · ∑|θ_p|
    have habs_sum : |sumS| ≤ ∑ p ∈ S, |θ p| := by
      simp only [hsumS]; exact Finset.abs_sum_le_sum_abs _ _
    have hsin_term : |Real.sin (θ a) * Real.sin sumS| ≤ |θ a| * ∑ p ∈ S, |θ p| := by
      rw [abs_mul]
      have h1 : |Real.sin (θ a)| ≤ |θ a| := Real.abs_sin_le_abs
      have h2 : |Real.sin sumS| ≤ |sumS| := Real.abs_sin_le_abs
      calc |Real.sin (θ a)| * |Real.sin sumS|
          ≤ |θ a| * |sumS| := by
            apply mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
        _ ≤ |θ a| * ∑ p ∈ S, |θ p| := by
            apply mul_le_mul_of_nonneg_left habs_sum (abs_nonneg _)
    -- Bound second term: |cos θ_a · (cos sumS - prodS)| ≤ |cos sumS - prodS|
    have hcos_term : |Real.cos (θ a) * (Real.cos sumS - prodS)| ≤ |Real.cos sumS - prodS| := by
      rw [abs_mul]
      calc |Real.cos (θ a)| * |Real.cos sumS - prodS|
          ≤ 1 * |Real.cos sumS - prodS| := by
            apply mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |Real.cos sumS - prodS| := by ring
    -- Combine using IH: |cos sumS - prodS| ≤ ∑_{(p,q)∈S.offDiag} (1/2)|θ_p||θ_q|
    have hih : |Real.cos sumS - prodS|
        ≤ ∑ pq ∈ S.offDiag, (1/2 : ℝ) * |θ pq.1| * |θ pq.2| := ih
    -- Now expand (insert a S).offDiag.
    -- Note: `Finset.offDiag_insert` takes the element `a` as an explicit
    -- first argument (Mathlib `variable (a : α)` ahead of the theorem),
    -- with `s` implicit; pass `a` explicitly to avoid metavariable unification
    -- failure flagged by Mathlib API drift in earlier rounds.
    have hoffDiag : (insert a S).offDiag
        = S.offDiag ∪ ({a} ×ˢ S) ∪ (S ×ˢ {a}) :=
      Finset.offDiag_insert a has
    -- Disjointness: S.offDiag is disjoint from {a}×ˢS (first coord ≠ a) and S×ˢ{a} (second ≠ a),
    -- and {a}×ˢS is disjoint from S×ˢ{a} since a ∉ S.
    have hd_S_aS : Disjoint S.offDiag (({a} : Finset ι) ×ˢ S) := by
      rw [Finset.disjoint_left]
      rintro ⟨p, q⟩ hpq h2
      rw [Finset.mem_product, Finset.mem_singleton] at h2
      rw [Finset.mem_offDiag] at hpq
      obtain ⟨hpa, _⟩ := h2
      exact has (hpa ▸ hpq.1)
    have hd_S_Sa : Disjoint S.offDiag (S ×ˢ ({a} : Finset ι)) := by
      rw [Finset.disjoint_left]
      rintro ⟨p, q⟩ hpq h2
      rw [Finset.mem_product, Finset.mem_singleton] at h2
      rw [Finset.mem_offDiag] at hpq
      obtain ⟨_, hqa⟩ := h2
      exact has (hqa ▸ hpq.2.1)
    have hd_aS_Sa : Disjoint (({a} : Finset ι) ×ˢ S) (S ×ˢ ({a} : Finset ι)) := by
      rw [Finset.disjoint_left]
      rintro ⟨p, q⟩ h1 h2
      rw [Finset.mem_product, Finset.mem_singleton] at h1 h2
      exact has (h1.1 ▸ h2.1)
    -- Sum decomposition over (insert a S).offDiag
    have hd_first : Disjoint (S.offDiag ∪ ({a} ×ˢ S)) (S ×ˢ ({a} : Finset ι)) :=
      Finset.disjoint_union_left.mpr ⟨hd_S_Sa, hd_aS_Sa⟩
    have hsum_split : ∑ pq ∈ (insert a S).offDiag, (1/2 : ℝ) * |θ pq.1| * |θ pq.2|
        = (∑ pq ∈ S.offDiag, (1/2 : ℝ) * |θ pq.1| * |θ pq.2|)
          + (∑ pq ∈ ({a} ×ˢ S : Finset (ι × ι)), (1/2 : ℝ) * |θ pq.1| * |θ pq.2|)
          + (∑ pq ∈ (S ×ˢ {a} : Finset (ι × ι)), (1/2 : ℝ) * |θ pq.1| * |θ pq.2|) := by
      rw [hoffDiag, Finset.sum_union hd_first, Finset.sum_union hd_S_aS]
    -- Compute each piece
    have hsum_aS : (∑ pq ∈ ({a} ×ˢ S : Finset (ι × ι)), (1/2 : ℝ) * |θ pq.1| * |θ pq.2|)
        = (1/2 : ℝ) * |θ a| * ∑ p ∈ S, |θ p| := by
      rw [Finset.sum_product]
      simp only [Finset.sum_singleton]
      rw [Finset.mul_sum]
    have hsum_Sa : (∑ pq ∈ (S ×ˢ {a} : Finset (ι × ι)), (1/2 : ℝ) * |θ pq.1| * |θ pq.2|)
        = (1/2 : ℝ) * (∑ p ∈ S, |θ p|) * |θ a| := by
      rw [Finset.sum_product]
      simp only [Finset.sum_singleton]
      rw [show (∑ x ∈ S, (1/2 : ℝ) * |θ x| * |θ a|)
          = ∑ x ∈ S, ((1/2 : ℝ) * |θ a|) * |θ x| from
        Finset.sum_congr rfl (fun x _ => by ring)]
      rw [← Finset.mul_sum]; ring
    -- Now chain everything
    calc |-(Real.sin (θ a) * Real.sin sumS) + Real.cos (θ a) * (Real.cos sumS - prodS)|
        ≤ |Real.sin (θ a) * Real.sin sumS|
          + |Real.cos (θ a) * (Real.cos sumS - prodS)| := hbound1
      _ ≤ |θ a| * (∑ p ∈ S, |θ p|) + |Real.cos sumS - prodS| := by
          apply add_le_add hsin_term hcos_term
      _ ≤ |θ a| * (∑ p ∈ S, |θ p|)
          + ∑ pq ∈ S.offDiag, (1/2 : ℝ) * |θ pq.1| * |θ pq.2| := by
          gcongr
      _ = (∑ pq ∈ S.offDiag, (1/2 : ℝ) * |θ pq.1| * |θ pq.2|)
          + ((1/2 : ℝ) * |θ a| * ∑ p ∈ S, |θ p|)
          + ((1/2 : ℝ) * (∑ p ∈ S, |θ p|) * |θ a|) := by ring
      _ = ∑ pq ∈ (insert a S).offDiag, (1/2 : ℝ) * |θ pq.1| * |θ pq.2| := by
          rw [hsum_split, hsum_aS, hsum_Sa]

/-- M-scale cosine-product cross-block swap inequality (M-block generalisation of
`abs_cosProd_two_scale_swap`).

For `n ≥ 1`, `M : ℕ`, `δ : Fin M → ℝ` strictly positive, `t : Fin M → ℝ`, and
`θ_k^{(p)} = (√n)⁻¹ · t_p · exp(-δ_p · k / n)`,
`|∏cos(∑_p θ_k^{(p)}) − ∏_p ∏cos(θ_k^{(p)})|`
`  ≤ ∑_{(p,q)∈offDiag} |t_p|·|t_q| / (4·√(δ_p·δ_q))`.
The factor `4` (vs `2` in the two-block case) comes from each unordered pair
appearing twice in the symmetric `offDiag` sum. -/
theorem abs_cosProd_M_scale_swap
    (n : ℕ) (hn : 0 < n) {M : ℕ}
    (δ : Fin M → ℝ) (hδ : ∀ p, 0 < δ p) (t : Fin M → ℝ) :
    |∏ k ∈ Finset.Icc 1 n, Real.cos
        (∑ p, (Real.sqrt n)⁻¹ * (t p * Real.exp (-(δ p * k / n))))
     - ∏ p, ∏ k ∈ Finset.Icc 1 n, Real.cos
          ((Real.sqrt n)⁻¹ * (t p * Real.exp (-(δ p * k / n))))|
    ≤ ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
        |t pq.1| * |t pq.2| / (4 * Real.sqrt (δ pq.1 * δ pq.2)) := by
  -- Define θ : Fin M → ℕ → ℝ
  set θ : Fin M → ℕ → ℝ :=
    fun p k => (Real.sqrt n)⁻¹ * (t p * Real.exp (-(δ p * k / n))) with hθ_def
  -- Rewrite both sides in terms of θ
  have hLHS_eq : (fun k : ℕ => Real.cos
        (∑ p, (Real.sqrt ↑n)⁻¹ * (t p * Real.exp (-(δ p * ↑k / ↑n)))))
      = (fun k : ℕ => Real.cos (∑ p, θ p k)) := by
    funext k; rfl
  rw [show (∏ k ∈ Finset.Icc 1 n, Real.cos
              (∑ p, (Real.sqrt ↑n)⁻¹ * (t p * Real.exp (-(δ p * ↑k / ↑n)))))
        = ∏ k ∈ Finset.Icc 1 n, Real.cos (∑ p, θ p k) from rfl]
  rw [show (∏ p, ∏ k ∈ Finset.Icc 1 n, Real.cos
              ((Real.sqrt ↑n)⁻¹ * (t p * Real.exp (-(δ p * ↑k / ↑n)))))
        = ∏ p, ∏ k ∈ Finset.Icc 1 n, Real.cos (θ p k) from rfl]
  -- Combine ∏_p ∏_k = ∏_k ∏_p (Fubini for products)
  rw [Finset.prod_comm]
  -- Step 1: telescoping with u k = cos(∑θ), v k = ∏cos θ
  set u : ℕ → ℝ := fun k => Real.cos (∑ p, θ p k) with hu_def
  set v : ℕ → ℝ := fun k => ∏ p, Real.cos (θ p k) with hv_def
  have hu_bd : ∀ i ∈ Finset.Icc 1 n, |u i| ≤ 1 := fun i _ => Real.abs_cos_le_one _
  have hv_bd : ∀ i ∈ Finset.Icc 1 n, |v i| ≤ 1 := by
    intro i _
    simp only [v, abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
  have htel : |∏ i ∈ Finset.Icc 1 n, u i - ∏ i ∈ Finset.Icc 1 n, v i|
      ≤ ∑ i ∈ Finset.Icc 1 n, |u i - v i| :=
    abs_prod_sub_prod_le_sum_abs_sub _ u v hu_bd hv_bd
  -- Step 2: per-factor M-block bound
  have hpf : ∀ i ∈ Finset.Icc 1 n,
      |u i - v i| ≤ ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
        (1/2 : ℝ) * |θ pq.1 i| * |θ pq.2 i| := by
    intro i _
    simp only [u, v]
    exact abs_cos_sum_sub_prod_cos_le_sum_offDiag _ _
  have hsum_le : ∑ i ∈ Finset.Icc 1 n, |u i - v i|
      ≤ ∑ i ∈ Finset.Icc 1 n,
          ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
            (1/2 : ℝ) * |θ pq.1 i| * |θ pq.2 i| :=
    Finset.sum_le_sum hpf
  -- Step 3: swap sums (k ↔ pq)
  rw [Finset.sum_comm] at hsum_le
  -- Step 4: per-pair, |θ p k| · |θ q k| = |t p| |t q| / n · exp(-(δp+δq) k / n)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrtn_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrtn_pos
  have hsqrtn_sq : Real.sqrt n * Real.sqrt n = n :=
    Real.mul_self_sqrt hn_pos.le
  have hθ_abs : ∀ (p : Fin M) (k : ℕ),
      |θ p k| = (Real.sqrt n)⁻¹ * |t p| * Real.exp (-(δ p * (k : ℝ) / n)) := by
    intro p k
    have h1 : |(Real.sqrt n)⁻¹| = (Real.sqrt n)⁻¹ :=
      abs_of_pos (inv_pos.mpr hsqrtn_pos)
    have h2 : |Real.exp (-(δ p * (k : ℝ) / n))| = Real.exp (-(δ p * (k : ℝ) / n)) :=
      abs_of_pos (Real.exp_pos _)
    simp only [θ, abs_mul, h1, h2]; ring
  have hθθ_abs : ∀ (p q : Fin M) (k : ℕ),
      |θ p k| * |θ q k|
        = |t p| * |t q| / n * Real.exp (-((δ p + δ q) * (k : ℝ) / n)) := by
    intro p q k
    rw [hθ_abs p k, hθ_abs q k]
    have hexp_add : Real.exp (-(δ p * (k : ℝ) / n)) * Real.exp (-(δ q * (k : ℝ) / n))
        = Real.exp (-((δ p + δ q) * (k : ℝ) / n)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hinv_sq : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
      rw [← mul_inv, hsqrtn_sq]
    calc (Real.sqrt n)⁻¹ * |t p| * Real.exp (-(δ p * (k : ℝ) / n)) *
          ((Real.sqrt n)⁻¹ * |t q| * Real.exp (-(δ q * (k : ℝ) / n)))
        = ((Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹) * (|t p| * |t q|) *
          (Real.exp (-(δ p * (k : ℝ) / n)) * Real.exp (-(δ q * (k : ℝ) / n))) := by ring
      _ = (n : ℝ)⁻¹ * (|t p| * |t q|) * Real.exp (-((δ p + δ q) * (k : ℝ) / n)) := by
          rw [hinv_sq, hexp_add]
      _ = |t p| * |t q| / n * Real.exp (-((δ p + δ q) * (k : ℝ) / n)) := by
          rw [div_eq_inv_mul]; ring
  -- Step 5: per-pair bound by reindexing Icc 1 n -> range n + Riemann
  have hreidx_pair : ∀ (p q : Fin M),
      ∑ i ∈ Finset.Icc 1 n, (1/2 : ℝ) * |θ p i| * |θ q i|
        = ∑ k ∈ Finset.range n, (1/2 : ℝ) * (|t p| * |t q| / n) *
            Real.exp (-((δ p + δ q) * ((k : ℝ) + 1) / n)) := by
    intro p q
    rw [show (Finset.Icc 1 n) = (Finset.range n).image (· + 1) from ?_]
    · rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k _
        have : (1/2 : ℝ) * |θ p (k+1)| * |θ q (k+1)|
            = (1/2 : ℝ) * (|θ p (k+1)| * |θ q (k+1)|) := by ring
        rw [this, hθθ_abs p q (k+1)]
        push_cast; ring
      · intro a _ b _ h; exact Nat.add_right_cancel h
    · ext m; simp [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨m - 1, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩; omega
  -- Per-pair Riemann bound
  have hpair_bound : ∀ (p q : Fin M), p ≠ q →
      ∑ i ∈ Finset.Icc 1 n, (1/2 : ℝ) * |θ p i| * |θ q i|
        ≤ |t p| * |t q| / (4 * Real.sqrt (δ p * δ q)) := by
    intro p q _
    rw [hreidx_pair p q]
    have hδpq_pos : 0 < δ p + δ q := by linarith [hδ p, hδ q]
    -- Pull out constant factor
    have hsum_eq : ∑ k ∈ Finset.range n, (1/2 : ℝ) * (|t p| * |t q| / n) *
          Real.exp (-((δ p + δ q) * ((k : ℝ) + 1) / n))
        = (1/2 : ℝ) * (|t p| * |t q|) * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              Real.exp (-((δ p + δ q) * ((k : ℝ) + 1) / n))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [div_eq_inv_mul]; ring
    rw [hsum_eq]
    have hsum_riemann : ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          Real.exp (-((δ p + δ q) * ((k : ℝ) + 1) / n)))
        ≤ (δ p + δ q)⁻¹ :=
      sum_exp_neg_div_le_inv n hn hδpq_pos
    -- AM-GM: 1/(δp+δq) ≤ 1/(2√(δpδq))
    have hsqrtδp : 0 < Real.sqrt (δ p) := Real.sqrt_pos.mpr (hδ p)
    have hsqrtδq : 0 < Real.sqrt (δ q) := Real.sqrt_pos.mpr (hδ q)
    have hAMGM : 2 * Real.sqrt (δ p * δ q) ≤ δ p + δ q := by
      have h := two_mul_le_add_sq (Real.sqrt (δ p)) (Real.sqrt (δ q))
      rw [Real.sqrt_mul (hδ p).le]
      have hsq1 : (Real.sqrt (δ p)) ^ 2 = δ p := Real.sq_sqrt (hδ p).le
      have hsq2 : (Real.sqrt (δ q)) ^ 2 = δ q := Real.sq_sqrt (hδ q).le
      rw [hsq1, hsq2] at h
      linarith
    have h2sqrt_pos : 0 < 2 * Real.sqrt (δ p * δ q) := by
      apply mul_pos two_pos
      exact Real.sqrt_pos.mpr (mul_pos (hδ p) (hδ q))
    have hinv_le : (δ p + δ q)⁻¹ ≤ (2 * Real.sqrt (δ p * δ q))⁻¹ := by
      rw [show (δ p + δ q)⁻¹ = 1 / (δ p + δ q) by ring,
          show (2 * Real.sqrt (δ p * δ q))⁻¹ = 1 / (2 * Real.sqrt (δ p * δ q)) by ring]
      exact one_div_le_one_div_of_le h2sqrt_pos hAMGM
    have ht_nn : 0 ≤ (1/2 : ℝ) * (|t p| * |t q|) := by
      apply mul_nonneg (by norm_num)
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc (1/2 : ℝ) * (|t p| * |t q|) * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            Real.exp (-((δ p + δ q) * ((k : ℝ) + 1) / n)))
        ≤ (1/2 : ℝ) * (|t p| * |t q|) * (δ p + δ q)⁻¹ := by
          apply mul_le_mul_of_nonneg_left hsum_riemann ht_nn
      _ ≤ (1/2 : ℝ) * (|t p| * |t q|) * (2 * Real.sqrt (δ p * δ q))⁻¹ := by
          apply mul_le_mul_of_nonneg_left hinv_le ht_nn
      _ = |t p| * |t q| / (4 * Real.sqrt (δ p * δ q)) := by
          field_simp; ring
  -- Step 6: chain everything via the swapped sum
  -- We have: ∑_pq ∑_i (1/2)|θ_p i||θ_q i| ≤ ∑_pq |t_p||t_q|/(4√(δp δq))
  have hsum_pq_bound :
      ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
        ∑ i ∈ Finset.Icc 1 n, (1/2 : ℝ) * |θ pq.1 i| * |θ pq.2 i|
      ≤ ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
          |t pq.1| * |t pq.2| / (4 * Real.sqrt (δ pq.1 * δ pq.2)) := by
    apply Finset.sum_le_sum
    intro pq hpq
    rw [Finset.mem_offDiag] at hpq
    exact hpair_bound pq.1 pq.2 hpq.2.2
  -- Combine
  calc |∏ i ∈ Finset.Icc 1 n, u i - ∏ i ∈ Finset.Icc 1 n, v i|
      ≤ ∑ i ∈ Finset.Icc 1 n, |u i - v i| := htel
    _ ≤ ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
          ∑ i ∈ Finset.Icc 1 n, (1/2 : ℝ) * |θ pq.1 i| * |θ pq.2 i| := hsum_le
    _ ≤ ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
          |t pq.1| * |t pq.2| / (4 * Real.sqrt (δ pq.1 * δ pq.2)) := hsum_pq_bound

end Erdos524.Helpers
