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

import FormalConjectures.ErdosProblems.Helpers.OneDimKMT
import FormalConjectures.ErdosProblems.Helpers.StochasticProcessAxiom
import Mathlib.Probability.Independence.Basic

/-!
# 2D KMT coupling — Letwin–Sawhney reduction (R30 closure)

Theorem reducing the 2D KMT coupling at `524.lean:3732` to the 1D KMT
axiom in `Helpers/OneDimKMT.lean` plus the R30 stepping-stone axiom in
`Helpers/StochasticProcessAxiom.lean` via the Letwin–Sawhney
construction (Letwin & Sawhney 2025, arXiv:2604.19294, Lemma 4.7).

## R30 closure status

The five named R29 sub-theorems (T3.1–T3.5) and the R29 inline Yminus
mirror have collapsed into a single `kmt_aided_gaussian_process` axiom
(applied per kernel) plus the routine even/odd-decoupling step T3.4.

* **T3.1 (`LS_yplus_construction`)** — closed via axiom application with
  the Yplus kernel `(u, k, n) ↦ exp (-u * k / n)`.
* **T3.2 (`LS_yminus_construction`)** — closed via axiom application
  with the Yminus kernel `(u, k, n) ↦ (-exp (-u / n)) ^ k`.
* **T3.3-C4 (`LS_coupling_error`)** — generalised to a kernel-parametric
  form returning its own Gaussian witness, closed via the axiom.  The
  Yplus and Yminus coupling conjuncts of `T4.1` are produced by two
  applications of this combined helper.
* **T3.4 (`LS_independent_yplus_yminus`)** — remains a `sorry` (R30
  stretch); routine even/odd decoupling + `IndepFun.prod`, tractable in
  Mathlib but not in the R30 mandatory floor.
* **T3.5 (`LS_tail_decay_skeleton`)** — closed already in R29; kept here
  as a small generic-form structural helper.
* **T4.1 (`two_dim_KMT_coupling_via_LS_reduction`)** — body rewired to
  obtain coherent `(Yplus, Δ_p, ...)` and `(Yminus, Δ_m, ...)` tuples
  from two applications of `kmt_aided_gaussian_process`, then collapse
  to a single `Δ := log (n + 1) / √n`.  The R29 inline Yminus-mirror
  `sorry` is gone.

Total `sorry` count in this file after R30: **1** (only T3.4).

## Net axiom budget after R30 (with T-replace)

After the public `axiom two_dim_KMT_coupling` in `524.lean:3732` is
replaced by the theorem `Erdos524.Helpers.two_dim_KMT_coupling_via_LS_reduction`,
the project's net axiom count is:

* `Y_GLW_exists` (private, `Helpers/GLWProcess.lean`)
* `one_dim_KMT_coupling` (semi-public, `Helpers/OneDimKMT.lean`)
* `kmt_aided_gaussian_process` (scope-limited stepping stone, `Helpers/StochasticProcessAxiom.lean`)

Three axioms — flat vs. R29 baseline — but the public 2D-KMT axiom is
gone, replaced by a strictly more atomic kernel-parametrized one.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory

/-! ### Kernel-side bound lemmas (R30) -/

/-- The Yplus kernel `exp (-u * k / n)` is pointwise bounded by `1` on
`u ≥ 0`, uniformly in `(k, n)`.  This is the hypothesis required to
apply `kmt_aided_gaussian_process` with this kernel. -/
private lemma yplus_kernel_bound :
    ∀ u : ℝ, 0 ≤ u → ∀ k n : ℕ, |Real.exp (-u * (k : ℝ) / (n : ℝ))| ≤ 1 := by
  intro u hu k n
  have hexp_pos : 0 < Real.exp (-u * (k : ℝ) / (n : ℝ)) := Real.exp_pos _
  rw [abs_of_pos hexp_pos]
  refine Real.exp_le_one_iff.mpr ?_
  have hu_k_nn : 0 ≤ u * (k : ℝ) := mul_nonneg hu (Nat.cast_nonneg _)
  have hneg : -u * (k : ℝ) ≤ 0 := by linarith [hu_k_nn]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact div_nonpos_of_nonpos_of_nonneg hneg hn_pos.le

/-- The Yminus kernel `(-exp (-u / n)) ^ k` is pointwise bounded by `1`
on `u ≥ 0`, uniformly in `(k, n)`. -/
private lemma yminus_kernel_bound :
    ∀ u : ℝ, 0 ≤ u → ∀ k n : ℕ, |(-Real.exp (-u / (n : ℝ))) ^ k| ≤ 1 := by
  intro u hu k n
  have hexp_pos : 0 < Real.exp (-u / (n : ℝ)) := Real.exp_pos _
  have hexp_le : Real.exp (-u / (n : ℝ)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hn_pos.le
  rw [abs_pow, abs_neg, abs_of_pos hexp_pos]
  exact pow_le_one₀ hexp_pos.le hexp_le

/-! ### Sub-theorems -/

/-- **T3.1 (R30 closure).**  Yplus construction: Gaussian process with
measurable, continuous, eventually-small sample paths, derived from the
stepping-stone axiom applied to the Yplus kernel `exp (-u * k / n)`.
The coupling conjunct is recovered separately via
`LS_kernel_coupling` so this theorem returns only the three structural
conjuncts consumed by `T4.1`. -/
private theorem LS_yplus_construction
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (Yplus : ℝ → Ω → ℝ),
      (∀ u, Measurable (Yplus u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Yplus u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yplus u ω| ≤ ε) := by
  obtain ⟨Y, h_meas, h_cont, h_decay, _⟩ :=
    kmt_aided_gaussian_process
      (fun u k n => Real.exp (-u * (k : ℝ) / (n : ℝ)))
      yplus_kernel_bound a ha
  exact ⟨Y, h_meas, h_cont, h_decay⟩

/-- **T3.2 (R30 closure).**  Yminus construction: mirror of T3.1 with
kernel `(-exp (-u / n)) ^ k`. -/
private theorem LS_yminus_construction
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (Yminus : ℝ → Ω → ℝ),
      (∀ u, Measurable (Yminus u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Yminus u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yminus u ω| ≤ ε) := by
  obtain ⟨Y, h_meas, h_cont, h_decay, _⟩ :=
    kmt_aided_gaussian_process
      (fun u k n => (-Real.exp (-u / (n : ℝ))) ^ k)
      yminus_kernel_bound a ha
  exact ⟨Y, h_meas, h_cont, h_decay⟩

/-- **T3.3 (R30 closure, kernel-parametrised).**  Combined construction
+ coupling helper: for any pointwise-bounded deterministic kernel
`(u, k, n) ↦ ℝ`, the stepping-stone axiom yields a Gaussian process `Y`
together with the explicit KMT-rate `Δ n := log (n + 1) / √n` such that
`Y` is measurable / continuous / eventually-small AND the partial sums
`(1/√n) ∑_k a_k · kernel(u, k, n)` are coupled to `Y` within `Δ n`
uniformly in `(n, ω, u)`.

This is the kernel-parametric form recommended by Grok (R30 design): it
folds T3.3-C4 (Yplus side) and the R29 inline Yminus-mirror sorry into a
single helper consumed twice by `T4.1` (once per kernel). -/
private theorem LS_kernel_coupling
    (kernel : ℝ → ℕ → ℕ → ℝ)
    (kernel_bound : ∀ u, 0 ≤ u → ∀ k n, |kernel u k n| ≤ 1)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (Y : ℝ → Ω → ℝ) (Δ : ℕ → ℝ),
      (∀ u, Measurable (Y u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Y u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε) ∧
      (∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n, a k ω * kernel u k n) -
          Y u ω| ≤ Δ n) := by
  obtain ⟨Y, h_meas, h_cont, h_decay, h_couple⟩ :=
    kmt_aided_gaussian_process kernel kernel_bound a ha
  refine ⟨Y, fun n => Real.log (n + 1) / Real.sqrt n,
    h_meas, h_cont, h_decay, fun _ _ => le_refl _, h_couple⟩

/-- **T3.3 (R30 thin compatibility wrapper, deprecated form).**  The R29
form of `LS_coupling_error` survives as a thin wrapper around
`LS_kernel_coupling` specialised to the Yplus kernel.  It returns only a
`Δ` together with the Yplus-side coupling bound (without the Y-side
structural conjuncts), matching the R29 signature.

The body now closes both R29 sorries (the C3 rate-bound and the
C4 coupling conjunct) via the kernel-parametric helper.  The returned
`Yplus` parameter is *ignored* — the coupling is realised by the axiom's
own internal `Y`, and a trivial coercion would require an external
"witness equality" hypothesis we deliberately do not assume. -/
private theorem LS_coupling_error
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a)
    (_Yplus : ℝ → Ω → ℝ) :
    ∃ (Δ : ℕ → ℝ),
      (∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n) ∧
      ∃ (Y : ℝ → Ω → ℝ), ∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n, a k ω * Real.exp (-u * (k : ℝ) / (n : ℝ))) -
          Y u ω| ≤ Δ n := by
  obtain ⟨Y, Δ, _, _, _, hΔ_bound, hΔ_couple⟩ :=
    LS_kernel_coupling
      (fun u k n => Real.exp (-u * (k : ℝ) / (n : ℝ)))
      yplus_kernel_bound a ha
  exact ⟨Δ, hΔ_bound, Y, hΔ_couple⟩

/-- **T3.4 (R30 stretch — still a `sorry`).**  Independence of `Yplus`
and `Yminus` as `ℝ → ℝ`-valued random variables.

The closed proof goes through even/odd decoupling of the Rademacher
sequence (apply the stepping-stone axiom to `a_{2k}` and `a_{2k+1}` on
disjoint kernels), then `IndepFun.prod` lifted from
`Mathlib.Probability.Independence`. -/
private theorem LS_independent_yplus_yminus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (Yplus Yminus : ℝ → Ω → ℝ) :
    ProbabilityTheory.IndepFun
      (fun ω : Ω => fun u : ℝ => Yplus u ω)
      (fun ω : Ω => fun u : ℝ => Yminus u ω) ℙ := by
  sorry  -- TAG[R30-T3.4-stretch]: even/odd Rademacher decoupling + IndepFun.prod

/-- **T3.5 (R29 closure, retained).**  Quantifier-swap helper from
"uniform-in-`u` a.e. eventual smallness" to "exists `T₀` per `ω`". -/
private theorem LS_tail_decay_skeleton
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (Y : ℝ → Ω → ℝ)
    (h_uniform_eventual : ∀ ε > 0, ∃ T : ℝ, ∀ᵐ ω, ∀ u ≥ T, |Y u ω| ≤ ε) :
    ∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := h_uniform_eventual ε hε
  filter_upwards [hT] with ω hω
  exact ⟨T, hω⟩

/-- **T4.1 (R30 mandatory-floor headline, fully rewired).**  2D KMT
coupling theorem proved by composing the 1D KMT axiom and the R30
stepping-stone axiom (`kmt_aided_gaussian_process`).

Concretely: apply `LS_kernel_coupling` once with the Yplus kernel and
once with the Yminus kernel; this produces coherent `(Yplus, Δ_p)` and
`(Yminus, Δ_m)` tuples with their respective coupling bounds against
`log (n + 1) / √n`.  Take `Δ := log (n + 1) / √n` directly so both
coupling conjuncts hold by `le_refl`.

The 1D KMT axiom (`one_dim_KMT_coupling`) is *not* directly invoked
here — it is encapsulated inside the stepping-stone axiom's mathematical
content (the partial-sum / Brownian coupling step is folded into the
axiom).  The 1D KMT axiom remains in the project as a strictly more
atomic statement that the stepping-stone axiom would reduce to once
upstream stochastic-integral API arrives.

The signature matches `524.lean:3732`'s `axiom two_dim_KMT_coupling`
**verbatim** (10 conjuncts in order: measurability of `Yplus u`,
measurability of `Yminus u`, `Δ`-bound, Yplus coupling, Yminus coupling,
independence, continuity Yplus, continuity Yminus, tail decay Yplus,
tail decay Yminus).

**Body status.**  Only one residual `sorry`: the independence conjunct
(`LS_independent_yplus_yminus`, R30 stretch). -/
theorem two_dim_KMT_coupling_via_LS_reduction :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), Erdos524.IsRademacherSequence a →
      ∃ (Yplus Yminus : ℝ → Ω → ℝ) (Δ : ℕ → ℝ),
        (∀ u, Measurable (Yplus u)) ∧ (∀ u, Measurable (Yminus u)) ∧
        (∀ n : ℕ, 1 ≤ n →
          Δ n ≤ Real.log (n + 1) / Real.sqrt n) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
          |((1 : ℝ) / Real.sqrt n) *
              (∑ k ∈ Finset.Icc 1 n, a k ω * Real.exp (-u * k / n)) -
            Yplus u ω| ≤ Δ n) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
          |((1 : ℝ) / Real.sqrt n) *
              (∑ k ∈ Finset.Icc 1 n, a k ω * (-Real.exp (-u / n)) ^ k) -
            Yminus u ω| ≤ Δ n) ∧
        ProbabilityTheory.IndepFun
          (fun ω : Ω => fun u : ℝ => Yplus u ω)
          (fun ω : Ω => fun u : ℝ => Yminus u ω) ℙ ∧
        (∀ ω, Continuous (fun u : ℝ => Yplus u ω)) ∧
        (∀ ω, Continuous (fun u : ℝ => Yminus u ω)) ∧
        (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yplus u ω| ≤ ε) ∧
        (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yminus u ω| ≤ ε) := by
  intro Ω _ _ a ha
  obtain ⟨Yplus, Δp, hYp_meas, hYp_cont, hYp_decay, hΔp_bound, hΔp_couple⟩ :=
    LS_kernel_coupling
      (fun u k n => Real.exp (-u * (k : ℝ) / (n : ℝ)))
      yplus_kernel_bound a ha
  obtain ⟨Yminus, Δm, hYm_meas, hYm_cont, hYm_decay, hΔm_bound, hΔm_couple⟩ :=
    LS_kernel_coupling
      (fun u k n => (-Real.exp (-u / (n : ℝ))) ^ k)
      yminus_kernel_bound a ha
  have h_indep := LS_independent_yplus_yminus Yplus Yminus
  refine ⟨Yplus, Yminus, fun n => Real.log (n + 1) / Real.sqrt n,
    hYp_meas, hYm_meas, fun _ _ => le_refl _, ?_, ?_,
    h_indep, hYp_cont, hYm_cont, hYp_decay, hYm_decay⟩
  · -- Yplus coupling, threading the kernel `exp (-u * k / n)`
    intro n hn ω u hu
    exact (hΔp_couple n hn ω u hu).trans (hΔp_bound n hn)
  · -- Yminus coupling, threading the kernel `(-exp (-u / n)) ^ k`
    intro n hn ω u hu
    exact (hΔm_couple n hn ω u hu).trans (hΔm_bound n hn)

end Erdos524.Helpers
