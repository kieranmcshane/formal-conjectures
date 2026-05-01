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
# 2D KMT coupling — Letwin–Sawhney reduction (R33-A Form β closure)

Theorem reducing the 2D KMT coupling at `524.lean:3732` to the 1D KMT
axiom in `Helpers/OneDimKMT.lean` plus the R33-A-tightened stepping-stone
axiom in `Helpers/StochasticProcessAxiom.lean` via the Letwin–Sawhney
construction (Letwin & Sawhney 2025, arXiv:2604.19294, Lemma 4.7).

## R33-A foundational correction (Form β)

The R30 closure (`two_dim_KMT_coupling_via_LS_reduction` in its R30 form)
was flagged by R31 audit and confirmed contradictory by the R32
foundational audit (`Helpers/AxiomFoundationAudit.md`): the
unconditional `IndepFun(Yplus, Yminus)` conjunct combined with full-sum
couplings at sub-CLT rate is mathematically unsatisfiable when both `Y±`
are functions of the same `(a_k)` Rademacher sequence.

**R33-A correction (Form β, paper-faithful Letwin–Sawhney Lemma 4.7):**
- Construct the witnesses on a product space `Ω' := Ω × Ω`.
- Apply the (R33-A-tightened) stepping-stone axiom on disjoint Rademacher
  sub-sequences (`a_even` from R31 lifted via `fst`, `a_odd` from R31
  lifted via `snd`).
- The resulting Yplus / Yminus are HALF-sum couplings (each over a
  half-sequence), and they are unconditionally independent on `Ω'` by
  the product-space construction (`indepFun_prod` in
  `Mathlib.Probability.Independence.Basic`).

## Form β file structure (R33-A → R33-B → R33-C)

* **Section 1 — R31 kernel/sequence infrastructure (kept).** The
  reparametrized kernel `kernel_even_plus`, its pointwise bound, the
  half-sequences `a_even` / `a_odd`, and their `IsRademacherSequence`
  derivations.  The R31 odd-minus kernel was deleted in R33-C as part
  of the linear-combo Form β consolidation (single plus-kernel applied
  to two sub-sequences).
* **Section 2 — R33-C T2.1 decay lemma.** Path A normalized L²-energy
  `kernel_even_plus_decay`, the R33-C-tightened second hypothesis to
  `kmt_aided_gaussian_process`.
* **Section 3 — R31 axiom applications.** `LS_yplus_via_even` (even
  sub-sequence) and `LS_y_odd_via_plus_kernel` (odd sub-sequence) — both
  threading `kernel_even_plus` + `kernel_even_plus_decay`.
* **Section 4 — Form β headline (R33-A T2.2 + T2.3 + R33-B T2.2).**
  `LS_independent_yplus_yminus_disjoint_blocks` (B1 corrected) and
  `two_dim_KMT_coupling_via_LS_reduction` (A4 corrected,
  R33-B linear-combo).

## What was deleted vs R30

The dead R30 helpers `LS_yplus_construction`, `LS_yminus_construction`,
`LS_kernel_coupling`, `LS_coupling_error` (and their kernel-bound
helpers `yplus_kernel_bound`, `yminus_kernel_bound`) are removed: they
fed into the R30 form of `two_dim_KMT_coupling_via_LS_reduction` which
was contradictory.  The contradictory `LS_independent_yplus_yminus`
(B1, "universal IndepFun on a single `Ω`") is replaced by the
product-space-correct `LS_independent_yplus_yminus_disjoint_blocks`.

## Net axiom budget after R33-A

The project's net axiom count is unchanged:

* `Y_GLW_exists` (private, `Helpers/GLWProcess.lean`)
* `one_dim_KMT_coupling` (semi-public, `Helpers/OneDimKMT.lean`)
* `kmt_aided_gaussian_process` (now with two hypotheses per R33-A
  Grok-validated tightening — `Helpers/StochasticProcessAxiom.lean`)

R33-B handles consumer migration (`524.lean:3732` and the four
downstream consumers) and the triangle bridge from half-sum to full-sum
small-ball lower bounds.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory

/-! ### Generic helpers (retained from R29) -/

/-- **R29 closure, retained.** Quantifier-swap helper from
"uniform-in-`u` a.e. eventual smallness" to "exists `T₀` per `ω`". Used
nowhere in the Form β proof, but preserved as a small generic-form
structural helper for downstream consumers in R33-B. -/
private theorem LS_tail_decay_skeleton
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (Y : ℝ → Ω → ℝ)
    (h_uniform_eventual : ∀ ε > 0, ∃ T : ℝ, ∀ᵐ ω, ∀ u ≥ T, |Y u ω| ≤ ε) :
    ∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := h_uniform_eventual ε hε
  filter_upwards [hT] with ω hω
  exact ⟨T, hω⟩

/-! ### Even/odd reparametrization (R31 T2.1 + T2.2 — infrastructure for R32 / R33-A)

The R31 consumer audit (`Helpers/R31APIScoping.md`) establishes that the
existing public `two_dim_KMT_coupling` shape (Y⁺ / Y⁻ approximating the
FULL discrete sums while being unconditionally independent) is
mathematically over-stated and that all four `524.lean` consumers of the
public theorem rely on the FULL-sum form, so a drop-in replacement by
the decoupled paper-faithful form is **not** consumer-compatible (R31
deferred T4.1 / T5.1 / T3.1 to R32).

The infrastructure in this section is what R32 will compose into the
mathematically-correct replacement, regardless of which corrective path
R32 chooses (joint-correlated form (α) or paper-faithful decoupled
form (β)). Specifically:

* **`kernel_even_plus`** is the kernel obtained from `exp(-u·k/n)` by
  substituting `k ↦ 2k`, compressing `m := n/2`, and inserting the
  `√(1/2)` factor that maintains the `1/√n` normalisation. After
  cancellation of the `2`s in numerator and denominator,
  `kernel_even_plus u k m = √(1/2) · exp(-u·k/m)`. Applied to
  `(a_{2j})_j` via `kmt_aided_gaussian_process`, it produces a Gaussian
  witness `Y_even` for the EVEN-indexed half of the FULL plus-kernel
  sum.

* **`kernel_odd_minus`** is the analogous kernel for the ODD-indexed
  half of the FULL minus-kernel sum
  `(1/√n) ∑_k a_k · (-exp(-u/n))^k`. The factor `(-1)^k` evaluated at
  odd `k = 2j+1` becomes `-1`, so the kernel carries an explicit
  negative sign: `kernel_odd_minus u k m = -√(1/2) · exp(-u·(2k+1)/(2m))`.

The two `LS_*_via_*` theorems below are the two axiom applications the
brief specifies (T2.2). Both go through verbatim because the actual
`kmt_aided_gaussian_process` axiom takes a pointwise `|kernel| ≤ 1`
hypothesis (not the originally-briefed geometric-decay hypothesis), and
both kernels satisfy the tighter pointwise bound `|·| ≤ √(1/2) ≤ 1`. -/

/-- **R31 / T2.1.** Reparametrized kernel for the EVEN-indexed half of
the FULL plus-kernel sum. Derived from `(u, k, n) ↦ exp(-u·k/n)` by:
substituting `2k` for `k` (even-indexing in the original sum),
compressing `m := n/2` (the new sequence length is half the original),
and inserting `√(1/2)` to maintain the `1/√n` normalization (since
`1/√n = √(1/2) · 1/√(n/2)`). The doubled-`u` and doubled-`m` from the
substitution cancel, leaving `√(1/2) · exp(-u·k/m)`. -/
private noncomputable def kernel_even_plus (u : ℝ) (k m : ℕ) : ℝ :=
  Real.sqrt (1/2) * Real.exp (-u * (k : ℝ) / (m : ℝ))

/-- **R31 / T2.1.a.** Pointwise bound `|kernel_even_plus u k m| ≤ 1`,
for `u ≥ 0`. This is the hypothesis required by the
`kmt_aided_gaussian_process` axiom. The proof uses
`|√(1/2)| ≤ 1` and `|exp(non-positive)| ≤ 1`. -/
private lemma kernel_even_plus_bound :
    ∀ u : ℝ, 0 ≤ u → ∀ k m : ℕ, |kernel_even_plus u k m| ≤ 1 := by
  intro u hu k m
  unfold kernel_even_plus
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (1/2) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_le_one : Real.sqrt (1/2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hexp_pos : 0 < Real.exp (-u * (k : ℝ) / (m : ℝ)) := Real.exp_pos _
  have hexp_le_one : Real.exp (-u * (k : ℝ) / (m : ℝ)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hu_k_nn : 0 ≤ u * (k : ℝ) := mul_nonneg hu (Nat.cast_nonneg _)
    have hneg : -u * (k : ℝ) ≤ 0 := by linarith [hu_k_nn]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact div_nonpos_of_nonpos_of_nonneg hneg hm_pos.le
  rw [abs_mul, abs_of_pos hsqrt_pos, abs_of_pos hexp_pos]
  calc Real.sqrt (1/2) * Real.exp (-u * (k : ℝ) / (m : ℝ))
      ≤ 1 * 1 :=
        mul_le_mul hsqrt_le_one hexp_le_one hexp_pos.le (by norm_num)
    _ = 1 := mul_one _

/-! ### R33-C / T2.1 — kernel decay lemma (Path A normalized L²-energy)

R33-C / T2.1 replaces the wrong-shape pointwise eventual-smallness
hypothesis (R33-A literal-Grok form, R33-B `1 ≤ k` retightening) with
the **Path A normalized L²-energy** form (Grok-validated R33-C):

```
kernel_decay : ∀ ε > 0, ∃ U > 0, ∀ n ≥ 1, ∀ u ≥ U,
    (1/n) · ∑_{k=1..n} (kernel u k n)² ≤ ε.
```

This form is satisfiable for `kernel_even_plus` with explicit witness
`U := 1/(4ε)`. The proof rewrites the squared kernel as
`(1/2) · exp(−2uk/n)`, bounds the geometric sum
`∑_{k=1..n} exp(−2uk/n)` via `a/(eᵃ − 1) ≤ 1` with `a = 2u/n`, and
combines the constants to get `(1/n) · ∑ ≤ 1/(4u) ≤ ε` for `u ≥ U`.

The dead `kernel_odd_minus` family (`kernel_odd_minus`,
`kernel_odd_minus_bound`, `kernel_odd_minus_decay`,
`LS_yminus_via_odd`) was deleted in R33-C: the linear-combo Form β
uses only `kernel_even_plus` (applied to both `a_even` and `a_odd`),
so the odd-minus kernel is no longer referenced. -/

/-- **R33-C / T2.1 sub-helper.** For `a > 0` and `n : ℕ`,
`∑_{k=1..n} exp(-a·k) ≤ 1/a`.  Proof: the partial sum
`S = ∑_{k=1..n} exp(-a·k)` satisfies `(exp a - 1) · S = 1 - exp(-a·n) ≤ 1`
(by telescoping with `(exp a - 1) exp(-a·k) = exp(-a·(k-1)) - exp(-a·k)`),
and `exp a - 1 ≥ a` (from `Real.add_one_le_exp`), hence `S ≤ 1/a`. -/
private lemma sum_exp_neg_mul_le_one_div {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, Real.exp (-(a * (k : ℝ))) ≤ 1 / a := by
  have h_exp_a_pos : 0 < Real.exp a := Real.exp_pos a
  have h_exp_lb : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
  have h_exp_a_sub_pos : 0 < Real.exp a - 1 := by linarith
  -- Telescoping identity by induction on m.
  have h_telescope : ∀ m : ℕ,
      (Real.exp a - 1) *
          ∑ k ∈ Finset.Icc 1 m, Real.exp (-(a * (k : ℝ)))
        = 1 - Real.exp (-(a * (m : ℝ))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h_Icc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have h_not_mem : (m + 1) ∉ Finset.Icc 1 m := by
        simp [Finset.mem_Icc]
      rw [h_Icc, Finset.sum_insert h_not_mem, mul_add, ih]
      -- Goal: 1 - exp(-(a*m)) + (exp a - 1) * exp(-(a*(m+1))) = 1 - exp(-(a*(m+1))).
      have h_exp_diff :
          Real.exp a * Real.exp (-(a * ((m + 1 : ℕ) : ℝ)))
            = Real.exp (-(a * (m : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      have h_step :
          (Real.exp a - 1) * Real.exp (-(a * ((m + 1 : ℕ) : ℝ)))
            = Real.exp (-(a * (m : ℝ))) -
              Real.exp (-(a * ((m + 1 : ℕ) : ℝ))) := by
        have : Real.exp a * Real.exp (-(a * ((m + 1 : ℕ) : ℝ)))
              - Real.exp (-(a * ((m + 1 : ℕ) : ℝ)))
            = Real.exp (-(a * (m : ℝ))) -
              Real.exp (-(a * ((m + 1 : ℕ) : ℝ))) := by
          rw [h_exp_diff]
        linarith
      linarith
  -- (exp a - 1) * S = 1 - exp(-(a*n)) ≤ 1.
  have h_exp_neg_pos : 0 < Real.exp (-(a * (n : ℝ))) := Real.exp_pos _
  have h_le_one :
      (Real.exp a - 1) *
          ∑ k ∈ Finset.Icc 1 n, Real.exp (-(a * (k : ℝ))) ≤ 1 := by
    rw [h_telescope n]; linarith
  -- Hence S ≤ 1/(exp a - 1) ≤ 1/a.
  have h_S :
      ∑ k ∈ Finset.Icc 1 n, Real.exp (-(a * (k : ℝ)))
        ≤ 1 / (Real.exp a - 1) := by
    rw [le_div_iff₀ h_exp_a_sub_pos, mul_comm]
    exact h_le_one
  have h_a_le : a ≤ Real.exp a - 1 := by linarith
  exact h_S.trans (one_div_le_one_div_of_le ha h_a_le)

/-- **R33-C / T2.1.** `kernel_decay` for `kernel_even_plus` in the Path A
normalized L²-energy form. The witness `U := 1/(4ε)` follows from
`(kernel_even_plus u k n)² = (1/2) · exp(-2u·k/n)`, the geometric-sum
bound `∑_{k=1..n} exp(-2u·k/n) ≤ n/(2u)` (via
`sum_exp_neg_mul_le_one_div` at `a = 2u/n`), and the chain
`(1/n) · (1/2) · n/(2u) = 1/(4u) ≤ ε` for `u ≥ U`. -/
private lemma kernel_even_plus_decay :
    ∀ ε > 0, ∃ U > 0, ∀ n : ℕ, 1 ≤ n → ∀ u ≥ U,
      (1 / (n : ℝ)) *
        (Finset.Icc 1 n).sum (fun k => (kernel_even_plus u k n) ^ 2) ≤ ε := by
  intro ε hε
  refine ⟨1 / (4 * ε), by positivity, fun n hn u hu => ?_⟩
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_n_pos_nz : (n : ℝ) ≠ 0 := ne_of_gt h_n_pos
  have h_U_pos : (0 : ℝ) < 1 / (4 * ε) := by positivity
  have h_u_pos : 0 < u := lt_of_lt_of_le h_U_pos hu
  -- Step 1: rewrite each squared kernel as (1/2) * exp(-(2u/n) * k).
  have h_sq : ∀ k : ℕ, (kernel_even_plus u k n) ^ 2
      = (1/2) * Real.exp (-((2 * u / n) * (k : ℝ))) := by
    intro k
    unfold kernel_even_plus
    rw [mul_pow]
    have h1 : (Real.sqrt (1/2))^2 = 1/2 :=
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)
    have h2 : (Real.exp (-u * (k : ℝ) / (n : ℝ)))^2
        = Real.exp (-((2 * u / n) * (k : ℝ))) := by
      rw [sq, ← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [h1, h2]
  -- Step 2: sum and factor out (1/2).
  have h_sum_eq :
      (Finset.Icc 1 n).sum (fun k => (kernel_even_plus u k n) ^ 2)
        = (1/2) * ∑ k ∈ Finset.Icc 1 n,
            Real.exp (-((2 * u / n) * (k : ℝ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _; exact h_sq k
  rw [h_sum_eq]
  -- Step 3: apply sum_exp_neg_mul_le_one_div with a = 2u/n.
  have h_a_pos : (0 : ℝ) < 2 * u / n := by positivity
  have h_geom :
      ∑ k ∈ Finset.Icc 1 n, Real.exp (-((2 * u / n) * (k : ℝ)))
        ≤ 1 / (2 * u / n) :=
    sum_exp_neg_mul_le_one_div h_a_pos n
  -- Step 4: combine factors. (1/n) * (1/2) * (1/(2u/n)) = 1/(4u).
  have h_simplify : (1 / (n : ℝ)) * ((1/2) * (1 / (2 * u / n))) = 1 / (4 * u) := by
    field_simp
    ring
  -- Step 5: 1/(4u) ≤ ε from u ≥ 1/(4ε).
  have h_u_gt : 1 / (4 * ε) ≤ u := hu
  have h_4u_pos : 0 < 4 * u := by positivity
  have h_4ε_pos : 0 < 4 * ε := by positivity
  have h_inv : 1 / (4 * u) ≤ ε := by
    rw [div_le_iff₀ h_4u_pos]
    have h_mul : 4 * u * ε ≥ 4 * (1 / (4 * ε)) * ε := by
      have : 4 * u ≥ 4 * (1 / (4 * ε)) := by linarith
      nlinarith [hε]
    have h_simplify2 : 4 * (1 / (4 * ε)) * ε = 1 := by
      field_simp
    linarith
  calc (1 / (n : ℝ)) * ((1/2) *
          ∑ k ∈ Finset.Icc 1 n, Real.exp (-((2 * u / n) * (k : ℝ))))
      ≤ (1 / (n : ℝ)) * ((1/2) * (1 / (2 * u / n))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left h_geom (by norm_num)
        · exact div_nonneg one_pos.le h_n_pos.le
    _ = 1 / (4 * u) := h_simplify
    _ ≤ ε := h_inv

/-- **R31 / T2.2 (helper).** The even sub-sequence `k ↦ a (2*k)`. -/
private def a_even {Ω : Type*} (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k ω => a (2 * k) ω

/-- **R31 / T2.2 (helper).** The odd sub-sequence `k ↦ a (2*k + 1)`. -/
private def a_odd {Ω : Type*} (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k ω => a (2 * k + 1) ω

/-- **R31 / T2.2 (helper); R33-C closure.** The even sub-sequence
inherits the i.i.d. Rademacher property from the parent sequence. The
`measurable / prob_pos / prob_neg` fields are direct specializations of
`ha` at index `2*k`; the `indep` field is closed via Mathlib's
`ProbabilityTheory.iIndepFun.precomp` applied to the injection
`g k := 2 * k`. -/
private lemma IsRademacherSequence_a_even
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    Erdos524.IsRademacherSequence (a_even a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- iIndepFun under sub-sequence selection k ↦ 2*k via precomp.
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by
      simpa using h
    have h := ha.indep.precomp (g := fun k : ℕ => 2 * k) hinj
    -- a_even a is definitionally `fun k => a (2 * k)`, matching `f ∘ g`.
    exact h
  · intro k; exact ha.measurable (2 * k)
  · intro k; exact ha.prob_pos (2 * k)
  · intro k; exact ha.prob_neg (2 * k)

/-- **R31 / T2.2 (helper); R33-C closure.** Mirror for the odd
sub-sequence, via the injection `g k := 2 * k + 1`. -/
private lemma IsRademacherSequence_a_odd
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    Erdos524.IsRademacherSequence (a_odd a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- iIndepFun under sub-sequence selection k ↦ 2*k + 1 via precomp.
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
      simpa using h
    have h := ha.indep.precomp (g := fun k : ℕ => 2 * k + 1) hinj
    exact h
  · intro k; exact ha.measurable (2 * k + 1)
  · intro k; exact ha.prob_pos (2 * k + 1)
  · intro k; exact ha.prob_neg (2 * k + 1)

/-- **R31 / T2.2.** First axiom application: produces a Gaussian witness
`Y_even` for the EVEN-indexed half of the FULL plus-kernel sum, by
applying `kmt_aided_gaussian_process` to `(a_even a, kernel_even_plus)`.

The output structural conjuncts (measurability, continuity, tail decay,
KMT coupling) are inherited verbatim from the axiom; consumers (R32) can
extract the EVEN-indexed identity
`(1/√m) ∑_{j=1..m} a (2*j) ω · √(1/2) · exp(-u·j/m)
   = (1/√(2m)) · ∑_{j=1..m} a (2*j) ω · exp(-u·(2*j)/(2m))`
to recover the half-sum interpretation. -/
private theorem LS_yplus_via_even
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (Y_even : ℝ → Ω → ℝ),
      (∀ u, Measurable (Y_even u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Y_even u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y_even u ω| ≤ ε) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt m) *
            (∑ k ∈ Finset.Icc 1 m, a_even a k ω * kernel_even_plus u k m) -
          Y_even u ω| ≤ Real.log (m + 1) / Real.sqrt m) :=
  kmt_aided_gaussian_process kernel_even_plus kernel_even_plus_bound
    kernel_even_plus_decay (a_even a) (IsRademacherSequence_a_even a ha)

/-- **R33-B / T2.2 (linear-combo construction).** Second axiom
application using the SAME plus-kernel `kernel_even_plus` as
`LS_yplus_via_even`, but on the ODD sub-sequence `a_odd`.  Produces a
Gaussian witness `Y_o` whose KMT coupling is against
`(a_odd, kernel_even_plus)`.

Together with `LS_yplus_via_even` (which produces `Y_e` against
`(a_even, kernel_even_plus)`), this is the pair of independent
processes the linear-combo Form β uses to build
`Yplus := Y_e + Y_o` and `Yminus := Y_e - Y_o`.

The key structural property: both Y_e and Y_o share the same kernel
+ same sequence-length parameter, so they are i.i.d. Gaussian
processes (when lifted to disjoint blocks of a product space).  This
i.i.d. property is what makes `Var(Y_e) = Var(Y_o)` in the brief's
covariance computation
`Cov(Y_e + Y_o, Y_e - Y_o) = Var(Y_e) - Var(Y_o) = 0`. -/
private theorem LS_y_odd_via_plus_kernel
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (Y_o : ℝ → Ω → ℝ),
      (∀ u, Measurable (Y_o u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Y_o u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y_o u ω| ≤ ε) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt m) *
            (∑ k ∈ Finset.Icc 1 m, a_odd a k ω * kernel_even_plus u k m) -
          Y_o u ω| ≤ Real.log (m + 1) / Real.sqrt m) :=
  kmt_aided_gaussian_process kernel_even_plus kernel_even_plus_bound
    kernel_even_plus_decay (a_odd a) (IsRademacherSequence_a_odd a ha)

/-! ### Section 4 — Form β headline (R33-B linear-combo correction)

The R33-A correction of A4 (`two_dim_KMT_coupling_via_LS_reduction`) and
B1 (`LS_independent_yplus_yminus`) used a "naive Form β" structure:
`Yplus = Y_even` (only even-plus summand) and `Yminus = Y_odd` (only
odd-minus summand), with half-sum couplings against the two
reparametrized kernels.

R33-B replaces this with the **linear-combo Form β** per Letwin–Sawhney
Lemma 3.3 (Grok R33-B response):

* Apply `kmt_aided_gaussian_process` twice with the *same* plus-kernel
  `kernel_even_plus`, once on `a_even` and once on `a_odd`.  This
  produces two i.i.d. Gaussian processes `Y_e` and `Y_o` (i.i.d. because
  same kernel, same sub-sequence law).
* Lift to the product space `Ω × Ω`: `Y_e` via `fst`, `Y_o` via `snd`.
* Define `Yplus := Y_e + Y_o` and `Yminus := Y_e - Y_o` (linear combo).

The structural advantages over the naive form:

1. **Full-sum control.** The combined coupling now bounds
   `(even-half + odd-half) - Yplus` and
   `(even-half - odd-half) - Yminus`, both sums having explicit
   summand-wise structure usable by downstream consumers (524.lean's
   triangle bridge in R33-C).
2. **Independence by Gaussian-uncorrelated → independent.**  In the
   joint Gaussian space spanned by `(Y_e, Y_o)`, the covariance
   `Cov(Y_e + Y_o, Y_e - Y_o) = Var(Y_e) - Var(Y_o) = 0` (i.i.d.), so
   the linear combinations are independent.  This requires Mathlib's
   `IsGaussian.iIndepFun_iff_zero_covariance` (or equivalent), which
   is a known API gap.

The R33-A `LS_independent_yplus_yminus_disjoint_blocks` lemma is
retained but is **no longer used** by the new `via_LS_reduction` body
(it bears witness to independence between two functions on the
product space lifted via `fst`/`snd`, but the linear combinations
intermix `fst` and `snd` and so don't fall under that lemma).  The
independence step in the new body uses a different argument
(Gaussian-uncorrelated → independent) and is TAG'd as a Mathlib API
gap.
-/

/-- **B1 (R33-A correction).** Independence of `Yplus` and `Yminus` as
`ℝ → ℝ`-valued random variables — the Form β replacement for the R30
contradictory `LS_independent_yplus_yminus`.

The R30 form claimed unconditional `IndepFun` between two functions of
the SAME `(a_k)` Rademacher sequence on a single `Ω`; R32 audit
established that this is mathematically impossible (both Y's are
deterministic-modulo-O(log n / √n) functions of the same input, ruling
out unconditional independence).

The Form β statement is independence-by-construction on a product space
`Ω₁ × Ω₂`, with `Yplus` lifted via `Prod.fst` and `Yminus` via
`Prod.snd`. This is mathematically true and discharged by Mathlib's
`indepFun_prod` lemma.

Hypotheses are the per-`u` measurability of each side (which lifts
through `measurable_pi_iff` to measurability of the curried form). -/
private theorem LS_independent_yplus_yminus_disjoint_blocks
    {Ω₁ Ω₂ : Type*}
    [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
    [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (Yplus : ℝ → Ω₁ → ℝ) (Yminus : ℝ → Ω₂ → ℝ)
    (h_meas_p : ∀ u, Measurable (Yplus u))
    (h_meas_m : ∀ u, Measurable (Yminus u)) :
    ProbabilityTheory.IndepFun
      (fun ω : Ω₁ × Ω₂ => fun u : ℝ => Yplus u ω.1)
      (fun ω : Ω₁ × Ω₂ => fun u : ℝ => Yminus u ω.2)
      ((ℙ : Measure Ω₁).prod (ℙ : Measure Ω₂)) :=
  indepFun_prod (measurable_pi_iff.mpr h_meas_p) (measurable_pi_iff.mpr h_meas_m)

/-- **A4 (R33-B linear-combo Form β).** 2D KMT coupling theorem in the
linear-combo Letwin–Sawhney form.

R33-A landed a "naive Form β" where Yplus / Yminus were single-summand
witnesses (Yplus = Y_even, Yminus = Y_odd via different kernels).  R33-B
replaces this with the **linear-combo Form β** per Grok R33-B response:

* Apply `kmt_aided_gaussian_process` twice with the *same* plus-kernel
  `kernel_even_plus`, once on `a_even` (→ `Y_e`) and once on `a_odd`
  (→ `Y_o`).  These are i.i.d. Gaussian processes (same kernel, same
  sub-sequence law).
* Lift to `Ω × Ω`: `Y_e` via `fst`, `Y_o` via `snd`.
* Define `Yplus := Y_e + Y_o` and `Yminus := Y_e - Y_o`.

The signature's coupling conjuncts now bound the **combined** half-sums
(even ± odd) against `Yplus` / `Yminus`, with `Δ_n = 2·log(n+1)/√n`
(factor `2` from the triangle inequality
`|F_even + F_odd - (Y_e + Y_o)| ≤ |F_even - Y_e| + |F_odd - Y_o|`).

**Signature note (kept from R33-A).** `Ω' := Ω × Ω` directly via
Mathlib's canonical `prod.measureSpace` instance.

**Coupling kernel (deviation from naive R33-A signature).** Both
coupling conjuncts use `kernel_even_plus` (the linear-combo brief's
single-kernel form), with the odd summand having a sign flip in the
Yminus conjunct.  The naive R33-A signature used `kernel_even_plus`
for Yplus and `kernel_odd_minus` for Yminus; the brief's R33-C
consumer migration will bridge to the original 524.lean
`exp(-uk/n)` / `(-exp(-u/n))^k` kernels via the sign-flip identity
`(-exp(-u/n))^(2k+1) = -(exp(-u/n))^(2k+1)` and a phase-shift
correction.

**Body status.** Two residual `sorry`s with TAG diagnostics:

* `?ha'` (T2.3): `IsRademacherSequence` lift on `Ω × Ω` with
  block-disjoint construction.  Mathlib API gap on lifting
  `iIndepFun` through product-space projections.  TAG[R33-B-T2.3-mathlib-gap].
* `?indep` (linear-combo IndepFun): `Yplus = Y_e + Y_o` and
  `Yminus = Y_e - Y_o` are linear combinations of the same independent
  pair `(Y_e, Y_o)`; the standard IndepFun-from-projection arguments do
  not apply.  Independence here requires the Gaussian-uncorrelated →
  independent property
  (`Cov(Y_e + Y_o, Y_e - Y_o) = Var(Y_e) - Var(Y_o) = 0` since `Y_e`,
  `Y_o` are i.i.d.).  TAG[R33-B-T2.2-gaussian-uncorrelated-indep].
-/
theorem two_dim_KMT_coupling_via_LS_reduction
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (a' : ℕ → Ω × Ω → ℝ) (_ha' : Erdos524.IsRademacherSequence a')
      (Yplus Yminus : ℝ → Ω × Ω → ℝ) (Δ : ℕ → ℝ),
      (∀ u, Measurable (Yplus u)) ∧ (∀ u, Measurable (Yminus u)) ∧
      (∀ ω : Ω × Ω, Continuous (fun u : ℝ => Yplus u ω)) ∧
      (∀ ω : Ω × Ω, Continuous (fun u : ℝ => Yminus u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω : Ω × Ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yplus u ω| ≤ ε) ∧
      (∀ ε > 0, ∀ᵐ ω : Ω × Ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yminus u ω| ≤ ε) ∧
      (∀ n : ℕ, 1 ≤ n → Δ n ≤ 2 * Real.log (n + 1) / Real.sqrt n) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ ω : Ω × Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            ((∑ k ∈ Finset.Icc 1 n,
                a' (2*k) ω * kernel_even_plus u k n)
            + (∑ k ∈ Finset.Icc 1 n,
                a' (2*k+1) ω * kernel_even_plus u k n)) -
          Yplus u ω| ≤ Δ n) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ ω : Ω × Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            ((∑ k ∈ Finset.Icc 1 n,
                a' (2*k) ω * kernel_even_plus u k n)
            - (∑ k ∈ Finset.Icc 1 n,
                a' (2*k+1) ω * kernel_even_plus u k n)) -
          Yminus u ω| ≤ Δ n) ∧
      ProbabilityTheory.IndepFun
        (fun ω : Ω × Ω => fun u : ℝ => Yplus u ω)
        (fun ω : Ω × Ω => fun u : ℝ => Yminus u ω)
        ((ℙ : Measure Ω).prod (ℙ : Measure Ω)) := by
  -- Axiom applications on the original space `Ω` produce `Y_e` / `Y_o`,
  -- both with the same `kernel_even_plus`.
  obtain ⟨Y_e, hYe_meas, hYe_cont, hYe_decay, hYe_couple⟩ :=
    LS_yplus_via_even a ha
  obtain ⟨Y_o, hYo_meas, hYo_cont, hYo_decay, hYo_couple⟩ :=
    LS_y_odd_via_plus_kernel a ha
  -- Linear-combo witnesses on `Ω × Ω`: Yplus = Y_e ∘ fst + Y_o ∘ snd,
  -- Yminus = Y_e ∘ fst - Y_o ∘ snd.
  refine ⟨fun k ω => if 2 ∣ k then a k ω.1 else a k ω.2,
    ?ha',
    fun u ω => Y_e u ω.1 + Y_o u ω.2,
    fun u ω => Y_e u ω.1 - Y_o u ω.2,
    fun n => 2 * Real.log (n + 1) / Real.sqrt n,
    ?meas_p, ?meas_m, ?cont_p, ?cont_m, ?decay_p, ?decay_m,
    ?Δ_bound, ?couple_p, ?couple_m, ?indep⟩
  case ha' =>
    -- T2.3 partial closure: split IsRademacherSequence into its four
    -- fields.  `measurable`, `prob_pos`, `prob_neg` close cleanly via
    -- product-measure projection lemmas
    -- (`Measure.fst_apply`/`Measure.fst_prod` and snd analogues).
    -- `iIndepFun` is the residual Mathlib API gap (lifting i.i.d.
    -- through disjoint-coordinate selection on a product measure).
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- iIndepFun on `Ω × Ω` of the alternating-fst/snd family.
      -- TAG[R33-C-T2.5-iIndepFun-prod-mathlib-gap]: genuine Mathlib API
      -- gap.  The required result is a "merge of two iIndepFun families
      -- on disjoint index sets, lifted via fst/snd to a product
      -- measure", but no single Mathlib lemma packages this.
      --
      -- Tried Mathlib alternatives (audited at R33-C / commit `6ae1b2d`
      -- against `Mathlib/Probability/Independence/`):
      --
      -- * `iIndepFun.precomp` (Basic.lean:324) — handles sub-sequence
      --   selection through an injection on a single iIndepFun family
      --   (used to close `IsRademacherSequence_a_{even,odd}.indep`
      --   above), but does NOT lift across product-space projections.
      --
      -- * `iIndepFun.comp` (Basic.lean:667) — per-index post-composition
      --   with measurable maps; requires the underlying family to
      --   already be iIndepFun on the target measure.
      --
      -- * `iIndepFun_iff_map_fun_eq_pi_map` (Basic.lean:705) — the
      --   characterization of iIndepFun via measure-pushforward equality
      --   on the product `∏ map (X i)`.  In principle, one could prove
      --   the goal by:
      --     (a) lifting the original iIndepFun on Ω to iIndepFun of
      --         `(a k ∘ fst)` on Ω × Ω via Fubini-style
      --         `Measure.map_prod_map` + projection identities;
      --     (b) similarly for `(a k ∘ snd)`;
      --     (c) merging the two halves using the independence between
      --         fst- and snd-measurable σ-algebras (`indepFun_prod`,
      --         already available).
      --   Each ingredient is in Mathlib but the composition is not
      --   packaged as a single applicable lemma; (c) in particular
      --   requires a "join two iIndepFun families with independent
      --   σ-algebras" result that is absent.
      --
      -- * `iIndepFun_pi` (Basic.lean:783) — for indexed-product spaces
      --   `Π i : ι, Ω i`, but the index set there is inside the iIndepFun
      --   family, not external.  Not applicable to a binary product
      --   `Ω × Ω`.
      --
      -- * `Measure.quasiMeasurePreserving_fst/snd` (used elsewhere in
      --   this file) — moves a.e.-statements through projections, but
      --   does not transport iIndepFun directly.
      --
      -- A full closure would require a new Mathlib lemma roughly:
      --   "If `(X_i)_{i ∈ I}` is iIndepFun on (Ω₁, μ) and `(Y_j)_{j ∈ J}`
      --   is iIndepFun on (Ω₂, ν), then the merged family on (Ω₁ × Ω₂,
      --   μ ⊗ ν) lifted via fst/snd is iIndepFun, indexed by `I ⊕ J`."
      -- This is mathematically standard (i.i.d. on disjoint blocks) but
      -- not a one-liner from existing Mathlib.
      --
      -- Honest TAG'd diagnostic, deferred to upstream Mathlib API
      -- arrival or a dedicated R33-D / R33-E formalization round.
      sorry
    · -- measurable
      intro k
      by_cases hk : (2 : ℕ) ∣ k
      · simp only [hk, ↓reduceIte]
        exact (ha.measurable k).comp measurable_fst
      · simp only [hk, ↓reduceIte]
        exact (ha.measurable k).comp measurable_snd
    · -- prob_pos
      intro k
      have hmeas_pos : MeasurableSet ({(1 : ℝ)} : Set ℝ) :=
        measurableSet_singleton 1
      have hpre : MeasurableSet ({ω : Ω | a k ω = 1}) :=
        ha.measurable k hmeas_pos
      by_cases hk : (2 : ℕ) ∣ k
      · have hset : {ω : Ω × Ω |
            (if (2 : ℕ) ∣ k then a k ω.1 else a k ω.2) = 1}
              = Prod.fst ⁻¹' {ω₁ : Ω | a k ω₁ = 1} := by
          ext ω; simp [hk]
        rw [hset, show (ℙ : Measure (Ω × Ω))
              = (ℙ : Measure Ω).prod (ℙ : Measure Ω) from rfl,
          ← MeasureTheory.Measure.fst_apply hpre,
          MeasureTheory.Measure.fst_prod]
        exact ha.prob_pos k
      · have hset : {ω : Ω × Ω |
            (if (2 : ℕ) ∣ k then a k ω.1 else a k ω.2) = 1}
              = Prod.snd ⁻¹' {ω₂ : Ω | a k ω₂ = 1} := by
          ext ω; simp [hk]
        rw [hset, show (ℙ : Measure (Ω × Ω))
              = (ℙ : Measure Ω).prod (ℙ : Measure Ω) from rfl,
          ← MeasureTheory.Measure.snd_apply hpre,
          MeasureTheory.Measure.snd_prod]
        exact ha.prob_pos k
    · -- prob_neg
      intro k
      have hmeas_neg : MeasurableSet ({(-1 : ℝ)} : Set ℝ) :=
        measurableSet_singleton (-1)
      have hpre : MeasurableSet ({ω : Ω | a k ω = -1}) :=
        ha.measurable k hmeas_neg
      by_cases hk : (2 : ℕ) ∣ k
      · have hset : {ω : Ω × Ω |
            (if (2 : ℕ) ∣ k then a k ω.1 else a k ω.2) = -1}
              = Prod.fst ⁻¹' {ω₁ : Ω | a k ω₁ = -1} := by
          ext ω; simp [hk]
        rw [hset, show (ℙ : Measure (Ω × Ω))
              = (ℙ : Measure Ω).prod (ℙ : Measure Ω) from rfl,
          ← MeasureTheory.Measure.fst_apply hpre,
          MeasureTheory.Measure.fst_prod]
        exact ha.prob_neg k
      · have hset : {ω : Ω × Ω |
            (if (2 : ℕ) ∣ k then a k ω.1 else a k ω.2) = -1}
              = Prod.snd ⁻¹' {ω₂ : Ω | a k ω₂ = -1} := by
          ext ω; simp [hk]
        rw [hset, show (ℙ : Measure (Ω × Ω))
              = (ℙ : Measure Ω).prod (ℙ : Measure Ω) from rfl,
          ← MeasureTheory.Measure.snd_apply hpre,
          MeasureTheory.Measure.snd_prod]
        exact ha.prob_neg k
  case meas_p =>
    intro u
    exact ((hYe_meas u).comp measurable_fst).add ((hYo_meas u).comp measurable_snd)
  case meas_m =>
    intro u
    exact ((hYe_meas u).comp measurable_fst).sub ((hYo_meas u).comp measurable_snd)
  case cont_p =>
    intro ω
    exact (hYe_cont ω.1).add (hYo_cont ω.2)
  case cont_m =>
    intro ω
    exact (hYe_cont ω.1).sub (hYo_cont ω.2)
  case decay_p =>
    -- |Y_e u ω.1 + Y_o u ω.2| ≤ |Y_e u ω.1| + |Y_o u ω.2| ≤ ε/2 + ε/2 = ε
    -- for u ≥ max T_e T_o.  T_e (resp. T_o) from hYe_decay (resp.
    -- hYo_decay) at ε/2 lifted via fst (resp. snd).
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    have hYe_lift :=
      (Measure.quasiMeasurePreserving_fst
        (μ := (ℙ : Measure Ω)) (ν := (ℙ : Measure Ω))).ae (hYe_decay (ε/2) hε2)
    have hYo_lift :=
      (Measure.quasiMeasurePreserving_snd
        (μ := (ℙ : Measure Ω)) (ν := (ℙ : Measure Ω))).ae (hYo_decay (ε/2) hε2)
    filter_upwards [hYe_lift, hYo_lift] with ω hYe_ω hYo_ω
    obtain ⟨T_e, hT_e⟩ := hYe_ω
    obtain ⟨T_o, hT_o⟩ := hYo_ω
    refine ⟨max T_e T_o, fun u hu => ?_⟩
    have h_e : |Y_e u ω.1| ≤ ε/2 := hT_e u (le_of_max_le_left hu)
    have h_o : |Y_o u ω.2| ≤ ε/2 := hT_o u (le_of_max_le_right hu)
    calc |Y_e u ω.1 + Y_o u ω.2|
        ≤ |Y_e u ω.1| + |Y_o u ω.2| := abs_add_le _ _
      _ ≤ ε/2 + ε/2 := add_le_add h_e h_o
      _ = ε := by ring
  case decay_m =>
    -- Mirror of decay_p with sub instead of add.
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    have hYe_lift :=
      (Measure.quasiMeasurePreserving_fst
        (μ := (ℙ : Measure Ω)) (ν := (ℙ : Measure Ω))).ae (hYe_decay (ε/2) hε2)
    have hYo_lift :=
      (Measure.quasiMeasurePreserving_snd
        (μ := (ℙ : Measure Ω)) (ν := (ℙ : Measure Ω))).ae (hYo_decay (ε/2) hε2)
    filter_upwards [hYe_lift, hYo_lift] with ω hYe_ω hYo_ω
    obtain ⟨T_e, hT_e⟩ := hYe_ω
    obtain ⟨T_o, hT_o⟩ := hYo_ω
    refine ⟨max T_e T_o, fun u hu => ?_⟩
    have h_e : |Y_e u ω.1| ≤ ε/2 := hT_e u (le_of_max_le_left hu)
    have h_o : |Y_o u ω.2| ≤ ε/2 := hT_o u (le_of_max_le_right hu)
    calc |Y_e u ω.1 - Y_o u ω.2|
        = |Y_e u ω.1 + (- Y_o u ω.2)| := by rw [sub_eq_add_neg]
      _ ≤ |Y_e u ω.1| + |- Y_o u ω.2| := abs_add_le _ _
      _ = |Y_e u ω.1| + |Y_o u ω.2| := by rw [abs_neg]
      _ ≤ ε/2 + ε/2 := add_le_add h_e h_o
      _ = ε := by ring
  case Δ_bound =>
    intro _ _; exact le_refl _
  case couple_p =>
    -- Linear-combo coupling for Yplus: triangle bound on the two
    -- per-sub-sequence couplings (each ≤ log(n+1)/√n) gives 2·log(n+1)/√n.
    intro n hn ω u hu
    -- Identify the indicator-shaped sums with `a_even`/`a_odd` sums.
    have h_even_idx : ∀ k,
        (if (2 : ℕ) ∣ (2*k) then a (2*k) ω.1 else a (2*k) ω.2)
          = a_even a k ω.1 := by
      intro k
      have : (2 : ℕ) ∣ (2*k) := Nat.dvd_mul_right 2 k
      simp [a_even, this]
    have h_odd_idx : ∀ k,
        (if (2 : ℕ) ∣ (2*k+1) then a (2*k+1) ω.1 else a (2*k+1) ω.2)
          = a_odd a k ω.2 := by
      intro k
      have h_not : ¬ (2 : ℕ) ∣ (2*k+1) := by omega
      simp [a_odd, h_not]
    have h_sum_even :
        (∑ k ∈ Finset.Icc 1 n,
            (if (2 : ℕ) ∣ (2*k) then a (2*k) ω.1 else a (2*k) ω.2)
              * kernel_even_plus u k n)
          = ∑ k ∈ Finset.Icc 1 n,
              a_even a k ω.1 * kernel_even_plus u k n := by
      refine Finset.sum_congr rfl ?_
      intro k _; rw [h_even_idx]
    have h_sum_odd :
        (∑ k ∈ Finset.Icc 1 n,
            (if (2 : ℕ) ∣ (2*k+1) then a (2*k+1) ω.1 else a (2*k+1) ω.2)
              * kernel_even_plus u k n)
          = ∑ k ∈ Finset.Icc 1 n,
              a_odd a k ω.2 * kernel_even_plus u k n := by
      refine Finset.sum_congr rfl ?_
      intro k _; rw [h_odd_idx]
    rw [h_sum_even, h_sum_odd]
    -- Per-summand couplings.
    have h_e_couple := hYe_couple n hn ω.1 u hu
    have h_o_couple := hYo_couple n hn ω.2 u hu
    -- Algebraic regrouping: (A + B) - (X + Y) = (A - X) + (B - Y).
    set A := (1 : ℝ) / Real.sqrt n *
        ∑ k ∈ Finset.Icc 1 n, a_even a k ω.1 * kernel_even_plus u k n
    set B := (1 : ℝ) / Real.sqrt n *
        ∑ k ∈ Finset.Icc 1 n, a_odd a k ω.2 * kernel_even_plus u k n
    have h_eq : (1 : ℝ) / Real.sqrt n *
        ((∑ k ∈ Finset.Icc 1 n, a_even a k ω.1 * kernel_even_plus u k n)
        + (∑ k ∈ Finset.Icc 1 n, a_odd a k ω.2 * kernel_even_plus u k n))
          - (Y_e u ω.1 + Y_o u ω.2)
          = (A - Y_e u ω.1) + (B - Y_o u ω.2) := by
      simp only [A, B]
      ring
    rw [h_eq]
    calc |(A - Y_e u ω.1) + (B - Y_o u ω.2)|
        ≤ |A - Y_e u ω.1| + |B - Y_o u ω.2| := abs_add_le _ _
      _ ≤ Real.log (n + 1) / Real.sqrt n + Real.log (n + 1) / Real.sqrt n :=
            add_le_add h_e_couple h_o_couple
      _ = 2 * Real.log (n + 1) / Real.sqrt n := by ring
  case couple_m =>
    -- Mirror of couple_p with the sign flip on the odd summand.
    intro n hn ω u hu
    have h_even_idx : ∀ k,
        (if (2 : ℕ) ∣ (2*k) then a (2*k) ω.1 else a (2*k) ω.2)
          = a_even a k ω.1 := by
      intro k
      have : (2 : ℕ) ∣ (2*k) := Nat.dvd_mul_right 2 k
      simp [a_even, this]
    have h_odd_idx : ∀ k,
        (if (2 : ℕ) ∣ (2*k+1) then a (2*k+1) ω.1 else a (2*k+1) ω.2)
          = a_odd a k ω.2 := by
      intro k
      have h_not : ¬ (2 : ℕ) ∣ (2*k+1) := by omega
      simp [a_odd, h_not]
    have h_sum_even :
        (∑ k ∈ Finset.Icc 1 n,
            (if (2 : ℕ) ∣ (2*k) then a (2*k) ω.1 else a (2*k) ω.2)
              * kernel_even_plus u k n)
          = ∑ k ∈ Finset.Icc 1 n,
              a_even a k ω.1 * kernel_even_plus u k n := by
      refine Finset.sum_congr rfl ?_
      intro k _; rw [h_even_idx]
    have h_sum_odd :
        (∑ k ∈ Finset.Icc 1 n,
            (if (2 : ℕ) ∣ (2*k+1) then a (2*k+1) ω.1 else a (2*k+1) ω.2)
              * kernel_even_plus u k n)
          = ∑ k ∈ Finset.Icc 1 n,
              a_odd a k ω.2 * kernel_even_plus u k n := by
      refine Finset.sum_congr rfl ?_
      intro k _; rw [h_odd_idx]
    rw [h_sum_even, h_sum_odd]
    have h_e_couple := hYe_couple n hn ω.1 u hu
    have h_o_couple := hYo_couple n hn ω.2 u hu
    set A := (1 : ℝ) / Real.sqrt n *
        ∑ k ∈ Finset.Icc 1 n, a_even a k ω.1 * kernel_even_plus u k n
    set B := (1 : ℝ) / Real.sqrt n *
        ∑ k ∈ Finset.Icc 1 n, a_odd a k ω.2 * kernel_even_plus u k n
    have h_eq : (1 : ℝ) / Real.sqrt n *
        ((∑ k ∈ Finset.Icc 1 n, a_even a k ω.1 * kernel_even_plus u k n)
        - (∑ k ∈ Finset.Icc 1 n, a_odd a k ω.2 * kernel_even_plus u k n))
          - (Y_e u ω.1 - Y_o u ω.2)
          = (A - Y_e u ω.1) - (B - Y_o u ω.2) := by
      simp only [A, B]
      ring
    rw [h_eq]
    calc |(A - Y_e u ω.1) - (B - Y_o u ω.2)|
        = |(A - Y_e u ω.1) + (- (B - Y_o u ω.2))| := by rw [sub_eq_add_neg]
      _ ≤ |A - Y_e u ω.1| + |- (B - Y_o u ω.2)| := abs_add_le _ _
      _ = |A - Y_e u ω.1| + |B - Y_o u ω.2| := by rw [abs_neg]
      _ ≤ Real.log (n + 1) / Real.sqrt n + Real.log (n + 1) / Real.sqrt n :=
            add_le_add h_e_couple h_o_couple
      _ = 2 * Real.log (n + 1) / Real.sqrt n := by ring
  case indep =>
    -- TAG[R33-C-T2.4-gaussian-uncorrelated-indep-mathlib-gap]: Linear
    -- combinations of the same independent pair (Y_e ∘ fst, Y_o ∘ snd)
    -- — Yplus and Yminus do NOT factor through different projections,
    -- so `indepFun_prod` (Basic.lean:750, the lemma used in
    -- `LS_independent_yplus_yminus_disjoint_blocks` above) does not
    -- apply here.
    --
    -- Mathematical content: Y_e and Y_o are i.i.d. centered Gaussian
    -- processes (same kernel, same sub-sequence law, applied
    -- independently on `Ω × Ω` via fst/snd).  In the joint Gaussian
    -- space spanned by `(Y_e ∘ fst, Y_o ∘ snd)`,
    -- `Cov(Y_e + Y_o, Y_e - Y_o) = Var(Y_e) - Var(Y_o) = 0` (since
    -- i.i.d.), and **for joint Gaussians, uncorrelated → independent**.
    --
    -- Tried Mathlib alternatives (audited at R33-C / commit `6ae1b2d`
    -- against `Mathlib/Probability/`):
    --
    -- * `IndepFun.covariance_eq_zero` (Moments/Covariance.lean:297) —
    --   the FORWARD direction (independent → cov = 0).  We need the
    --   REVERSE direction (cov = 0 → independent, for Gaussians).  No
    --   such reverse-direction lemma exists in Mathlib.
    --
    -- * `IsGaussian` API
    --   (`Probability/Distributions/Gaussian/Basic.lean`,
    --    `CharFun.lean`, `Fernique.lean`, `Real.lean`) — provides
    --   `IsGaussian` for `Measure E` (typeclass on the pushforward
    --   measure), `charFun`/`charFunDual` characterizations, and
    --   `IsGaussian.ext_covarianceBilinDual`.  None give a direct
    --   "uncorrelated centered Gaussians are independent" lemma; the
    --   characteristic-function factorization required (`charFun_prod
    --   = charFun · charFun` ⟹ independence via
    --   `indepFun_iff_charFun_prod`) needs the joint distribution to
    --   be IsGaussian as a 2-vector, which the
    --   `kmt_aided_gaussian_process` axiom does NOT certify (its
    --   output is just `(measurability, continuity, tail decay,
    --   coupling bound)`).
    --
    -- * `indepFun_iff_charFun_prod` (CharacteristicFunction.lean:52)
    --   — would close this if we could establish charFun
    --   factorization, but that requires the joint Gaussian-ness
    --   not provided by the axiom.
    --
    -- A full closure requires either:
    --   (i) strengthen the `kmt_aided_gaussian_process` axiom output
    --       to certify joint Gaussian-ness (`IsGaussian (μ.map (Y_e,
    --       Y_o))`), and add a Mathlib lemma "joint Gaussian +
    --       cov = 0 ⟹ independent"; or
    --   (ii) construct an ad-hoc characteristic-function argument on
    --       the pair `(Yplus, Yminus)` using the axiom's coupling
    --       bound + Rademacher-sequence char-fun structure.
    --
    -- Both routes are substantial new formalization work, deferred to
    -- the Mathlib stochastic-integral landing (which would also retire
    -- the `kmt_aided_gaussian_process` axiom altogether, replacing it
    -- with a proper Itô-isometry construction that certifies joint
    -- Gaussian-ness directly).
    --
    -- Honest TAG'd diagnostic, deferred.
    sorry

/-! ### R33-D / T2.4 — phase-shift correction (calc lemma)

The original public-theorem minus-kernel `(-exp(-u/n))^k` and the linear-combo
Form β construction `Yminus = Y_e − Y_o` carry the same phase information.
The lemma below verifies the algebraic identity at the sum level: the full
minus-kernel sum `∑_{k=1..n} a k · (-exp(-u/n))^k` splits as the even-indexed
plus-kernel sum minus the odd-indexed plus-kernel sum, which is exactly the
even/odd decomposition that R33's Form β implements via
`(a_even, kernel_even_plus)` and `(a_odd, kernel_even_plus)` on `Ω × Ω.fst`
and `Ω × Ω.snd` respectively.  This is the formal certificate that R33's
linear-combo construction preserves the phase content of the original
minus-kernel form. -/

/-- **R33-D / T2.4 — phase-shift sum identity.**
`∑_{k=1..n} a k · (-exp(-u/n))^k = (∑_{k even} a k · exp(-u·k/n))
                                   − (∑_{k odd}  a k · exp(-u·k/n))`
for `1 ≤ n`.  Combines the per-summand identity
`(-exp(-u/n))^k = (-1)^k · exp(-u·k/n)` (`neg_pow` + `exp_neg_div_pow`)
with an even/odd partition of `Finset.Icc 1 n` and `Even.neg_one_pow`,
`Odd.neg_one_pow`. -/
private lemma minus_kernel_phase_shift_sum
    (a : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (u : ℝ) :
    ∑ k ∈ Finset.Icc 1 n, a k * (-Real.exp (-u / n)) ^ k
      = (∑ k ∈ (Finset.Icc 1 n).filter Even,
            a k * Real.exp (-u * k / n))
        - (∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ Even k),
            a k * Real.exp (-u * k / n)) := by
  -- Step 1: per-summand `a k · (-exp(-u/n))^k = (-1)^k · (a k · exp(-u·k/n))`.
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_exp_pow : ∀ k : ℕ,
      Real.exp (-u / n) ^ k = Real.exp (-u * (k : ℝ) / n) := by
    intro k
    rw [← Real.exp_nat_mul]
    congr 1; field_simp
  have h_term : ∀ k ∈ Finset.Icc 1 n,
      a k * (-Real.exp (-u / n)) ^ k
        = (-1 : ℝ) ^ k * (a k * Real.exp (-u * (k : ℝ) / n)) := by
    intro k _
    rw [neg_pow, h_exp_pow]; ring
  rw [Finset.sum_congr rfl h_term]
  -- Step 2: split by parity (Even vs ¬Even).
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun k => Even k)]
  -- Step 3a: on the Even part, `(-1)^k = 1`.
  have h_even : (∑ k ∈ (Finset.Icc 1 n).filter (fun k => Even k),
        (-1 : ℝ) ^ k * (a k * Real.exp (-u * (k : ℝ) / n)))
      = ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Even k),
          a k * Real.exp (-u * (k : ℝ) / n) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hev : Even k := (Finset.mem_filter.mp hk).2
    rw [hev.neg_one_pow]; ring
  -- Step 3b: on the ¬Even part, `(-1)^k = -1` (k is odd).
  have h_odd : (∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ Even k),
        (-1 : ℝ) ^ k * (a k * Real.exp (-u * (k : ℝ) / n)))
      = - ∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ Even k),
          a k * Real.exp (-u * (k : ℝ) / n) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hnot : ¬ Even k := (Finset.mem_filter.mp hk).2
    have hodd : Odd k := Nat.not_even_iff_odd.mp hnot
    rw [hodd.neg_one_pow]; ring
  rw [h_even, h_odd]; ring

end Erdos524.Helpers
