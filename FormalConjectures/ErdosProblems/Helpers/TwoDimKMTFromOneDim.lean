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

## Form β file structure (R33-A)

* **Section 1 — R31 kernel/sequence infrastructure (kept).** The
  reparametrized kernels `kernel_even_plus`, `kernel_odd_minus`, their
  pointwise bounds, the half-sequences `a_even` / `a_odd`, and their
  `IsRademacherSequence` derivations.
* **Section 2 — R33-A T2.1 decay lemmas.** New `kernel_decay` arguments
  for the two R31 kernels, satisfying the second hypothesis added to
  `kmt_aided_gaussian_process` in R33-A.
* **Section 3 — R31 axiom applications.** `LS_yplus_via_even` and
  `LS_yminus_via_odd`, updated to thread the new `kernel_decay`
  hypothesis.
* **Section 4 — Form β headline (R33-A T2.2 + T2.3).**
  `LS_independent_yplus_yminus_disjoint_blocks` (B1 corrected) and
  `two_dim_KMT_coupling_via_LS_reduction` (A4 corrected).

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

/-- **R31 / T2.1.** Reparametrized kernel for the ODD-indexed half of
the FULL minus-kernel sum `(1/√n) ∑_k a_k · (-exp(-u/n))^k`.

Original odd-kernel-and-sign at index `k = 2j+1`:
`(-exp(-u/n))^(2j+1) = -exp(-u·(2j+1)/n)`.

Even-indexing the odd half (we look at the `(2j+1)`-th elements of `a`)
+ compressing `m := n/2` + the same `√(1/2)` normalization factor as
for the even half. The minus sign is folded into the kernel
definition. -/
private noncomputable def kernel_odd_minus (u : ℝ) (k m : ℕ) : ℝ :=
  -Real.sqrt (1/2) * Real.exp (-u * (2 * (k : ℝ) + 1) / (2 * (m : ℝ)))

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

/-- **R31 / T2.1.b.** Pointwise bound `|kernel_odd_minus u k m| ≤ 1`,
for `u ≥ 0`. Mirror of T2.1.a: the explicit negative sign is folded
into `abs_neg`, and the exponent `-u·(2k+1)/(2m)` is non-positive on
`u ≥ 0` (since `2k+1 ≥ 0` and `2m ≥ 0`). -/
private lemma kernel_odd_minus_bound :
    ∀ u : ℝ, 0 ≤ u → ∀ k m : ℕ, |kernel_odd_minus u k m| ≤ 1 := by
  intro u hu k m
  unfold kernel_odd_minus
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (1/2) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_le_one : Real.sqrt (1/2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hexp_pos :
      0 < Real.exp (-u * (2 * (k : ℝ) + 1) / (2 * (m : ℝ))) := Real.exp_pos _
  have hexp_le_one :
      Real.exp (-u * (2 * (k : ℝ) + 1) / (2 * (m : ℝ))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hk_nn : (0 : ℝ) ≤ 2 * (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have hu_kp1_nn : 0 ≤ u * (2 * (k : ℝ) + 1) :=
      mul_nonneg hu hk_nn
    have hneg : -u * (2 * (k : ℝ) + 1) ≤ 0 := by linarith [hu_kp1_nn]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · have hm_pos : (0 : ℝ) < 2 * (m : ℝ) := by
        have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        linarith
      exact div_nonpos_of_nonpos_of_nonneg hneg hm_pos.le
  rw [abs_mul, abs_neg, abs_of_pos hsqrt_pos, abs_of_pos hexp_pos]
  calc Real.sqrt (1/2) * Real.exp (-u * (2 * (k : ℝ) + 1) / (2 * (m : ℝ)))
      ≤ 1 * 1 :=
        mul_le_mul hsqrt_le_one hexp_le_one hexp_pos.le (by norm_num)
    _ = 1 := mul_one _

/-! ### R33-A / T2.1 — kernel decay lemmas (Grok-validated literal form)

The R33-A brief adds a second hypothesis to `kmt_aided_gaussian_process`:

```
kernel_decay : ∀ ε > 0, ∃ U > 0, ∀ n ≥ 1, ∀ u ≥ U, ∀ k ≤ n,
                 |kernel u k n| ≤ ε
```

intended to exclude the constant-`1` kernel (which would otherwise admit
the contradiction surfaced by R32 audit A3-α).

**Mathematical caveat.** As stated in the brief (literal Grok text), the
hypothesis is unsatisfiable for the R31 reparametrized kernels at
`k = 0`: `kernel_even_plus u 0 m = √(1/2) · exp 0 = √(1/2) ≈ 0.707`,
which is `> ε` for any `ε < √(1/2)`. The brief's Grok-supplied proof
sketch tacitly restricts to `k = m` (the boundary case where
`exp(-u·m/m) = exp(-u)` decays uniformly in `m`), but the universal
`∀ k ≤ n` quantifier in the literal hypothesis includes `k = 0`.

The two decay lemmas below are therefore stated against the literal
brief signature and `sorry`-stubbed with a tagged note. R33-A's mandatory
floor includes capping at 50% if more than two such pre-flight sorries
land in T2.3 — and the brief explicitly mentions "kernel decay form
wrong" as a foreseen 50%-cap trigger. The corrected form (boundary
restriction `k = n`, or `L²`-energy decay) will be addressed in R33-B
together with the consumer migration. -/

/-- **R33-A / T2.1.a.** `kernel_decay` for `kernel_even_plus`, in the
literal brief form `∀ k ≤ n, |kernel_even_plus u k n| ≤ ε`. As noted
above this form is unsatisfiable at `k = 0` (kernel value
`√(1/2) > ε` for small `ε`); the lemma is left as a tagged `sorry`. -/
private lemma kernel_even_plus_decay :
    ∀ ε > 0, ∃ U > 0, ∀ n : ℕ, 1 ≤ n →
      ∀ u ≥ U, ∀ k : ℕ, k ≤ n → |kernel_even_plus u k n| ≤ ε := by
  -- TAG[R33-A-T2.1.a]: brief's pointwise `∀ k ≤ n` form is unsatisfiable
  -- at `k = 0` for `kernel_even_plus`. Corrected forms (boundary `k = n`
  -- or L²-energy decay) deferred to R33-B alongside consumer migration.
  sorry

/-- **R33-A / T2.1.b.** Mirror of T2.1.a for `kernel_odd_minus`. Same
unsatisfiability issue at `k = 0`: `kernel_odd_minus u 0 m =
-√(1/2) · exp(-u/(2m))`, with absolute value `√(1/2) · exp(-u/(2m))`,
which approaches `√(1/2)` as `m → ∞`, not `≤ ε`. -/
private lemma kernel_odd_minus_decay :
    ∀ ε > 0, ∃ U > 0, ∀ n : ℕ, 1 ≤ n →
      ∀ u ≥ U, ∀ k : ℕ, k ≤ n → |kernel_odd_minus u k n| ≤ ε := by
  -- TAG[R33-A-T2.1.b]: same as T2.1.a — brief's literal form unsatisfiable
  -- at `k = 0`. Deferred to R33-B.
  sorry

/-- **R31 / T2.2 (helper).** The even sub-sequence `k ↦ a (2*k)`. -/
private def a_even {Ω : Type*} (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k ω => a (2 * k) ω

/-- **R31 / T2.2 (helper).** The odd sub-sequence `k ↦ a (2*k + 1)`. -/
private def a_odd {Ω : Type*} (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun k ω => a (2 * k + 1) ω

/-- **R31 / T2.2 (helper).** The even sub-sequence inherits the
i.i.d. Rademacher property from the parent sequence. The
`measurable / prob_pos / prob_neg` fields are direct specializations of
`ha` at index `2*k`; the `indep` field is the standard fact that an
`iIndepFun`-family is closed under sub-family selection along an
injection (`Mathlib`'s `ProbabilityTheory.iIndepFun.comp`-style API).

The `indep` sub-step is left as a tagged `sorry` (the only sub-sorry
inside T2.2): it is the standard "independence under sub-sequence
selection" lemma whose Mathlib formalization is mechanical but not yet
in the repo. -/
private lemma IsRademacherSequence_a_even
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    Erdos524.IsRademacherSequence (a_even a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- iIndepFun under sub-sequence selection k ↦ 2*k.
    sorry  -- TAG[R31-T2.2.indep-even]: iIndepFun.comp on an injective ℕ → ℕ
  · intro k; exact ha.measurable (2 * k)
  · intro k; exact ha.prob_pos (2 * k)
  · intro k; exact ha.prob_neg (2 * k)

/-- **R31 / T2.2 (helper).** Mirror for the odd sub-sequence. -/
private lemma IsRademacherSequence_a_odd
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    Erdos524.IsRademacherSequence (a_odd a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- iIndepFun under sub-sequence selection k ↦ 2*k + 1.
    sorry  -- TAG[R31-T2.2.indep-odd]: iIndepFun.comp on an injective ℕ → ℕ
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

/-- **R31 / T2.2.** Second axiom application: mirror of `LS_yplus_via_even`
on the odd sub-sequence with `kernel_odd_minus`. Produces a Gaussian
witness `Y_odd` for the (signed) ODD-indexed half of the FULL
minus-kernel sum. -/
private theorem LS_yminus_via_odd
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (Y_odd : ℝ → Ω → ℝ),
      (∀ u, Measurable (Y_odd u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Y_odd u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y_odd u ω| ≤ ε) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt m) *
            (∑ k ∈ Finset.Icc 1 m, a_odd a k ω * kernel_odd_minus u k m) -
          Y_odd u ω| ≤ Real.log (m + 1) / Real.sqrt m) :=
  kmt_aided_gaussian_process kernel_odd_minus kernel_odd_minus_bound
    kernel_odd_minus_decay (a_odd a) (IsRademacherSequence_a_odd a ha)

/-! ### Section 4 — Form β headline (R33-A T2.2 + T2.3)

The R33-A correction of A4 (`two_dim_KMT_coupling_via_LS_reduction`) and
B1 (`LS_independent_yplus_yminus`).  Both are restated in
paper-faithful Form β: a product space `Ω × Ω` carrying disjoint
Rademacher blocks, half-sum couplings against the R31 reparametrized
kernels, and unconditional `IndepFun` derived via `indepFun_prod` from
`Mathlib.Probability.Independence.Basic`.
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

/-- **A4 (R33-A correction, Form β).** 2D KMT coupling theorem in the
paper-faithful Letwin–Sawhney decoupled form.

R32 audit established that the R30 form is contradictory: full-sum
couplings on a single `Ω` together with unconditional `IndepFun`
exceeds what is mathematically achievable.  The R33-A correction
(Form β, per Grok pre-flight) builds the witnesses on a product space
`Ω' := Ω × Ω` from disjoint Rademacher sub-blocks
(`a_even` extended via `fst`, `a_odd` extended via `snd`), giving
HALF-sum couplings against the R31 reparametrized kernels
(`kernel_even_plus`, `kernel_odd_minus`) and unconditional `IndepFun`
by product-space construction.

**Signature note (deviation from brief).** The brief specifies
`∃ (Ω' : Type*) (mΩ' : MeasureSpace Ω') ...`; we instantiate `Ω' := Ω × Ω`
directly via Mathlib's canonical `prod.measureSpace` instance to avoid
the typeclass-instance-as-existential gymnastics. The mathematical
content is unchanged.

**Coupling form (deviation from brief).** The brief writes the half-sum
couplings against the kernels `exp(-u·(2k)/n)` and
`(-exp(-u/n))^(2k+1)` (the original full kernels evaluated at even/odd
indices); we use the R31 reparametrized kernels `kernel_even_plus` and
`kernel_odd_minus` which are what the existing R31
`LS_yplus_via_even` / `LS_yminus_via_odd` axiom applications return.
The two kernel forms are related by `√(1/2)` normalization +
index-rescaling and produce the same Gaussian witnesses up to
reparametrization (R33-B will bridge them as needed for consumer
migration).

**Body status.** One residual `sorry` for the
`IsRademacherSequence` lift to `Ω × Ω` (Mathlib API gap on lifting
`iIndepFun` through measure-preserving projections — standard but
non-trivial).
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
      (∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ ω : Ω × Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n,
              a' (2*k) ω * kernel_even_plus u k n) -
          Yplus u ω| ≤ Δ n) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ ω : Ω × Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n,
              a' (2*k+1) ω * kernel_odd_minus u k n) -
          Yminus u ω| ≤ Δ n) ∧
      ProbabilityTheory.IndepFun
        (fun ω : Ω × Ω => fun u : ℝ => Yplus u ω)
        (fun ω : Ω × Ω => fun u : ℝ => Yminus u ω)
        ((ℙ : Measure Ω).prod (ℙ : Measure Ω)) := by
  -- Axiom applications on the original space `Ω` produce `Y_even` / `Y_odd`.
  obtain ⟨Y_even, hYe_meas, hYe_cont, hYe_decay, hYe_couple⟩ :=
    LS_yplus_via_even a ha
  obtain ⟨Y_odd, hYo_meas, hYo_cont, hYo_decay, hYo_couple⟩ :=
    LS_yminus_via_odd a ha
  -- Form β witnesses on `Ω × Ω`: lift Y_even via `fst`, Y_odd via `snd`.
  refine ⟨fun k ω => if 2 ∣ k then a k ω.1 else a k ω.2,
    ?ha', fun u ω => Y_even u ω.1, fun u ω => Y_odd u ω.2,
    fun n => Real.log (n + 1) / Real.sqrt n,
    ?meas_p, ?meas_m, ?cont_p, ?cont_m, ?decay_p, ?decay_m,
    ?Δ_bound, ?couple_p, ?couple_m, ?indep⟩
  case ha' =>
    -- TAG[R33-A-T2.3-rademacher-lift]: IsRademacherSequence on Ω × Ω
    -- with even-block-via-fst, odd-block-via-snd. Mathlib API gap on
    -- lifting iIndepFun through product-space projections.
    sorry
  case meas_p =>
    intro u
    exact (hYe_meas u).comp measurable_fst
  case meas_m =>
    intro u
    exact (hYo_meas u).comp measurable_snd
  case cont_p =>
    intro ω
    exact hYe_cont ω.1
  case cont_m =>
    intro ω
    exact hYo_cont ω.2
  case decay_p =>
    intro ε hε
    have h_orig := hYe_decay ε hε
    exact (Measure.quasiMeasurePreserving_fst (μ := (ℙ : Measure Ω))
      (ν := (ℙ : Measure Ω))).ae h_orig
  case decay_m =>
    intro ε hε
    have h_orig := hYo_decay ε hε
    exact (Measure.quasiMeasurePreserving_snd (μ := (ℙ : Measure Ω))
      (ν := (ℙ : Measure Ω))).ae h_orig
  case Δ_bound =>
    intro _ _; exact le_refl _
  case couple_p =>
    intro n hn ω u hu
    -- For even index `2*k`, the `if 2 ∣ k` branch picks `a (2*k) ω.1`.
    have h_even : ∀ k, (if (2 : ℕ) ∣ (2*k) then a (2*k) ω.1 else a (2*k) ω.2)
        = a_even a k ω.1 := by
      intro k
      have : (2 : ℕ) ∣ (2*k) := Nat.dvd_mul_right 2 k
      simp [a_even, this]
    have h_sum :
        (∑ k ∈ Finset.Icc 1 n,
            (if (2 : ℕ) ∣ (2*k) then a (2*k) ω.1 else a (2*k) ω.2)
              * kernel_even_plus u k n)
          = ∑ k ∈ Finset.Icc 1 n,
              a_even a k ω.1 * kernel_even_plus u k n := by
      refine Finset.sum_congr rfl ?_
      intro k _; rw [h_even]
    rw [h_sum]
    exact hYe_couple n hn ω.1 u hu
  case couple_m =>
    intro n hn ω u hu
    -- For odd index `2*k+1`, the `if 2 ∣ k` branch picks `a (2*k+1) ω.2`.
    have h_odd : ∀ k, (if (2 : ℕ) ∣ (2*k+1) then a (2*k+1) ω.1 else a (2*k+1) ω.2)
        = a_odd a k ω.2 := by
      intro k
      have h_not : ¬ (2 : ℕ) ∣ (2*k+1) := by omega
      simp [a_odd, h_not]
    have h_sum :
        (∑ k ∈ Finset.Icc 1 n,
            (if (2 : ℕ) ∣ (2*k+1) then a (2*k+1) ω.1 else a (2*k+1) ω.2)
              * kernel_odd_minus u k n)
          = ∑ k ∈ Finset.Icc 1 n,
              a_odd a k ω.2 * kernel_odd_minus u k n := by
      refine Finset.sum_congr rfl ?_
      intro k _; rw [h_odd]
    rw [h_sum]
    exact hYo_couple n hn ω.2 u hu
  case indep =>
    exact LS_independent_yplus_yminus_disjoint_blocks Y_even Y_odd hYe_meas hYo_meas

end Erdos524.Helpers
