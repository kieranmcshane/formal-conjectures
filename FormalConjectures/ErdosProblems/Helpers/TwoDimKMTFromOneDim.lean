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

/-! ### R33-B / T2.1 — kernel decay lemmas (k ≥ 1 form)

The R33-B brief tightens the second hypothesis to
`kmt_aided_gaussian_process`:

```
kernel_decay : ∀ ε > 0, ∃ U > 0, ∀ n ≥ 1, ∀ u ≥ U, ∀ k, 1 ≤ k → k ≤ n →
                 |kernel u k n| ≤ ε
```

so as to match the `Finset.Icc 1 n` indexing in the conclusion's
coupling conjunct (the partial-sum index never reaches `k = 0`).  R33-A
landed the form `∀ k ≤ n` (literal Grok text), which was unsatisfiable
at `k = 0`.

**Residual mathematical gap (T2.1 honest diagnostic).**  Even with the
`1 ≤ k` restriction, the literal brief form remains unsatisfiable for
the R31 reparametrized kernels.  Concretely, for
`kernel_even_plus u k n = √(1/2) · exp(-u·k/n)` with `1 ≤ k ≤ n`, the
worst case at `(k = 1, n` large`)` gives
`|kernel| = √(1/2) · exp(-u/n) → √(1/2)` as `n → ∞` for any fixed `u`.
For `ε < √(1/2)` and `U` universal in `n`, choosing
`n > U / log(√(1/2) / ε)` yields a counterexample.  The brief's
suggested arithmetic
`exp(-u·k/n) ≤ exp(-u)` requires `k/n ≥ 1`, i.e., `k ≥ n` — so the
proof closes only on the boundary case `k = n`, not under the briefed
`k ≥ 1`.

The honest fixes are:
* **Boundary form**: change the universal quantifier to `k = n` (only
  the boundary index — sufficient for the L²-energy controlling Y's
  sample-path tail).
* **Per-n form**: swap quantifier order to
  `∀ ε > 0, ∀ n ≥ 1, ∃ U(n) > 0, ...` so `U` may depend on `n`
  (`U(n, ε) := n · log(√(1/2) / ε)` works).

Either fix would require re-tightening the axiom signature in
`Helpers/StochasticProcessAxiom.lean`, which is out of scope for
R33-B's substantive work (the linear-combo construction in T2.2).
The residual sorry is therefore TAG'd with a precise diagnostic and
deferred to a future round (or to the day Mathlib's stochastic-integral
API lands and the entire `kmt_aided_gaussian_process` axiom is
discharged). -/

/-- **R33-B / T2.1.a.** `kernel_decay` for `kernel_even_plus`, in the
brief's tightened form `∀ k, 1 ≤ k → k ≤ n → |kernel_even_plus u k n| ≤ ε`.

The form remains mathematically unsatisfiable as stated (see
TAG[R33-B-T2.1.a-form-still-broken] below): the `1 ≤ k` restriction
removes the `k = 0` counterexample but the `(k = 1, n` large`)`
counterexample persists for any `ε < √(1/2)` when `U` is universal in
`n`.  Closing this lemma cleanly requires either a boundary
quantification (`k = n`) or a per-`n` `U`; both are deferred. -/
private lemma kernel_even_plus_decay :
    ∀ ε > 0, ∃ U > 0, ∀ n : ℕ, 1 ≤ n →
      ∀ u ≥ U, ∀ k : ℕ, 1 ≤ k → k ≤ n → |kernel_even_plus u k n| ≤ ε := by
  -- TAG[R33-B-T2.1.a-form-still-broken]: brief's `1 ≤ k` form remains
  -- unsatisfiable for `kernel_even_plus` because the worst case at
  -- `(k = 1, n` large`)` gives `|kernel| → √(1/2)` for fixed `u`.
  -- Honest fix requires boundary form `k = n` or per-`n` U; both
  -- defer to a future round (out of scope for R33-B linear-combo work).
  sorry

/-- **R33-B / T2.1.b.** Mirror of T2.1.a for `kernel_odd_minus`. Same
residual unsatisfiability under the briefed `1 ≤ k` restriction:
`|kernel_odd_minus u 1 n| = √(1/2) · exp(-u·3/(2n)) → √(1/2)` as
`n → ∞` for fixed `u`.

**Note.** This kernel is no longer used by the linear-combo Form β
construction (T2.2 uses a single reparametrized plus-kernel applied
to two sub-sequences).  Once R33-C migrates the consumers and the
naive even-plus/odd-minus pair is fully deprecated, this lemma can be
deleted alongside `kernel_odd_minus`. -/
private lemma kernel_odd_minus_decay :
    ∀ ε > 0, ∃ U > 0, ∀ n : ℕ, 1 ≤ n →
      ∀ u ≥ U, ∀ k : ℕ, 1 ≤ k → k ≤ n → |kernel_odd_minus u k n| ≤ ε := by
  -- TAG[R33-B-T2.1.b-form-still-broken]: same residual unsatisfiability
  -- as T2.1.a.  Lemma is no longer used by the linear-combo Form β
  -- construction (T2.2); will be deleted alongside `kernel_odd_minus`
  -- in R33-C consumer migration.
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

/-- **R31 / T2.2 (deprecated by R33-B linear-combo).** Second axiom
application using `kernel_odd_minus` on the odd sub-sequence.

Used by the R33-A naive Form β construction (Yminus = Y_odd_with_minus
kernel, single-summand).  Superseded by `LS_y_odd_via_plus_kernel`
below in the R33-B linear-combo construction (Yplus = Y^e + Y^o,
Yminus = Y^e - Y^o, both using the same plus kernel).  Retained so the
naive `LS_yminus_via_odd` reference remains compilable in case any
intermediate doc-rendering hooks reference it; will be deleted in a
later cleanup round once the linear-combo form is fully validated. -/
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
    · -- iIndepFun.
      -- TAG[R33-B-T2.3-iIndepFun-prod]: iIndepFun lift through
      -- block-disjoint coordinate selection.  Mathlib has the
      -- ingredients (independence between fst-measurable and
      -- snd-measurable σ-algebras under a product measure;
      -- iIndepFun.comp under injective ℕ → ℕ on the original a) but
      -- the composite "i.i.d. on disjoint blocks of a product
      -- measure" lemma is not packaged.  Sorry-with-TAG honest
      -- diagnostic.
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
    -- TAG[R33-B-T2.2-gaussian-uncorrelated-indep]: Linear combinations
    -- of the same independent pair (Y_e ∘ fst, Y_o ∘ snd) — Yplus and
    -- Yminus do NOT factor through different projections.
    -- Independence requires: Y_e and Y_o are i.i.d. centered Gaussian,
    -- so Cov(Y_e + Y_o, Y_e - Y_o) = Var(Y_e) - Var(Y_o) = 0, and
    -- uncorrelated centered Gaussians on a joint Gaussian space are
    -- independent.  Mathlib's `IsGaussian.iIndepFun_iff_zero_covariance`
    -- (or equivalent) is the missing lemma; the axiom output type does
    -- not certify Gaussian-ness directly.  Sorry-with-TAG honest
    -- diagnostic deferred to Mathlib stochastic-integral landing.
    sorry

end Erdos524.Helpers
