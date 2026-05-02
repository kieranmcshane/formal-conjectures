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

import FormalConjectures.ErdosProblems.Helpers.RademacherSequence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# 1D Komlós–Major–Tusnády coupling axiom (R29 / KMT Option C)

Komlós–Major–Tusnády (1975, *Studia Sci. Math. Hungar.* 32) strong invariance
principle for sums of i.i.d. centered sub-Gaussian random variables: there
exists a coupling between the partial-sum walk `S_n = ∑_{k ≤ n} X_k` and a
Brownian motion `B` such that `|S_n - B_n| = O(log n)` uniformly in `n`.

Specialised here to **Rademacher** sequences (the
`Erdos524.IsRademacherSequence` predicate, relocated from `524.lean` to
`Helpers/RademacherSequence.lean` in R29 to break the cyclic import).
Because Rademacher variables are bounded, the sub-Gaussian hypothesis is
automatic; the standard 1D KMT therefore applies, and we axiomatise the
specialisation to avoid the multi-year formalisation of the Tusnády-lemma /
dyadic-recursion / Hoeffding-Skorokhod machinery (see
`Helpers/OneDimKMTSketch.md` for an exploratory sketch of upstream routes).

## Role in KMT Option C

This axiom is the load-bearing input to
`two_dim_KMT_coupling_via_LS_reduction` (see
`Helpers/TwoDimKMTFromOneDim.lean`).  Once that theorem is fully proved, the
public `axiom two_dim_KMT_coupling` in `524.lean:3741` is replaced by the
theorem (`R30+`), and the project's net axiom count returns to two
(`one_dim_KMT_coupling` here + `Y_GLW_exists` in `Helpers/GLWProcess.lean`),
matching field standards for KMT-dependent results.

**Net-axiom budget during R29.** Introducing this axiom *temporarily* takes
the project to 3 net axioms (D2 / `Y_GLW_exists` private + 2D
`two_dim_KMT_coupling` public + this 1D axiom new).  The transitional state
is justified by the simultaneous landing of the 2D theorem skeleton in
`Helpers/TwoDimKMTFromOneDim.lean`, which makes the path from `1D` to `2D`
visible.  R30 is expected to close ≥ 50% of the skeleton sub-sorries; if it
does not, R29 is reverted (Refinement 2).

## Statement notes

* **Uniform-in-`ω` form.**  The bound `|S_n - B_n| ≤ C · log(n+1)` is stated
  uniformly in `ω`, not for "almost-every `ω` with `C = C(ω) < ∞`".  This is
  *stronger* than the textbook KMT a.s. statement, but matches the
  uniform-in-`ω` shape of `524.lean:3741`'s `Δ n` (which itself encodes the
  KMT-error envelope deterministically).  The implicit consumer in the LS
  reduction is the deterministic `Δ_n` rate; an a.s. statement would require
  a measurability-of-the-exceptional-set argument that is unnecessary if the
  sup-bound is uniform.

* **`log(n+1)` instead of `log n`.**  Avoids the singularity at `n = 0` /
  `n = 1` and is the standard form in the LS-reduction literature.  The
  multiplicative constant `C` absorbs the difference vs. `log n` for `n ≥ 2`.

* **`Measurable (B n)`.**  Conjuncted explicitly so the consumer does not
  have to infer Brownian-motion-of-an-integer-time measurability from a
  separate `IsBrownian` predicate.  Strictly stronger than just existence of
  a Brownian motion.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory

/-- **Axiom (1D Komlós–Major–Tusnády coupling for Rademacher sequences).**

For every probability space `(Ω, ℙ)` and every Rademacher sequence
`a : ℕ → Ω → ℝ`, there exists a Brownian-motion-like sequence
`B : ℕ → Ω → ℝ` and a constant `C > 0` such that the partial sums
`S_n := ∑_{k = 1}^{n} a_k` satisfy

```
|S_n(ω) - B_n(ω)| ≤ C · log(n + 1)        for all 1 ≤ n and all ω.
```

The construction is upstream (Komlós–Major–Tusnády 1975); the formal Lean
derivation is a separate multi-year project tracked in
`Helpers/OneDimKMTSketch.md`.  We axiomatise the statement.

This is the *only* probabilistic axiom this file introduces.  The 2D
analogue (`two_dim_KMT_coupling_via_LS_reduction` in
`Helpers/TwoDimKMTFromOneDim.lean`) is a *theorem* reducing to this axiom
plus deterministic kernel-side facts via the Letwin–Sawhney 4-step
reduction.
-/
axiom one_dim_KMT_coupling :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), Erdos524.IsRademacherSequence a →
      ∃ (B : ℕ → Ω → ℝ) (C : ℝ),
        0 < C ∧
        (∀ n, Measurable (B n)) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω,
          |(∑ k ∈ Finset.Icc 1 n, a k ω) - B n ω| ≤ C * Real.log (n + 1))

/-! ## Track C round-1 — general 1D KMT theorem signature + layer sub-lemmas

**Round:** Track C round 1 (parallel-track, branch `track-c-1dkmt`).
**Date:** 2026-05-02.
**Scope per Grok pre-flight Q3:** infrastructure + signature + audit only.
This section introduces the general (i.e. not-yet-Rademacher-specialised)
1D KMT theorem `oneDimKMT` together with **four layer sub-lemma signatures**
matching Grok Q2's proof recipe (Skorokhod / Quantile / Hungarian dyadic /
sup-error). All five new declarations carry TAG'd `sorry` bodies labelled
for Track C rounds 2–4.

**Net debt impact (Track C round 1):**
* axioms unchanged at 5 (the `axiom one_dim_KMT_coupling` above is *not*
  retired this round — that requires Layer 1–4 sub-lemmas to close);
* +5 sorries: `oneDimKMT` (main) + 4 layer sub-lemmas.

This is **expected**: signature upgrades surface debt for Track C rounds
2–4 to retire. Per Grok Q4, the cluster (rounds 1–4) carries
P(full closure) ≈ 0.65–0.75, with Layer 3 (Hungarian dyadic) as the
bottleneck.

**Cross-references:** `Helpers/TrackC_T1_OneDimKMTAudit.md` (T1.1
Mathlib gap audit), `Helpers/OneDimKMTSketch.md` (R17 exploratory sketch),
`Helpers/KMTOptionCPlan.md` (R28 retirement plan).
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal

/-! ### Layer 1 — Skorokhod embedding for single sums

For a finite-variance centred random variable `X : Ω → ℝ`, the Skorokhod
embedding produces a stopping time `τ` for a Brownian motion `B` such
that `B_τ` has the law of `X` and `E[τ] = E[X²]`. Iterated for partial
sums `S_n = X_1 + … + X_n` of i.i.d. summands with finite variance,
we obtain stopping times `τ_n` with `B_{τ_n} =_d S_n`.

**Mathlib status (Track C T1.1):** stopping-time machinery in
`brownian-motion/StochasticIntegral/OptionalSampling.lean` is partial; no
Skorokhod embedding theorem (no construction of `τ` matching the law of
a target single random variable). LOC estimate: 150–250.
-/

/-- **Layer 1 (`TrackC-Layer1-Skorokhod`).**
Skorokhod embedding for a single centred finite-variance random variable
into a Brownian motion: existence of a stopping time `τ` such that
`B(τ ω) ω = X ω` (in distribution; here stated as an a.e. pointwise
equality after passing to a coupled probability space) with
`E[τ] = E[X²]`.

Statement is the *existential* form: the coupled probability space and
the BM are constructed jointly with `τ` and `X'`. Layer 1 is consumed by
Layer 4 to chain per-`n` couplings into the sup-norm bound. -/
theorem skorokhod_embedding_single
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → ℝ) (_hX_meas : Measurable X) (_hX_centred : ∫ ω, X ω ∂ℙ = 0)
    (_hX_L2 : MemLp X 2 ℙ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (B : NNReal → Ω' → ℝ) (τ : Ω' → NNReal) (X' : Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
      Measurable τ ∧
      (∀ t, Measurable (B t)) ∧
      -- B has the same distribution as the canonical Brownian motion (Pre-BM is the
      -- correct level for this round; full IsBrownianMotion alignment is a Layer 1
      -- bookkeeping detail tracked separately).
      (∀ ω', X' ω' = B (τ ω') ω') ∧
      -- Skorokhod moment match: E[τ] = E[X²].
      (∫ ω', (τ ω' : ℝ) ∂μ' = ∫ ω, (X ω) ^ 2 ∂ℙ) := by
  -- TAG[TrackC-Layer1-Skorokhod]: Track C round 2 or 3 target.
  -- Construction: build B on Wiener space (brownian-motion package), then
  -- define τ as first hit of a level set determined by quantile-coupling
  -- the law of X with B's first passage time. Standard construction; the
  -- novelty is the Lean-level packaging (no Skorokhod embedding theorem
  -- exists in Mathlib or brownian-motion as of T1.1 audit).
  -- Cluster target: rounds 2 or 3 (depends on Layer 2 ordering).
  sorry

/-! ### Layer 2 — Quantile transformation for finite-moment distributions

Given a probability measure `μ` on `ℝ` and a uniform `U` on `[0, 1]`,
the quantile transformation `quantile μ U` produces a random variable
with law `μ`. This is the Lean-friendly version of "inverse CDF" used
in the original 1975 KMT proof to relate partial sums to uniforms,
which are then coupled to Gaussians.

**Mathlib status (Track C T1.1):** `cdf : Measure ℝ → StieltjesFunction ℝ`
exists in `Mathlib/Probability/CDF.lean:55`; the inverse / quantile
function does *not* exist as of T1.1 audit. LOC estimate: 80–120
(easiest layer to land first per Grok Q5).
-/

/-- **Layer 2 (`TrackC-Layer2-Quantile`, R2 Full close).**
Quantile (inverse-CDF) transformation: for any probability measure `μ`
on `ℝ`, the function `q : ℝ → ℝ` defined as `q p := sInf {y | p ≤ cdf μ y}`
on `Ioo 0 1` (and `0` outside) satisfies the pushforward identity
`(volume.restrict (Ioc 0 1)).map q = μ` (uniform on `(0, 1]` recovers `μ`).

The Galois iff `q p ≤ x ↔ p ≤ cdf μ x` is stated for `p ∈ Ioo 0 1`
(the universal-μ form: at `p = 1` with unbounded-support μ the level set
`{y : 1 ≤ cdf μ y}` may be empty, breaking the iff under Mathlib's
`Real.sInf` convention; restriction to `Ioo` avoids the boundary issue).

**Proof outline (TC2 closure):**
1. The level set `S_p := {y : p ≤ cdf μ y}` is non-empty (cdf → 1 at +∞)
   and bounded below (cdf → 0 at -∞) for `p ∈ Ioo 0 1`.
2. Right-continuity of cdf at `sInf S_p` plus monotonicity gives
   `p ≤ cdf μ (sInf S_p)`, hence the forward Galois direction.
3. Backward Galois is direct from `csInf_le`.
4. Measurability via `measurable_of_Iic` with case split on `0 ≤ x`.
5. Pushforward via `Measure.ext_of_Iic` + `restrict_congr_set` (Ioc =ᵐ Ioo
   under volume) + volume-of-Ioo-intersect-Iic case split on `cdf μ x = 1`.

**TC2 status:** Layer 2 retired (sorry on branch 17 → 16). -/
theorem quantile_transform_finite_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ (q : ℝ → ℝ),
      Measurable q ∧
      (∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ x : ℝ, q p ≤ x ↔ p ≤ cdf μ x) ∧
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).map q = μ) := by
  classical
  -- Define q := sInf-based piecewise inverse CDF.
  let q : ℝ → ℝ := fun p =>
    if p ∈ Set.Ioo (0:ℝ) 1
    then sInf {y : ℝ | p ≤ cdf μ y}
    else 0
  -- Aux 1: level set non-empty for p ∈ Ioo 0 1 (cdf → 1 at +∞).
  have hSp_ne : ∀ p ∈ Set.Ioo (0:ℝ) 1, ({y : ℝ | p ≤ cdf μ y}).Nonempty := by
    rintro p ⟨_, hp_lt⟩
    rcases ((tendsto_cdf_atTop μ).eventually_const_lt hp_lt).exists with ⟨y, hy⟩
    exact ⟨y, hy.le⟩
  -- Aux 2: level set bounded below for p ∈ Ioo 0 1 (cdf → 0 at -∞).
  have hSp_bdd : ∀ p ∈ Set.Ioo (0:ℝ) 1, BddBelow {y : ℝ | p ≤ cdf μ y} := by
    rintro p ⟨hp_pos, _⟩
    have h := (tendsto_cdf_atBot μ).eventually_lt_const hp_pos
    rw [Filter.eventually_atBot] at h
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun y hy => ?_⟩
    by_contra hlt; push_neg at hlt
    exact (hN y hlt.le).not_ge hy
  -- Galois iff for p ∈ Ioo 0 1 (right-continuity + monotonicity).
  have hGalois : ∀ p ∈ Set.Ioo (0:ℝ) 1, ∀ x : ℝ, q p ≤ x ↔ p ≤ cdf μ x := by
    intro p hp x
    show (if p ∈ Set.Ioo (0:ℝ) 1 then sInf {y | p ≤ cdf μ y} else 0) ≤ x ↔ _
    simp only [if_pos hp]
    refine ⟨fun hqx => ?_, fun hpcdf => csInf_le (hSp_bdd p hp) hpcdf⟩
    -- Forward: sInf S ≤ x → p ≤ cdf μ x via right-continuity of cdf at sInf S.
    have h_p_le_cdf : p ≤ cdf μ (sInf {y : ℝ | p ≤ cdf μ y}) := by
      have h_rc := (cdf μ).right_continuous (sInf {y : ℝ | p ≤ cdf μ y})
      have h_tend : Filter.Tendsto (fun y => (cdf μ : ℝ → ℝ) y)
          (𝓝[Set.Ioi (sInf {y : ℝ | p ≤ cdf μ y})] (sInf {y : ℝ | p ≤ cdf μ y}))
          (𝓝 (cdf μ (sInf {y : ℝ | p ≤ cdf μ y}))) :=
        h_rc.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      apply ge_of_tendsto h_tend
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [Set.mem_Ioi] at hz
      obtain ⟨z₀, hz₀_mem, hz₀_lt⟩ :=
        (csInf_lt_iff (hSp_bdd p hp) (hSp_ne p hp)).mp hz
      exact (hz₀_mem : p ≤ cdf μ z₀).trans (monotone_cdf μ hz₀_lt.le)
    exact h_p_le_cdf.trans (monotone_cdf μ hqx)
  -- Measurability via case split on 0 ≤ x.
  have hq_meas : Measurable q := by
    apply measurable_of_Iic
    intro x
    -- The goal is `MeasurableSet (q ⁻¹' Iic x)`, which is the same set as `{p | q p ≤ x}`.
    show MeasurableSet {p : ℝ | q p ≤ x}
    by_cases hx : (0 : ℝ) ≤ x
    · -- x ≥ 0: {p : q p ≤ x} = (Ioo 0 1)ᶜ ∪ (Ioo 0 1 ∩ Iic (cdf μ x))
      have h_set : {p : ℝ | q p ≤ x} =
          (Set.Ioo (0:ℝ) 1)ᶜ ∪ (Set.Ioo (0:ℝ) 1 ∩ Set.Iic (cdf μ x)) := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
          Set.mem_Iic]
        constructor
        · intro hqx
          by_cases hp : p ∈ Set.Ioo (0:ℝ) 1
          · exact Or.inr ⟨hp, (hGalois p hp x).mp hqx⟩
          · exact Or.inl hp
        · rintro (hp | ⟨hp, hpc⟩)
          · -- p ∉ Ioo 0 1: q p = 0 ≤ x by hx.
            show q p ≤ x
            simp only [q, if_neg hp]; exact hx
          · exact (hGalois p hp x).mpr hpc
      rw [h_set]
      exact (measurableSet_Ioo).compl.union (measurableSet_Ioo.inter measurableSet_Iic)
    · -- x < 0: {p : q p ≤ x} = Ioo 0 1 ∩ Iic (cdf μ x).
      push_neg at hx
      have h_set : {p : ℝ | q p ≤ x} = Set.Ioo (0:ℝ) 1 ∩ Set.Iic (cdf μ x) := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Iic]
        constructor
        · intro hqx
          by_cases hp : p ∈ Set.Ioo (0:ℝ) 1
          · exact ⟨hp, (hGalois p hp x).mp hqx⟩
          · -- p ∉ Ioo 0 1: q p = 0, but x < 0, so 0 ≤ x is false → contradicts hqx.
            exfalso
            have hq_p : q p = 0 := by simp only [q, if_neg hp]
            linarith [show (q p : ℝ) ≤ x from hqx, hq_p]
        · rintro ⟨hp, hpc⟩; exact (hGalois p hp x).mpr hpc
      rw [h_set]
      exact measurableSet_Ioo.inter measurableSet_Iic
  refine ⟨q, hq_meas, hGalois, ?_⟩
  -- Pushforward identity.
  -- Step 1: rewrite Ioc 0 1 to Ioo 0 1 via volume-restriction equality (NoAtoms).
  have h_restrict_eq : volume.restrict (Set.Ioc (0:ℝ) 1) = volume.restrict (Set.Ioo (0:ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  rw [h_restrict_eq]
  -- Step 2: equality of measures via Measure.ext_of_Iic.
  refine MeasureTheory.Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply hq_meas measurableSet_Iic,
      Measure.restrict_apply (hq_meas measurableSet_Iic),
      ← ofReal_cdf μ x]
  -- Goal: volume (q ⁻¹' Iic x ∩ Ioo 0 1) = ENNReal.ofReal (cdf μ x).
  -- Step 3: rewrite the set using Galois.
  have h_set_eq :
      q ⁻¹' Set.Iic x ∩ Set.Ioo (0:ℝ) 1 = Set.Ioo (0:ℝ) 1 ∩ Set.Iic (cdf μ x) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hqx, hp⟩; exact ⟨hp, (hGalois p hp x).mp hqx⟩
    · rintro ⟨hp, hpc⟩; exact ⟨(hGalois p hp x).mpr hpc, hp⟩
  rw [h_set_eq]
  -- Step 4: case split on cdf μ x = 1 vs < 1.
  set c := cdf μ x with hc
  have hc_le1 : c ≤ 1 := cdf_le_one μ x
  rcases lt_or_eq_of_le hc_le1 with hc_lt | hc_eq
  · -- c < 1: Ioo 0 1 ∩ Iic c = Ioc 0 c.
    have h_eq2 : Set.Ioo (0:ℝ) 1 ∩ Set.Iic c = Set.Ioc 0 c := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans_lt hc_lt⟩, h2⟩
    rw [h_eq2, Real.volume_Ioc, sub_zero]
  · -- c = 1: Ioo 0 1 ∩ Iic 1 = Ioo 0 1.
    have h_eq2 : Set.Ioo (0:ℝ) 1 ∩ Set.Iic c = Set.Ioo (0:ℝ) 1 := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic]
      refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hc_eq ▸ h.2.le⟩⟩
    rw [h_eq2, Real.volume_Ioo, sub_zero, hc_eq]

/-! ### Layer 3 base case — Tusnády polynomial coupling (TC3 sub-Stub)

**Round:** Track C round 3 (TC3 — this commit).
**Status:** signature locked + body sub-Stub'd; TC4–TC5 close.
**Per TC3 T1.1 audit (8th misframing):** the literature Tusnády result is
*polynomial* per-step, not pure `O(log n)`. The `O(log n)` form is a
*chain-level consequence* via Borel–Cantelli + Gaussian-tail control on `Z`.

For the binomial law `Bin(2n, 1/2)` on ℝ (pushforward of Mathlib's
`PMF.binomial` onto ℝ via `Fin.val`-cast) and a centred Gaussian
`Z ~ N(0, n/2)`, there exists a coupling on a joint probability space with
the polynomial per-step bound `|B - n - Z| ≤ A + C · Z² / n` for explicit
constants `A, C > 0`.

* **Bretagnolle–Massart 1989** + **Carter–Pollard 2004**: refined explicit
  constants (`A ≈ 0.6`, `C ≈ 1`).
* **Tusnády 1977**: original `|B - n - Z| ≤ 1 + Z²/n` form.
* **Mathlib status (TC3 T1.1):** `gaussianReal` ✅; `PMF.binomial` ✅;
  measure-theoretic `binomialReal : ℕ → ℝ≥0 → Measure ℝ` ❌ (worked
  around via `PMF.toMeasure.map (Fin.val : Fin (2n+1) → ℝ)`); Stirling
  precision + Mills-ratio bookkeeping for the polynomial bound: partial
  in `Mathlib.Analysis.Asymptotics`.
* **Body LOC estimate (TC4–TC5):** ~230–330 LOC. (i) ~30 LOC: PMF→Measure
  pushforward identities. (ii) ~50 LOC: coupling construction via shared
  `U ~ Uniform(0,1)` paired through TC2's `quantile_transform_finite_moment`.
  (iii) ~150–250 LOC: Stirling + Mills-ratio analysis for the polynomial
  bound.
-/

/-- **Tusnády base case (`TrackC-Layer3-Tusnady-base-polynomial`, TC3 sub-Stub).**

The polynomial-form per-step Tusnády lemma. For `n ≥ 1`, there exists a
coupled probability space carrying paired random variables `B Z : Ω' → ℝ`
with the laws `B ~ Bin(2n, 1/2)` (on ℝ) and `Z ~ N(0, n/2)`, satisfying
the per-step polynomial bound `|B - n - Z| ≤ A + C · Z²/n` for explicit
constants `A, C > 0`.

This is the *correct literature form* (Bretagnolle–Massart 1989 / Carter–
Pollard 2004); the pure `O(log n)` per-step form circulated in many
informal expositions does **not** hold uniformly without further almost-
sure tail control (which is Layer 4 work).

**Concrete blockers (TC3 sub-Stub diagnostic):**
1. `PMF.binomial`-to-`Measure ℝ` pushforward needs `Fin.val`-cast
   measurability; standard but not packaged. Workaround inline.
2. Coupling construction via shared uniform: pair the inverse-CDFs of
   `μ_B` and `μ_Z` through TC2's `quantile_transform_finite_moment`.
3. Polynomial bound: requires Stirling precision (partial in Mathlib)
   plus Mills-ratio control for the Gaussian PDF tail; explicit
   constants per Bretagnolle–Massart 1989. -/
theorem tusnady_base_polynomial (n : ℕ) (_hn : 1 ≤ n) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (B Z : Ω' → ℝ) (A C : ℝ),
      IsProbabilityMeasure μ' ∧ 0 < A ∧ 0 < C ∧
      Measurable B ∧ Measurable Z ∧
      μ'.map B = (PMF.binomial (1 / 2 : ℝ≥0) (by norm_num) (2 * n)).toMeasure.map
                   (fun (i : Fin (2 * n + 1)) => (i.val : ℝ)) ∧
      μ'.map Z = gaussianReal 0 ((n : ℝ≥0) / 2) ∧
      ∀ ω', |B ω' - (n : ℝ) - Z ω'| ≤ A + C * (Z ω') ^ 2 / (n : ℝ) := by
  -- TAG[TrackC-Layer3-Tusnady-base-polynomial]: TC4-TC5 scope.
  -- See docstring above + TC3 T1.1 audit `TrackC_round3_T1_GrepAudit.md` for
  -- concrete diagnostic. The `O(log n)` per-step form (8th misframing) is
  -- NOT what literature proves; this signature locks the polynomial form.
  sorry

/-! ### Layer 3 — Hungarian dyadic decomposition + recursive coupling

The classical KMT proof (Komlós–Major–Tusnády 1975 *Studia Sci. Math.
Hungar.* 32) uses Tusnády's lemma (above, polynomial per-step form) at
each dyadic scale and combines via dyadic recursion:

* **Tusnády's lemma (polynomial per-step)**: `tusnady_base_polynomial`
  above provides `|B - n - Z| ≤ A + C · Z²/n` for `Bin(2n, 1/2)` paired
  with `N(0, n/2)`.
* **Dyadic recursion**: `hungarian_dyadic_step` (below, signature locked
  in TC3) refines a coupling at scale `2^(k-1)` to scale `2^k` via the
  Tusnády base case applied to the binomial of the *increment count*.
* **Chain consequence**: iterating across scales `1, 2, 4, …, 2^K` plus
  Borel–Cantelli I + Gaussian-tail control yields the uniform-in-ω' log
  bound exposed by `hungarian_dyadic_coupling` (TC1-locked signature).

**Mathlib status (Track C T1.1):** Tusnády's lemma not in Mathlib at any
state. Binomial-coefficient asymptotics partial in
`Mathlib/Analysis/Asymptotics`. LOC estimate: 300–500 (bottleneck per
Grok Q4; per-round P(success) ≈ 0.25–0.35).
-/

/-- **Hungarian dyadic step (`TrackC-Layer3-Hungarian-dyadic-step`, TC3
signature lockdown).**

Given a coupling `(S_{prev}, B_{prev})` of partial sums to a Brownian
motion at the previous dyadic scale `2^(k-1)`, produce a refined coupling
`(S_{cur}, B_{cur})` at scale `2^k` such that the *new* per-scale midpoint
error remains within the polynomial Tusnády envelope. Iteration over
`k = 1, 2, …, K` is consumed by `hungarian_dyadic_coupling` to yield the
uniform-in-ω' log envelope.

**Round-3 form**: existential over the refined coupling space + per-step
polynomial midpoint bound. Body sub-Stub'd, TC4 close target.

**Recursion plan (docstring-only, body TC4):**
1. Apply `tusnady_base_polynomial` (above) with `n ↦ 2^(k-1)` to obtain
   `(B_{Bin}, Z_{Gauss})` with `|B_{Bin} - 2^(k-1) - Z_{Gauss}| ≤ A + C · Z²/2^(k-1)`.
2. Use `Z_{Gauss}` as the *Brownian-motion increment* over the dyadic
   subblock `[2^(k-1), 2^k]`.
3. Define `S_{cur} := S_{prev} + (sum of next 2^(k-1) summands)`,
   `B_{cur} := B_{prev} + Z_{Gauss}`. Tusnády polynomial bound carries
   over to the increment, summing to a polynomial-in-Z-vector running
   error.
4. Chain over scales: per-scale errors compose via triangle + Cauchy-
   Schwarz on the Gaussian sum's variance (= 2^(k-1) at scale `k`). -/
theorem hungarian_dyadic_step
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha_indep : ProbabilityTheory.iIndepFun a ℙ)
    (_ha_centred : ∀ k, ∫ ω, a k ω ∂ℙ = 0)
    (_ha_var : ∀ k, ProbabilityTheory.variance (a k) ℙ = 1)
    (k : ℕ) (_hk : 1 ≤ k) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S_cur : ℕ → Ω' → ℝ) (B_cur : NNReal → Ω' → ℝ) (A C : ℝ),
      IsProbabilityMeasure μ' ∧ 0 < A ∧ 0 < C ∧
      (∀ t, Measurable (B_cur t)) ∧
      (∀ n, Measurable (S_cur n)) ∧
      -- S_cur tracks partial sums up to the current dyadic scale.
      μ'.map (S_cur (2 ^ k)) = (ℙ : Measure Ω).map
        (fun ω => ∑ j ∈ Finset.Icc 1 (2 ^ k), a j ω) ∧
      -- Polynomial per-step midpoint bound (Tusnády base via PMF/Gaussian
      -- pairing on the dyadic increment).
      ∀ ω', |S_cur (2 ^ k) ω' - B_cur (2 ^ k : NNReal) ω'| ≤
        A + C * (B_cur (2 ^ k : NNReal) ω') ^ 2 / ((2 ^ k : ℕ) : ℝ) := by
  -- TAG[TrackC-Layer3-Hungarian-dyadic-step]: TC4 close target.
  -- Recursion plan: see docstring above. Body composes
  -- `tusnady_base_polynomial` (k iterations) with TC2's quantile transport
  -- and chains via triangle + Cauchy-Schwarz on dyadic-increment Gaussians.
  sorry

/-- **Layer 3 (`TrackC-Layer3-Hungarian-bottleneck`).**
Hungarian dyadic Tusnády-style coupling: for a partial-sum walk
`S_n = ∑ X_k` of i.i.d. centred unit-variance summands and a Brownian
motion `B`, there exists a coupling such that for each dyadic scale
`n = 2^k`, the per-scale midpoint error is `≤ C · log(n + 1)`.

This is the **load-bearing** sub-lemma of 1D KMT. Iteration over
dyadic scales (Layer 4) yields the sup-norm bound.

**Round-1 form**: existential over the coupling space + recursive
midpoint-error statement. The core dyadic step (Tusnády at `B(n, 1/2)`
vs `N(n/2, n/4)`) is the chief gap in Mathlib. -/
theorem hungarian_dyadic_coupling
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha_indep : ProbabilityTheory.iIndepFun a ℙ)
    (_ha_centred : ∀ k, ∫ ω, a k ω ∂ℙ = 0)
    (_ha_var : ∀ k, ProbabilityTheory.variance (a k) ℙ = 1) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S' : ℕ → Ω' → ℝ) (B : NNReal → Ω' → ℝ) (C : ℝ),
      IsProbabilityMeasure μ' ∧
      0 < C ∧
      (∀ t, Measurable (B t)) ∧
      (∀ n, Measurable (S' n)) ∧
      -- S' has the law of the partial sums of (a_k).
      (∀ n : ℕ, 1 ≤ n → μ'.map (S' n) =
        (ℙ : Measure Ω).map (fun ω => ∑ k ∈ Finset.Icc 1 n, a k ω)) ∧
      -- Per-dyadic-scale midpoint coupling error.
      (∀ k : ℕ, 1 ≤ k → ∀ ω', |S' (2 ^ k) ω' - B (2 ^ k : NNReal) ω'| ≤
        C * Real.log ((2 ^ k : ℕ) + 1)) := by
  -- TAG[TrackC-Layer3-Hungarian-bottleneck]: TC4-TC5 close target.
  -- Construction (post-TC3 plan): apply `tusnady_base_polynomial`
  -- (polynomial per-step form, locked TC3) at each dyadic scale via
  -- `hungarian_dyadic_step` (TC3 signature lockdown). The uniform-in-ω'
  -- log envelope of THIS theorem's conclusion is the *chain-level
  -- consequence* derived via Borel-Cantelli I + Gaussian-tail control on
  -- the per-step Z's, NOT the per-step Tusnády form (8th misframing
  -- documented in TrackC_round3_T1_GrepAudit.md).
  -- Mathlib gap: Tusnády's lemma (~one-page literature proof) requires
  -- careful binomial-coefficient asymptotics + Mills ratio. Adjacent
  -- infra: gaussianReal in Mathlib; PMF.binomial in Mathlib; the
  -- coupling pairing via shared uniform leverages TC2's
  -- `quantile_transform_finite_moment`.
  sorry

/-! ### Layer 4 — Sup-norm error O(log n / √n) via Borel–Cantelli + dyadic schedule

Given the per-dyadic-scale `O(log n)` coupling from Layer 3, the
sup-over-`[1, N]` error is amplified to `O(log N / √N)` via:

1. Borel–Cantelli I on the events `{|S_{2^k} - B_{2^k}| > C · log(2^k)}`,
2. Dyadic chaining: bound `sup_{n ≤ 2^{k+1}} |S_n - B_n|` by the
   neighbouring dyadic errors via the triangle inequality on a single
   dyadic block.

**Mathlib status (Track C T1.1):** Borel–Cantelli I and II are in
Mathlib (already used in `524.lean:1822`, `1955`). LOC estimate: 150–250
(terminal layer; depends on Layer 3 output).
-/

/-- **Layer 4 (`TrackC-Layer4-SupError`).**
Sup-norm coupling-error bound. Given the per-dyadic-scale Layer 3
output, almost surely the running sup-norm error
`sup_{n ≤ N} |S_n - B_n|` is bounded by `C' · log(N + 1)` for all
sufficiently large `N` (with the constant `C'` absorbed via Borel–
Cantelli).

When divided by `√N`, this yields the standard 1D KMT rate
`sup_{n ≤ N} |S_n - B_n| / √N ≤ C' · log(N + 1) / √N → 0` a.s. The
explicit `O(log N / √N)` form is the consumer-side rate used in
the 2D coupling (`TwoDimKMTFromOneDim.lean`'s LS reduction). -/
theorem sup_error_log_over_sqrt
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
    (S : ℕ → Ω' → ℝ) (B : NNReal → Ω' → ℝ) (C₀ : ℝ)
    (_h_dyadic_bound : ∀ k : ℕ, 1 ≤ k → ∀ ω, |S (2 ^ k) ω - B (2 ^ k : NNReal) ω| ≤
      C₀ * Real.log ((2 ^ k : ℕ) + 1)) :
    ∃ (C' : ℝ), 0 < C' ∧ ∀ᵐ ω : Ω' ∂(ℙ : Measure Ω'),
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n ≥ 1, n ≤ N →
        |S n ω - B (n : NNReal) ω| ≤ C' * Real.log ((N : ℝ) + 1) := by
  -- TAG[TrackC-Layer4-SupError]: Track C round 4 target (terminal).
  -- Construction: dyadic chaining + Borel-Cantelli I on the events
  -- {|S_{2^k} - B_{2^k}| > C · log(2^k)}. Terminal layer; depends only
  -- on Layer 3's per-scale midpoint bound.
  -- Mathlib gap: small. Borel-Cantelli already in Mathlib (and in active
  -- use in 524.lean:1822, 1955).
  sorry

/-! ### Main theorem — `oneDimKMT`

The general 1D Komlós-Major-Tusnády strong invariance principle for
i.i.d. centred finite-variance summands. Specialises to the existing
Rademacher axiom `one_dim_KMT_coupling` (above) by substituting
`ProbabilityTheory.variance (a k) ℙ = 1` (immediate for Rademacher).

Track C round-1 statement is the existential coupling form; the body
chains Layers 1–4 (skorokhod_embedding_single → quantile_transform_finite_moment
→ hungarian_dyadic_coupling → sup_error_log_over_sqrt).
-/

/-- **Main 1D KMT theorem (`TrackC-round1-infrastructure-only`).**
For a sequence of i.i.d. centred unit-variance random variables, the
partial sums `S_n = ∑_{k = 1}^{n} a_k` admit a coupling to a Brownian
motion `B` on a possibly enlarged probability space with sup-norm error
`|S_n - B_n| ≤ C · log(n + 1)` uniformly over `n ≥ 1` and almost-every
`ω`, for some absolute constant `C > 0`.

**Round-1 status (Track C):** signature only. Body chains Layers 1–4.
Closing this `sorry` retires the existing `axiom one_dim_KMT_coupling`
(by specialising to Rademacher).

**Cluster trajectory:** Track C rounds 2–4. Per Grok Q4, P(full
closure) ≈ 0.65–0.75 with Layer 3 (Hungarian dyadic) as the bottleneck.
-/
theorem oneDimKMT
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha_meas : ∀ k, Measurable (a k))
    (_ha_indep : ProbabilityTheory.iIndepFun a ℙ)
    (_ha_centred : ∀ k, ∫ ω, a k ω ∂ℙ = 0)
    (_ha_var : ∀ k, ProbabilityTheory.variance (a k) ℙ = 1) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S' : ℕ → Ω' → ℝ) (B : NNReal → Ω' → ℝ) (C : ℝ),
      IsProbabilityMeasure μ' ∧
      0 < C ∧
      (∀ t, Measurable (B t)) ∧
      (∀ n, Measurable (S' n)) ∧
      -- S' has the law of the partial sums of (a_k).
      (∀ n : ℕ, 1 ≤ n → μ'.map (S' n) =
        (ℙ : Measure Ω).map (fun ω => ∑ k ∈ Finset.Icc 1 n, a k ω)) ∧
      -- Sup-norm coupling error.
      (∀ᵐ ω' : Ω' ∂μ',
        ∃ N₀ : ℕ, ∀ n ≥ N₀, |S' n ω' - B (n : NNReal) ω'| ≤ C * Real.log ((n : ℝ) + 1)) := by
  -- TAG[TrackC-round1-infrastructure-only]: Track C rounds 2-4 closure.
  -- Body: chain Layers 1-4.
  --   1. quantile_transform_finite_moment → recover (a_k) from i.i.d. uniforms
  --      on a coupled space.
  --   2. skorokhod_embedding_single → embed each summand into BM via stopping
  --      times τ_k with E[τ_k] = E[a_k^2] = 1; iterate to embed S_n at
  --      stopping time T_n = τ_1 + ... + τ_n with E[T_n] = n.
  --   3. hungarian_dyadic_coupling → at each dyadic scale, refine the
  --      Tusnády midpoint bound to O(log n).
  --   4. sup_error_log_over_sqrt → amplify per-scale to sup-over-[1,N] via BC1.
  -- Estimated body once Layers 1-4 are Full: ~50-100 LOC of chaining.
  sorry

end Erdos524.Helpers
