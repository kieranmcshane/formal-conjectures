# R19 API Scoping (T1.1)

Pre-flight verification of the three R18 diagnostic claims that gate
the conjunct-9 proof strategy. Each claim was checked against the
local Mathlib mirror (`.lake/packages/mathlib/`) and the brownian-
motion package (`.lake/packages/brownian-motion/`) on the `r18-finish`
HEAD `f282779`. Verdicts include verbatim signatures, file:line
citations, and explicit grep paths.

## Summary of findings

| # | R18 claim | Verdict | Strategic impact |
|---|-----------|---------|------------------|
| 1 | "No Gaussian-tail bound in Mathlib." | **PARTIALLY WRONG.** Sub-Gaussian framework (`HasSubgaussianMGF`) + `mgf_id_gaussianReal` exist; only ~5 LOC of glue is missing. | Marginal tail at integer points becomes cheap. |
| 2 | "`exists_modification_holder'''` returns C(ω) only existentially; no measurable Hölder constant." | **WRONG (corrected post-pre-flight).** `holderOnWith_holderModification` (`KolmogorovChentsov.lean:646-670`) has the explicit formula `C ω := ⨆ (s, t : denseCountable T ∩ U), edist (X s ω) (X t ω) ^ p / edist s t ^ (β·p)` (lines 650-651). This is a countable iSup of measurable functions ⇒ measurable by construction. The `holderModification` def at line 587 is concrete (not behind an existential). My initial T1.1 verdict on Claim 2 was wrong — the `..._measurable` sibling search missed that the *explicit constant* is right there in the proof body. Path A2 (the manifest's preferred path) is therefore feasible at ~30-50 LOC, not ~200. | Pivot T2.1.b: define `glwHolderConstant` directly from the explicit iSup formula. |
| 3 | "No process-level sup-tail in either library." | **CORRECT but incomplete.** No direct sup-tail; HOWEVER `IsKolmogorovProcess.finite_set_bound_of_edist_le` (`IsKolmogorovProcess.lean:972`) gives a quantitative L^p moment bound on `sup_{(s,t)∈J×J} edist(X_s, X_t)` for finite J. Markov + Fatou turns this into a quantitative sup-tail. | Surfaces a third route ("Path B") missed by R18. |

## Claim 1 — Gaussian sub-Gaussian tail

### What exists

* `Mathlib/Probability/Moments/SubGaussian.lean:142` — definition:
  ```lean
  structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
      (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
    integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
    mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)
  ```
* `Mathlib/Probability/Moments/SubGaussian.lean:606` — non-kernel
  variant `HasSubgaussianMGF`.
* `Mathlib/Probability/Moments/SubGaussian.lean:704` — non-kernel
  tail-bound lemma:
  ```lean
  lemma measure_ge_le (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
      μ.real {ω | ε ≤ X ω} ≤ exp (-ε ^ 2 / (2 * c))
  ```
* `Mathlib/Probability/Distributions/Gaussian/Real.lean:461`:
  ```lean
  theorem mgf_id_gaussianReal :
    mgf id (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2)
  ```
* `Mathlib/Probability/Distributions/Gaussian/Real.lean:470`:
  ```lean
  lemma integrable_exp_mul_gaussianReal (t : ℝ) :
    Integrable (fun x ↦ rexp (t * x)) (gaussianReal μ v)
  ```

### What is missing

No instance / theorem of the shape `HasSubgaussianMGF id (v) (gaussianReal 0 v)`.
The MGF formula above already matches the sub-Gaussian shape `exp(c · t²/2)`
with `c = v`, so a direct adapter is ~5 LOC:

```lean
theorem hasSubgaussianMGF_gaussianReal (v : ℝ≥0) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp; ring_nf
```

### Verdict

R18's "no Gaussian tail in Mathlib" was overstated: the *framework* is
there and so is the *MGF identity*; only the *adapter* is missing. With
~5 LOC, `HasSubgaussianMGF.measure_ge_le` gives:
`P(Y u ≥ ε) ≤ exp(-ε² / (2 · K_GLW(u, u)))` for any single `u ≥ 0`.
The two-sided bound `P(|Y u| ≥ ε)` is `≤ 2 · exp(-ε² / (2 · K_GLW(u, u)))`
(applied to ±X). Combined with `K_GLW(u, u) ≤ 1/(2u)`
(`YGLWConstruction.K_GLW_var_le_recip`) this gives `P(|Y u| ≥ ε) ≤
2 · exp(-ε² u)` at integer points `u = T : ℕ`.

## Claim 2 — measurable Hölder constant

**Verdict update (post-pre-flight from Cowork v2 manifest):** the
initial T1.1 verdict was *wrong*. Cowork pointed at
`holderOnWith_holderModification` (lines 646-670) rather than at the
existential wrapper `exists_modification_holder'''`. Local toolchain
verification confirms Cowork's reading: the explicit countable-iSup
formula at lines 650-651 is the Hölder constant by construction,
exposed concretely in the proof body. The patch cost is therefore
~30-50 LOC (a `glwHolderConstant` def + a measurability proof + a
HolderOnWith adapter), not ~200.

The original-verdict body below is retained as historical context
(it correctly catalogues the existential wrapper's API) but the
**operative path for R19** is to copy the explicit formula at
KolmogorovChentsov.lean:650-651 directly.

### `holderModification` definition (the concrete term)

`brownian-motion/BrownianMotion/Continuity/KolmogorovChentsov.lean:587`:
```lean
noncomputable
def holderModification (X : T → Ω → E) (β : ℝ≥0) (p : ℝ) (U : Set T)
    [DecidablePred (· ∈ U)] : T → Ω → E :=
  fun t ω ↦ if t ∈ U then limUnder (comap Subtype.val (𝓝 t))
    (fun t' : denseCountable T ↦
      indicatorProcess X (holderSet X (denseCountable T) p β U) t' ω)
    else hE.some
```

### Explicit Hölder constant formula

`brownian-motion/BrownianMotion/Continuity/KolmogorovChentsov.lean:650-651`,
inside `holderOnWith_holderModification`:
```lean
let C ω := ⨆ (s : (denseCountable T ∩ U : Set T))
              (t : (denseCountable T ∩ U : Set T)),
    edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
```
This is a countable iSup over `(denseCountable T ∩ U)²` of
measurable functions of `ω` (since `X s` and `X t` are measurable for
each fixed `s, t` and `edist`, division, and `^` preserve
measurability). The Hölder constant returned at line 665 is
`(C ω ^ p⁻¹).toNNReal`.

### Original-verdict body (for reference)

The original T1.1 grep flagged `exists_modification_holder'''` at
line 1228 as the wrapper API. Its proof body uses `Classical.choose`
at lines 1242 and 1319 to extract a constant — but the *underlying*
concrete construction goes through `holderModification`, where the
constant has the explicit formula above.

### Signature of `exists_modification_holder'''`

`brownian-motion/BrownianMotion/Continuity/KolmogorovChentsov.lean:1228`:
```lean
lemma exists_modification_holder''' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0), 0 < β → β < (q - d) / p →
        ∃ C, HolderOnWith C β (Y · ω) U) ∧
      IsLimitOfIndicator Y X P Set.univ
```

The Hölder constant `C` is existentially quantified per-ω (and per-β,
per-neighbourhood). No public access to `(ω ↦ C(ω))` as a measurable
random variable.

### Where C is constructed

Proof body, `KolmogorovChentsov.lean:1242`:
```lean
choose Z hZ hZ_eq hZ_holder hZ_extend
  using fun n ↦ exists_modification_holder'' (hC.hasBoundedCoveringNumber n) ...
```
and `KolmogorovChentsov.lean:1319`:
```lean
obtain ⟨C', hC'⟩ := hZ_holder (nt t) β₀ hβ₀_pos hβ₀_lt ω
```
The `C'` here is `Classical.choose` on a per-ω existential — not
measurable as currently written.

### Sibling search

Grep for `exists_modification_holder''''`, `exists_modification_holder.*measurable`,
or any `_measurable`-suffixed Hölder-constant exposure in
`.lake/packages/brownian-motion/`: **no matches**. The named hierarchy
ends at `'''`.

### Patch cost

To expose `Measurable C`, the `Classical.choose` calls at line 1242 and
line 1319 would have to be replaced by a *measurable* selection,
typically via the countable-supremum representation
`C(ω) := ⨆ (s, t : J), edist (X s ω) (X t ω) / edist s t ^ β` over a
countable dense `J`. Each summand is measurable; `Measurable.iSup` over
countable index gives the conclusion. ~50-80 LOC, deep brownian-motion
library work. Out of scope for one R19 wave.

## Claim 3 — process-level sup-tail

### Direct search

No lemma named `IsKolmogorovProcess.measure_sup_le`,
`IsKolmogorovProcess.tail_bound`, `Borell_TIS`, `concentration_sup`,
or similar exists in either library. Confirmed by grepping all
`brownian-motion/BrownianMotion/**/*.lean` and
`mathlib/Mathlib/Probability/**/*.lean`.

### What DOES exist (R18 missed this)

`brownian-motion/BrownianMotion/Continuity/IsKolmogorovProcess.lean:972`:
```lean
lemma finite_set_bound_of_edist_le (hJ : HasBoundedInternalCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hδ : δ ≠ 0) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }),
      edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (2 * p + 4 * q + 1) * M * c * δ ^ (q - d)
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d
            * δ.toReal⁻¹ ^ d))) ^ q + Cp d p q)
```

This is a *quantitative* L^p moment bound on the modulus-of-continuity
supremum over a **finite** subset `J`. By Markov's inequality this
gives a quantitative tail bound on
`sup_{(s,t) ∈ J × J, edist s t ≤ δ} |X_s - X_t|`.

Companion: `IsKolmogorovProcess.ae_iSup_rpow_edist_div_lt_top`
(`KolmogorovChentsovInequality.lean:348`) provides the a.s.
finiteness of the iSup over the *full* (continuous) space, which by
Fatou's lemma can absorb finite-set bounds back to a single
quantitative iSup-tail.

### What this enables (Path B, new)

The chaining argument:

1. Marginal sub-Gaussian tail at `T : ℕ`:
   `P(|Y T| ≥ ε/2) ≤ 2 · exp(-ε² T / 2)` (via Claim 1's adapter).
2. Modulus tail on `[T, T+1]`:
   apply `finite_set_bound_of_edist_le` to a countable dense
   `J ⊂ [T, T+1]`, take Fatou-limit; Markov gives
   `P(sup_{s,t ∈ [T,T+1]} |Y_s - Y_t| ≥ ε/2) ≤ C / ε^p`.
3. Combine:
   `P(sup_{[T,T+1]} |Y_s| ≥ ε) ≤ P(|Y_T| ≥ ε/2) + P(modulus ≥ ε/2)`.
4. Continuity of paths (already established in conjunct 8) lifts the
   countable-dense iSup to a continuous sup.

This route does **not** require a measurable Hölder constant. The
`finite_set_bound_of_edist_le` step gives the quantitative bound
directly, and Fatou converts it to a measurable tail without going
through `Classical.choose`.

## Strategic implication (post-correction)

The corrected reading of Claim 2 makes Path A2 (measurable Hölder
constant via the explicit `holderModification` formula) the
**lowest-cost route**:

* `glwHolderConstant ω := (C ω ^ p⁻¹).toNNReal` where `C ω` is the
  iSup formula at lines 650-651 — measurable by construction.
* Combined with the `hasSubgaussianMGF_id_gaussianReal` adapter
  (Claim 1, ~5-15 LOC) and Chernoff `measure_ge_le`, this gives the
  marginal-tail piece for the chaining argument:
  `P(sup_{[T,T+1]} |Y u| ≥ ε) ≤ P(|Y T| ≥ ε/2) + P(K(ω) ≥ ε/2)`.
* The Markov-on-`E[K^p]` step uses the chaining moment bound from
  `finite_set_bound_of_edist_le` / `exists_edist_modification_holder_aux'`.

**R19 manifest implication (v2):** T2.1.a (sub-Gaussian adapter) +
T2.1.b (`glwHolderConstant` measurable) are both feasible in a single
round. T2.2 (chaining-based sup-tail) is the technical bottleneck —
the `Cp(p,q,d)` constant + Markov assembly is ~60 LOC if the chaining
moment bound has the right shape, but may stall on integration setup
(`IsKolmogorovProcess.measurable_pair`-style).

The +500 retirement bonus on T3.1 remains gated on T2.4 Full. The
v2-manifest projection of 600-850 base + bonus is plausible if the
chaining bound composes cleanly; if not, T2.1.a + T2.1.b Full +
structured sorry on T2.2 is the calibration-honest fallback (~280 pts
on Phase 2).
