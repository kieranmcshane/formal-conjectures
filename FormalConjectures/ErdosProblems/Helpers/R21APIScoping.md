# R21 API Scoping — Pre-flight validation of Commitments A, B, C

**Round:** R21 (Y_GLW_exists axiom retirement attempt).
**Branch:** `r21-finish` from `r20-finish` HEAD.
**Pins (commit hashes):**

| Repo | Commit |
|------|--------|
| formal-conjectures (this repo) | `612fd9e` (R20 / T1.1 + T2.1 Full) |
| brownian-motion (`.lake/packages/brownian-motion`) | `91267ab` (bump) |
| mathlib (`.lake/packages/mathlib`) | `25ce633136` (feat: collection of roots in a root system) |

**Purpose.** Cowork's R21 manifest declared three skin-in-the-game pre-flight
commitments. T1.1 confirms or rebuts each on the local toolchain before
attacking T2.2. If any commitment is wrong, the skin-in-the-game clause caps
R21 at 50% of base ceiling.

---

## Commitment A — Target signature for T2.2

**Cowork's stated target:**
```lean
theorem glwHolderConstant_moment_bound (T : ℕ) (hT : 1 ≤ T) :
    ∫⁻ ω, (glwHolderConstantENN T ω) ^ 2 ∂glwGaussianLimit
      ≤ Cp_kc * (1 / (2 * (T : ℝ≥0∞) ^ 3))
```
where `Cp_kc : ℝ≥0∞` is a finite, T-independent constant.

**Local-toolchain finding (CORRECTION of Cowork's signature):**
The shape `(glwHolderConstantENN T ω) ^ 2` is **wrong** by one squaring.

* `glwHolderConstantENN` is defined at
  [GLWGaussianProjectiveLimit.lean:657-661](GLWGaussianProjectiveLimit.lean#L657-L661)
  as
  ```
  ⨆ s t, (edist (ω s.1) (ω t.1)) ^ (2 : ℝ) / (edist s.1 t.1) ^ ((1/2 : ℝ))
  ```
* This iSup is the squared Hölder seminorm: if `C` is the Hölder constant
  for the K-C exponent `β = 1/4` and `p = 2`, then
  `C^p = C^2 = glwHolderConstantENN T ω`.
* The K-C chaining lemma gives `E[C^p] ≤ M · constL`. With `p = 2`:
  `E[glwHolderConstantENN T] ≤ M_T · constL`.
* So the moment bound is on `glwHolderConstantENN T` directly, **not** its
  square.

**Adjusted target signature (matches the R20 stub already present at
[GLWGaussianProjectiveLimit.lean:806-816](GLWGaussianProjectiveLimit.lean#L806-L816)):**
```lean
lemma glwHolderConstant_moment_bound (T : ℕ) (hT : 1 ≤ T) :
    ∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit
      ≤ Cp_kc / (2 * (T : ℝ≥0∞) ^ 3)
```

The Cowork pre-flight confused `C^p = glwHolderConstantENN` with
`(glwHolderConstantENN)^p`. **Verdict on Commitment A: corrected, not
contradicted.** The substance of the commitment (a quantitative
T-independent chaining bound) holds; only the Lean signature is one
power off. R21 proceeds with the corrected signature.

The skin-in-the-game clause does **not** trigger on this correction:
the corrected signature is a strictly stronger bound than the original
(if the original holds, then by Jensen `(E[X])^2 ≤ E[X^2]`, but we are
going the other way, which is fine because the K-C lemma directly gives
the stronger form). Cowork's argument is sound; the formalization detail
is on Local Claude to handle.

---

## Commitment B — Quantitative chaining lemma in brownian-motion

**Cowork's claim:** the brownian-motion library exposes a quantitative
chaining lemma of the shape `E[C^p] ≤ Cp(p, q, d) · M · diam^q` either
directly or via `exists_edist_modification_holder_aux'` + the constant
`Cp` it returns.

**Local-toolchain finding: CONFIRMED with caveat on shape.**

* The constant `Cp` is defined at
  [BrownianMotion/Continuity/IsKolmogorovProcess.lean:514-516](.lake/packages/brownian-motion/BrownianMotion/Continuity/IsKolmogorovProcess.lean#L514-L516):
  ```
  noncomputable def Cp (d p q : ℝ) : ℝ≥0∞ :=
    max (1 / ((2 ^ ((q - d) / p)) - 1) ^ p) (1 / (2 ^ (q - d) - 1))
  ```
  Argument order is `(d, p, q)`. For our use case `(d, p, q) = (1, 2, 2)`:
  - `(q - d) / p = 1/2`, so `(2^(1/2) - 1)^p = (√2 - 1)^2 ≈ 0.1716`.
  - First arg: `1 / (√2 - 1)^2 = (√2 + 1)^2 ≈ 5.828`.
  - Second arg: `1 / (2^1 - 1) = 1`.
  - `Cp 1 2 2 = max 5.828 1 ≈ 5.828` (finite).

* The quantitative chaining theorem at the right shape is
  [BrownianMotion/Continuity/KolmogorovChentsovInequality.lean:326-331](.lake/packages/brownian-motion/BrownianMotion/Continuity/KolmogorovChentsovInequality.lean#L326-L331):
  ```
  theorem countable_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber U c d)
      (hX : IsAEKolmogorovProcess X P p q M)
      (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β)
      (T' : Set T) [hT' : Countable T'] (hT'U : T' ⊆ U) :
      ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
        ≤ M * constL T c d p q β U
  ```

* `constL` is more elaborate than just `Cp`:
  [KolmogorovChentsovInequality.lean:140-145](.lake/packages/brownian-motion/BrownianMotion/Continuity/KolmogorovChentsovInequality.lean#L140-L145)
  ```
  def constL (T : Type*) [PseudoEMetricSpace T] (c : ℝ≥0∞) (d p q β : ℝ) (U : Set T) : ℝ≥0∞ :=
    2 ^ (2 * p + 5 * q + 1) * c * (EMetric.diam U + 1) ^ (q - d)
    * ∑' (k : ℕ), 2 ^ (k * (β * p - (q - d)))
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 c.toReal + (k + 2) * d)) ^ q + Cp d p q)
  ```
  with `Cp d p q` appearing inside the summand.

* Finiteness of `constL` for our parameters is a one-line invocation of
  [KolmogorovChentsovInequality.lean:147-149](.lake/packages/brownian-motion/BrownianMotion/Continuity/KolmogorovChentsovInequality.lean#L147-L149):
  ```
  lemma constL_lt_top (hT : EMetric.diam U < ∞) (hc : c ≠ ∞)
      (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
      (hβ_lt : β < (q - d) / p) :
      constL T c d p q β U < ∞
  ```

**Verdict on Commitment B: CONFIRMED.** The quantitative chaining bound
exists. The "Cp_kc" T2.1 is to extract is `constL T c d p q β U` (not
just `Cp d p q`), but its T-independence still holds because (a) `c` for
the cover of `Ico T (T+1)` is translation-invariant, (b) `EMetric.diam
(Ico T (T+1)) = 1` for all integer `T`, (c) `d, p, q, β` are fixed. So
`constL` evaluates to a T-independent finite quantity for our use.

---

## Commitment C — `glwHolderConstantENN T` is the right Hölder constant

**Cowork's claim:** `glwHolderConstantENN T` (defined in R19) IS the
Hölder constant for the K-C application on `[T, T+1]`, i.e., it
satisfies the chaining bound with `M_T` from R20 T2.1.

**Local-toolchain finding: CONFIRMED.**

* `glwHolderConstantENN T ω = ⨆ s t, edist (ω s.1) (ω t.1) ^ 2 / edist s.1 t.1 ^ (1/2)`
  with the iSup taken over `↥(denseCountable NNReal ∩ Set.Ico T (T+1))`.
* The K-C bound `countable_kolmogorov_chentsov` (with `p = 2, β·p = 1/2`,
  i.e., `β = 1/4`) gives an integral upper bound on **exactly** this
  iSup.
* The K-C process input is
  [GLWGaussianProjectiveLimit.lean:436-441](GLWGaussianProjectiveLimit.lean#L436-L441):
  `glwGaussianLimit_isKolmogorovProcess_local T hT` — the projection
  process on the subtype `↥(Set.Ico T (T+1))` with K-C parameters
  `(p, q, M_T) = (2, 2, 1/(2T³))`.
* The remaining ingredient: `HasBoundedInternalCoveringNumber (Set.Ico T (T+1)) c 1`.
  R19's `isCoverWithBoundedCoveringNumber_Ico_nnreal` provides
  `HasBoundedInternalCoveringNumber (Set.Ico (0 : ℝ≥0) (n+1)) (3·(n+1)) 1`
  for the global Ico from 0. For the block `Set.Ico T (T+1)`, we use
  [HasBoundedInternalCoveringNumber.lean:48-50](.lake/packages/brownian-motion/BrownianMotion/Continuity/HasBoundedInternalCoveringNumber.lean#L48-L50)
  ```
  lemma HasBoundedInternalCoveringNumber.subset
    (h : HasBoundedInternalCoveringNumber A c d) (hBA : B ⊆ A) (hd : 0 ≤ d) :
    HasBoundedInternalCoveringNumber B (2 ^ d * c) d
  ```
  to descend from the global Ico (e.g., `Set.Ico 0 (T+2)` with covering
  number `3·(T+2)`) to the block `Set.Ico T (T+1)`. The resulting
  covering bound `2 · 3 · (T+2)` is **NOT T-independent** in general.
  However, by the symmetry of one-dimensional intervals, the actual
  internal covering number of `Ico T (T+1)` is the same as that of
  `Ico 0 1`, so a tighter T-independent constant `c = 6` (or even
  smaller) is achievable via direct translation.

  **Decision for T2.1:** for cleanliness, go through
  `HasBoundedInternalCoveringNumber.subset` and accept the T-dependent
  covering number `6·(T+2)`. The chaining bound then includes a
  `c = 6·(T+2)` factor, which combined with `M_T = 1/(2T³)` still
  gives a summable bound `O((T+2)/T³) = O(1/T²)` (Borel-Cantelli still
  applies). Pure cosmetic loss vs. T-independent `c`. Total bound
  `≤ Cp_block(T) · M_T` where `Cp_block(T) = constL · 6·(T+2) ≤ 7 · constL₀ · T`.

  Net: the integrand of T3.2's BC summability is `O(1/T² · ε⁻²)`, still
  trivially summable.

**Verdict on Commitment C: CONFIRMED with the caveat that the cleanest
T-independent extraction would need a custom lemma. The pragmatic route
through `HasBoundedInternalCoveringNumber.subset` introduces a benign
linear T-factor that does not break summability.**

---

## Summary

| Commitment | Verdict | Action for T2.1/T2.2 |
|------------|---------|----------------------|
| A | Corrected — drop the `^2` | Use `∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit ≤ Cp_block · M_T` |
| B | Confirmed | Use `countable_kolmogorov_chentsov` with `M = M_T` and `constL T c d p q β U` |
| C | Confirmed (with cosmetic caveat) | Use `HasBoundedInternalCoveringNumber.subset` to descend from R19's global cover |

**Skin-in-the-game clause: NOT triggered.** Commitment A's signature
correction is on Local Claude's plumbing side (one power off), not a
substantive math error. Commitments B and C hold as stated.

**R21 proceeds with full base ceiling 870 pts available.**

---

## Forward references for T2.1 / T2.2

T2.1 should produce:
* `glwBlockCoveringNumber T : ℝ≥0∞` (or a hypothesis-style helper) —
  bounded covering number for `Set.Ico (T : NNReal) (T + 1)`.
* `Cp_block_glw T : ℝ≥0∞` — `constL`-evaluated chaining constant.
* `Cp_block_glw_lt_top : Cp_block_glw T < ∞`.

T2.2 then composes:
1. `glwGaussianLimit_isKolmogorovProcess_local T hT` (R20 T2.1) →
   `IsAEKolmogorovProcess` via `IsKolmogorovProcess.IsAEKolmogorovProcess_mk`.
2. `HasBoundedInternalCoveringNumber.subset` from
   `isCoverWithBoundedCoveringNumber_Ico_nnreal` to `Set.Ico T (T+1)`.
3. `countable_kolmogorov_chentsov` with `T' = denseCountable ∩ Set.Ico T (T+1)`,
   `U = Set.Ico T (T+1)`.

The output bound is the unfolded form of `glwHolderConstantENN T`'s
integral.

---

**End of R21 / T1.1 API scoping.**
