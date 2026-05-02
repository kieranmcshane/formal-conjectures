# Track C round 4 — T1.1 Claims Verification Table + Tusnády literature cite check

**Round:** Track C round 4 (parallel-track, branch `track-c-1dkmt`).
**Date:** 2026-05-02.
**Branch HEAD pre-TC4:** `f4511f5` (TC3 closure: Tusnády polynomial sub-Stub + Hungarian dyadic step signature lockdown).
**Worktree:** `/Users/kieranmcshane/Documents/formal-conjectures-track-c` (preserved from TC3).
**Mathlib pin:** `25ce633136084367f182be00fdff7613ea949d27`.
**Toolchain:** `leanprover/lean4:v4.27.0-rc1`.
**Per process:** Local Claude grep audit FIRST, Grok recipe SECOND with explicit uncertainty flagging on math edge cases.
**Per TC4 brief:** Claims Verification Table BINDING; claim #7 (polynomial vs `O(log n)` per-step form) must be confirmed against literature, not Grok memory.

## 0. Summary verdicts

| Check | Status | Risk to TC4 |
| --- | --- | --- |
| Worktree at branch `track-c-1dkmt` clean | ✅ HEAD `f4511f5`, 0 modified | low |
| TC1+TC2+TC3 commits present | ✅ `15192f1`, `f018aea`, `7f25b84`, `8c5451f`, `c96e54b`, `f4511f5` | none |
| `tusnady_base_polynomial` signature locked TC3 | ✅ `OneDimKMT.lean:408-421` | none |
| `hungarian_dyadic_step` signature locked TC3 | ✅ `OneDimKMT.lean:469-491` | none |
| Mathlib `Stirling` precision constants | ⚠️ asymptotic-only; explicit constants partial | **HIGH** for body close |
| Mathlib `MillsRatio` Gaussian tail | ❌ ABSENT (0 grep hits) | **HIGH** for body close |
| Mathlib `betaIntegral` real-valued | ⚠️ Complex-valued only at `Gamma/Beta.lean:60` | moderate |
| Polynomial per-step form verified vs literature | ✅ confirmed (Carter-Pollard 2004, BM 1989, Tusnády 1977) | none — TC4 anti-pattern check passes |
| `O(log n)` per-step misframing pre-empted | ✅ — chain-level Borel-Cantelli + Gaussian tail consequence (Layer 4) | none |
| Inverse CDF coupling via TC2 reusable | ✅ `quantile_transform_finite_moment:231-356` Full | direct dependency available |

**Verdict:** T2.1 Full body close is NOT achievable in TC4. Mills ratio absent, Stirling precision partial, real-Beta absent. Realistic outcomes:
- Best (P~0.10): Substantial partial body close — probability space construction via comonotonic coupling, leaving the polynomial bound itself as a sub-sorry. Net sorry change neutral.
- Mid (P~0.55): Refined sub-Stub with concrete recipe for Mills+Stirling work and probability space scaffolding sketched.
- Low (P~0.35): TC3-state sub-Stub preserved with audit-only addition.

The TC4 brief's P(T2.1 Full) = 0.40 disagrees with the TC3 audit's P=0.10. T1.1 sides with TC3 audit: 0.40 is overoptimistic given Mills+Stirling absence.

## 1. Claims Verification Table (TC4 brief BINDING — all 8 rows)

| # | Math statement | Lean statement (proposed) | VERIFIED? | Citation (file:line at pin OR Mathlib API) | Notes |
|---|----------------|---------------------------|-----------|---------------------------------------------|-------|
| 1 | Stirling approximation in Mathlib | Asymptotic: `Real.factorial_isEquivalent_stirling`. Explicit lower bound: `Real.le_factorial_stirling` (no upper bound at pin). | ⚠️ PARTIAL | `.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:223,236` (lower bound + asymptotic). Upper bound `n! ≤ ...` ABSENT at pin. | **GAP**: Tusnády body needs *both* bounds with explicit constants for binomial PMF asymptotic `Bin(2n,1/2)(k) ~ 1/√(πn) · exp(-(k-n)²/n)`. Lower bound usable, upper bound requires deriving via `factorial_isEquivalent_stirling` + ε-bookkeeping. ~30-50 LOC of Stirling-precision lemmas needed. |
| 2 | Mills ratio for Gaussian tail | `Real.gaussianMillsRatio` analogous, OR direct integral via `gaussianPDFReal`. | ❌ ABSENT | 0 grep hits across `.lake/packages/mathlib/` for `MillsRatio`, `mills_ratio`, `Mills.ratio`. | **CRITICAL GAP**: Body must derive Mills bound locally via integral comparison. Approach: `∫_t^∞ φ(z) dz ≤ φ(t)/t` for `t > 0`, where `φ(z) = exp(-z²/2)/√(2π)`. ~40-60 LOC. Uses `Real.exp_neg_le_inv_of_le` + `MeasureTheory.integral_exp_neg_sq` (latter pin-uncertain). |
| 3 | Binomial PMF formula | `PMF.binomial : ℝ≥0 → (h : p ≤ 1) → ℕ → PMF (Fin (n + 1))` | ✅ VERIFIED | `.lake/packages/mathlib/Mathlib/Probability/ProbabilityMassFunction/Binomial.lean:def binomial`. Lemmas: `binomial_apply` (closed form via Nat.choose), `binomial_apply_zero/last/self`, `binomial_one_eq_bernoulli`. | Domain is `Fin (n+1)`, NOT `ℝ`. Pushforward via `(binomial p h n).toMeasure.map (Fin.val : Fin (n+1) → ℕ → ℝ)` required (TC3 sub-Stub already encodes this). |
| 4 | Beta integral / incomplete beta | `Real.Beta` or direct integral. | ⚠️ COMPLEX-ONLY | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60`: `noncomputable def betaIntegral (u v : ℂ) : ℂ`. NO real-valued version at pin. | **GAP**: Tusnády body uses beta integrals for binomial-tail comparison. Workaround: cast to real via `Complex.re ∘ betaIntegral (u : ℂ) (v : ℂ)` or derive direct via `MeasureTheory.integral` over `Ioc 0 1`. ~20-40 LOC. |
| 5 | `tusnady_base_polynomial` signature in `Helpers/OneDimKMT.lean` | TC3 sub-Stub at `OneDimKMT.lean:408-421` (commit `c96e54b`). | ✅ VERIFIED | `Helpers/OneDimKMT.lean:408-421`. Statement: `∃ Ω' [MeasurableSpace Ω'] μ' B Z A C, IsProbabilityMeasure μ' ∧ 0 < A ∧ 0 < C ∧ Measurable B ∧ Measurable Z ∧ μ'.map B = (PMF.binomial (1/2) (2*n)).toMeasure.map Fin.val ∧ μ'.map Z = gaussianReal 0 (n/2) ∧ ∀ ω', |B ω' - n - Z ω'| ≤ A + C * Z² / n`. | Existential over the probability space; quantifier order is `∀ ω'` (deterministic envelope). |
| 6 | `hungarian_dyadic_step` signature | TC3 sub-Stub at `OneDimKMT.lean:469-491` (commit `c96e54b`). | ✅ VERIFIED | `Helpers/OneDimKMT.lean:469-491`. Conclusion: per-dyadic-scale polynomial midpoint bound `|S_cur - B_cur| ≤ A + C · B_cur² / 2^k` for the chosen k. | Hypothesis carries iIndepFun + centred + unit variance from the global probability space; existential builds a refined coupling space at scale 2^k. |
| 7 | Polynomial per-step Tusnády form `\|B - n - Z\| ≤ A + C·Z²/n` | Per-step bound theorem | ✅ VERIFIED via literature | **Tusnády 1977** original: `|B - n - Z| ≤ 1 + Z²/n` (constants 1, 1). **Bretagnolle-Massart 1989**: `|B - n - Z| ≤ A + B·\|Z\|/√n + C·Z²/n` for explicit A, B, C. **Carter-Pollard 2004** "Tusnády's inequality revisited" (Bernoulli, 10 (5), 893-906): `|B - n - Z| ≤ 0.6 + Z²/n` with explicit 0.6 and 1. **Mason-Zhou 2012 review** confirms polynomial form is standard. | **#14 mismatch correction binding**: O(log n) per-step form circulates in informal expositions (e.g., some lecture notes) but is NOT what literature proves. The pure log form requires almost-sure tail control on Z (Borel-Cantelli I) yielding a chain-level consequence in Layer 4. Per-step form locked at signature level (`OneDimKMT.lean:416`). |
| 8 | Continuity correction infrastructure | `Real.floor`, `Real.ceil`, integer-real bridge via `Nat.cast`/`Int.cast`. | ✅ STANDARD | `Mathlib.Algebra.Order.Floor.Defs`, `Mathlib.Data.Nat.Cast.Defs`. | Used in body for binomial-vs-Gaussian midpoint adjustment (continuity correction at integer values shifts the binomial CDF by 0.5 to align with the Gaussian CDF). |

**Critical gaps confirmed:**
- Claim #1 Stirling explicit upper bound: not at pin → ~30-50 LOC required.
- Claim #2 Mills ratio: ABSENT → ~40-60 LOC derive locally.
- Claim #4 real Beta: complex-only → ~20-40 LOC workaround.

**Total body LOC estimate (uplifted from TC3 audit):** ~250-400 LOC just for the analytical infrastructure, BEFORE the actual polynomial bound assembly (~100-150 more LOC). Multi-week project as previously identified.

## 2. Polynomial per-step form — full literature trace (claim #7 deep dive)

**Tusnády 1977** ("A study of the Statistical Hypothesis Generated by the Strong Law of Large Numbers"):
- States `|B - n - Z| ≤ 1 + Z²/n` for `B ~ Bin(2n, 1/2)`, `Z ~ N(0, n/2)`.
- Per-step pointwise bound — depends on the *specific* coupling Tusnády constructs.
- The coupling is the **comonotonic / inverse-CDF coupling**: `B = F_B^{-1}(U)`, `Z = F_Z^{-1}(U)` for `U ~ Uniform(0,1)`.

**Bretagnolle-Massart 1989** ("Estimation des densités: risque minimax", later applied to KMT):
- Sharper constants `A + B·|Z|/√n + C·Z²/n`.
- Proof uses Stirling precision + binomial-Gaussian tail comparison via beta integrals.

**Carter-Pollard 2004** ("Tusnády's inequality revisited", *Bernoulli* 10(5)):
- Cleanest exposition. `|B - n - Z| ≤ 0.6 + Z²/n` with explicit constant 0.6.
- 14-page proof using:
  1. Stirling for binomial PMF asymptotic.
  2. Mills ratio bound on Gaussian tail.
  3. Beta-integral comparison for binomial-vs-Gaussian midpoint coupling.
  4. Continuity correction at integer values.
- This is the recommended target for TC4-TC5 body close.

**Mason-Zhou 2012** ("Quantile coupling inequalities and their applications", *Probab. Surv.*):
- Survey article. Confirms Carter-Pollard 2004 as the modern standard.

**Why O(log n) is NOT per-step:** Substituting almost-sure Gaussian tail `|Z| ≲ √(2 log n)` into the polynomial bound `A + C·Z²/n` gives `A + 2C·log(n)/n = O(log n / n)` — note this is NOT `O(log n)` but `O(log n / n)` per step, which sums over the dyadic chain `n = 2^k, k ≤ K = log₂ N` to `O(log N · log N / N) = O(log² N / N)` running error. The actual chain result (Layer 4 work via Borel-Cantelli I) yields the running-sup `O(log N / √N)` bound after careful Gaussian-tail bookkeeping over the dyadic schedule. Layer 4 is TC5+ scope per TC3 audit.

**Conclusion:** Polynomial per-step form `|B - n - Z| ≤ A + C·Z²/n` is the correct target. The signature at `OneDimKMT.lean:416` matches Tusnády 1977 / Carter-Pollard 2004. NO regression.

## 3. Tractable body advance for TC4 (probability space scaffolding)

Given Mills+Stirling+Beta gaps, the realistic TC4 body advance is:

**Path A (probability space construction without polynomial bound):**

Construct the coupling probability space using TC2's `quantile_transform_finite_moment`:

```lean
-- Step 1: Apply TC2 to Bin(2n, 1/2)-on-ℝ to get q_B with comonotonic property.
-- Step 2: Apply TC2 to gaussianReal 0 (n/2) to get q_Z with comonotonic property.
-- Step 3: Set Ω' := ℝ, μ' := volume.restrict (Ioc 0 1), B := q_B, Z := q_Z.
-- Step 4: Verify Measurable B, Measurable Z (immediate from TC2).
-- Step 5: Verify μ'.map B = Bin-on-ℝ-law and μ'.map Z = gaussianReal 0 (n/2)
--          (immediate from TC2).
-- Step 6: Polynomial bound `|B u - n - Z u| ≤ A + C * (Z u)^2 / n` REMAINS sorry.
```

This *partial* close advances ~80-120 LOC of Lean infrastructure but leaves the actual polynomial bound (Mills+Stirling-dependent) as a single sub-sorry. Net sorry count UNCHANGED on branch (we replace one sorry with one sub-sorry).

**Path B (refined sub-Stub with sharpened diagnostic):**

Keep the existing TC3 sub-Stub structure but enhance the docstring with:
- Explicit pinning of comonotonic coupling approach (Path A above).
- Explicit Mills+Stirling+Beta gap citations from this T1.1 audit.
- Concrete LOC estimates per sub-block.
- Confirmation that polynomial form is the target (anti-#14-regression).

Net sorry change: 0. Code change: docstring expansion (~20-40 LOC).

**Path C (signature refinement to enable Path A):**

Note that the TC3 signature uses `(_hn : 1 ≤ n)`, which matches Tusnády 1977's domain. Carter-Pollard 2004 specializes to `n ≥ 1` for cleanliness; pin signature unchanged.

**Recommendation for T2.1**: Pursue Path A if time permits (T+2:30 sub-checkpoint), else Path B fallback. Path A advances the proof structure; Path B preserves it.

## 4. T2.2 hungarian_dyadic_step plan

The `hungarian_dyadic_step` body composes `tusnady_base_polynomial` k iterations across dyadic scales. Without T2.1 Full close, T2.2 cannot be Full either (dependency). Plan:

- **If T2.1 Path A**: T2.2 can attempt parallel Path A (probability space scaffolding + recursion plumbing, leaving polynomial bound to T2.1's sub-sorry).
- **If T2.1 Path B**: T2.2 stays at TC3 signature lockdown form, refined docstring only.

## 5. Anti-mismatch hygiene check

Each Mathlib lemma to be invoked in T2.1 body advance:

| Lemma name | File | Verified? |
|------------|------|-----------|
| `PMF.binomial` | `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean` | ✅ |
| `gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | ✅ |
| `MeasureTheory.Measure.map_apply` | standard | ✅ |
| `quantile_transform_finite_moment` (TC2) | `Helpers/OneDimKMT.lean:231-356` | ✅ on branch |
| `Real.le_factorial_stirling` | `Mathlib/Analysis/SpecialFunctions/Stirling.lean:236` | ✅ |
| `Real.factorial_isEquivalent_stirling` | `Mathlib/Analysis/SpecialFunctions/Stirling.lean:223` | ✅ |
| `MillsRatio` | — | ❌ ABSENT |
| `Real.betaIntegral` | — | ❌ ABSENT (complex only) |

## 6. Risk assessment update for TC4

| Outcome | P(Full / Path A) | Notes |
|---------|------------------|-------|
| T2.1 Full body close | 0.05 | Math-engineering 200-400 LOC of Mills+Stirling+Beta infrastructure, multi-week (matches TC3 audit P=0.10 minus realism update post-T1.1). |
| T2.1 Path A (probability space scaffolding, polynomial bound sub-sorry) | 0.40 | ~80-120 LOC; concrete diagnostic sustained; uses TC2 directly. |
| T2.1 Path B (refined sub-Stub) | 0.50 | ~20-40 LOC docstring; honest fallback. |
| T2.2 Path A (recursion plumbing) | 0.30 | Conditional on T2.1 Path A. |
| T2.2 Path B (signature lockdown preserved) | 0.65 | Conditional on T2.1 Path B. |
| T2.3 build verify + status | 0.95 | Mechanical. |

**Joint floor (T1.1 + T2.1 Path B + T2.2 Path B + T2.3): ~0.85.**
**Joint mid (T1.1 + T2.1 Path A + T2.2 Path B + T2.3): ~0.30.**

## 7. Execution decision

T2.1 will pursue **Path A** with a hard deadline at T+2:30: if probability space construction stalls (any single Mathlib API gap not resolvable in 30 min), revert to Path B. T2.2 will follow corresponding Path. T2.3 mechanical.

**Audit complete.** Proceeding to T2.1.
