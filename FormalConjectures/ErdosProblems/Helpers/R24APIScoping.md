# R24 API Scoping — Discharge of `R23-bound-pointwise`

**Round 24 single-task**: discharge the residual sorry tagged
`R23-bound-pointwise` in `tsum_Cp_T_explicit_lt_top_R22`. After R23,
the only sorry standing in `GLWGaussianProjectiveLimit.lean` is the
*pointwise bound* `Cp_T_explicit T ≤ ENNReal.ofReal (K / (T+1)^(3/2))`
for an absolute constant K, conditional on T ≥ 1 (T = 0 case Full).

## Verbatim Grok response (Q1–Q7 + bonus, transcribed)

> **Your proposed strategy is clean, correct, and the cleanest practical
> route in current Mathlib4.** It minimizes boilerplate while staying
> fully constructive in `ENNReal`. No step is mathematically or
> formally wrong; the only minor friction points are the usual ENNReal
> coercion dance and the absorption inequality (both very short).
>
> **Q1 (AM-QM trick):** Yes, preferable. Closed-form expansion of
> `(L+k+2)^2 = L^2 + 2L(k+2) + (k+2)^2` requires three separate `tsum`
> identities; AM-QM collapses to two constant series. **One-liner**:
> `have h_sq : (L_T + k + 2)^2 ≤ 2 * (L_T + 2)^2 + 2 * k^2 := by nlinarith`.
>
> **Q2 (`summable_pow_mul_geometric_of_norm_lt_one`):** Exact match.
> File: `Mathlib.Analysis.SpecificLimits.Normed`. Signature:
> `theorem summable_pow_mul_geometric_of_norm_lt_one (k : ℕ) {r : R}
>  (hr : ‖r‖ < 1) : Summable fun n : ℕ => (n : ℝ) ^ k * r ^ n`.
>
> **Q3 (ENNReal path):** **(a) + tiny bit of (b) is shortest.** For S₀:
> use `ENNReal.tsum_geometric ρ` directly. For S_k²: prove summable in
> ℝ, lift with `ENNReal.ofReal_tsum_of_nonneg`. Two lines total.
>
> **Q4 (change of base):** `Real.logb_def : Real.logb b x = Real.log x
> / Real.log b`.
>
> **Q5 (absorption `(T+1)/T³ ≤ 8/(T+1)²`):** Short `calc + nlinarith`.
>
> **Q6 (positivity):** `L_T + 2 > 0` trivially. `positivity` tactic
> eats it.
>
> **Q7 (`K_outer` finite):** Yes. Product/sum of finitely many finite
> ENNReal is finite.

## Local toolchain confirmation

### Confirmed

* **`Real.summable_one_div_nat_rpow`** at `p = 3/2` (already used in
  R23's `summable_K_div_succ_rpow_three_halves`).
* **`summable_pow_mul_geometric_of_norm_lt_one`** at
  `Mathlib/Analysis/SpecificLimits/Normed.lean:485`: signature
  `(k : ℕ) {r : R} (hr : ‖r‖ < 1) : Summable (fun n => (n : R)^k * r^n)`.
* **`summable_geometric_of_norm_lt_one`** at
  `Mathlib/Analysis/SpecificLimits/Normed.lean:274`.
* **`Real.logb`** defined at `Mathlib/Analysis/SpecialFunctions/Log/Base.lean:43`
  as `Real.logb b x = Real.log x / Real.log b`. Companion `log_div_log`
  at line 46 gives the unfold lemma directly.
* **`constL`** defined at
  `.lake/packages/brownian-motion/BrownianMotion/Continuity/KolmogorovChentsovInequality.lean:142`:
  ```
  constL T c d p q β U =
    2 ^ (2*p + 5*q + 1) * c * (diam(U) + 1) ^ (q - d)
    * ∑' k : ℕ, 2 ^ (k * (β·p - (q-d)))
        * (4^d * ofReal(logb 2 c.toReal + (k+2)·d)^q + Cp d p q)
  ```
* **`Cp`** defined at
  `.lake/packages/brownian-motion/BrownianMotion/Continuity/IsKolmogorovProcess.lean:515`:
  ```
  Cp d p q = max (1 / ((2^((q-d)/p)) - 1)^p) (1 / (2^(q-d) - 1))
  ```
  For `d=1, p=q=2`: `Cp 1 2 2 = max(1/(√2-1)², 1/(2-1)) = max(~5.83, 1)
  ≈ 5.83`.
* **R23 helpers (load-bearing)**:
  - `log_sq_le_sqrt`: `(log x)^2 ≤ 16 · x^(1/2)` for `x ≥ 1`.
  - `summable_K_div_succ_rpow_three_halves`: summability of bound.
  - `K_div_succ_rpow_nonneg`: nonneg of bound for ofReal lift.

### Not present (Grok over-reported)

* **`ENNReal.tsum_geometric`** does NOT exist as a named lemma in
  Mathlib HEAD. Grok asserted it as a "direct closed form
  `(1-r)⁻¹`". The actual route is to prove summability in ℝ for the
  S₀ piece via `summable_geometric_of_lt_one (h0 : 0 ≤ ρ) (h1 : ρ < 1)`
  with `ρ = 2^(-1/2)`, then lift via `ENNReal.ofReal_tsum_of_nonneg`.
  Adds ~3 LOC vs the projected direct route. **Skin-in-the-game clause
  not triggered**: this is plumbing-shape correction, not a strategy
  error.

### No black-box `constL` quantitative bound

* `constL_lt_top` (line 147) gives finiteness only.
* No `constL_le_log_squared_times_c` or similar: the inner-tsum
  unfolding is required.

## Strategy commitments (A, B, C — pre-flighted)

### A — AM-QM simplification trick

```
∀ L : ℝ, ∀ k : ℕ, (L + k + 2)^2 ≤ 2 * (L + 2)^2 + 2 * k^2
```

via `nlinarith`. Skips the closed-form tsum-of-`A_n` arithmetic of
expanding `(L + (k+2))² = L² + 2L(k+2) + (k+2)²` into three separate
power-series moments.

### B — geometric × polynomial summability

* **S₀** = `∑' k : ℕ, (2^(-1/2))^k = (1 - 2^(-1/2))⁻¹ ≤ 4` (real).
* **S_k²** = `∑' k : ℕ, k² · (2^(-1/2))^k < ∞` via
  `summable_pow_mul_geometric_of_norm_lt_one 2`.

Both lifted to ENNReal via `ENNReal.ofReal_tsum_of_nonneg`.

### C — `constL` unfolding strategy

Self-contained: unfold `constL` directly via the `def` at
`KolmogorovChentsovInequality.lean:142`, propagate the AM-QM bound
through the tsum via `ENNReal.tsum_le_tsum`, multiply by prefactors
`2^15 · c_T · (diam+1)`, multiply by `M_T = 1/(2T³)`, absorb
`(T+1)/T³ ≤ 8/(T+1)²` (T ≥ 1), apply `log_sq_le_sqrt` to get the
final `K_total / (T+1)^(3/2)` bound.

## Realistic LOC estimate

- AM-QM lemma: ~5 LOC.
- S₀ bound (real): ~10 LOC.
- S_k² bound (real): ~15 LOC.
- Inner tsum `S(T)` ENNReal bound (linearity): ~30-50 LOC.
- `constL T c_T 1 2 2 (1/4) univ` ≤ explicit polynomial: ~30-50 LOC.
- Multiply by M_T, absorb to `K/(T+1)^(3/2)`: ~30-50 LOC.
- `log_sq_le_sqrt` applied to absorption: ~10 LOC.

Total: **~150-250 LOC**. Grok's "15-20 lines" estimate is
aspirational; even with optimal API knowledge the ENNReal arithmetic
plumbing alone runs 5-10× that.

## Skin-in-the-game posture

Commitments A, B, C are intact. The Grok over-report on
`ENNReal.tsum_geometric` is a **plumbing variation, not a strategy
error**: the workaround (real summability + `ofReal_tsum_of_nonneg`
lift) is mechanical and adds 3 LOC. Therefore the skin-in-the-game
clause does not trigger at T1.1; it remains binding for T2.1 if a
*new class* of error surfaces (e.g., a Mathlib lemma asserted to
exist that doesn't, beyond what's listed here).

R24 proceeds with the strategy as-stated, with the lift correction
integrated. **Predicted P(T2.1 Full): downgraded from 0.72 to 0.55**
given the LOC realism check + the surfaced Grok over-report. The
project remains within the 350-600 base + 55% chance of +500 bonus
expected-value envelope.
