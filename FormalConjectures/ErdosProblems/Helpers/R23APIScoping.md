# R23 — API scoping for `tsum_Cp_T_explicit_lt_top_R22`

R23 mono-task: discharge the single named sorry in
`Helpers/GLWGaussianProjectiveLimit.lean` at the bottom of the file
(R22 / T4.3 stub `tsum_Cp_T_explicit_lt_top_R22`). Once Full, the BC
closure on the dense-iSup block events is sorry-free, conjunct 9 of
`glwGaussianLimit_Y_GLW_existence` lands Full, and the Y_GLW_exists
axiom in `Helpers/GLWProcess.lean` retires.

This document scopes the Mathlib API used in the T2.1 discharge and
records the Grok validation transcript verbatim.

## Commitment A — Asymptotic decomposition (corrected)

For each `T : ℕ` with `T ≥ 1`, the explicit chaining-moment constant
unfolds as

```
Cp_T_explicit T = (ofReal(1/(2T³)) : ℝ≥0∞)
  * 2^15 · c_T · (diam_S + 1) · ∑' k, 2^(-k/2) · (4 · ofReal((log_2(c_T.toReal) + (k+2))²) + Cp_const)
```

with `c_T = 6 * (T+1 : ℝ≥0∞)`, `S = Set.Ico T (T+1) ⊂ NNReal`,
`diam_S ≤ 1` (so `diam_S + 1 ≤ 2`), and `Cp_const = Cp 1 2 2 < ∞`.

The cleanest split (Cauchy-Schwarz on the inner square):

```
(log_2(c_T.toReal) + (k+2))² ≤ 2 · (log_2(c_T.toReal))² + 2 · (k+2)²
```

separates the `k`-sum from the `T`-dependence, leaving:

```
constL ≤ 2^15 · c_T · 2 · (8 · ofReal((log_2(c_T.toReal))²) · S_geom + 8 · S_quad + Cp_const · S_geom)
```

where `S_geom = ∑' k, 2^(-k/2) < ∞` and `S_quad = ∑' k, 2^(-k/2) · (k+2)² < ∞`.

Both `S_geom` and `S_quad` are absolute (T-independent), and finite by
the standard polynomial × geometric summability.

## Commitment B — Summability comparison (α = 1/2, p = 3/2)

The asymptotic `(Real.log x)² = O(x^(1/2))` for x ≥ 1 can be proved
*uniformly* (without an N₀ threshold) via `Real.log_le_rpow_div`:

```
Real.log x ≤ x^(1/4) / (1/4) = 4 · x^(1/4)   for x ≥ 0
```

Squaring: `(log x)² ≤ 16 · x^(1/2)` for `x ≥ 0`.

Combined with `log_2 c = log c / log 2`, this gives an absolute bound
`(log_2 c)² ≤ K · c^(1/2)`.

For our `c_T = 6(T+1)`:

```
(log_2(6(T+1)))² ≤ K_log · (T+1)^(1/2) ≤ K_log · 2 · T^(1/2)   for T ≥ 1
```

Thus:

```
Cp_T_explicit T ≤ ofReal(K_main / T^(3/2)) + ofReal(K_minor / T^2)
```

for absolute `K_main, K_minor`. Both terms are summable by
`Real.summable_one_div_nat_rpow` at p = 3/2 > 1.

## Commitment C — ENNReal coercion plumbing

The proof composes through:

* `ENNReal.tsum_le_tsum (h : ∀ a, f a ≤ g a) : ∑' a, f a ≤ ∑' a, g a`
* `ENNReal.tsum_lt_top` via `Summable.hasSum`
* `ENNReal.ofReal_tsum_of_nonneg` to drop into ℝ-summability
* `Real.summable_one_div_nat_rpow {p : ℝ} : Summable (fun n => 1 / (n:ℝ)^p) ↔ 1 < p`

No `ENNReal.toReal` round-trip on potentially-infinite quantities.

## Mathlib API confirmations

| Lemma | File | Purpose |
|-------|------|---------|
| `Real.summable_one_div_nat_rpow` | `Mathlib/Analysis/PSeries.lean:293` | p-series at p > 1, real-valued |
| `Real.summable_nat_pow_inv` | `Mathlib/Analysis/PSeries.lean:300` | p-series, natural p |
| `Real.log_le_rpow_div` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:880` | `log x ≤ x^ε/ε` for x ≥ 0, ε > 0 |
| `ENNReal.tsum_le_tsum` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:620` | Pointwise bound on ENNReal tsums |
| `ENNReal.ofReal_tsum_of_nonneg` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:1074` | ENNReal → ℝ tsum coercion |
| `summable_one_div_nat_pow` | `Mathlib/Analysis/PSeries.lean:306` | p-series ℕ exponent |
| `constL` | `BrownianMotion/Continuity/KolmogorovChentsovInequality.lean:142` | The chaining constant |
| `constL_lt_top` | `BrownianMotion/Continuity/KolmogorovChentsovInequality.lean:147` | Per-T finiteness (used in R22 `Cp_T_explicit_lt_top`) |

## Grok validation transcript (verbatim)

> **All steps are correct.** No errors in the math, the chaining bound, the expansion of `constL`, the asymptotic for `Cp_T_explicit T`, or the summability argument. The only minor note is that the suggested N₀ ≈ 30 for α = 1/4 is too optimistic (see Q2 below), but the underlying principle is fine.
>
> **1. Asymptotic `Cp_T_explicit T = O((log T)² / T²)`** — Yes, exactly correct (and the constant K is finite and independent of T). `constL` expands precisely as written: prefactors 2¹⁵ ⋅ 6(T+1) ⋅ 2 are linear in (T+1). Inner tsum splits as `S_geom`, `∑ 2^{-k/2}(k+2)`, `∑ 2^{-k/2}(k+2)²` — all convergent (geometric × polynomial). Thus `S_quad(T) ≤ C₁ L² + C₂ L + C₃ ≤ C(L+1)²` for absolute C. Multiplying by M_T = 1/(2T³) and absorbing `(T+1)/T³ ≤ 2/T²` (T ≥ 1) gives the claimed bound. K_outer is finite.
>
> **2. Summability comparison** — Yes, `(log x)² = o(x^α)` is standard for any α > 0. **However: N₀ ≈ 30 for α = 1/4 is an underestimate** — the actual crossover is on the order of **10¹¹–10¹²**, harmless mathematically but inconvenient in Lean (huge explicit N₀ is annoying to verify by `norm_num`).
>
> **3. Recommended Lean route**: **(3b) α = 1/2, comparison to p = 3/2.** Reasons: (a) p=3/2 is the most "standard" p-series in Mathlib (cleanest `summable` lemma); (b) α=1/4 forces an impractically large N₀; (c) for α=1/2 with reasonable c (~10), N₀ ≈ 10⁴–3·10⁴ is enough — **safe default N₀ = 10⁵ (or even 10⁶)**. Discharge in Lean by `calc` block + `norm_num`/`linarith`, or by appeal to `tendsto` lemmas for `log_pow_div_pow`. **Alternative (3c) Cauchy condensation**: `∑(log n)²/n² < ∞ ⇔ ∑ k²(log 2)²/2^k < ∞` (RHS = polynomial × geometric, Mathlib `summable_mul` + `summable_geometric` + `summable_k_pow_r_pow`). Slick and avoids N₀ entirely if `summable_condensed_iff` is available.
>
> **4–5. Anything missed?** Nothing material. K_outer < ∞ as stated. Routine ENNReal ↔ ℝ coercions (`ENNReal.coe_le_coe`, `ENNReal.summable_coe`, `toReal_tsum`) are needed since `constL` lives in ENNReal. `Real.summable_one_div_nat_rpow` (or its ENNReal sibling) is the right hammer once you have the comparison.
>
> **Summary:** Math is flawless and the Lean route works. Bump α to 1/2 (or use Cauchy condensation) for a comfortable N₀, and the discharge goes through cleanly with standard `summable` lemmas + a short comparison block.

## R23 deviation: stronger uniform `(log)² ≤ rpow` bound

R23 plumbs the proof through `Real.log_le_rpow_div` at α = 1/4, which
is uniform in `x ≥ 0` (no threshold). Squaring: `(log x)² ≤ 16 √x`.
This avoids both the N₀ split and the Cauchy condensation route.

The route is:

1. Prove `S_geom < ∞` and `S_quad < ∞` (geometric × polynomial).
2. Prove `tsum_inner(c) ≤ 8 · ofReal((log_2 c.toReal)²) · S_geom + Const_inner`
   for absolute `Const_inner < ∞`.
3. Prove `(log_2(6(T+1)))² ≤ K_log · √T` for `T ≥ 1` (uniform via
   `log_le_rpow_div` at α = 1/4).
4. Compose: `Cp_T_explicit T ≤ ofReal(K_main / T^(3/2)) + ofReal(K_minor / T²)`.
5. Sum: each term is a p-series at p = 3/2 or p = 2, both > 1.

## R23 status

- T1.1 (this doc): Full (Mathlib lemmas grep-confirmed, Grok response transcribed).
- T2.1: in progress.
