# R25 API Scoping — skeleton review

**Round 25** · LOC-level pre-flight protocol · Cowork-authored skeleton · Local Claude reviewing

## Skeleton structural review

Walking the 8 sub-sorries of `Cp_T_explicit_le_log_sq_R25` against:
- Mathlib HEAD signatures (Lean 4.27.0-rc1)
- brownian-motion `KolmogorovChentsovInequality.lean:142` — `constL` definition
- the four R24-landed aux lemmas:
  - `am_qm_three_term : ∀ (L : ℝ) (k : ℕ), (L + k + 2)² ≤ 2(L+2)² + 2k²`
  - `summable_S_zero_real : Summable (fun k : ℕ => (2 ^ (-(1/2 : ℝ))) ^ k)`
  - `summable_S_ksq_real : Summable (fun k : ℕ => (k : ℝ)² * (2 ^ (-(1/2 : ℝ)))^k)`
  - `diam_unit_block_le_one (T : ℕ) : EMetric.diam (Set.univ : Set ↥(Set.Ico T (T+1))) ≤ 1`

### Per-sub-sorry assessment

| Sub-sorry | Type-checks? | Mathlib API confirmed? | Cowork's LOC budget realistic? | Notes |
|-----------|:------------:|:----------------------:|:------------------------------:|-------|
| step-0a (`ρ < 1` in ℝ≥0∞) | ✓ | `ENNReal.rpow_lt_one_of_one_lt_of_neg` exists; `(2 : ℝ≥0∞) ^ (-1/2 : ℝ)` is well-formed via `ENNReal.rpow` | Yes (3 LOC) | one-liner |
| step-0b (L_T positivity) | ✓ | `Real.logb_def`, `Real.log_pos` | Yes (5 LOC) | log_2(12) > 0 is trivial |
| step-1 (S(T) bound via AM-QM) | ✓ | `ENNReal.tsum_le_tsum`, `ENNReal.tsum_add`, `ENNReal.tsum_mul_left`, `ENNReal.ofReal_tsum_of_nonneg`, `am_qm_three_term`, `summable_S_zero_real`, `summable_S_ksq_real` | Tight (30 LOC) | AM-QM + lift |
| step-2 (constL unfold) | ⚠️ **constant `2^16` numerically wrong** | `constL` def matches; arithmetic on `2^15 · c_T · (diam+1)` straightforward | Tight, fixable with `2^19` | See note below |
| step-3a (absorption) | ✓ | `nlinarith` for the real arithmetic; `ENNReal.ofReal_le_ofReal` to lift | Yes (20 LOC) | `(T+1)/(2T³) ≤ 4/(T+1)²` ⇔ `(T+1)³ ≤ 8T³` ⇔ `T ≥ 1`. Sound |
| step-3b (M_T · constL) | ✓ | `ENNReal.mul_le_mul`, unfold `Cp_T_explicit` | Yes (15 LOC) | mechanical |
| step-4 (logb change) | ✓ | `Real.logb_def` (= `log/log`), `Real.log_mul` (`log(6(T+1)) = log 6 + log(T+1)`) | Yes (15 LOC) | `(a+b)² ≤ 2a² + 2b²` |
| step-5 (final calc) | ⚠️ algebra needs care | `ENNReal.ofReal_pow`, `ENNReal.ofReal_mul`, lift to match goal RHS shape | Tight (30 LOC) | The `(log + K_inner)²` lower bound `≥ K_inner² + log²` requires `log ≥ 0` (which is true for T ≥ 1) |

### Issues found (NOT zero-cap)

**Step 2 numerical constant.** The skeleton claims `2^15 · c_T · (diam+1) · S(T) ≤ 2^16 · (T+1) · S_bound`. Plugging in `c_T = 6(T+1)` and `(diam+1) ≤ 2`:

```
2^15 · 6(T+1) · 2 · S = 2^15 · 12 · (T+1) · S
```

For `2^15 · 12 ≤ 2^16 = 2^15 · 2`, we'd need `12 ≤ 2`, which is false. So `2^16` is too tight by factor 6.

**Resolution:** Replace `2^16` with `2^19` (since `12 ≤ 16 = 2^4`, we get `2^15 · 12 ≤ 2^19`). The skeleton author's own comment (lines after step-2 sorry) flagged this: *"with slack since 2^15·12 ≤ 2^15·16 = 2^19; tightening optional"* — but then wrote `2^16` in the goal. **Local Claude will use `2^19` in the discharge.**

This is a NUMERICAL bound issue in skeleton authorship — the goal shape is structurally fine, only the constant value needs adjusting. Per the zero-cap clause this is NOT a structural error: type composition is preserved.

**Step 1 ofReal-vs-rpow shape.** The constL inner term is `(ENNReal.ofReal (logb 2 c.toReal + (k+2)*d))^q`. With `q = 2`, this is `(ofReal X)^2`. The skeleton's `h_S_bound` writes `4 * ENNReal.ofReal ((L_T + k + 2)^2) + Cp 1 2 2`, which uses `ofReal((...)²)`. These agree iff `L_T + k + 2 ≥ 0` (which we have for T ≥ 1, since `L_T ≥ logb 2 12 > 0`). Lift via `ENNReal.ofReal_pow` after non-negativity. **OK.**

### The four R24 aux lemmas — signature compatibility

All four match the skeleton's invocations verbatim:
- `am_qm_three_term L_T k` produces `(L_T + k + 2)² ≤ 2(L_T+2)² + 2k²` ✓
- `summable_S_zero_real`, `summable_S_ksq_real` provide the real-valued summability that lifts via `ENNReal.ofReal_tsum_of_nonneg` ✓
- `diam_unit_block_le_one T` provides the diam ≤ 1 needed in step 2 ✓

### The chain to retire `Y_GLW_exists`

After `Cp_T_explicit_le_log_sq_R25` lands, we still need to chain through `log_sq_le_sqrt` (R23 Full) to discharge the *existing* R23-bound-pointwise sorry at line 1806:

```
Cp_T_explicit T ≤ ENNReal.ofReal (K_total / (T+1)^(3/2))   for T ≥ 1
```

Path:
1. From `Cp_T_explicit_le_log_sq_R25`: `Cp_T_explicit T ≤ K_outer · (log(T+1) + K_inner)² / (T+1)²`
2. `(log(T+1) + K_inner)² ≤ 2(log(T+1))² + 2 K_inner²` (Cauchy-Schwarz / am_qm_two_term)
3. `(log(T+1))² ≤ 16 · √(T+1)` from `log_sq_le_sqrt`
4. So RHS ≤ `K_outer · (32√(T+1) + 2 K_inner²) / (T+1)² ≤ K_total / (T+1)^(3/2)` for some `K_total` (since `√(T+1)/(T+1)² = 1/(T+1)^(3/2)` and `1/(T+1)² ≤ 1/(T+1)^(3/2)` for T ≥ 0).

Estimated additional ~30-50 LOC for the chain.

## Recommendation

**Proceed with discharge** in order 0a → 0b → 3a → 3b → 4 → 1 → 2 → 5, then chain to R23-pointwise. Honesty: **the sub-sorries 1, 2, 5 are the load-bearing ones**; 0a, 0b, 3a, 3b, 4 are mechanical and very likely to land Full.

LOC actuals will be reported in T4.1.

---

**T1.1 self-rating: Full.** Skeleton type-checks structurally; one numerical-constant adjustment needed in step 2 (`2^16` → `2^19`) but not a zero-cap structural issue. Four R24 aux lemmas confirmed compatible.
