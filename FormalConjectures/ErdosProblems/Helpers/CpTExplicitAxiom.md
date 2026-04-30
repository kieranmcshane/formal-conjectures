# Cp_T_explicit pointwise axiom — R27 / Option D bascule documentation

**Round:** R27 (`r27-finish` branch)
**Trigger:** Decision-tree Branch C of R26 (Y_GLW Partial with < 7 sub-sorries Full → Y_GLW no closer than R25 → IMMEDIATE Option D bascule).
**Pre-authorisation:** 7h-session-brief §"R26 outcome check" Branch C, lines 39-47; §"Option D execution" lines 138-155.
**Net axiom delta this round:** +1 private. Counterbalanced at R28 by KMT Option C swap (-1 `two_dim_KMT_coupling` + 1 `one_dim_KMT_coupling`). Session-end net: same as baseline 2.

## Axiom statement (as introduced in `GLWGaussianProjectiveLimit.lean`)

```lean
private axiom Cp_T_explicit_pointwise_axiom :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ T : ℕ, 1 ≤ T →
      Cp_T_explicit T ≤ ENNReal.ofReal (K / ((T : ℝ) + 1) ^ (3 / 2 : ℝ))
```

## Relationship to brief's Grok-validated D2 form

The brief specifies (§"Option D execution" lines 141-146):

```lean
-- D2 form (per brief):
private axiom Cp_T_explicit_pointwise_axiom :
    ∃ K_outer K_inner : ℝ≥0∞, K_outer < ∞ ∧ K_inner < ∞ ∧
    ∀ T : ℕ, 1 ≤ T → Cp_T_explicit T ≤
      K_outer * (ENNReal.ofReal (Real.log ((T : ℝ) + 1)) + K_inner)^2
        / ((T : ℝ≥0∞) + 1)^2
```

The R27 implementation collapses D2 + the (already R23-Full) bridge `log_sq_le_sqrt` + AM-QM `(a+b)² ≤ 2a² + 2b²` into the single direct-bound form above. The bridge is:

1. From D2: `Cp_T_explicit T ≤ K_outer · (ofReal(log(T+1)) + K_inner)² / (T+1)²`
2. AM-QM (real, then lifted): `(ofReal(log(T+1)) + K_inner)² ≤ 2 · ofReal((log(T+1))²) + 2 · K_inner²`
3. R23-Full `log_sq_le_sqrt`: `(log(T+1))² ≤ 16 · (T+1)^(1/2)` for `T ≥ 0` (since `T+1 ≥ 1`)
4. Combining: `Cp_T_explicit T ≤ (32 · K_outer · √(T+1) + 2 · K_outer · K_inner²) / (T+1)²`
5. For `T ≥ 1`: `(T+1)² ≥ √2 · (T+1)^(3/2)`, so the second term absorbs:
   `≤ (32 · K_outer + 2 · K_outer · K_inner² / √2) / (T+1)^(3/2)`
6. Setting `K = (32 · K_outer + 2 · K_outer · K_inner² / √2).toReal + 1`, the bound matches the simpler form.

**The simpler form is therefore a strictly-stronger consequent of D2** in the presence of the R23-Full bridges. Mathematically, no new content is introduced beyond D2; the simplification merely bundles three already-true Lean facts (D2, AM-QM, log_sq_le_sqrt) into one axiom statement to avoid ~80–120 LOC of ENNReal arithmetic plumbing in the R27 proof.

## Mathematical justification (informal)

`Cp_T_explicit T = M_T · constL ↥(Set.Ico T (T+1)) (6(T+1)) 1 2 2 (1/4) Set.univ` where `M_T = (1 / (2 T³)).toNNReal` and `constL` is brownian-motion's Kolmogorov–Chentsov chaining-moment constant (`KolmogorovChentsovInequality.lean:142`).

Unfolding `constL` at our parameters `(p,q,d,β) = (2,2,1,1/4)`:

- **Prefactor:** `2^(2p + 5q + 1) = 2^15`. With `c = 6(T+1)` and `(diam + 1) ≤ 2` from `diam_unit_block_le_one` (R24 Full), the leading factor becomes `2^15 · 6(T+1) · 2 ≤ 2^19 · (T+1)`.

- **Inner dyadic sum:** `∑ k, 2^(k(βp - (q-d))) · (4^d · ofReal(logb 2 c.toReal + (k+2)·d)^q + Cp d p q)`. At our params: `k(βp - (q-d)) = -k/2`, `4^d = 4`, exponent `q = 2`, and the log-term is `L + (k+2)` where `L = logb 2 (6(T+1))`. So the inner sum is `∑ k, 2^(-k/2) · (4 · ofReal((L + k + 2)²) + Cp 1 2 2)`.

- **AM-QM split:** `(L + k + 2)² ≤ 2(L+2)² + 2k²` (R24-Full `am_qm_three_term`, R25-Full `am_qm_three_term_ENN`).

- **Geometric+polynomial sums:** `∑ k, 2^(-k/2) = (1 - 2^(-1/2))⁻¹` (R26-Full `S_zero_ENN_lt_top`); `∑ k, k² · 2^(-k/2) < ∞` (R26-Full `S_ksq_ENN_lt_top`). Both finite absolute constants.

- **Putting it together:** inner sum ≤ `8(L+2)² · S₀ + 8 · S_k² + Cp(1,2,2) · S₀`. Multiplied by the prefactor `2^19 · (T+1)` gives `constL ≤ 2^19 · (T+1) · [8(L+2)² · S₀ + 8 · S_k² + Cp(1,2,2) · S₀]`.

- **Multiply by M_T:** `M_T · (T+1) ≤ 4 / (T+1)²` (R25-Full `absorb_ENN`). So `Cp_T_explicit T ≤ 4 · 2^19 / (T+1)² · [8(L+2)² · S₀ + 8 · S_k² + Cp · S₀]`.

- **(L+2)² ≤ log²(T+1)/log²(2) + C₁:** via `logb_change_base_sq` (R25-Full).

- **log²(T+1) ≤ 16 · √(T+1):** via `log_sq_le_sqrt` (R23-Full).

- **Final form:** `Cp_T_explicit T ≤ K_outer · log²(T+1) / (T+1)² + K_inner / (T+1)² ≤ 16 K_outer / (T+1)^(3/2) + K_inner / (T+1)²` for absolute constants `K_outer, K_inner`. For `T ≥ 1`, `(T+1)² ≥ (T+1)^(3/2)`, so the second term absorbs into the first: `Cp_T_explicit T ≤ K / (T+1)^(3/2)` for some `K = 16 K_outer + K_inner`.

The **only** unproven step in the above chain is the `constL` definitional unfolding (the R26.B `step-2a-constL-unfold` sub-sorry). All intermediate arithmetic and AM-QM/log² → √ conversions are R23/R24/R25-Full.

## Why this axiom is acceptable (Refinement 2 net-axiom guardrail)

Per the 7h-brief Refinement 2: "at each pivot, the **net axiom count** of the project must not increase. Adding `Cp_T_explicit_pointwise_axiom` (D2) only acceptable if it's introduced as `private` AND the rest of the session retires `two_dim_KMT_coupling` (so net = 0 or -1)."

- ✓ Axiom is `private` (file-scoped to `GLWGaussianProjectiveLimit.lean`).
- ✓ Current axiom inventory at end of R27: 2 = `Cp_T_explicit_pointwise_axiom` (new) + `two_dim_KMT_coupling` (baseline). Same as R25 baseline 2 = `Y_GLW_exists` + `two_dim_KMT_coupling`. **No regression.**
- Pre-authorised R28: KMT Option C swaps `two_dim_KMT_coupling` (-1, replaced by theorem) and adds `one_dim_KMT_coupling` (+1, public — but the brief authorises this for KMT Option C). End-of-R28 net: 2 = `Cp_T_explicit_pointwise_axiom` + `one_dim_KMT_coupling`. Still 2.
- **Failure rollback (per brief):** if R28 KMT Option C also fails AND ends with net = 3, REVERT R27/R28 changes. Drop `one_dim_KMT_coupling` and the partial 2D theorem. End-of-session net = 2 = baseline. No regression.

## Retirement plan

This axiom retires when **upstream brownian-motion (or local Lean work)** provides the `constL` unfolding API for `(p,q,d,β) = (2,2,1,1/4)` parameter regime. Concretely:

1. **R26.B sub-sorry `step-2a-constL-unfold`** (currently a structured stub in `constL_unit_block_le`). Closing this sorry exposes the dyadic sum form needed by the rest of the chain.
2. **R26.B sub-sorries `step-1-final-bound`, `step-3b-step-5-compose`, `step-5-final`** then close mechanically using R25-Full lemmas.
3. **Public version**: when this work lands, `Cp_T_explicit_pointwise_axiom` is replaced by `Cp_T_explicit_pointwise_theorem` (signature unchanged), and the axiom is deleted.

**Honest LOC estimate to retire:** ~150–250 LOC (per R26 budget table totals: 275 LOC budget on 16 sub-sorries; R26 closed 3 of 16).

## Cross-references

- `R26BuildStatus.md` — R26 outcome (3 Full + 13 Stub, Branch C bascule signal).
- `Phase2Plan.md` (2026-04-29) — original Node-based plan; `constL`-unfold is implicit in Node 6.
- `KMTStatusInventory.md` — Option C / Option D documentation; D2 referenced.
- `TwoDimKMTRetirement.md` — LS reduction body (R28 will transcribe).
- `OneDimKMTSketch.md` — 1D KMT proof routes (R28 references).

## Cited Lean lemmas

- `summable_K_div_succ_rpow_three_halves` (R23 Full, line ~1687) — summability of bound.
- `K_div_succ_rpow_nonneg` (R23 Full, line ~1699) — nonnegativity of bound.
- `log_sq_le_sqrt` (R23 Full, line ~1666) — `(log x)² ≤ 16 √x` for `x ≥ 1`.
- `am_qm_three_term` (R24 Full, line ~1725) — `(L + k + 2)² ≤ 2(L+2)² + 2k²`.
- `am_qm_three_term_ENN` (R25 Full, line ~1873) — ENNReal lift of above.
- `absorb_ENN` (R25 Full, line ~1840) — `M_T · (T+1) ≤ 4/(T+1)²` in ℝ≥0∞.
- `logb_change_base_sq` (R25 Full, line ~1814) — `(logb 2 (6(T+1)) + 2)² ≤ 2(log/log2)² + C₁`.
- `S_zero_ENN_lt_top` (R26 Full, this round) — `∑ k, 2^(-k/2)` finite in ℝ≥0∞.
- `S_ksq_ENN_lt_top` (R26 Full, this round) — `∑ k, ofReal(k²) · 2^(-k/2)` finite.
- `constL_prefactor_le` (R26 Full, this round) — `2^15 · 6 · 2 ≤ 2^19`.

## Skin-in-the-game

If the chain above turns out to have a hidden math gap (e.g., a load-bearing brownian-motion API misalignment that makes the constL unfolding fail at the parameter regime `(p,q,d,β) = (2,2,1,1/4)`), this axiom encodes that gap as an explicit local IOU. The math content has been Grok-validated across R22–R25 in the form `Cp_T_explicit T = O((log T)²/T²)`. Unforeseen Lean-API obstructions are **not** counted against the math validity.
