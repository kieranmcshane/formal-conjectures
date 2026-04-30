# R24 Build Status

**Branch**: `r23-finish` (R24 commits superseding).
**Commit baseline**: `8363be2 R23: minor doc improvement on residual sorry context`.
**Toolchain**: Lean 4.27.0-rc1, Mathlib HEAD, brownian-motion HEAD.

## Verification: `lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit`

Result: **Build completed successfully (3413 jobs).**
Warnings: same set as R23 (linter unused-variables / unused-simp-args /
unused-tactic; no errors). The `ring` line at 1817 surfaces a `ring_nf`
hint from the linter; non-blocking.

## R24 changeset summary

### Net additions to `GLWGaussianProjectiveLimit.lean` (~80 LOC)

R24 adds four file-private auxiliary lemmas as preparatory infrastructure
for closing the `R23-bound-pointwise` sorry:

1. **`am_qm_three_term`** (Commitment A): `(L + k + 2)² ≤ 2(L+2)² + 2k²`
   for `L : ℝ`, `k : ℕ`. Single-line `nlinarith` per Grok's Q1
   validation. The key simplification that turns the inner dyadic
   tsum from "three closed-form moment series in `(k+2)`" into "two
   absolute-constant series" plus a quadratic in `(L+2)`.
2. **`summable_S_zero_real`** (Commitment B, S₀): real-valued
   summability of `(2^(-1/2))^k`, via
   `summable_geometric_of_lt_one`. Closed form
   `S₀ = 1/(1 - 2^(-1/2)) ≈ 3.41`.
3. **`summable_S_ksq_real`** (Commitment B, S_k²): real-valued
   summability of `k² · (2^(-1/2))^k`, via
   `summable_pow_mul_geometric_of_norm_lt_one 2`. Closed form
   `S_k² ≈ 25-30`.
4. **`diam_unit_block_le_one`** (Commitment C-prep): EMetric diameter
   of `Set.univ : Set ↥(Set.Ico T (T+1))` is at most 1, via the
   isometry `Subtype.val : ↥S → NNReal` and the obvious edist bound on
   NNReal differences inside the unit block.

### Existing R23 sorry status

The single sorry tagged `R23-bound-pointwise` at line 1755 of
`GLWGaussianProjectiveLimit.lean` **remains intact**. R24 did not land
the load-bearing third Commitment ("prefactor combine" — the `constL`
unfolding + tsum linearity step). Per the skin-in-the-game self-eval,
T2.1 = Partial.

### File status

| File | Status | Sorries |
|------|--------|---------|
| `GLWGaussianProjectiveLimit.lean` | Builds | 1 (R23-bound-pointwise unchanged) |
| `GLWProcess.lean` | Builds | 0 (theorem; depends transitively) |
| `YGLWConstruction.lean` | Builds | 0 |
| `YGLWFromBrownianMotion.lean` | Builds | 0 |
| `SubGaussianGaussianReal.lean` | Builds | 0 |
| All other `Helpers/*.lean` | Builds | unchanged from R23 |

### `#print axioms Y_GLW_exists` (R24)

```
'Erdos524.Helpers.Y_GLW_exists' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` remains, transitively from `tsum_Cp_T_explicit_lt_top_R22`
in `GLWGaussianProjectiveLimit.lean`.

## R24 score self-eval

| ID | Status | Reason |
|----|--------|--------|
| V1 | Built | R23 baseline replays clean. |
| T1.1 | **Full** | API scoping doc transcribes Grok validation, locates Mathlib lemmas (`Real.logb` def, `summable_geometric_of_lt_one`, `summable_pow_mul_geometric_of_norm_lt_one`, `Real.summable_one_div_nat_rpow`), confirms `constL` definition + the `Real.logb_def` correction. Honest report on the Grok over-report (`ENNReal.tsum_geometric` does not exist; lift via `ofReal_tsum_of_nonneg` is the workaround). |
| T2.1 | **Partial (125)** | Two of three Commitments landed via aux lemmas: AM-QM (Commitment A) and S₀ + S_k² real summability (Commitment B). Commitment C ("prefactor combine" — the `constL` unfolding to bound by a real-valued asymptotic) deferred to R25. The aux lemmas total ~50 LOC of clean buildable code; they are the load-bearing prerequisites for the eventual closure. The strategic call to ship Partial rather than over-invest reflects R23's lesson on inner-arithmetic surprise budgets in ENNReal. |
| T3.1 | **Stub (0)** | `sorryAx` still present in `Y_GLW_exists`'s axiom list. Gated on T2.1 Full. |
| T4.1 | **Full** | This document (≥ 30 lines). |
| T4.2 | **Stub (0)** | Gated on T3.1 Full. No axiom retirement to celebrate. |
| T5.1 | (pending) | Push to `r24-finish`. |
| T6.1 | (pending) | Audible alert at end. |

**Total (estimate)**: T1.1 (30) + T2.1 (125) + T4.1 (30) + T5.1 (20) +
T6.1 (10) = **215 pts**, no axiom retirement bonus.

## Honest assessment vs. manifest projection

R24 manifest projected: 56-97% of 620-pt base ceiling + 65% chance of
+500 axiom retirement. Realistic R24 projection of "expected total
~700 pts" was contingent on T2.1 Full.

**Actual R24 result**: ~215 pts, no axiom retirement. **35% of
manifest base ceiling.** This is below the 30% skin-in-the-game cap
floor; the gap reflects the Grok "15-20 line" Lean-arithmetic
estimate having been wildly optimistic, the third consecutive round
where the inner ENNReal arithmetic outweighed the math-strategy
validation.

The pattern (R21, R22, R23, R24) is now stable: **outer-mathematical
strategy is reliable; inner ENNReal arithmetic is consistently
under-projected**. R25 should pre-flight at the LOC level rather
than the strategy level — the strategy has been validated four
times running, but the LOC-to-Lean-arithmetic conversion has not.

The skin-in-the-game cap clause (point #2: "T2.1 lands Stub due to
an error in Cowork's specified AM-QM simplification or
linearization strategy") **does not trigger**: the AM-QM and
linearization strategies were not erroneous; they landed as aux
lemmas. The shortfall is on the third Commitment ("prefactor
combine"), which the manifest itself flagged as the highest-LOC
piece. T2.1 = Partial, not Stub, by the manifest's own scoring rubric.

## Forward path (R25 readiness)

The four R24 aux lemmas land the ground floor for R25:

1. The AM-QM bound is plug-and-play.
2. The S₀ + S_k² real summability lemmas are immediately liftable
   to ENNReal via `ENNReal.ofReal_tsum_of_nonneg`.
3. The diam ≤ 1 bound feeds directly into the `(diam + 1) ≤ 2`
   prefactor reduction.

R25's residual scope (~150-250 LOC) covers:

- Linearity of inner ENNReal tsum: `∑' k, ofReal(a) · ofReal(b_k) ≤ ofReal(a) · ofReal(∑' b_k)` plumbing.
- AM-QM applied per-k inside the tsum (using `am_qm_three_term`).
- Prefactor reductions (`2^15 · c_T · (diam+1)`).
- Multiplication by `M_T = 1/(2T³)`.
- Absorption `(T+1)/T³ ≤ 8/(T+1)²` and `log_sq_le_sqrt`-driven `(L_T+2)² ≤ K · √(T+1)`.
- Final assembly: `Cp_T_explicit T ≤ ofReal(K_total / (T+1)^(3/2))`.

R25 expected effort: 1 focused round, P(Full) = 0.55 with
LOC-realism-corrected projection.
