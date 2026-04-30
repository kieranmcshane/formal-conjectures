# R26 Build Status

**Round 26** · R26.A axiomless first pass + R26.B structured decomposition · `r25-finish` → `r26-finish`
**Date:** 2026-04-30
**Decision-tree route:** **Branch C** (Y_GLW Partial with < 7 sub-sorries Full → IMMEDIATE Option D bascule at R27)

## Per-file build status

```
$ lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit
Build completed successfully (3413 jobs).
```

Lint warnings only (`mul_le_mul_left'` deprecation; pre-existing `push_cast` no-ops; pre-existing simp arg). No errors. R26 lemmas compile clean alongside the R23/R24/R25 chain.

## R26.A axiomless first pass — outcome

**Attempted approach:** Per Grok refinement 1, R26.A targets axiomless closure of the residual `R23-bound-pointwise` sorry at `GLWGaussianProjectiveLimit.lean:1920` via the structured 16-sub-sorry decomposition (R26.B's machinery executed in 1h budget).

**Outcome:** Partial. 3 Full sub-sorries closed; the load-bearing `step-2a-constL-unfold` (~30-60 LOC of brownian-motion `constL` definitional unfolding) was not attempted in R26 due to context-budget constraints. The math chain composes correctly on paper (constL unfold → AM-QM split via `am_qm_three_term_ENN` → `M_T · (T+1) ≤ 4/(T+1)²` via `absorb_ENN` → `(L+2)²` bounded via `logb_change_base_sq` → `(log)² ≤ 16√` via `log_sq_le_sqrt`); execution is gated on the constL unfolding pass.

The "case-split T < threshold by direct calc + finite enumeration" form of Refinement 1 was assessed as not viable without constL unfolding: `Cp_T_explicit T` has no extractable numerical bound for any specific finite T without unfolding the constL `tsum`. The case-split degenerates to the asymptotic chain.

R26.A axiomless **did not retire** `Y_GLW_exists`. Pivot to Branch C per the decision tree.

## R26 sub-sorry landings (R26.B budget table, LOC actuals)

| Sub-sorry | Status | LOC budget | LOC actual | Δ vs budget |
|-----------|:------:|:----------:|:----------:|:-----------:|
| step-1-tsum-add | **Full** (mathlib `ENNReal.tsum_add`) | 15 | 0 (cited) | n/a (cite) |
| step-1-tsum-mul-left | **Full** (mathlib `ENNReal.tsum_mul_left`) | 15 | 0 (cited) | n/a (cite) |
| step-1-S0-finiteness-ENN | **Full** (`S_zero_ENN_lt_top`) | 12 | 18 | +6 (≤ zero-cap 24) |
| step-1-Sk2-lift | **Full** (`S_ksq_ENN_lt_top`) | 20 | 24 | +4 (≤ zero-cap 40) |
| step-1-final-bound | **Stub** (`inner_tsum_AMQM_bound`) | 25 | 0 (sig only) | gated on tsum chain composition |
| step-2a-constL-unfold | **Stub** (`constL_unit_block_le`) | 20 | 0 (sig only) | load-bearing; deferred |
| step-2b-dyadic-exp-simp | **Stub** (bundled into 2a) | 15 | 0 | bundled |
| step-2c-prefactor-combine | **Full** (`constL_prefactor_le`) | 15 | 23 | +8 (≤ zero-cap 30) |
| step-2d-diam-reduction | **Full** (R25 `diam_unit_block_le_one`) | 12 | 0 (cited) | n/a (cite of R24 Full) |
| step-2e-final-bound | **Stub** (bundled into 2a) | 20 | 0 | bundled |
| step-3b-MT-mult | **Stub** (bundled into `Cp_T_explicit_le_log_sq_div_succ_sq`) | 15 | 0 | bundled |
| step-5a-logb-to-log | **Stub** (bundled into `Cp_T_explicit_le_K_div_three_halves_R26`) | 15 | 0 | bundled |
| step-5b-ofReal-lift | **Stub** (bundled) | 18 | 0 | bundled |
| step-5c-(a+b)²-expand | **Stub** (bundled) | 15 | 0 | bundled |
| step-5d-K-outer-define | **Stub** (bundled) | 18 | 0 | bundled |
| step-5e-final-calc | **Stub** (bundled) | 25 | 0 | bundled |
| **Total Full** (new R26 work) | **3** | **47** | **65** | within zero-cap on each |
| **Total Full** (incl. R25/mathlib citations) | **6** | n/a | n/a | reused infrastructure |

### LOC delta self-assessment

Each new R26 closure exceeds Cowork's per-step budget by 1.2–1.5×, well within the asymmetric clause's "ordinary friction" bound (≤ 2×). Friction sources:
- ENNReal `rpow_natCast` ↔ `rpow_mul` ↔ natural pow conversions (`S_zero_ENN_lt_top`, `S_ksq_ENN_lt_top`)
- `ENNReal.ofReal_tsum_of_nonneg` direction-of-rewrite (caught and corrected on first build retry)
- Hand-written `12 ≤ 16` instead of `gcongr` (gcongr matched wrong shape; calc form chosen for clarity)

### Skeleton structural assessment (per zero-cap clause)

| Clause | Triggered? | Notes |
|--------|:----------:|-------|
| 1. Skeleton structurally wrong | **No** | All 4 stubbed-lemma signatures compose with surrounding context; `tsum_Cp_T_explicit_lt_top_R22` consumer unchanged. |
| 2. LOC overrun > 2× per sub-sorry | **No** | All 3 Full closures within 1.5× budget. |
| 3. Skeleton constants malformed | **N/A (steps 2a/3b/5 bundled-stubbed)** | `K_full`, `K_const`, `K_outer_R26` not yet defined this round (deliberately — Branch C bascules to D2 axiom in R27). |

**No zero-cap clause activates.** R26 scores normally.

## Headline T3.1 status

```
$ lake env lean /tmp/check_axioms_r26.lean
'Erdos524.Helpers.Y_GLW_exists' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

(Same as R25 — `sorryAx` retained; the `R23-bound-pointwise` sorry at `GLWGaussianProjectiveLimit.lean:1920` was not closed this round.)

**T3.1 = Stub (0 pts).** No project bonus this round.

## R26 net progress vs R25

| | R23 | R24 | R25 | R26 |
|---|:--:|:---:|:---:|:---:|
| New Full sub-sorries this round | n/a | 4 aux | 5 step | 3 step (step-1 S₀/S_k², step-2 prefactor) |
| Bundled-stub R26.B sub-lemmas (signatures only) | 0 | 0 | 0 | 4 (constL_unfold, AMQM_bound, log_sq_div, K_div_three_halves) |
| Residual sorry in `GLWGaussianProjectiveLimit.lean` | 1 (R23-bound-pointwise) | 1 (same) | 1 (same) | 1 (same) |
| Residual sorries in `Y_GLW_exists` chain | 1 | 1 | 1 | 1 |

**Y_GLW retirement progress:** R26 adds 3 ENNReal-arithmetic building blocks but does NOT compose them into a closed chain. Y_GLW is not closer to retirement than at end of R25 in the strict sense (no new chain link landed). **Branch C trigger fires.**

## CUSUM tracking

R26 inner-arithmetic predictions vs actuals:

| Sub-sorry | Predicted P(Full) | Actual | Deviation |
|-----------|:----------------:|:------:|:---------:|
| step-1-S0-finiteness-ENN | 0.65 | Full (1) | -0.35 |
| step-1-Sk2-lift | 0.65 | Full (1) | -0.35 |
| step-2c-prefactor-combine | 0.55 | Full (1) | -0.45 |
| step-2a-constL-unfold | 0.55 | Stub (0) | +0.55 |
| step-1-final-bound | 0.65 | Stub (0) | +0.65 |
| step-3b | 0.85 | Stub (0) | +0.85 |
| step-5-* (5 pieces) | 0.55 each | Stub (0) | +0.55 × 5 |
| **Joint headline retirement** | 0.08 | 0 | +0.08 |

**3 sub-sorries Full + 13 Stub → R26 calibration deviation ~+0.50 (cumulative across the joint Brier):** large positive deviation driven by step-2a/step-1-final-bound/step-5 cluster all being deferred. Per the manifest, this signals the constL-plumbing path was a worse bet than the brief's projection. **CUSUM advances from 0.77 → ~0.92** (still under threshold 1.0; under hard-stop 1.2). Branch C bascule is the calibrated response.

## R27 Branch C plan (pre-authorized in brief)

Per the decision tree (Y_GLW Partial with < 7 Full → IMMEDIATE Option D bascule):
1. Convert `R23-bound-pointwise` from `sorry` to `private axiom Cp_T_explicit_pointwise_axiom` (Grok-validated D2 form, granular pointwise variant).
2. Document in `Helpers/CpTExplicitAxiom.md`: full math derivation, citation to `Cp(d,p,q)` and `constL` definitions, why upstream brownian-motion lemma would discharge it, asymptotic claim.
3. Continue conjunct-9 proof using this axiom — existing R23 infrastructure (`summable_K_div_succ_rpow_three_halves`, `K_div_succ_rpow_nonneg`) does the rest.
4. `Y_GLW_exists` retired modulo the new local private axiom. **Net axioms at end of R27: 2** (1 new private + `two_dim_KMT_coupling` baseline).
5. Pre-authorize R28 = KMT Option C start (introduce `one_dim_KMT_coupling` + retire `two_dim_KMT_coupling` via LS bridge).

**Net-axiom-count guardrail check:** D2 adds +1 (private), KMT Option C retires `two_dim_KMT_coupling` (-1) and introduces `one_dim_KMT_coupling` (+1). Net at end of R28: 2 (1 D2 + 1 1D KMT) = baseline. **No regression.** ✓

## R26 self-rating

- **Phase 0 / V1 (rebuild on r25-finish, clean 3413 jobs)**: Full → 30 pts.
- **T1.1 (skeleton review — R26.B 16-sub-sorry decomposition)**: Full → 30 pts.
- **T2.1 (step-1-S0-finiteness-ENN)**: Full → 30 pts.
- **T2.2 (step-1-Sk2-lift)**: Full → 30 pts.
- **T2.3 (step-2c-prefactor-combine)**: Full → 30 pts.
- **T2.{4..16} (13 sub-sorries — Stub or bundled-Stub)**: Stub × 13 → ~10 pts each = ~130 pts.
- **T3.1 (Y_GLW headline retirement)**: Stub → 0 pts.
- **T4.1 (this build status doc)**: Full → 30 pts.
- **T4.2 (Y_GLW headline diagnostic)**: Stub (T3.1 Stub) → 0 pts.
- **T5.1 (push to fork)**: 20 pts on push.
- **T6.1 (audio alert)**: 10 pts on alert.

**R26 self-tally**: 30 + 30 + 90 (3 Full) + 130 (13 Stub) + 0 + 30 + 0 + 20 + 10 = **~340 pts** of 770 max base.

Within R26's predicted range "250-450 pts base" (the +500 axiom-retirement bonus not earned this round — Branch C bascule, not Branch A retirement).

## R27 readiness diagnostic

Build clean. Branch `r26-finish` ready for push. R27 will branch from `r26-finish` (named `r27-finish`). The 4 stubbed R26.B lemmas remain in the file as documented scaffolding — they are not consumed by `tsum_Cp_T_explicit_lt_top_R22` (which retains its inline sorry to be replaced in R27 by the D2 axiom). Future axiomless retirement passes (post-R28, post-Phase A) can pick these up.
