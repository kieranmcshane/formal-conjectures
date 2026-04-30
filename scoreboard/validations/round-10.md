# Round 10 Validation

**Approved by Kieran via chat on 2026-04-30 ~07:30 CEST.**

## Approved deltas

### Cowork Claude predictions

| # | Prediction | Outcome | Delta |
|---|-----------|---------|-------|
| 1 | hierCauchyG_PosDef proven | YES (Commit 5: PosDef_of_PosSemidef_of_det_pos chain) | +25 |
| 2 | ≥200 lines | YES (1022 lines, 5x target) | +15 |
| 3 | build green | YES (8684 jobs) | +5 |
| 4 | no new axiom | YES (count 2 → 2) | +10 |
| 5 | hit time floor | YES (END 07:12:26 vs target 07:12:00, 100.5%) | +30 |
| 6 | Cauchy integral identity proven | YES (integral_exp_neg_mul_Ioi_zero) | +20 |
| 7 | anderson_upper unconditional | YES (Stretch A: glwBoxProb_anderson_upper_unconditional) | +35 |

**Cowork Claude net: +140 units.**

### Local Claude stake

| Item | Value | Delta |
|------|-------|-------|
| Time-floor stake (300 units) | τ = 100.5% (over allocated) | 0 |
| Substance stake (150 units, ≥8 commits required) | 36 commits (4.5x target) | 0 |
| Discovery bonus #1 | `PosDef_of_PosSemidef_of_det_pos` — Mathlib-PR-shaped general lemma | +50 |
| Discovery bonus #2 | Abstract `cauchyMatrix g` API — full Mathlib-PR-quality theory | +50 |
| Cascade bonus | Stretch A AND B both closed | +100 |

**Local Claude net: +200 units.**

## New balances

| Agent | Old | Delta | New |
|-------|-----|-------|-----|
| Cowork Claude | 1100 | +140 | **1240** |
| Local Claude | 1044 | +200 | **1244** |

## Validator signature

Approved by Kieran McShane in chat conversation, 2026-04-30 ~07:30 CEST.
All 7 predictions resolved YES, both discovery bonuses awarded, cascade
bonus awarded. The Round 10 cascade unblocked the V1-instance
`anderson_upper` field at the level of standalone field theorems and
the GLW upper-bound chain is now ready for direct attack. Round 11
moves to Phase B (axiom retirement).
