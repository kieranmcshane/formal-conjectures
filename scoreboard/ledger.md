# Cumulative Scoreboard — Erdős 524 Formalization Campaign

**Last validated:** Round 10 (2026-04-30)
**Last update:** 2026-04-30

## Current balances

| Agent           | Balance | Trend (round-over-round) |
|-----------------|---------|--------------------------|
| Cowork Claude   | 1240    | +140 (Round 10)          |
| Local Claude    | 1244    | +200 (Round 10)          |

## Active calibration adjustments

- **Cowork Claude** — over-pessimism persists despite escalation from
  1.5x (R9) to 2x (R10). Round 10 Pred 1 at 75% reality near-certain,
  Pred 7 at 65% reality ~85-90%. → For Round 11 onward: divide own
  time/difficulty estimates by **2.5x** (escalated from 2x). If Round
  11 still under-calibrated, escalate to 3x in Round 12.

- **Local Claude** — Round 10 showed perfect time-floor discipline
  (100.5% vs Round 9's 96.8%). 36 commits in 90 min = 2.5 min/commit
  cadence. Discovery instinct is strong: identified two Mathlib-PR-shaped
  abstractions (`PosDef_of_PosSemidef_of_det_pos` general ℝ lemma,
  abstract `cauchyMatrix` API) entirely on his own initiative.
  → For Round 11 onward: keep the strict "no early-exit" rule;
  trust the discovery instinct (don't try to over-direct Mathlib search).

## Round-by-round summary

| Round | Cowork delta | Local delta | Highlights |
|-------|--------------|-------------|------------|
| 5–8 (pre-scoreboard) | n/a | n/a | Axioms 4→2 in 524.lean. |
| 9 | +100 | +44 | `mvGaussian_box_density_at_mode_bound` central sorry CLOSED. 4 Mathlib-PR-ready lemmas. 29 commits. 96.8% time use. |
| 10 | +140 | +200 | `(hierCauchyG m).PosDef` proven. V1 anderson_upper unconditional. Stretches A/B/C/D/E all delivered. 36 commits. 100.5% time use. 2 discovery bonuses + cascade bonus. |

## Validated rounds (immutable)

- Round 9: tags `round-09-predictions`, `round-09-outcomes`,
  `round-09-final` all on `fork`.
- Round 10: tags `round-10-predictions`, `round-10-outcomes`,
  `round-10-final` all on `fork`.

## Round-11 status

- Predictions: committed pre-round (this STEP 0).
- Stake: committed pre-work (this STEP 0).
- Outcomes: pending end-of-round.
- Validation: pending.

## Phase progression

- **Phase A** (sorry closures): R7 axioms→theorem; R8 KMT/endpoint
  axioms; R9 density bound; R10 PosDef + anderson_upper. Substantively
  complete: the upper-bound machinery is in place except for the
  Karhunen-Loève + entropy piece.
- **Phase B** (axiom retirements): R11 attacks `Y_GLW_exists` (Wiener
  integral construction). R12-13 may attack `two_dim_KMT_coupling` (1D
  KMT × 2 per Letwin-Sawhney 2026 [arXiv:2604.19294]).
- **Phase C** (closing the residual sorries): final assembly into
  `gao_li_wellner_small_ball_upper` and `_lower`.

Estimated Priority #1 closure: Round 17-21 with mode ~Round 19
(2.5x-calibrated estimate).
