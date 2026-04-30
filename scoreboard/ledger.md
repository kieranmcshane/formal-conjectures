# Cumulative Scoreboard — Erdős 524 Formalization Campaign

**Last validated:** Round 9 (2026-04-30)
**Last update:** 2026-04-30

## Current balances

| Agent           | Balance | Trend (round-over-round) |
|-----------------|---------|--------------------------|
| Cowork Claude   | 1100    | +100 (Round 9)           |
| Local Claude    | 1044    | +44 (Round 9)            |

## Active calibration adjustments

- **Cowork Claude** — over-pessimism persists despite Round 8's ÷1.5
  correction. Round 9 sorry-closure prediction was 70%; reality was
  near-certain YES with bonus of 4 Mathlib-PR-ready lemmas.
  → For Round 10 onward: divide own time/difficulty estimates by **2x**
  (was 1.5x in Round 9). If still under-calibrated, escalate to 2.5x.

- **Local Claude** — Round 9 showed major improvement on time-floor
  discipline (96.8% vs Round 8's 35%). Tiny early-stop remained.
  → For Round 10 onward: keep the strict "no early-exit even when
  criteria met" rule; stretch-goal cascade should be specified
  generously so there's always something to attack.

## Round-by-round summary

| Round | Cowork delta | Local delta | Highlights |
|-------|--------------|-------------|------------|
| 5–8 (pre-scoreboard) | n/a | n/a | Axioms 4→2 in 524.lean. Discovery: scoreboard system instated post-Round 8 to fix early-stop pattern. |
| 9 | +100 | +44 | `mvGaussian_box_density_at_mode_bound` central sorry CLOSED. 4 Mathlib-PR-ready lemmas. 29 substantive commits. 96.8% time use. |

## Validated rounds (immutable)

- Round 9: tags `round-09-predictions`, `round-09-outcomes`,
  `round-09-final` all on `fork`.

## Round-10 status

- Predictions: committed pre-round (this STEP 0).
- Stake: committed pre-work (this STEP 0).
- Outcomes: pending end-of-round.
- Validation: pending.
