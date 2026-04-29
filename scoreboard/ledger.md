# Cumulative Scoreboard — Erdős 524 Formalization Campaign

**Last validated:** initial state (pre-Round 9)
**Last update:** 2026-04-30 (initial)

## Current balances

| Agent           | Balance | Trend  |
|-----------------|---------|--------|
| Cowork Claude   | 1000    | start  |
| Local Claude    | 1000    | start  |

## Active calibration adjustments

These are bias corrections derived from past performance that should be
applied to the NEXT round's behavior:

- **Cowork Claude** — documented over-pessimism on time/difficulty
  estimates (factor 1.5–2x in 4 of last 5 estimates).
  → For Round 9 onward: divide own time/session estimates by 1.5x
    before publishing them, OR explicitly note "raw estimate before
    pessimism correction" + adjusted figure.

- **Local Claude** — tendency to early-stop when success criteria are
  met (Round 6 wait-loop, Round 7 attempt, Round 8 explicit).
  → For Round 9 onward: hard time floor with NO early-exit clause,
    even when criteria met. Stretch goals must be specified in the
    prompt for the post-criteria phase.

## Round-by-round summary (informal, pre-scoreboard)

These rounds happened *before* the scoreboard system was instituted, so
no currency was awarded. They are recorded here for calibration only.

| Round | Prediction calibration                         | Discipline %  |
|-------|-----------------------------------------------|---------------|
| 5     | Underestimated V1 fields output 8x            | 100%          |
| 6     | Underestimated V1 fields output 3x            | 100% (small drift, auto-corrected) |
| 7     | Missed axiom-falsity bug; needed user relance | 80% (early-stop attempt, recovered) |
| 8     | Overestimated time-required 3x                | 35% (31min/90min, hard regression) |

**Net pre-scoreboard takeaway:** Cowork Claude's prediction error has
been roughly symmetric in count but skewed toward over-pessimism in
magnitude. Local Claude's discipline has been monotonically degrading
under "criteria met" rationalization.

## Validated rounds

(none yet — Round 9 will be the first scored)

## Round-9 status

- Predictions: not yet committed (waiting for Round 9 design)
- Stake: not yet committed (will be committed by Local Claude at session start)
- Outcomes: pending
- Validation: pending
