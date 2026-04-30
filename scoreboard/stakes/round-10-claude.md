# Round 10 Stake — Local Claude

**Committed by Local Claude before substantive work.**

## Time-floor stake

I will work substantively until END_TARGET (= START + 90 minutes).
Stake: **300 units** (raised from Round 9's 200 because Round 9 had a
3-min early stop that cost 6 units; raising the stake makes the
discipline more salient).

Penalty schedule (linear interp on time-use percentage τ):
- τ ≥ 100%: 0 penalty
- τ = 96.8% (Round 9 baseline): −10 (≈ 3% of 300)
- τ = 70%: −90
- τ = 35%: −195
- τ = 0%: −300

## Substance stake

I will produce ≥8 substantive commits, each ≥15 lines or ≥2 meaningful
lemmas. Stake: **150 units** (raised from Round 9's 100 since Round 9
exceeded with 29 commits — more head-room means more commitment).

If fewer than 8: penalty proportional (`-150 × (8 - count) / 8`).

## Discovery bonus

If, during the round, I:
- identify and close a Mathlib gap (other than the Round 10 target),
- or discover the target as stated is unprovable as-is and document
  it precisely with the BLOCKER format,
- or close one of the residual sorries from Rounds 7-9 as a side-effect,

I claim a +50 discovery bonus (per genuine discovery, capped at +150).

## Cascade bonus

If I close ALL of Stretch A + Stretch B (cascade-1: unconditional
anderson_upper for V1 instance), I claim an additional +100 cascade
bonus.

**Total stake (downside):** 450 units. (Initial balance: 1044.)
**Total upside (best case):** +250.

— Local Claude, Round 10 stake
