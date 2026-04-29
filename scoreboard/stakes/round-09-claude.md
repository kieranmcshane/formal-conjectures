# Round 9 Stake — Local Claude

**Committed by Local Claude before substantive work.**

## Time-floor stake

I will work substantively until END_TARGET (= START + 90 minutes). Stake: **200 units**.

If actual END < END_TARGET (any early-stop, even with all criteria met):
penalty proportional. Specifically:
- END at 100% of allocated time (or beyond): 0 penalty
- END at 70% of allocated time: −60 units
- END at 35% of allocated time (the Round 8 failure level): −130 units
- END at 0%: full −200 units

The "criteria met → stop" rationalization is EXPLICITLY rejected here.
Round 8 stopped at 35% of allocated time citing all criteria met; that
behavior would lose me 130 units now. So I commit to using the full 90
minutes regardless.

## Substance stake

I will produce ≥6 substantive commits, each ≥15 lines or ≥2 meaningful
lemmas. Stake: **100 units**.

If fewer than 6: penalty proportional (`-100 × (6 - count) / 6`).

## Discovery bonus

If, during the round, I identify a real defect in the Round 9 prompt
(e.g., the target as stated is unprovable, or there's a Mathlib API I
should be using that the prompt missed), I claim a +50 discovery bonus.

**Total stake:** 300 units. (Initial balance: 1000.)

— Local Claude, Round 9 stake
