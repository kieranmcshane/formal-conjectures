# Round 11 Stake — Local Claude

**Committed by Local Claude before substantive work.**

## Time-floor stake

I will work substantively until END_TARGET (= START + 90 minutes).
Stake: **300 units** (kept at Round 10's level — perfect Round 10
discipline justifies same stake, no need to escalate).

Penalty schedule (linear interp on time-use percentage τ):
- τ ≥ 100%: 0 penalty
- τ = 96.8% (Round 9 baseline): −10
- τ = 70%: −90
- τ = 35%: −195
- τ = 0%: −300

## Substance stake

I will produce ≥10 substantive commits, each ≥15 lines or ≥2 meaningful
lemmas. Stake: **150 units** (kept at Round 10's level; Round 10
delivered 36 vs target 8, head-room is generous).

If fewer than 10: penalty proportional (`-150 × (10 - count) / 10`).

## Discovery bonus

If, during the round, I:
- identify and use a Mathlib lemma not previously used in the campaign
  AND that lemma turns out to be load-bearing for a non-trivial
  argument (e.g., Wiener integral construction, Gaussian process API),
- or close one of the residual sorries from Rounds 7-9 as a side-effect
  of the Wiener-integral infrastructure,
- or prove a Mathlib-PR-shaped general lemma (e.g., a clean statement
  of the Wiener integral's covariance for deterministic L² integrands),

I claim a +50 discovery bonus (per genuine discovery, capped at +150).

## Axiom retirement bonus

If the `Y_GLW_exists` axiom is genuinely retired (i.e., the line
`axiom Y_GLW_exists :` is gone, replaced by `theorem Y_GLW_exists :`
or definition + theorem, with no other axiom added), I claim a
**+150 axiom retirement bonus**. This is a Phase-B-specific bonus,
reflecting the qualitative leap of moving from "depending on an
unproven assumption" to "constructing an explicit witness".

## Mathlib-construction bonus

If I succeed in defining `Y(u)` as a *concrete* Wiener integral
(not just an existence claim), AND I prove its covariance equals
`K_GLW(u,v)`, I claim an additional **+50 Mathlib-construction bonus**.
This is independent of the axiom-retirement bonus and rewards the
specifically-constructive aspect.

## Cascade bonus

If I close ALL of Stretch A + Stretch B + Stretch C (cascade-2:
continuity + L² inner-product + IsGLWProcess refactor), I claim
an additional **+100 cascade bonus**.

**Total stake (downside):** 450 units. (Current balance: 1244.)
**Total upside (best case):** +600 (axiom +150, discovery 3x +150, construction +50, cascade +100, plus partial credits).

— Local Claude, Round 11 stake
