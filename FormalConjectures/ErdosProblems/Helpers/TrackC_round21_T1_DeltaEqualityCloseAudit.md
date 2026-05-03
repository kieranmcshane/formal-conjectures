# Track C round 21 — Delta equality close audit

**Date:** 2026-05-03.  
**Branch:** `tc12-cdx-bulk-upper`.  
**Target file:** `CarterPollardEq7Bridge.lean`.

## Paper equation being matched

The target remains Carter--Pollard equation (7):

`P{X ≥ k} = exp(Δ) * sqrt(N/(2π)) *
  ∫_0^1 exp(N*h(s) - Nε^2/2) ds`,

with

`Δ = log(1 + N^(-1)) + Λ - (1/2)log(1 - ε^2) + entropy`,

where the entropy form is the pre-`γ` expression already encoded as
`carterPollardEntropyDelta`.

## Lean target theorem

The intended theorem was

`carterPollardDeltaRaw_eq_deltaPaperShape`.

The attempted multiplicative proof reduced the problem to the final finite
cancellation between:

* the Stirling-core powers in `carterPollardLambda_exp_eq`;
* the entropy denominator
  `(1+ε)^K * (1-ε)^(N-K)`;
* the square-root factor `(1 - ε^2)^(-1/2)`;
* the separate `m/N = 1 + N^(-1)` factor;
* the raw normalizing factor `sqrt(2π) / sqrt N`;
* the powers of `1/2`.

This is the correct mathematical remaining goal, but the Lean proof did not
close debt-free in this round.

## Positivity facts used

TC20 already supplies the needed log/square-root domain facts:

* `carterPollard_lambda_indices_pos`;
* `carterPollard_one_add_eps_pos`;
* `carterPollard_one_sub_eps_pos`;
* `carterPollard_one_sub_eps_sq_pos`;
* positivity of `carterPollardN`, `K`, and `N-K` from the paper range
  `28 ≤ m`, `m/2 < k`, `k ≤ m - 1`.

## Deferred work

The next attempt should isolate a private square-root/power cancellation lemma
instead of pushing the whole equality through one `field_simp`/`ring_nf` block.
No `γ` rewrite, normal-tail ratio, quantile inversion, endpoint handling, or
`tusnady_base_polynomial` closure is part of this equality close.

## Outcome

TC21 did not land the requested public equality theorem. Net debt remains
unchanged, and the forbidden Gaussian-CDF API was not introduced.
