# Track C round 19 — sharp Delta infrastructure audit

**Date:** 2026-05-03.  
**Branch:** `tc12-cdx-bulk-upper`.  
**Source rechecked:** Carter--Pollard, *Tusnády's inequality revisited*,
arXiv:math/0508606 / Annals of Statistics 32(6), 2731--2741.

## Paper recheck

Formula (3) is the Robbins/Stirling convention used throughout the paper:

`n! = sqrt(2π) * exp((n + 1/2)log n - n + λ_n)`,

equivalently

`n! = sqrt(2πn) * (n/e)^n * exp(λ_n)`.

The paper records the bounds

`(12n + 1)^(-1) ≤ λ_n ≤ (12n)^(-1)`.

For equation (7), Carter--Pollard set `K = k - 1`, `N = n - 1`, and
`ε = (2K - N)/N`. They define

`Λ = λ_N - λ_K - λ_(N-K)`

and

`Δ = log(1 + N^(-1)) + Λ - (1/2)log(1 - ε^2) - Nε^4γ(ε)`.

The function `γ` is defined by

`γ(ε) =
((1+ε)log(1+ε) + (1-ε)log(1-ε) - ε^2)/(2ε^4)`

away from zero, and by the displayed power series at zero. The paper states
that `γ(0)=1/12`, `γ(1)=-1/2+log 2`, and uses monotonicity later.

Theorem 1 assumes `n ≥ 28` and the upper-half non-extreme range
`n/2 < k ≤ n - 1`. Under the Lean convention `m = n`, this becomes
`28 ≤ m`, `m/2 < k`, and `k ≤ m - 1`.

## Audit answers

**1. What exact Lean definition of `λ_j` matches formula (3)?**  
TC19 uses

`carterPollardLambdaTerm j =
  log(j! / (sqrt(2πj) * (j/e)^j))`.

This is exactly the second equivalent form of formula (3):
`j! = sqrt(2πj) * (j/e)^j * exp(λ_j)`.

**2. Does `λ_0` ever appear, or does the range avoid it?**  
The target range avoids it. With `28 ≤ m`, `m/2 < k`, and `k ≤ m - 1`,
Lean proves all three indices are positive:

* `1 ≤ N = m - 1`,
* `1 ≤ K = k - 1`,
* `1 ≤ N-K = m-k`.

TC19 lands this as `carterPollard_lambda_indices_pos`.

**3. What hypotheses are needed to prove `K = k - 1`, `N-K = m-k` are
positive?**  
`28 ≤ m` and `m/2 < k` make `k` far enough above zero to give `1 ≤ k - 1`;
`k ≤ m - 1` gives `1 ≤ m-k`. The lower bound on `m` also gives
`1 ≤ m - 1`.

**4. Is the `γ` rewrite feasible debt-free this round, or should TC19 stop at
the entropy expression?**  
TC19 should stop before the `γ` rewrite. Defining `γ` as a total function
would require a removable-singularity choice at `ε=0`, and proving the
identity with the entropy expression would require a separate case split plus
power-series or algebraic continuation support. The debt-free payload in TC19
therefore introduces the paper-shaped entropy term
`carterPollardEntropyDelta` and `carterPollardDeltaPaperShape`, but does not
claim the final `γ` equality.

**5. What exact theorem is sufficient for TC20 normal-tail/quantile inversion?**  
TC20 needs the normalized tail theorem from TC17 together with a paper-shaped
upper bound for

`exp(carterPollardDeltaPaperShape m k)`.

The immediate next bridge is to prove
`carterPollardDeltaRaw = carterPollardDeltaPaperShape` and then bound the
entropy term plus `Λ`. TC19 supplies the exact `λ` definitions, the positive
range facts, and the available Robbins bounds for all three `λ` terms; it
does not yet discharge the full entropy equality.

## Lean outcome

TC19 lands debt-free sharp infrastructure:

* `carterPollardK`, `carterPollardNK`;
* `carterPollardStirlingCore`;
* `carterPollardLambdaTerm`;
* `carterPollardLambda`;
* `carterPollardEntropyDelta`;
* `carterPollardDeltaPaperShape`;
* `carterPollard_lambda_indices_pos`;
* `carterPollardStirlingCore_pos`;
* `carterPollardLambdaTerm_exp_eq`;
* `carterPollardLambdaTerm_nonneg_le`;
* `carterPollardLambdaTerm_bounds_of_range`.

The available Lean lower bound for `λ_j` is nonnegative; the paper's sharper
strict lower bound `(12j+1)^(-1) ≤ λ_j` remains a later refinement if needed.
The upper Robbins bound `λ_j ≤ (12j)^(-1)` is landed.
