# Track C round 20 — exact Delta equality audit

**Date:** 2026-05-03.  
**Branch:** `tc12-cdx-bulk-upper`.  
**Source rechecked:** Carter--Pollard, *Tusnády's inequality revisited*,
arXiv:math/0508606 / Annals of Statistics 32(6), 2731--2741.

## Equality path in the paper

Formula (3) supplies the exact correction convention

`j! = sqrt(2πj) * (j/e)^j * exp(λ_j)`.

In the equation-(7) derivation, Carter--Pollard use `K = k - 1`,
`N = n - 1`, and `ε = (2K - N)/N`. The Stirling ratio gives

`Λ = λ_N - λ_K - λ_(N-K)`.

The entropy expression before the optional `γ` rewrite is

`-(N/2) * ((1+ε)log(1+ε) + (1-ε)log(1-ε) - ε^2)`.

Equation (7) then packages the prefactor as

`exp(log(1 + N^(-1)) + Λ - (1/2)log(1 - ε^2) + entropy)`.

The Lean range is the paper's non-extreme upper half:
`28 ≤ m`, `m/2 < k`, `k ≤ m - 1`.

## Audit answers

**1. Which multiplicative factors in `carterPollardPrefactorRaw` correspond to
`exp(Λ)`?**  
After rewriting `m * choose(m-1,k-1)` as
`(1 + N^(-1)) * N!/(K!(N-K)!)`, the factorial ratio decomposes as
`exp(Λ)` times the Stirling-core ratio
`core(N)/(core(K)core(N-K))` inverted in the appropriate direction. In Lean,
TC19 exposes this through `carterPollardLambdaTerm_exp_eq`.

**2. Which factors correspond to the entropy term?**  
The factors from the Stirling cores involving
`K = N(1+ε)/2` and `N-K = N(1-ε)/2`, together with `(1/2)^m` and
`exp(Nε^2/2)`, form the entropy exponential
`exp(-(N/2) * ((1+ε)log(1+ε) + (1-ε)log(1-ε) - ε^2))`.

**3. Where exactly does `log(1 + N⁻¹)` enter?**  
It comes from the paper's total-trials factor `n/N`. Under Lean's convention,
`m = N + 1`, so `m/N = 1 + N⁻¹`. This factor is separate from the factorial
ratio and must not be hidden inside the entropy algebra.

**4. Which positivity facts are needed to avoid illegal `log_mul` /
`log_div` rewrites?**  
The proof needs positivity of `N`, `K`, `N-K`, the Stirling cores, the raw
prefactor, `1+ε`, `1-ε`, and `1-ε^2`. The range
`28 ≤ m`, `m/2 < k`, `k ≤ m-1` gives positive `N`, `K`, and `N-K`; the
relations `K = N(1+ε)/2` and `N-K = N(1-ε)/2` then give the sign facts for
the logarithms.

**5. Is the multiplicative route easier than direct log algebra?**  
Yes. The multiplicative route lets the proof use `exp(log x)=x` only after
positivity has been isolated. Direct log algebra would require nested
`log_mul`/`log_div` rewrites across factorials, powers, square roots, and
the entropy terms, making the positivity obligations much harder to control.

## TC20 boundary

TC20 should prove the exact bridge to `carterPollardDeltaPaperShape` and stop
there. The `γ(ε)` rewrite, normal-tail ratio estimates, quantile inversion,
and `tusnady_base_polynomial` closure remain later work.
