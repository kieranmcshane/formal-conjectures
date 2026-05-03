# Track C round 18 — Delta-bound audit

**Date:** 2026-05-03.  
**Branch:** `tc12-cdx-bulk-upper`.  
**Source rechecked:** Carter--Pollard, *Tusnády's inequality revisited*,
arXiv:math/0508606 / Annals of Statistics 32(6), 2731--2741.

## Paper recheck

Equation (7) writes the upper binomial tail in the form

`P{X ≥ k} = exp(Δ) * sqrt(N/(2π)) *
  ∫_0^1 exp(N*h(s) - N*ε^2/2) ds`,

where `K = k - 1`, `N = n - 1`, and `ε = (2K - N)/N`.

The paper's prefactor exponent is

`Δ = log(1 + N⁻¹) + Λ - (1/2)log(1 - ε²) - Nε⁴γ(ε)`,

with

* `Λ = λ_N - λ_K - λ_(N-K)`, coming from the Robbins/Stirling correction
  terms in formula (3),
* `γ(ε)` defined by
  `((1+ε)log(1+ε) + (1-ε)log(1-ε) - ε²) / (2ε⁴)` away from zero, and by
  its even power-series continuation at zero.

Theorem 1 is stated for `n ≥ 28` and the non-extreme upper-half range
`n/2 < k ≤ n - 1`; the outline translates this to
`0 ≤ ε ≤ 1 - 2/N` up to the parity-dependent lower endpoint. Theorem 2
again assumes `n ≥ 28` and works with the same Carter--Pollard `ε`.

## Lean comparison

TC17 defines

`Δ_raw = log(A(m,k) * sqrt(2π) * (sqrt N)⁻¹)`,

where `A(m,k)` is the exact combinatorial prefactor
`m * choose(m-1,k-1) * (1/2)^m * exp(Nε²/2)`.

This is algebraically the same prefactor as paper `exp(Δ)`, but proving the
paper-shaped equality requires expanding `choose(m-1,k-1)` through exact
factorials, then applying the Robbins formula (3) with named correction
terms `λ_N`, `λ_K`, and `λ_(N-K)`, and finally rewriting the entropy piece into
`-(1/2)log(1-ε²) - Nε⁴γ(ε)`. That infrastructure is not yet present as Lean
definitions.

## Required audit answers

**Does paper `Δ` exactly equal `log(carterPollardPrefactorRaw m k)` under
TC16 conventions?**  
Mathematically yes, in the non-extreme range where all factorial correction
terms are defined. In current Lean, the exact equality is not available
because the paper's `λ` and `γ` terms have not been introduced as Full
definitions and the Stirling/entropy expansion has not been formalized.

**If not, what finite algebraic/Stirling gap remains?**  
The remaining gap is finite and explicit:

1. rewrite the binomial coefficient into factorials;
2. introduce Robbins `λ_j` via formula (3);
3. prove the `Λ = λ_N - λ_K - λ_(N-K)` decomposition;
4. rewrite the entropy expression into the paper's
   `-(1/2)log(1-ε²) - Nε⁴γ(ε)` form.

**What range assumptions are required?**  
For the paper theorem: total trials `m ≥ 28`, upper-half non-extreme
threshold `m/2 < k ≤ m - 1`, equivalently `0 ≤ ε ≤ 1 - 2/N` with
`N = m - 1`. The Lean TC18 diagnostic lemmas only need `2 ≤ m`, `1 ≤ k`,
and `k ≤ m` for positivity; the loose explicit bound also uses the existing
`stirling_prefactor_bound`.

**What bound on `exp(Δ_raw)` is sufficient for the next quantile inversion
round?**  
TC19 will need a paper-shaped bound of the form
`exp(Δ_raw) ≤ exp(A_n(ε))`, where `A_n(ε)` isolates
`-Nε⁴γ(ε) - (1/2)log(1-ε²)` plus controlled `λ` and `O(1/N)` terms. The loose
prefactor bound landed in TC18 is not sufficient for the quantile inversion
round; it is a debt-free diagnostic bound exposing exactly where the sharper
paper expansion must enter.

**Are endpoint/small-`m` cases deferred or handled here?**  
Deferred. TC18 does not handle `m < 28`, the extreme endpoint `k = m`, or
the symmetry reduction for lower-half thresholds.

## TC18 Lean boundary

TC18 should land debt-free algebra around `Δ_raw`: positivity, unfolding, and
a loose explicit bound from the existing prefactor inequality. It should not
claim the paper `Δ` retirement, quantile inversion, or
`tusnady_base_polynomial` closure.
