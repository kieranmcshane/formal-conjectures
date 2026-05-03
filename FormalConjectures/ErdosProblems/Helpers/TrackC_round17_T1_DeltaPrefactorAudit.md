# Track C round 17 — Delta-prefactor audit

**Date:** 2026-05-03.  
**Branch:** `tc12-cdx-bulk-upper`.  
**Source rechecked:** Carter--Pollard, *Tusnády's inequality revisited*,
arXiv:math/0508606 / Annals of Statistics 32(6), 2731--2741.

## Paper recheck

Equation (7) rewrites the upper binomial tail as

`P{X ≥ k} = exp(Δ) * sqrt(N / (2π)) *
  ∫_0^1 exp(N*h(s) - N*ε^2/2) ds`,

with `K = k - 1`, `N = n - 1`, and
`ε = (2K - N) / N`. The same passage defines

`Δ = log(1 + N⁻¹) + Λ - (1/2)log(1 - ε²) - Nε⁴γ(ε)`.

Immediately after equation (7), the paper explains that replacing the
integral by the Gaussian kernel integral and changing variables gives

`exp(Δ) * Φ̄(ε * sqrt N)`.

Section 4 turns this heuristic upper bound into the rigorous inequality
`P{X ≥ k} ≤ exp(Δ) * Φ̄(ε * sqrt N)` by using the one-sided Taylor bound
for `h` and the nonnegativity of the omitted tail integral beyond `s = 1`.

## Lean prefactor correspondence

TC16 gives the raw instantiated upper bound

`binomialPolyTail m k (1/2) ≤ A(m,k) *
  ((sqrt N)⁻¹ * ∫_{sqrt N * ε}^∞ exp(-t²/2) dt)`,

where

* `N = m - 1`,
* `ε = (2*k - m - 1) / (m - 1)`,
* `A(m,k) = m * choose(m-1,k-1) * (1/2)^m * exp(Nε²/2)`.

The normalized standard-Gaussian tail is

`GaussianTail(x) = (sqrt(2π))⁻¹ * ∫_x^∞ exp(-t²/2) dt`.

Therefore the raw Lean prefactor corresponding to paper `exp(Δ)` is

`A(m,k) * sqrt(2π) * (sqrt N)⁻¹`.

TC17 should define

`Δ_raw(m,k) = log(A(m,k) * sqrt(2π) * (sqrt N)⁻¹)`

and prove the purely algebraic normalization bridge

`binomialPolyTail m k (1/2) ≤ exp(Δ_raw(m,k)) *
  GaussianTail(sqrt N * ε)`.

## Required audit answers

**Which part of Lean's exact prefactor corresponds to paper `exp(Δ)`?**  
The whole factor
`m * choose(m-1,k-1) * (1/2)^m * exp(Nε²/2) *
sqrt(2π) * (sqrt N)⁻¹` corresponds to `exp(Δ)`.

**Does TC16's raw theorem already include all combinatorial prefactors?**  
Yes. TC16 already includes the binomial/Beta coefficient
`m * choose(m-1,k-1)`, the `(1/2)^m` factor, and the exponential
`exp(Nε²/2)` from equation (7)'s shifted integrand.

**What exact normalized-tail theorem is needed before Theorem 2 /
inequality (5)?**  
The next exact bridge is the debt-free theorem
`binomialPolyTail_half_le_exp_delta_mul_gaussian_tail_instantiated`,
stating the TC16 raw tail bound as
`exp(Δ_raw) * gaussianTailRaw(sqrt N * ε)`.

**Which later step must bound `Δ_raw` or compare it to paper `Δ`?**  
A later constants round must either prove that `Δ_raw` equals the paper's
Stirling-expanded `Δ`, or prove direct upper/lower bounds for `Δ_raw` strong
enough to reproduce the paper's `A_n(ε)` estimates.

**Why is quantile inversion still out of scope for TC17?**  
TC17 is only a normalization step. The quantile argument needs normal-tail
ratio inequalities and the perturbation from `ε*sqrt N` to the cutpoint
`z_k`; those are the Theorem 2 / inequality (5) layer, not part of the
raw Δ-prefactor algebra.

## TC17 boundary

TC17 should not introduce a CDF API, should not use
`Real.Gaussian.compl_cdf`, and should not claim any retirement of
`tusnady_base_polynomial`.
