# Track C round 16 — Carter-Pollard constants audit

**Date:** 2026-05-03.  
**Branch:** `tc12-cdx-bulk-upper`.  
**Source rechecked:** Carter--Pollard, *Tusnády's inequality revisited*,
arXiv:math/0508606 / Annals of Statistics 32(6), 2731--2741.

## Paper constants

The paper starts from the one-sided upper binomial tail
`P{Bin(n, 1/2) ≥ k}` and the beta representation
`n! / ((k-1)!(n-k)!) * ∫_0^{1/2} t^(k-1) (1-t)^(n-k) dt`
(equation (2)).

In Theorem 1 and the outline, Carter--Pollard set

* `K = k - 1`,
* `N = n - 1`,
* `ε = (2K - N) / N`.

Thus `K / N = (1 + ε) / 2`, and the complementary exponent is
`(N - K) / N = (1 - ε) / 2`.

Equation (7) is therefore the same total-trials `n` upper tail rewritten as

`P{X ≥ k} = exp(Δ) * sqrt(N / (2π)) *
  ∫_0^1 exp(N*h(s) - N*ε^2/2) ds`,

where `h(s) = H((1-s)/2) - H(1/2)` and
`Δ = log(1 + N⁻¹) + Λ - (1/2)log(1-ε²) - Nε⁴γ(ε)`.

Equation (5) is downstream of Theorem 2. It bounds
`β_k - k + 1/2` for `n/2 ≤ k ≤ n`; it is not just the raw tail bound.
It needs the normal-tail ratio analysis and quantile inversion after the
equation-(7) tail comparison.

## Lean convention check

In Lean, `Erdos524.Helpers.binomialPolyTail m k (1/2)` is the polynomial
tail for total trials `m`, summing from `k` through `m`. Therefore the paper's
binomial total `n` corresponds to Lean's variable `m`.

Consequently, the Carter--Pollard constants for Lean `m, k` are

* `N = m - 1`,
* `K = k - 1`,
* `ε = (2K - N) / N = (2*k - m - 1) / (m - 1)`.

The TC15 abstract equations then become exactly

* `N * (1 + ε) / 2 = k - 1`,
* `N * (1 - ε) / 2 = m - k`.

So the correct TC16 instantiation is `N = m - 1`, not `m` or `m + 1`.

## Required audit answers

**Does Carter--Pollard use `N = n - 1`, `N = n`, or `N = n + 1` under our
`binomialPolyTail` convention?**  
`N = m - 1`, where `m` is Lean's total-trials variable in
`binomialPolyTail m k`.

**Does Lean `k` correspond to the paper threshold `k`, `k-1`, or `k+1`?**  
Lean `k` is the same threshold as the paper's `k` in `P{Bin(n,1/2) ≥ k}`.
The shifted parameter is `K = k - 1`, which appears only inside the
Beta/Carter--Pollard exponent matching.

**Is the final Tusnády use one-sided upper tail, lower tail, or both via
symmetry?**  
The paper proves the upper-half one-sided upper tail and uses binomial/normal
symmetry to cover the lower half. Lean should expect a separate symmetry
adapter or a theorem stated only for the upper-half range.

**What exact bridge is still needed from this tail bound to the quantile
polynomial inequality in `tusnady_base_polynomial`?**  
TC16 only gives an instantiated raw upper-tail comparison. To reach
`tusnady_base_polynomial`, the remaining bridge must relate this tail bound
to the normal cutpoint/quantile relation defining the coupling, then reproduce
the Theorem-2-to-inequality-(5) consequence. In particular, the raw integral
tail still lacks the `Δ` prefactor analysis, normal-tail ratio inequalities,
and quantile inversion.

**Is the constants path sufficient for universal `A = 0.6`, `C = 1`, or does
it still need endpoint/small-`n` case splits?**  
The constants path is not yet sufficient for the universal `A = 0.6`, `C = 1`
claim. Carter--Pollard's Theorem 1/2 range assumes `n ≥ 28` and an upper-half
non-extreme range before symmetry. A final universal theorem will still need
endpoint and small-`n` case handling, plus any constants audit required to
convert unspecified paper constants into the particular Lean constants.

## TC16 Lean target

Add a debt-free theorem in `CarterPollardEq7Bridge.lean` that instantiates
TC15's abstract parameters with
`N = (m - 1 : ℕ)` and
`ε = ((2 * k : ℝ) - m - 1) / (m - 1)`.

This is a constants bridge only. It should not be framed as a retirement of
`tusnady_base_polynomial`.
