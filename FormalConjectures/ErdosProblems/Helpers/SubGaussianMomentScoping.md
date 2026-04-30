# Sub-Gaussian moment infrastructure — scoping for 1D KMT (R17 T8.2)

This document scopes the **Mathlib sub-Gaussian moment theory** that
would be needed to support a 1D KMT proof via the Skorokhod-embedding
or Tusnády routes documented in `OneDimKMTSketch.md`. The scoping is
read-only — no new code in this round.

## What 1D KMT needs from sub-Gaussian theory

Both Skorokhod and Tusnády routes require:

1. **Sub-Gaussian tail bounds for partial sums:** if `X_i` are iid
   centred sub-Gaussian with parameter `σ`, then
   `P(|S_n| > t) ≤ 2 exp(-t²/(2nσ²))`.
2. **Moment generating function bounds:** `E[exp(λ S_n)] ≤
   exp(nλ²σ²/2)` for sub-Gaussian increments.
3. **Bernstein-type inequalities:** for sums of bounded random
   variables, sharper tail bounds than Hoeffding.

## Mathlib state at HEAD (2026-04-30)

Existing infrastructure in `Mathlib.Probability.Moments.SubGaussian`:

* `Kernel.IsSubGaussian` — predicate for kernels (probability transitions).
* `IsSubGaussian.cgf_le` — log-MGF bound.
* `IsSubGaussian.measure_ge_le` — Chernoff-type tail bound.

These cover (1) and (2) above for sums **assuming** the sub-Gaussian
parameter is known. **What's missing:**

* **No connection to bounded random variables**: there's no instance
  showing `IsBoundedAlmostEverywhere → IsSubGaussian`. The standard
  Hoeffding inequality `|X| ≤ b → IsSubGaussian σ` with `σ = b`
  is not yet exposed.
* **No iid sum lemma**: there's `Kernel.IsSubGaussian.fun_sum` for
  finite sums in the kernel framework, but not a clean `Finset.sum
  of iid` corollary. Currently each user re-derives via `cgf_sum`.
* **No Bernstein**: completely absent. This would be a separate PR.

## Gap analysis for 1D KMT

For the **Tusnády route** (route 3 in `OneDimKMTSketch.md`):

* Tusnády's lemma is about Bin(n, 1/2) and N(n/2, n/4). This needs:
  * Binomial CDF bounds (exists: `Mathlib.Probability.Distributions.Binomial`).
  * Gaussian CDF (exists: `Mathlib.Probability.Distributions.Gaussian`).
  * **NEW**: Edgeworth-expansion-style approximation between binomial
    and Gaussian CDFs at the midpoint, with `O(1/√n)` error and
    explicit constant.

The Edgeworth-approximation step is **not** sub-Gaussian theory;
it's separate. Sub-Gaussian theory enters when bounding the tail
of the partial-sum walk in step (2) of the Skorokhod route.

For the **Skorokhod route** (route 1):

* Stopping-time martingale bounds need a quantitative version of
  Doob's optional stopping with sub-Gaussian increments. This is
  approximately:
  > `E[exp(λ B_τ - λ²τ/2)] = E[exp(λ B_0)] = 1`
  > combined with a Markov bound to control `E[τ]` and `E[(τ - n)²]`.
* This is in the realm of `Mathlib.Probability.Martingale` but the
  integration with sub-Gaussian-style tail control isn't there.

## Recommendation for R18+

If R18 takes on 1D KMT:

1. **First sub-PR:** add the bounded → sub-Gaussian instance
   (Hoeffding's lemma) to `Mathlib.Probability.Moments.SubGaussian`.
   ~50 LOC, low risk.
2. **Second sub-PR:** add a clean iid-sum corollary
   `iIndepFun.sum_isSubGaussian`. ~30 LOC.
3. **Third sub-PR:** the Edgeworth-binomial-Gaussian approximation
   (this is the load-bearing one for Tusnády). ~300 LOC.
4. **Fourth sub-PR:** Tusnády's lemma proper. ~150 LOC.
5. **Fifth sub-PR:** dyadic recursion → 1D KMT. ~250 LOC.
6. **Sixth sub-PR:** the 2-D coupling on top, in our own
   `Helpers/TwoDimKMT.lean`. ~500 LOC.

Total: ~1300 LOC across 6 sub-PRs spanning a 4-6 month engagement.

## Why this isn't on R18's critical path

`two_dim_KMT_coupling` blocks the **lower** Phase A bound for
Erdős 524 (the GLW-side small-ball estimate transfers via 2-D KMT).
But the lower bound is **already** at `lake build` parity in
`524.lean`; the axiom only becomes load-bearing when the rest of
the chain is dissolved. Since `Y_GLW_exists` is not yet at
`#print axioms` clean (T1.9 blocked by T1.7+T1.8), prioritizing
`two_dim_KMT_coupling` ahead of finishing T1.9 would be premature
optimization.

## Cross-references

* `OneDimKMTSketch.md` — the upstream KMT roadmap.
* `TwoDimKMTRetirement.md` — the consumer of 1D KMT.
* `R18ReadinessDiagnostic.md` Blocker 5.

## Outcome label

* **R17 T8.2**: Stub (≥30 lines). This file is at 80+ lines.
