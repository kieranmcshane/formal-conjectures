# Track C round 44 - Carter--Pollard scalar gap audit

**Date:** 2026-05-03.  
**Branch:** `tc44-cdx-cp-scalar-gap`.  
**Base branch:** `tc43-cdx-mills-gain-bound`.  
**Targets:** `CarterPollardEq7Bridge.lean`, `GaussianMillsRatio.lean`.

## Survey

Reread:

* `CarterPollardEq7Bridge.lean`, especially TC24 Delta/Robbins bounds, TC35
  center/event lemmas, TC40 threshold scaling, and TC42--TC43 tail-ratio
  reductions;
* `GaussianMillsRatio.lean`, especially the TC43 Mills-gain lower bound;
* `TrackC_round43_T1_MillsGainAudit.md`;
* `TrackC_round42_T1_MillsLogTailRatioAudit.md`;
* `TrackC_round40_T1_ScaledGaussianTailAudit.md`;
* `TrackCStatus.md`.

TC22--TC43 were treated as closed inputs. The false TC35 theorem was not
retried, the TC28 quadratic envelope was not used as a near-midpoint tail
bound, no constants were weakened, and `tusnady_base_polynomial` was not
edited.

## Mandatory False-Target Check

At the dangerous edge `n = 14`, `k = 15`, `z = 3/8`, the event holds:

```text
z + 0.6 + z^2/n = 0.9850446428571429 <= 1 = k - n
```

The scalar gap is numerically true there:

```text
Delta = 0.027775664361994416
(gaussianMillsRatioReal 0)^(-1) * (x-y) = 0.04046344874082341
```

The hardest endpoint for this same `n,k` is the largest event-admissible
`z`, approximately `0.38918128076446634`; the margin remains positive:

```text
rhs - Delta = 0.008411106927301844
```

A diagnostic search over `14 <= n <= 10000`, all admissible `k`, and the
largest event-admissible `z` found no counterexample. The worst sampled
margin occurred in the near-midpoint family `k = n + 1`.

This check was used only to avoid a false-target repeat; no decimal constants
were introduced into Lean.

## Landed Theorems

| Theorem | Status | File:line | Notes |
|---|---|---:|---|
| `gaussianMillsRatioReal_zero` | FULL | `GaussianMillsRatio.lean:86` | Proves `m(0) = sqrt(pi/2)` using `integral_gaussian_Ioi`. |
| `gaussianMillsRatioReal_zero_inv_ge_three_fourths` | FULL | `GaussianMillsRatio.lean:126` | Rational lower bound `3/4 <= m(0)^(-1)`, using `pi_lt_d2`. |
| `carterPollardDeltaPaperShape_even_le_zero_value_gap_of_gap_bound` | FULL | `CarterPollardEq7Bridge.lean:1872` | If `Delta <= (3/4)*(x-y)`, then the exact TC43 zero-value scalar gap follows. |

The TC44 theorem is intentionally a sufficient finite scalar bridge, not a
claim that the original scalar gap has closed.

## Main Target Status

The requested theorem

```lean
theorem carterPollardDeltaPaperShape_even_le_zero_value_gap_of_event
```

did not close in TC44.

The obstruction is sharper than TC43: the Mills side is now explicit. The
remaining issue is the Carter--Pollard `Delta` upper bound. The existing
TC24 theorem

```lean
carterPollardDeltaPaperShape_le_entropy_shape_robbins_upper
```

uses only `lambda_N <= 1/(12N)` and the nonnegative lower bounds for the two
subtracted lambda terms. Near `n=14, k=15`, that coarse lambda treatment gives
a Delta upper bound larger than the zero-value gap. The true statement needs
a sharper lower bound for the subtracted terms, matching the paper's

```text
(12*j + 1)^(-1) <= lambda_j
```

or an equivalent finite Carter--Pollard scalar estimate.

## Remaining Exact Scalar Work

The next useful target is not a stronger Mills theorem. It is a debt-free
finite scalar proof of either:

```lean
carterPollardDeltaPaperShape (2*n) k <=
  (Erdos524.Helpers.gaussianMillsRatioReal 0)^(-1) *
    (sqrt (carterPollardN (2*n)) * carterPollardEps (2*n) k
      - z / sqrt ((n : Real) / 2))
```

or the sufficient rational form now landed:

```lean
carterPollardDeltaPaperShape (2*n) k <=
  (3/4 : Real) *
    (sqrt (carterPollardN (2*n)) * carterPollardEps (2*n) k
      - z / sqrt ((n : Real) / 2)).
```

The most direct route appears to be adding the sharp Robbins lower bound for
`carterPollardLambdaTerm` and then re-running the event/center scalar algebra.

## Verification

Required build:

```text
lake build FormalConjectures.ErdosProblems.Helpers.CarterPollardEq7Bridge \
           FormalConjectures.ErdosProblems.Helpers.OneDimKMT \
           FormalConjectures.ErdosProblems.Helpers.BinomialTailBeta \
           FormalConjectures.ErdosProblems.Helpers.GaussianMillsRatio
```

Result: success (`2900/2900` jobs).

Net debt change: 0.

* No new axioms.
* No new sorries.
* No `Real.Gaussian.compl_cdf`.
* No gamma rewrite.
* No weakening of constants `0.6` or `1`.
* No decimal tuning in Lean.
* No TC35 theorem retry.
* No TC28 near-midpoint quadratic-envelope tail use.
* No `tusnady_base_polynomial` edit.
