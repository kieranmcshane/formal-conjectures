# Track C round 43 - Mills-gain audit

**Date:** 2026-05-03.  
**Branch:** `tc43-cdx-mills-gain-bound`.  
**Base branch:** created from `tc42-cdx-mills-log-tail-ratio`.  
**Targets:** `CarterPollardEq7Bridge.lean`, `GaussianMillsRatio.lean`.

## Survey

Reread:

* `CarterPollardEq7Bridge.lean`, especially the TC41/TC42 tail-ratio and
  Mills-gain scaffold;
* `GaussianMillsRatio.lean`, especially Mills positivity, truncation,
  antitonicity, and the derivative proof;
* `TrackC_round42_T1_MillsLogTailRatioAudit.md`;
* `TrackC_round41_T1_DeltaTailRatioAudit.md`;
* `TrackC_round40_T1_ScaledGaussianTailAudit.md`;
* `TrackCStatus.md`.

TC22--TC42 were treated as closed inputs. The false TC35 theorem was not
retried, the TC28 quadratic envelope was not used near the midpoint, no
decimal tuning was introduced, and `tusnady_base_polynomial` was not edited.

## Landed Mills API

| Theorem | Status | File:line | Notes |
|---|---|---:|---|
| `gaussianMillsRatioReal_hasDerivAt` | FULL | `GaussianMillsRatio.lean:354` | Promoted the already-proved derivative identity from private to public API. |
| `gaussianMillsRatioReal_antitone_nonneg` | FULL | `GaussianMillsRatio.lean:418` | Extends antitonicity to `[0, infinity)` by the same derivative-sign argument on the interior. |
| `gaussianMillsRatioReal_le_zero_value_of_nonneg` | FULL | `GaussianMillsRatio.lean:443` | Gives `m x <= m 0` for `0 <= x`. |
| `gaussianMillsRatioReal_log_hasDerivAt` | FULL | `GaussianMillsRatio.lean:447` | Derivative of `log m`: `x - (m x)⁻¹` on `(0, infinity)`. |
| `gaussianMillsRatioReal_log_ratio_eq_integral_inv_sub` | FULL | `GaussianMillsRatio.lean:457` | FTC identity `log(m y / m x) = integral_y^x ((m t)⁻¹ - t)` for `0 < y <= x`. |
| `gaussianMillsRatioReal_log_ratio_ge_zero_value_bound` | FULL | `GaussianMillsRatio.lean:496` | Quantitative lower bound `(m 0)⁻¹*(x-y) - (x^2-y^2)/2 <= log(m y / m x)`. |

The lower bound is the requested Step A/B architecture, stated with
`(gaussianMillsRatioReal 0)⁻¹` rather than rewriting it to `sqrt(2/pi)`.
This avoids adding extra half-Gaussian integral algebra to the critical path.

## Carter--Pollard Reduction

Landed:

```lean
theorem carterPollardDeltaPaperShape_even_remainder_le_mills_gain_of_event_of_delta_le_zero_value_gap
```

at `CarterPollardEq7Bridge.lean:1834`.

It proves the exact TC43 Mills-gain consumer from the finite scalar hypothesis

```lean
carterPollardDeltaPaperShape (2 * n) k <=
  (gaussianMillsRatioReal 0)⁻¹ *
    (sqrt (carterPollardN (2*n)) * carterPollardEps (2*n) k
      - z / sqrt ((n : Real) / 2))
```

under the same event hypotheses. The proof composes the TC42 threshold package
with `gaussianMillsRatioReal_log_ratio_ge_zero_value_bound`; the quadratic
density-ratio terms cancel exactly.

## Main Target Status

The unqualified theorem

```lean
theorem carterPollardDeltaPaperShape_even_remainder_le_mills_gain_of_event
```

did not close in TC43. The remaining missing statement is no longer a Mills
inequality; it is the explicit Carter--Pollard scalar gap above.

This is a finite symbolic inequality involving the paper-shaped `Delta`, the
event lower bound on the midpoint gap, and the standardized gap
`sqrt(N)*eps - z/sqrt(n/2)`. Existing TC24 Robbins/entropy bounds do not
currently imply that linear gap in the local API.

## Verification

Required build:

```text
lake build FormalConjectures.ErdosProblems.Helpers.CarterPollardEq7Bridge \
           FormalConjectures.ErdosProblems.Helpers.OneDimKMT \
           FormalConjectures.ErdosProblems.Helpers.BinomialTailBeta \
           FormalConjectures.ErdosProblems.Helpers.GaussianMillsRatio
```

Result: success (`2899/2899` jobs).

Net debt change: 0.

* No new axioms.
* No new sorries.
* No `Real.Gaussian.compl_cdf`.
* No gamma rewrite.
* No weakening of constants `0.6` or `1`.
* No decimal tuning.
* No TC35 theorem retry.
* No TC28 near-midpoint quadratic-envelope use.
* No `tusnady_base_polynomial` edit.
