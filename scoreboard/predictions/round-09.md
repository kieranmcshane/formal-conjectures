# Round 9 Predictions — Cowork Claude

**Committed before round start.**
Round target: close `mvGaussian_box_density_at_mode_bound` (Round 6 residual sorry).

Recalibration applied: prior over-pessimism factor of ~1.5–2x; confidences below
are intentionally above what my naive instinct says, to correct the bias. Past
predictions were consistently right on direction but wrong on magnitude (always
underestimating productivity, overestimating difficulty).

## Predictions

| # | Prediction | Confidence | Stake |
|---|------------|-----------|-------|
| 1 | `mvGaussian_box_density_at_mode_bound` central sorry CLOSED (no sorry on the headline statement). | 70% | 70 |
| 2 | At least 250 lines of substantive math added across `Helpers/MVGaussianDensityBound.lean` and any new `Helpers/MVGaussian*` file. | 80% | 80 |
| 3 | Full build of `FormalConjectures.ErdosProblems.«524»` remains green at end of round. | 95% | 95 |
| 4 | No new axiom introduced (axiom count stays at 2). | 90% | 90 |
| 5 | Local Claude hits the time floor (90-min wall clock, no early stop). | 65% | 65 |
| 6 | At least 1 new Mathlib lemma is identified by name (and used) that wasn't referenced in any prior round. | 75% | 75 |

**Total at risk:** 475 units.

## Resolution mechanics (Brier-style)

For each prediction with confidence `c%` and stake `c` units:
- Resolves YES → gain `(100 − c)` units (e.g. 70%-confidence YES gains +30)
- Resolves NO → lose `c` units (e.g. 70%-confidence NO loses −70)
- Resolves PARTIAL → judged by Kieran in the validation step; typically 0 to ±25%
  of the stake.

If Round 9 produces no sorry-closure on `mvGaussian_box_density_at_mode_bound`
but at least produces a substantial new infrastructure file with progress on
the route, Prediction 1 likely resolves PARTIAL.

## Stretch goal (no stake, just declared)

If the central sorry is closed by minute 60, Local Claude is instructed to
attack the cascade: retire the now-unblocked
`mvGaussian_box_density_at_mode_bound_one` consumer dependencies in
`StandardMVGaussianBox.lean` and `MVGaussianRotation.lean`, and add a
PosDef-general `mvGaussianFromPosDef`-flavored consumer lemma.

## Notes for Kieran (validator)

- All 6 predictions are independent.
- The big stake is on Pred 2 and Pred 3 — adding substance + keeping build
  green should be safe even if Pred 1 fails. Net upside of the round is
  insulated from the hardest-target outcome.
- Pred 5 is the discipline prediction (no early stop). It's set lower than
  Round 8's because Round 8 failed at exactly this criterion. This is the
  test of whether the new "no-early-exit" rule in the prompt actually
  prevents the failure.

— Cowork Claude, Round 9 prep
