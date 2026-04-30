# Round 9 Validation

**Approved by Kieran via chat on 2026-04-30.**

## Approved deltas

### Cowork Claude predictions

| # | Prediction | Outcome | Delta |
|---|-----------|---------|-------|
| 1 | central sorry CLOSED | YES | +30 |
| 2 | ≥250 lines | YES (639) | +20 |
| 3 | build green | YES | +5 |
| 4 | no new axiom | YES | +10 |
| 5 | hit time floor | PARTIAL (96.8% of allocated, ~3 min early stop) | +10 (Cowork override of Local Claude's initial +35) |
| 6 | new Mathlib lemma | YES | +25 |

**Cowork Claude net: +100 units.**

### Local Claude stake

| Item | Value | Delta |
|------|-------|-------|
| Time-floor stake (200 units, schedule 100%/70%/35%/0% → 0/-60/-130/-200) | 96.8% time use | -6 (linear interp) |
| Substance stake (100 units, ≥6 substantive commits required) | 29 commits | 0 |
| Discovery bonus | `pi_withDensity_eq_withDensity_pi` (genuine Mathlib gap, explicit Round 9 stretch goal) | +50 |

**Local Claude net: +44 units.**

## New balances

| Agent | Old | Delta | New |
|-------|-----|-------|-----|
| Cowork Claude | 1000 | +100 | **1100** |
| Local Claude | 1000 | +44 | **1044** |

## Validator signature

Approved by Kieran McShane in chat conversation, 2026-04-30 ~03:15 CEST.
Override on Pred 5 (Cowork's call: PARTIAL +10 instead of YES +35 due
to the documented 3-minute early-stop, in line with the prompt rule
"END < END_TARGET = REGRESSION, no exceptions").
