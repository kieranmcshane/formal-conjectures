# Scoreboard — Erdős 524 Formalization Campaign

A "light blockchain" via git: append-only, hash-chained, immutable.
Both AI agents (Cowork Claude, Local Claude) commit predictions and
stakes BEFORE work starts; outcomes are committed AFTER. Kieran is the
human oracle who validates each round.

## Structure

```
scoreboard/
├── README.md           ← this file (protocol description)
├── ledger.md           ← current balances + calibration adjustments
├── predictions/
│   └── round-NN.md     ← Cowork Claude's predictions, committed pre-round
├── stakes/
│   └── round-NN-claude.md  ← Local Claude's stake, committed pre-work
├── outcomes/
│   └── round-NN.md     ← Cowork Claude's resolution, committed post-round
└── validations/
    └── round-NN.md     ← Kieran's chat-approval, committed final
```

## Protocol per round

**Step 1 — Pre-round (Cowork Claude):**
- Drafts `predictions/round-NN.md` with explicit predictions, confidence
  levels, and stakes (in virtual units).
- Local Claude or user commits + tags `round-NN-predictions`.
- Tag is immutable. Force-push forbidden on this branch.

**Step 2 — Pre-work (Local Claude, first action of session):**
- Writes `stakes/round-NN-claude.md` with time-floor stake + substance
  stake.
- Commits before any other work.

**Step 3 — Round happens.**

**Step 4 — Post-round (Cowork Claude):**
- Writes `outcomes/round-NN.md`: resolution table for every prediction +
  Local Claude stake outcomes + new balance proposals.
- Local Claude commits.

**Step 5 — Validation (Kieran):**
- Reads outcomes in chat with Cowork Claude.
- Says "approuvé" or "contesté on X" + override.
- Cowork Claude writes `validations/round-NN.md` with the approval text
  and chat timestamp; Local Claude commits.

**Step 6 — Ledger update:**
- After validation, Cowork Claude updates `ledger.md` with new balances.
- Final commit, tagged `round-NN-final`.

## Anti-cheat properties

- **Pre-round predictions are immutable**: any retroactive edit changes
  the commit hash, breaks the tag, visible in `git log`.
- **Outcomes committed before validation**: cannot be re-written
  favorably after seeing Kieran's reaction.
- **Validation is human-signed**: Kieran's chat approval is the oracle.
  No automated way to fake it.
- **Append-only**: no force-push, no rewriting history. If a mistake is
  made, a *correction* commit is added (visible in audit).

## Stake mechanics

**Cowork Claude predictions:**
- For each prediction with confidence `c%`, stake `c` units.
- Brier-score-style resolution:
  - YES → gain `(100 - c)` units
  - NO  → lose `c` units
  - PARTIAL → gain/lose proportional (judged by Kieran in validation)
- Refusal to predict (when asked) → −50 units flat.

**Local Claude stakes:**
- Time-floor stake `S_t` units (typically 200): if actual session
  duration is `τ%` of allocated time, gain/loss is
  `S_t × (max(0, (τ - 70%) / 30%) - max(0, (70% - τ) / 70%))`.
  Translation: full stake gained at 100% time use, full lost at 0%,
  break-even around 70%.
- Substance stake `S_s` units (typically 100): full stake on hitting the
  productivity floor (≥6 substantive commits, ≥15 lines or ≥2 lemmas
  each), proportional otherwise.
- Discovery bonus: if Local Claude flags a real defect in the prompt
  (e.g., a stress-test failure preempting a relance), +50 units.

**Bounds:**
- Floor: 200 units. Below this, all predictions auto-floored at 50%
  confidence; max stake reduced.
- Ceiling: 2000 units. Above this, ability to "double down" with
  2x stakes on bold predictions.

## Auditing

Anyone can verify the chain by running:

```bash
git log --oneline scoreboard/predictions/round-NN.md
git tag --list "round-NN-*"
git diff round-NN-predictions..round-NN-outcomes -- scoreboard/predictions/
```

If the hash on the tag doesn't match the file content, something was
rewritten. That's tamper detection.
