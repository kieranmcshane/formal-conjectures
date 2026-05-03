---
name: Track C cluster round process (Erdős 524 1D KMT)
description: Binding process for Track C rounds 2+ — TC2 brief drafted by Cowork, T1.1 grep-FIRST then Grok recipe SECOND with mandatory uncertainty flagging, dispatch-only (no /schedule), active user engagement on math content
type: feedback
originSessionId: 8a6755f7-738f-4b21-9372-1a1ba59ec1b4
---
For Track C rounds 2+ (Erdős 524 1D KMT cluster, branch `track-c-1dkmt` from `r33-c-helpers-consolidation`):

1. **Brief authorship.** Cowork Claude drafts the TC<N> brief; Local Claude (the executing instance) does NOT propose its own brief shape.

2. **T1.1 sequencing.** In every TC<N> round-1-equivalent step, the grep audit of pinned-Mathlib state runs FIRST. The Grok recipe is consulted SECOND, with mandatory uncertainty flagging (per Q4(ii) from the Track C strategic pre-flight).

3. **Dispatch model.** TC<N> ships when the user dispatches it manually. **Do not offer `/schedule`** for autonomous Track C round 2+ kickoff. The user explicitly cancelled the round-1 trailing offer.

4. **Engagement model.** Math content (Skorokhod / Quantile / Hungarian dyadic / SupError closure attempts) requires active user engagement, not background autonomous runs.

**Why:** Track C round 1 closed clean as infrastructure work; rounds 2–4 attempt actual mathematical closure of Layers 1–4 of 1D KMT, where Grok recipe optimism and pinned-Mathlib reality may diverge. Grep-FIRST ensures Brier-honest grounding before Grok-derived LOC budgets / P(success) figures bias planning. Dispatch-only ensures the user sets the cadence (math content vs. signature work need different operator presence).

**How to apply:**
* Do not draft a TC<N> mandatory floor or hard-stop trigger from scratch — wait for Cowork's brief.
* When invoked for TC<N>, the first executable step is `grep -rE …` against `.lake/packages/mathlib` and `brownian-motion` to verify the assumed gap, NOT Grok recipe restatement.
* If grep results contradict any Grok claim, flag the uncertainty in T1.1 audit doc explicitly with line citations; do not silently defer to Grok.
* End-of-round summary may report status, but **must not** offer `/schedule` for the next Track C round.
