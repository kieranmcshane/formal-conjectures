# Erdős 524 Lean Handover Brief

**Last updated** : 2026-05-03 post-R61 close + R62 audit-redirect + Probe 5 grounded recalibration.
**Maintainer-on-leave** : Kieran McShane.
**Repo** : `~/Documents/formal-conjectures` (Google DeepMind `formal-conjectures` repo, fork at `kieranmcshane/formal-conjectures`).
**Mathlib pin** : `mathlib4 @ 25ce633136`, August 2024. **Do NOT bump without user-coordinated FS window** (cluster-collision discipline, see `feedback_v2_cluster_filesystem_discipline.md`).
**Current mainline branch** : `r46-track-a-mge-posdef` HEAD `f4011b9`.

> **Every new AI session (Claude / GPT / Gemini / Codex / Antigravity) MUST start by pasting this entire file at the top of its first prompt.** This brief is the canonical context that prevents the chain-mismatch errors we caught at R50, R62, and Probe 5.

---

## 1. Project goal

Formalise Erdős problem 524 in Lean 4 + Mathlib. The mathematical content is the **asymmetric scaling law for PPT (Positive Partial Transpose) entanglement thresholds in random bipartite quantum states** — an extension of the Aubrun / Banica–Nechita / Collins–Nechita line, incorporating the Carter–Pollard 2004 refinement of the KMT/Hungarian coupling.

**Priority #1 (binding, user directive post-R38)** : *"sorry-free, axiom-free solution of problem 524."*

**Honest current target (post-R62 audit + Probe 5 Local-vs-Grok grounded analysis)** : **5-axiom-conditional / 6-axiom-realistic ship**. The 3-axiom target from earlier Probes was conditioned on R62 retiring A4+A5 via the GLW shortcut ; that path was audit-rejected (mismatch ledger #16, #17). A4 + A5 are now classified as multi-year upstream-Mathlib gaps.

---

## 2. Current ledger (post-R61, post-R62-audit-redirect)

**Mainline gate items** : see canonical count in `AXIOM_INVENTORY.md`. As of 2026-05-03 post-R61: 9 user-defined axioms + N sorries (run `grep -rcn "sorry" --include="*.lean" --exclude-dir=.lake . | grep -v ":0"` for the live sorry count). A1 (`Cp_T_explicit_pointwise_axiom`) status: still present at `FormalConjectures/ErdosProblems/Helpers/GLWGaussianProjectiveLimit.lean:2013` as `private axiom` (the prior `^axiom ` grep missed it because of the `private` prefix).

### Axioms (10 total)

| # | Name | Location | Reason / Source | Retirable ? |
|---|---|---|---|---|
| A1 | `Cp_T_explicit_pointwise_axiom` | `524.lean` | D2-property (Carter-Pollard 2004 §3 threshold) | NO — irreducible classical oracle |
| A2 | `one_dim_KMT_coupling` | `524.lean` | 1D KMT/Hungarian coupling existence (Komlós-Major-Tusnády 1975) | NO — irreducible (TC15+ contributing infra only) |
| A3 | `kmt_aided_gaussian_process` | `524.lean` | Stepping-stone Gaussian process (depends on A2) | NO until A2 retires |
| A4 | `gao_li_wellner_small_ball_lower` | `524.lean:3643` | Continuous-index Gaussian-process small-ball lower (full half-line `[0, ∞)`) | NO — multi-year Mathlib gap (Anderson + KL + Talagrand + BTIS) |
| A5 | `gao_li_wellner_small_ball_upper` | `524.lean:3574` | Continuous-index small-ball upper (truncated `Icc 0 (T ε)`) | NO — same gap as A4 ; Q1a/b/c re-localised gap to {multivariate Esseen + multivariate CF integration}, also project-blocked |
| A6 | `glw_det_lower_bound` | `Helpers/GLWSmallBallShortcut.lean:364` | Cauchy-matrix det lower bound `(240·e)^{-2m³}` (R61-introduced under hybrid (c) Path A) | **YES** — R63 brief drafted, ~350-600 LOC, single round, Vandermonde + multilinearity route |
| A7-A10 | (4 other technical axioms) | `AXIOM_INVENTORY.md` | various | tracked in inventory |

### TAG'd sorries (8 total — exact count + locations to verify via `grep -rn "sorry" --include="*.lean"`)

These are deferred for various reasons documented in their TAG comments. Each sorry has a TAG in the form `R##-<topic>` indicating the planned closure round.

---

## 3. The two binding discipline rules (BOTH must be applied to every brief / probe / dispatch)

### Rule 1 : Paper-recheck T1.0 (`feedback_paper_recheck_t10`)

When a brief depends on paper-stated claims (signatures, constants, theorem statements), **the next round's audit MUST fetch the paper before writing any body.** Cowork-derived recall is unreliable. R59 → R60 was the canonical case where the audit-first protocol caught false sigs ; do not skip T1.0.

### Rule 2 : Bridge-gap audit before LOC estimation (`feedback_probe_bridge_gap_audit`)

Before estimating LOC for any axiom-retirement round, write the end-to-end proof sketch from existing in-tree primitives to the axiom's verbatim signature, naming each step. **If any step requires multi-paragraph upstream-Mathlib infrastructure** (Anderson's multivariate inequality, Karhunen-Loève spectral expansion, Talagrand entropy, Slepian, Borel-TIS, multivariate Esseen, multivariate CF integration, KMT coupling at Brownian scale, dyadic-block embeddings, etc.), **the round is contributing infrastructure, not retirement.** Flag the bridge-gap blocker and decline to estimate LOC.

**One-sentence pre-flight question** : *"Does the exact downstream consumer statement require the full continuous-index process with sup-over-`[0, ∞)`, or only a finite-grid version? Verify the hypothesis match in the axiom docstring verbatim."*

**The "delegation via `_compat` hypothesis" cousin failure mode** : when an in-tree file appears to advance toward closure but the deep math has been architecturally relocated into `_compat` / `compat` hypotheses (the lemma body discharges trivially via `exact compat ε hε`), **the producer of the compat witness must be verified to exist in-tree or be in-flight.** If the producer is "out of scope" or absent entirely, the file delegates the gap rather than closing it. Grep recipe :

```bash
grep -rn "_compat\b\|\.compat\b" --include="*.lean" Helpers/<TargetFile>.lean
# Then for each compat hypothesis:
grep -rn "<compat_name> :" --include="*.lean" --exclude-dir=.lake FormalConjectures/
# Zero hits outside the consumer's hypothesis declaration = delegated, not closed.
```

---

## 4. AI Collaboration Protocol (binding for ALL colleagues + ALL models)

1. **Every new session pastes this entire file at the top of the first prompt**, before any task description.
2. **Use the Grok strategic pre-flight probe format** for cross-AI questions : self-contained context (no project acronyms without expansion ; verbatim Lean signatures ; full state explained), numbered questions, explicit success criterion. Bad probes get bad answers ; good probes get usable answers regardless of model.
3. **Never invent new axioms.** Any proposed new axiom must be added to `AXIOM_INVENTORY.md` with full provenance + the bridge-gap audit (Rule 2) demonstrating why it can't be a theorem at this pin.
4. **Brief T1.0 = paper-recheck.** When proposing axiom retirement, T1.0 fetches the paper (or cites a recent T1.0 fetch from another round) and verifies the consumer signature. Skipping T1.0 is what caused R50 + R62 audit-redirects.
5. **Brief T1.0.5 = bridge-gap audit.** Apply Rule 2 BEFORE T1.1 Mathlib API audit. If GAP annotation surfaces, abort the round and downgrade to "contributing infrastructure" framing.
6. **Preferred executor for Lean code** : Claude (largest context, best at long Lean proofs at this Mathlib pin). Use GPT-4o / Codex / Gemini for **planning and small tactics** (Strategy proposals, audit doc drafting, sub-lemma sketches) — but Claude actually writes the bodies. Multi-model handoff works as long as the brief is self-contained per Rule 4.
7. **End every AI response with a 3-line ledger update** :
   - "Mainline gate items now : N (X axioms + Y sorries), delta from start of session : ±M."
   - "Next-round LOC estimate + net debt change."
   - "Whether this moves us toward the 5-axiom (or 6-axiom) ship target."

If a model output doesn't include this 3-line ledger update, treat it as incomplete and ask again.

---

## 5. Branch + worktree hygiene (CRITICAL — cluster collision discipline)

**Mandatory worktree pre-step** for any parallel-track work (cross-collision discipline, see `feedback_v2_cluster_filesystem_discipline.md`) :

```bash
git worktree add ../formal-conjectures-track-c track-c-1dkmt
git worktree add ../formal-conjectures-track-d track-d-btis-honest
# After each git worktree add OR after any lake update mathlib :
cd <worktree-path> && lake exe cache get   # MANDATORY ~2-5 min vs 30-60 min cold compile
```

Each session works in its own worktree. **No cross-state mutation possible.** Lake mutations (pin bumps, `lake update`, `.lake/packages` checkouts) cannot leak across worktrees.

**Active worktrees + branches at handoff** :
- `~/Documents/formal-conjectures` — mainline `r46-track-a-mge-posdef` HEAD `f4011b9` (post-R61, post-R62-audit-redirect-pending-commit).
- `~/Documents/formal-conjectures-track-c` — `track-c-1dkmt` HEAD `efe78d7` (post-TC11, ready for TC12).
- `~/Documents/formal-conjectures-track-d` — `track-d-btis-honest` HEAD `2ed4eae` (post-TD5 axiomatisation, dormant pending TD-drop housekeeping).

**Branch naming for new dispatches** : `r<round>-<initials-or-ai>-<topic>`, e.g. `r63-claude-cauchy-det`, `r64-gpt-q1abc-audit`, `tc12-gemini-bulk-upper`.

---

## 6. Operational tooling (already installed)

- **`lean-doctor`** : run when Mac CPU saturates. `lean-doctor` for diagnosis, `lean-doctor --fix` for cleanup. Auto-runs every 15 min via launchd, notifies on warnings/critical via macOS notification.
- **`lean-build-sweep`** : weekly Sunday 03:00 cron via launchd. Runs `lake build` incrementally in each worktree, notifies only on regression. Log : `~/Library/Logs/lean-build-sweep.log`.
- **Cache discipline** : `lake exe cache get` (alias `lakecache` in `~/.zshrc`) is MANDATORY after `git worktree add`, `lake update mathlib`, or toolchain bump. Skip = ~30-60 min cold compile.
- **Targeted builds** : `lake build FormalConjectures.ErdosProblems.Helpers.<File>` (alias `lakebuild` with `-j 4` cap) instead of full `lake build`.

If a colleague's Mac chokes : tell them to run `lean-doctor` first. The script identifies the heavy process (usually a ghost LSP, an orphaned `lake build`, or a forgotten `ollama`).

---

## 7. Round queue (prioritised, see `ROADMAP.md` for full detail)

**Immediate dispatchable rounds** (briefs in `outputs/`) :

| Round | Dispatch surface | Priority | Brief |
|---|---|---|---|
| R62 audit-redirect commit | mainline | **DO FIRST** (just commit + push) | `outputs/R62_SmallBall_Retirement_brief.md` (audit doc only, no body) |
| R63 Cauchy det + retire glw_det_lower_bound | mainline | HIGH (drops axiom inventory 10 → 9, gets 5-axiom ship target on table) | `outputs/R63_Cauchy_Det_Retirement_brief.md` |
| TC12 Carter-Pollard §2 eq (7) + §4 bulk upper | track-c | HIGH (parallel to R63, no FS conflict) | `outputs/TC12_CarterPollard_Eq7_BulkUpper_brief.md` |
| TD-drop housekeeping | track-d | LOW (after R63) | `outputs/TD_drop_housekeeping_brief.md` |

**Forecast for next ~10 dispatch rounds** : R63 + TD-drop + TC12-TC14 + start TC15 audit (BEFORE TC15 dispatch, apply Rule 2 to `hungarian_dyadic_step` body — flag GAP risk on Brownian-motion-marginal construction).

---

## 8. What NOT to do (anti-patterns + recent precedents)

- ❌ Propose axiom retirement via "compose now-Full finite-dim Lemma X with consumer code in N LOC" without applying Rule 2. **R50 + R62 audit-redirected for this exact error.**
- ❌ Estimate LOC for a round whose brief skipped T1.0 paper-recheck. **R60-attempt-1 halted for this exact error.**
- ❌ Bump Mathlib pin without user-coordinated FS window. **TD4 pin-bump probe collided with TC2 session, see `feedback_v2_cluster_filesystem_discipline`.**
- ❌ Run `lake build` (full project) during edit rounds. Use targeted `lake build <Module>`. Full project build runs only via the weekly `lean-build-sweep`.
- ❌ Modify TC1-TC11 Full theorems or R59-R61 GLW theorems. They are sealed for downstream consumption.
- ❌ Skip the 3-line end-of-response ledger update. It's the self-audit that catches drift.

---

## 9. Where to find the canonical state

- **`AXIOM_INVENTORY.md`** at repo root : canonical axiom list (10 entries) with file:line + retirement status.
- **`ROADMAP.md`** at repo root : prioritised round queue + LOC budgets + dependencies + Probe 4/5 trajectory math.
- **`BACKGROUND.md`** at repo root : full project history (round-by-round), maintained by Cowork Claude. Currently untracked-local in mainline ; commit before handoff if not done.
- **`outputs/` directory** : all dispatched briefs, audit docs, Grok probes, memory notes, scripts. Per-session ; share contents with colleagues by copying selected files into the repo or pointing them at the path.
- **Memory notes** at `~/.claude/projects/-Users-kieranmcshane/memory/` : feedback notes capturing discipline rules. Notable :
  - `feedback_paper_recheck_t10.md` (Rule 1)
  - `feedback_probe_bridge_gap_audit.md` (Rule 2)
  - `feedback_v2_cluster_filesystem_discipline.md` (worktree discipline)
  - `feedback_lean_cpu_fix.md` (CPU saturation cure)

---

## 10. Quickstart for new colleague (5 minutes)

1. `git clone https://github.com/google-deepmind/formal-conjectures.git && cd formal-conjectures && git remote add fork https://github.com/kieranmcshane/formal-conjectures.git && git fetch fork`
2. `git checkout -b <my-init>-test fork/r46-track-a-mge-posdef && lake exe cache get && lake build FormalConjectures.ErdosProblems.«524»` (verify environment).
3. Read this `HANDOVER_BRIEF.md` end-to-end.
4. Read `ROADMAP.md` to pick a round from the queue.
5. Open your AI of choice, paste this `HANDOVER_BRIEF.md` at top, then paste the round brief from `outputs/`. Begin work.

End brief.
