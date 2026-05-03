# Track D drop — housekeeping round

**Type**: Pure housekeeping. Archive + axiom removal. No math content closure, no Lean proof work.
**Dispatch surface**: `track-d-btis-honest` worktree (`~/Documents/formal-conjectures-track-d/`), HEAD `2ed4eae` (post-TD5 axiomatisation). Final commit on this branch then archive.
**Scope binding**: only the operations listed in §"Mandatory floor" below. Do NOT modify any other Track A or Track C files.

---

## Why drop Track D

Grok strategic pre-flight (Probe 3) returned : the two parallel paths to retire `gao_li_wellner_small_ball_upper` (Path 1 = Track D Borell-TIS via `borell_tis` + `lipschitz_sup_finite_gaussian` axiom ; Path 2 = Track A GLW algebraic via `glw_lemma_4_1_perturbation` + `glw_det_lower_bound`) are mathematically interchangeable. Verdict :

> Drop Path 1 (Borell-TIS) entirely once Path 2 discharge is verified. Redundancy here provides no proof-theoretic gain (both paths are ultimately axiomatic at the base layer, so neither independently verifies the other beyond simple type-checking) and is a net maintenance burden (duplicate consumer wiring, dual-track synchronization on every future pin bump or refactoring, extra `AXIOM_INVENTORY.md` entries).

Concrete consequence : Track D's `lipschitz_sup_finite_gaussian` axiom is orphaned once R61-A + R62 land Path 2 retirement. The `BTISHonestProof.lean` file becomes dead code.

**Net axiom impact** : -1 axiom (`lipschitz_sup_finite_gaussian` removed from inventory).

---

## Pre-condition

This dispatch can run **at any time after R62 lands** (i.e., after Path 2 has actually retired `gao_li_wellner_small_ball_upper` on mainline). If R62 hasn't landed, hold this dispatch — Path 1 is still load-bearing as a safety net until Path 2 is verified.

If you want to be extra-safe : wait until R62's commit + `gao_li_wellner_small_ball_upper` is confirmed retired (theorem with body, no longer axiom) on mainline `r46-track-a-mge-posdef`, AND the file builds clean without `lipschitz_sup_finite_gaussian` referenced anywhere.

---

## Mandatory floor

### T1 — verification (Full)
1. **Confirm Path 2 landed** : grep mainline for `gao_li_wellner_small_ball_upper` declaration ; confirm it's `theorem` not `axiom`. Document in `Helpers/TrackD_drop_T1_VerificationAudit.md`.
2. **Confirm orphan status** : grep mainline AND track-c AND track-d for `lipschitz_sup_finite_gaussian` callers. Expected : zero callers outside `BTISHonestProof.lean` itself once Path 2 is in place. If any caller exists, halt this dispatch and surface — Track D has a downstream consumer we missed.
3. **Confirm `borell_tis` orphan** : same grep for `borell_tis`. Expected : zero callers outside Track D files.

### T2 — archive (Full)
On `track-d-btis-honest` worktree, move Track D files to a `.archived/` subdirectory :

```sh
fc-d
mkdir -p FormalConjectures/ErdosProblems/Helpers/.archived
git mv FormalConjectures/ErdosProblems/Helpers/BTISHonestProof.lean \
       FormalConjectures/ErdosProblems/Helpers/.archived/BTISHonestProof.lean.archived

# Status doc + audit docs follow (preserve the historical record)
git mv FormalConjectures/ErdosProblems/Helpers/TrackDStatus.md \
       FormalConjectures/ErdosProblems/Helpers/.archived/TrackDStatus.md.archived
git mv FormalConjectures/ErdosProblems/Helpers/TrackD_T1_BTISAudit.md \
       FormalConjectures/ErdosProblems/Helpers/.archived/TrackD_T1_BTISAudit.md.archived
git mv FormalConjectures/ErdosProblems/Helpers/TrackD_round2_T1_PortabilityAudit.md \
       FormalConjectures/ErdosProblems/Helpers/.archived/TrackD_round2_T1_PortabilityAudit.md.archived
git mv FormalConjectures/ErdosProblems/Helpers/TrackD_round3_T1_SemanticVerificationAudit.md \
       FormalConjectures/ErdosProblems/Helpers/.archived/TrackD_round3_T1_SemanticVerificationAudit.md.archived
git mv FormalConjectures/ErdosProblems/Helpers/TrackD_round4_T1_PinBumpProbe.md \
       FormalConjectures/ErdosProblems/Helpers/.archived/TrackD_round4_T1_PinBumpProbe.md.archived
git mv FormalConjectures/ErdosProblems/Helpers/TrackD_round5_prep_T1_Q31Audit.md \
       FormalConjectures/ErdosProblems/Helpers/.archived/TrackD_round5_prep_T1_Q31Audit.md.archived
git mv FormalConjectures/ErdosProblems/Helpers/TrackD_round5_T1_SubLemma3Axiomatization.md \
       FormalConjectures/ErdosProblems/Helpers/.archived/TrackD_round5_T1_SubLemma3Axiomatization.md.archived
```

The `.archived` extension prevents `lake build` from picking up the file. The git history is preserved.

### T3 — verify build (Full)
```sh
fc-d
lake build  # full project build
```
Must succeed cleanly with no `lipschitz_sup_finite_gaussian` or `borell_tis` references remaining as live code.

### T4 — update mainline AXIOM_INVENTORY.md + BACKGROUND.md (Full)
Switch to mainline worktree, update inventory :

```sh
fc-main
# Edit AXIOM_INVENTORY.md to remove lipschitz_sup_finite_gaussian (Track D) entry
# Edit BACKGROUND.md to add a "Track D status: archived (Path 1 dropped per Probe 3)" note
git add AXIOM_INVENTORY.md BACKGROUND.md
git commit -m "Drop Track D Path 1 (Borell-TIS); single-path GLW algebraic ship per Probe 3"
git push fork r46-track-a-mge-posdef
```

### T5 — push Track D archive commit (Full)
```sh
fc-d
git add -A
git commit -m "TD-drop: archive Track D files; Path 1 superseded by Path 2 GLW algebraic"
git push fork track-d-btis-honest
```

---

## Out of scope

- Reviving Track D under a different formalisation strategy (e.g., importing `lean-stat-learning-theory` for a direct Borell-TIS body) — separate decision, not this housekeeping round.
- Removing the `track-d-btis-honest` branch from git — keep the branch for historical access ; only archive the files within it.
- Modifying the worktree itself (`git worktree remove`) — keep the worktree for cross-checks ; just archive the files.

---

## Calibration

- **Budget** : 0 LOC. Pure file moves + inventory updates.
- **Risk band** : zero. The verification gates (T1) prevent dropping if Path 2 isn't actually landed.
- **Closure tier** : housekeeping. Net debt change : **-1 axiom** (`lipschitz_sup_finite_gaussian` orphaned, removed from inventory).
- **Cross-track FS discipline** : applicable. T4 modifies mainline files (AXIOM_INVENTORY, BACKGROUND). Coordinate with any concurrent mainline session — no parallel work on those two files.

---

## Reversibility

If Probe 3's verdict is later revisited and Track D needs to be revived (e.g., a future Mathlib pin bump breaks Path 2 and Path 1 becomes the only stable route), the archived files can be restored with `git mv .archived/X.archived X.lean` and the axiom re-added. Git history preserves the full TC1-TC5 development chain.

End brief.
