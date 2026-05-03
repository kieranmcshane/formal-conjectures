---
name: V2 cluster cross-track filesystem discipline
description: Pin-bump experiments and any project-level (non-branch-isolated) state mutation in the V2 cluster require user-confirmed exclusive filesystem windows; probe-then-fork patterns do NOT survive shared-FS cross-track concurrency.
type: feedback
originSessionId: da060d08-a452-4de2-8f30-e3aa51731653
---
**Rule.** In the formal-conjectures V2 multi-track cluster, any
filesystem operation that mutates project-level state shared across
all branches — pin bumps in `lakefile.toml`, `lake update` calls,
`lake-manifest.json` rewrites, `.lake/packages/*` checkouts — must be
preceded by user confirmation of an exclusive filesystem window. Do
NOT initiate such operations on a shared filesystem when other Claude
sessions (Track A, B, C, D, etc.) may be active. Branch isolation is
NOT sufficient protection: project pin state lives outside any branch.

**Why:** TD4 (R52, Track D round 4, 2026-05-02) executed a probe-then-fork
pin-bump experiment per dispatch on `track-d-pinbump-probe` scratch
branch. The pin bump (mathlib `25ce63313608` → `d68c4dc09f5e`) and
`lake update mathlib` succeeded, but before `lake build` could be
invoked, the parallel TC2 Claude session on `track-c-1dkmt` intervened
to recover its own working tree: `git stash` of the probe-branch WIP,
branch switch, mathlib package restore (via `git checkout` in
`.lake/packages/mathlib`), and a TC2 commit at 15:49:40 CEST
(`7f25b84`) explicitly acknowledging "parallel-branch interference
during the session." A binding system-reminder followed: "the
lakefile.toml revert was intentional, do not revert it unless the user
asks you to."

This was the first V2 cross-track collision to leave persistent
filesystem evidence (`.tdbak` backup file in project root) and to
motivate a binding system-signal revert. R47-R48 prior collisions per
the project memory ledger involved branch-only switches without
project-state mutation; recovery there was via simple `git checkout`.
TD4 escalated by touching shared pin state, which exposed the
limitation of probe-then-fork on shared filesystems.

A second collision struck mid-T2.2: the parallel session checked out
`r46-track-a-mge-posdef` between Track D's T2.1 commit (`b9dcad1`) and
T2.2 append. The append silently created a fresh truncated
`TrackDStatus.md` on the wrong branch. Recovery required: branch
switch back to `track-d-btis-honest`, content preservation in `/tmp`,
re-application atomically with branch guards.

**How to apply:**

1. **Before any `lake update`, `lakefile.toml` mathlib `rev` edit, or
   `.lake/packages/*` checkout in formal-conjectures**: ask the user
   to confirm no parallel session is active. The project routinely
   runs Track A/B/C/D Claude sessions in parallel on the same
   filesystem.
2. **Probe-then-fork is sound on isolated filesystems** (worktrees,
   single-session sandboxes) but does NOT survive shared-FS cross-track
   concurrency. If the dispatch demands a pin-bump probe, either:
   (a) request a worktree/sandbox via `EnterWorktree` for the probe
   phase, or
   (b) request the user to coordinate the cluster (pause parallel
   sessions, then run the probe).
3. **For all multi-step file edits + commits in shared-FS V2 work**:
   wrap the edit + `git add` + `git commit` in a single bash invocation
   with branch guards (`BRANCH=$(git branch --show-current); [ "$BRANCH"
   = "expected-branch" ] && ...`). The TD4 T2.2 recovery used this
   pattern after the second collision; it works.
4. **Symptoms of an in-flight cross-track collision** (watch for these
   and stop immediately if observed):
   - `git status` reports a different current branch than the one you
     just checked out.
   - A previously-existing tracked file shows as untracked or is
     truncated.
   - `git stash list` shows new `WIP on <my-scratch-branch>` entries
     that you did not create.
   - `git reflog` shows checkout entries you did not initiate.
   - System-reminder declares an external file modification
     "intentional".
5. **If a collision is detected**: do NOT continue the original task on
   the contested filesystem branch. Recover the working tree, switch to
   the canonical branch for your task, document the collision in the
   round's diagnostic doc, and either ship the round in degraded form
   (sub-Stub with citation) or escalate to the user for coordination.
6. **System-reminder of "intentional revert" is binding.** If the user's
   parallel session reverts your edit and a system-reminder follows
   declaring the revert intentional, do not re-apply the edit on the
   shared filesystem this round. Document and migrate the unblocking
   condition to a future round with explicit user-coordinated window.

**Cross-reference:** Helpers/TrackD_round4_T1_PinBumpProbe.md
(verbatim probe diagnostic, reflog evidence, parallel-session commit
text), Helpers/TrackDStatus.md TD4 addendum sections T2.0 + T2.2.
