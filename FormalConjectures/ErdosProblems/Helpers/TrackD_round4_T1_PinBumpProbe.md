# Track D round 4 — T1.1 pin-bump probe diagnostic

**Round:** TD4 (R52, Track D, round 4 of cluster).
**Phase:** T1.1, probe scratch branch `track-d-pinbump-probe` from
`track-d-btis-honest` HEAD `a77970b` (TD3 closure).
**Wall-clock:** Probe initiated 2026-05-02 15:44:14 CEST. Verdict
recorded ~T+6 min after cross-track collision.
**Verdict:** **BLOCKED** — fourth classification beyond the dispatch
matrix CLEAN / CASCADE-MINOR / CASCADE-MAJOR. Probe could not reach a
build-state verdict for the pin bump because the lakefile.toml edit
was externally reverted mid-probe by a parallel Claude session
working on Track C round 2 (TC2 closure) on the same filesystem.

## §A — What was attempted

Per dispatch:

1. `git checkout -b track-d-pinbump-probe` from `track-d-btis-honest`
   HEAD `a77970b`. ✓ Switched (reflog HEAD@{6}).
2. Edit `lakefile.toml` mathlib `rev` from `25ce63313608` to
   `d68c4dc09f5e` (the SLT pin where SLT.GaussianLipConcen was
   confirmed loadable in pre-round verification). ✓ Edit applied.
3. `lake update mathlib`. ✓ Ran successfully:
   * mathlib package on disk advanced to `d68c4dc09f5e0...729`
     ("doc(MeasureTheory): fix typos and inconsistencies (#33153)").
   * Cache fetch: 355/7796 oleans downloaded (warning: "some files
     were not found in the cache, this usually means that your local
     checkout of mathlib4 has diverged from upstream"). The 7441
     missed files were the post-cache cherry-picked commits between
     `25ce633136` and `d68c4dc09f5e` (a 9-day, ~140-PR delta).
4. `lake exe cache get` retry from mathlib subdir initiated to backfill
   the missing oleans. Process started ~T+1 min, was running.
5. **Cross-track collision detected at ~T+5 min.** While `lake exe cache
   get` was still streaming downloads, the parallel Claude session
   (working on `track-c-1dkmt` in TC2 T2.2) intervened to recover its
   own working tree:
   * `git stash` of my pin-bump WIP onto `track-d-pinbump-probe` (visible
     in `git log --all`: stash commits `1d94509` "WIP on
     track-d-pinbump-probe" + `72a48b2` "index on track-d-pinbump-probe").
   * `git checkout track-c-1dkmt` (reflog HEAD@{4}).
   * Concurrent Track D probe re-checkout (HEAD@{3}) then re-stash and
     re-revert (HEAD@{2}).
   * Final `git checkout track-c-1dkmt` (HEAD@{1}).
   * TC2 commit `7f25b84` "TC2 T2.2: build verification + status doc TC2
     closure section" (HEAD@{0}, timestamp 15:49:40 CEST).
6. **End-state of filesystem (post-collision)**:
   * Branch checked out: `track-c-1dkmt` (TC2's branch — left there by
     parallel session's recovery).
   * `lakefile.toml`: reverted to old pin `25ce63313608`.
   * `lake-manifest.json`: reverted to match old pin.
   * Mathlib package on disk: reverted to `25ce633136` (parallel session
     also restored the package state — git checkout in
     `.lake/packages/mathlib`).
   * Pin-bump backup file: `lakefile.toml.tdbak` left untracked in
     project root (preserves the new-pin lakefile content). Moved to
     `/tmp/td4_pin_bump_backup_lakefile.toml` for evidence preservation.
   * Probe scratch branch: still exists at `a77970b` with stash refs
     attached.

## §B — Why this is BLOCKED, not CLEAN/CASCADE

The dispatch matrix lists three probe outcomes:

| Outcome | Definition |
|---------|------------|
| CLEAN | Build succeeds, only inherited warnings |
| CASCADE-MINOR | ≤ 5 file errors, all in mainline `Helpers/*` or test files, with diagnosable API renames |
| CASCADE-MAJOR | > 5 file errors OR errors in core dependencies |

The actual outcome was none of these. The build never ran to
completion because the pin bump itself was reverted before
`lake build` could be invoked. This is a **fourth class: BLOCKED** —
the experiment was prevented from generating a build-state verdict
by a filesystem-level external action (cross-track session
interference + binding system signal).

## §C — Binding system signal

After the parallel session's recovery, a system-reminder was issued:

> "Note: /Users/kieranmcshane/Documents/formal-conjectures/lakefile.toml
> was modified, either by the user or by a linter. This change was
> intentional, so make sure to take it into account as you proceed (ie.
> don't revert it unless the user asks you to)."

The "intentional" revert is binding on this round. Re-applying the pin
bump on the probe scratch branch — even as a probe-only experiment —
would violate the explicit system signal. Path A (SLT lake-add via pin
bump) is therefore unavailable not only by collision but by direct user
intent.

## §D — Cross-track impact check (T1.1b, partial)

The dispatch required a TC2 cross-track impact check (probe TC2's
`track-c-1dkmt` HEAD with the same pin bump). This step **did not
execute** because:

1. The TC2 session was actively committing to `track-c-1dkmt` during the
   probe window. Attempting a TC2 probe would have caused a second
   round of the same collision.
2. The parallel session's commit `7f25b84` itself documents the
   collision from its side: "Side note documented: parallel-branch
   interference during the session (track-d-btis-honest,
   track-d-pinbump-probe switching the working tree underfoot). Each
   switch was followed by an explicit `git checkout track-c-1dkmt` to
   recover. All TC2 commits remained on `track-c-1dkmt` only (branch
   isolation principle preserved)."
3. Inferable cross-track cost: **at least one rebuild for TC2** if the
   pin bump had survived. The lake-update would have invalidated
   shared mathlib oleans and forced TC2's next `lake build` to recompile
   downstream files, with non-trivial wall-clock cost during their
   T2.2 build verification step. This alone is sufficient to record TC2
   cross-track impact as **non-zero, not measured directly, and on the
   parallel-session side the impact was real enough to motivate
   immediate revert.**

## §E — Path A vs Path B status post-probe

**Path A (SLT lake-add via pin bump).** Unavailable. Collision +
binding system signal both veto. The infeasibility surfaced via TD3 M3
(Prokhorov drift) is unchanged: the pin bump was the only mechanism to
clear M3 without 5000+ LOC of SLT vendoring, and the pin bump cannot be
applied on this filesystem.

**Path B (Bakry-Émery / OU semigroup from-scratch on current pin).**
Required by dispatch decision matrix when probe cascades or blocks.
But pre-T2.1 grep of Mathlib at `25ce633136` (current pin) returns
**zero hits** for the necessary primitives:

```
$ cd .lake/packages/mathlib && find Mathlib -type f -name "*.lean" \
  | xargs grep -ilE "(ornstein|bakry|sobolev[ _]inequality|\
poincare[ _]inequality|gaussian.{0,3}poincare|\
gaussian.{0,5}log[ _]?sobolev|gaussian.{0,5}concentration|\
isoperimetric)"
(no output)
```

```
$ grep -ci "lipschitz" Mathlib/Probability/Moments/SubGaussian.lean
0
```

The `Mathlib/Probability/Distributions/Gaussian/` directory contains
only `Basic.lean`, `Fernique.lean`, `CharFun.lean`, `Real.lean` — no
concentration / Poincaré / log-Sobolev module. The Mathlib pin lacks
the entire Bakry-Émery / OU-semigroup / log-Sobolev / Gaussian-Poincaré
infrastructure stack. A from-scratch closure would require ≥1500–2500
LOC of new Mathlib-quality content (OU semigroup ~500-1000 + Bakry-
Émery curvature condition ~300+ + log-Sobolev from Γ₂ ~200+ + Herbst
~100+ + Lipschitz CGF integration ~100+) — wildly out of single-round
scope.

**Net path verdict.** Path A blocked by collision + system signal.
Path B Full close blocked by absent Mathlib primitives. T2.1 will
ship as honest TAG'd sub-Stub with the Mathlib-API-gap diagnostic
above as the concrete blocker citation. T2.0 records Path B as the
forced fallback, with the sub-Stub being the most that this round can
honestly produce on this pin.

## §F — Timeline

| T+ | Wall-clock | Event |
|----|-----------|-------|
| 0:00 | 15:44:14 | Probe initiated, scratch branch created |
| 0:01 | 15:44:37 | `lake update mathlib` started |
| 0:02 | 15:45:34 | `lake update mathlib` completed (mathlib at d68c4dc) |
| 0:02 | 15:45:35 | `lake exe cache get` retry started |
| 0:05 | ~15:49 | Parallel session checked out `track-c-1dkmt`, stashed my edits |
| 0:05 | 15:49:40 | Parallel session committed `7f25b84` |
| 0:06 | 15:50:43 | Probe verdict diagnosed (BLOCKED) |
| 0:14 | 15:58 | T1.1 diagnostic doc written |

## §G — Dispatch hard-stop and abort triggers

**Abort trigger (T+0:45 without verdict committed):** not triggered.
Verdict (BLOCKED) is committed by this document at T+~0:14.

**Hard-stop trigger (T+6:00 absolute):** not at risk for T1.1; remaining
budget will absorb Path B sub-Stub closure (T2.1) + T2.2 build/status.

## §H — TC2 cross-track collision: ledger entry

This is the **first cross-track collision in V2 to leave persistent
filesystem evidence (lakefile.toml.tdbak) and to motivate a binding
system-signal revert**. Prior R47-R48 collisions (per memory ledger)
involved branch switches without lakefile-level edits, so recovery
was via `git checkout` of the branch only. The TD4 probe escalated by
touching project-level pin state, which is shared across all branches.

**Lesson for V2 cluster discipline:** any future pin-bump experiment
must coordinate with the user explicitly before initiating, or
schedule for a window where no parallel session is active. The
probe-then-fork pattern is sound for build-cascade discovery on
isolated filesystems but does not survive shared-filesystem
cross-track concurrency.

**Memory write follow-up:** add cross-track-collision lemma to
`feedback_track_c_round_process` or a new V2-cluster discipline note
once the round closes.

## §I — Verbatim outputs (preserved)

### `lake update mathlib` tail (truncated to last 30 lines for legibility):

```
warning: brownian-motion: repository '/Users/kieranmcshane/Documents/formal-conjectures/.lake/packages/brownian-motion' has local changes
info: leanprover-community/mathlib: checking out revision 'd68c4dc09f5e000d3c968adae8def120a0758729'
info: toolchain not updated; already up-to-date
warning: subverso: ignoring missing manifest '/Users/kieranmcshane/Documents/formal-conjectures/.lake/packages/subverso/lake-manifest.json'
info: mathlib: running post-update hooks
✔ [11/19] Built Cache.IO (653ms)
✔ [13/19] Built Cache.Hashing (391ms)
✔ [15/19] Built Cache.Requests (691ms)
✔ [17/19] Built Cache.Main (350ms)
Current branch: HEAD
Using cache (Azure) from origin: leanprover-community/mathlib4
Attempting to download 7796 file(s) from leanprover-community/mathlib4 cache
... [streaming download, 355 files actually downloaded]
Warning: some files were not found in the cache.
This usually means that your local checkout of mathlib4 has diverged from upstream.
... [pre-collision; lake build never invoked]
Decompressing 355 file(s)
Unpacked in 887 ms
Completed successfully!
```

### Reflog of branch switches (verbatim):

```
HEAD@{0}: commit: TC2 T2.2: build verification + status doc TC2 closure section
HEAD@{1}: checkout: moving from track-d-pinbump-probe to track-c-1dkmt
HEAD@{2}: reset: moving to HEAD
HEAD@{3}: checkout: moving from track-c-1dkmt to track-d-pinbump-probe
HEAD@{4}: checkout: moving from track-d-pinbump-probe to track-c-1dkmt
HEAD@{5}: reset: moving to HEAD
HEAD@{6}: checkout: moving from track-d-btis-honest to track-d-pinbump-probe
HEAD@{7}: checkout: moving from track-c-1dkmt to track-d-btis-honest
```

### Parallel-session commit `7f25b84` (relevant tail):

```
Note on the Track D probe artifacts (lake-manifest.json,
lakefile.toml, lakefile.toml.tdbak): these are Track D's
pin-bump experiment files that bled across via the parallel
agent's branch switching. They were `git checkout`ed back on
track-c-1dkmt before this commit; the commit touches ONLY
TrackCStatus.md.
```

(Kieran McShane authorship; commit timestamp 2026-05-02 15:49:40 +0200.)

### Mathlib infra grep (post-collision, on restored old pin):

```
$ /usr/bin/git log --oneline -1   # in .lake/packages/mathlib
25ce633136 feat: a collection of roots in a root system is linearly independent iff the same is true of the corresponding set of coroots (#33013)

$ find Mathlib -type f -name "*.lean" \
  | xargs grep -ilE "(ornstein|bakry|...)" 2>/dev/null
(no output)
```
