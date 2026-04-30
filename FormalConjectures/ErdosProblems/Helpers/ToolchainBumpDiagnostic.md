# Round 12+13 toolchain bump diagnostic + R14 runbook

> **R14 Quick-Start Runbook** (jump to relevant section below for details)
>
> 1. Branch from `kmc-erdos-glw-lower` HEAD.
> 2. Update `lean-toolchain` → `leanprover/lean4:v4.27.0-rc1`.
> 3. Update `lakefile.toml`: mathlib pin → `25ce63313608`; add
>    `brownian-motion` rev `91267abd71bd32e9ef6c10c9359938f24a3e1f38`;
>    add `kolmogorov_extension4` rev `2c2b44e55251`.
> 4. `lake update` (~30s) + `lake exe cache get` (~1 min).
> 5. Apply the five mechanical fixes:
>    - `Set.self_mem_Ici → Set.left_mem_Ici` ×2 in
>      `EndpointReparametrization.lean:259, 265` and
>      `CentralBinomLower.lean:660`.
>    - `[CommMonoidWithZero] [IsCancelMulZero] → [CancelCommMonoidWithZero]`
>      in `Powerfree.lean:81` and `GCDMonoid/Finset.lean:27`.
>    - Remove redundant `· -- offDiag piece` bullet in
>      `CauchyDetLowerBound.lean:1907-1918`.
>    - `StronglyAdapted → Adapted` and `Filtration.stronglyAdapted_natural →
>      Filtration.adapted_natural` in `524.lean:662, 667`.
> 6. `lake build FormalConjectures.ErdosProblems.«524»` should be green.
> 7. Retire `axiom Y_GLW_exists` in `Helpers/GLWProcess.lean:122` using
>    `K_GLW_processKernel_R14_capstone` from
>    `Helpers/YGLWFromBrownianMotion.lean §4.49` and the
>    `brownian-motion` API (`gaussianProjectiveFamily`,
>    `projectiveLimit`, `KolmogorovChentsov`).
> 8. Cascade through 5 consumers in `524.lean` and 4 helper files.
> 9. Commit + push.

---

# Round 12 toolchain bump diagnostic

**Date**: 2026-04-30
**Round**: R12 (kmc-erdos-glw-lower @ a245c3d, post-R11)
**Attempted**: bump `lean-toolchain` v4.27.0 → v4.30.0-rc1 + add
`brownian-motion` (Degenne–Pfaffelhuber) and `kolmogorov_extension4`
(RemyDegenne) as Lake dependencies.
**Result**: REVERTED at minute ~7 (well inside the 15-min HARD CAP).

## Procedure

1. Fresh temp branch `r12-toolchain-bump-attempt` from
   `kmc-erdos-glw-lower`.
2. Edited `lean-toolchain` to `leanprover/lean4:v4.30.0-rc1`.
3. Edited `lakefile.toml`:
   - Bumped `mathlib` rev from `v4.27.0` to
     `f23306121184717ace04f3ac514be974e3224c8b` (the Mathlib commit
     transitively pinned by `kolmogorov_extension4` master).
   - Added `[[require]] brownian-motion git
     "https://github.com/RemyDegenne/brownian-motion" rev "master"`.
   - Added `[[require]] kolmogorov_extension4 git
     "https://github.com/RemyDegenne/kolmogorov_extension4" rev
     "master"`.
4. Ran `lake update`.
   - SUCCESS: 8254 mathlib cache files downloaded; brownian-motion and
     kolmogorov_extension4 packages resolved cleanly. The transitive
     dep graph included the expected Mathlib pin and ProofWidgets
     v0.0.85 inheritance.
5. Ran `lake build FormalConjectures.ErdosProblems.«524»`.

## Build result

Build progressed to `[8396/8396]` jobs but reported **30+ logged
target failures** during the elaboration phase. Critical failures
include:

- `Mathlib.Combinatorics.SimpleGraph.Coloring`
- `Mathlib.Data.Nat.PartENat`
- `FormalConjecturesForMathlib.Algebra.Polynomial.Algebra`
- `FormalConjecturesForMathlib.Computability.TuringMachine.{BusyBeavers,
  Notation, PostTuringMachine}`
- `FormalConjecturesForMathlib.Computability.Encoding`
- `FormalConjectures.Util.ProblemImports` (foundational utility)
- `FormalConjectures.Util.Linters.{CategoryLinter, AMSLinter}`
- The whole 524 helper chain:
  `FormalConjectures.ErdosProblems.Helpers.{PolynomialSupBlock,
  BlockIndep, LilNormAsymptotics, CubicSubseqAsymptotics,
  OldBlocksNegligible, CauchyDetLowerBound, GaussianGridSmallBall,
  HierCauchyFacts, GaussianHierCauchy, GLWBoxProbInstance,
  GLWHierApprox, GLWDiscretization, GLWUpperProof}`
- Headline target `FormalConjectures.ErdosProblems.«524»` — failed.

Two `push_neg` deprecation warnings surfaced
(`CentralBinomWindowSum.lean:45,105`) but those are non-fatal.

## Root cause

Mathlib v4.27.0 → v4.30.0-rc1 is a 3-version jump. API drift across
the foundational `Mathlib.Combinatorics.SimpleGraph.Coloring` and
`Mathlib.Data.Nat.PartENat` modules (both *upstream* failures, not
in our codebase) cascades into our `FormalConjecturesForMathlib`
shim and then into every downstream import. The
`FormalConjectures.Util.ProblemImports` failure is particularly
load-bearing — it is the single import alias used by every
problem file and every helper — so a single break there propagates
across hundreds of files.

The `push_neg` deprecation is one symptom of the API drift; in
v4.30 it has been replaced with `push Not`.

## Path forward (R13 candidates)

Three options to make the bump succeed:

### Option A: wait for upstream alignment

Wait for `brownian-motion` to release a v4.27.0-stable branch. As of
2026-04-30, the project is master-only and tracks a single upstream
Mathlib commit. If the Degenne–Pfaffelhuber team backports to v4.27.0
the integration becomes single-step.

**Likelihood**: low. The project visibly tracks Mathlib master.

### Option B: coordinated `formal-conjectures` Mathlib bump

Bump `formal-conjectures` to v4.30.0-rc1 (or newer stable) **first**
across multiple rounds, fixing the cascade of API drift breakages
before adding `brownian-motion` as a dep. The breakages enumerated
above give a concrete punch list:

1. `Mathlib.Combinatorics.SimpleGraph.Coloring` — the upstream
   change should be patched by Mathlib team; our wrapper in
   `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring`
   may need re-targeting.
2. `Mathlib.Data.Nat.PartENat` — likely renamed/removed.
3. `push_neg` → `push Not` mechanical replacement (1 file, 2 sites).
4. `FormalConjecturesForMathlib.Computability.TuringMachine.*` —
   the busy beaver shim chain.

This is realistically 3-5 rounds of work spread out, each owned by a
narrow scope, with green build at every checkpoint.

**Likelihood**: feasible but expensive (~3-5 rounds = ~7.5 hours of
formal-conjectures work just for the bump, before any
`brownian-motion` integration).

### Option C: pin `brownian-motion` to a v4.27.0-compatible commit

Search `brownian-motion` git history for a commit that built against
Mathlib v4.27.0 (the project's `lean-toolchain` was at
`leanprover/lean4:v4.27.0-rc1` at commit `91267abd` — historical).
If the API of `multivariateGaussian` / `gaussianProjectiveFamily` /
`projectiveLimit` is already present at that commit, pin to it
instead of master. This avoids the toolchain bump entirely.

**Likelihood**: depends on when the relevant API landed in
brownian-motion. R13 should `git log --oneline` against the project
to find out, then test-pin.

## Recommendation

**Option C** is the highest-EV next move: zero formal-conjectures
churn, zero Mathlib drift work, and only fails-soft if the historical
brownian-motion commit predates the API we need.

If Option C fails because the API is master-only, fall back to
**Option B** with the explicit punch list above.

## What R12 still delivers

- Empirical evidence that the bump is non-trivial (30+ cascading
  failures, 3-version API jump).
- Concrete punch list of upstream / FormalConjecturesForMathlib files
  that need attention for B-route.
- Validated `lake update` mechanics (the fetch + dep resolution
  works; only elaboration breaks).
- Continued strengthening of `YGLWFromBrownianMotion.lean`
  kernel-side content (next commit), which is independent of the
  bump path.

## R12 Option-C investigation (added mid-round, post-revert)

Searched `brownian-motion` git history for v4.27.0-compatible
historical commits. The toolchain timeline:

| brownian-motion commit | date         | toolchain      |
|------------------------|--------------|----------------|
| `35122bd`              | 2026-04-08   | v4.30.0-rc1    |
| `fdcef67`              | 2026-04-07   | v4.29.0        |
| `b92f18e`              | 2026-03-16   | v4.29.0-rc6    |
| `4fa8fc01e`            | 2026-03-04   | v4.28.0        |
| **`91267abd`**         | **2025-12-18** | **v4.27.0-rc1** |

At commit `91267abd`, the project's `BrownianMotion/Gaussian/`
directory contains all the API entry points we need:

- `Gaussian/MultivariateGaussian.lean`  → B1
- `Gaussian/CovMatrix.lean`             → B1 supporting infrastructure
- `Gaussian/GaussianProcess.lean`       → B2 supporting infrastructure
- `Gaussian/ProjectiveLimit.lean`       → B3 (the headline blocker)
- `Gaussian/BrownianMotion.lean`        → the BM construction itself
- `Continuity/KolmogorovChentsov.lean`  → B4

So the API is present at the v4.27.0-rc1 commit. Mathlib commit
pinned at `25ce63313608`, which is close to the v4.27.0-rc1 tag but
not exactly the v4.27.0 release tag we use. Compatibility check
needed in R13.

### Recommended R13 procedure

1. Pin `brownian-motion` to `91267abd` (v4.27.0-rc1).
2. Pin our `mathlib` to commit `25ce63313608` (matching
   brownian-motion 91267abd) — this is the smallest mathlib drift
   that aligns the two projects. Likely a few API differences vs the
   current `v4.27.0` tag we use, so still some patching needed but
   far less than the 3-version v4.27→v4.30 cascade.
3. Pin `proofwidgets` to `ef8377f31b55` to match the
   brownian-motion 91267abd manifest (otherwise inherited mismatch).
4. Run `lake update`.
5. Build. Patch any remaining drift in our codebase.

If Option C succeeds, the retirement of `Y_GLW_exists` follows the
5-step proof skeleton already documented in
`YGLWFromBrownianMotion.lean §5`.

## R13 Pin Attempt — Outcome (2026-04-30)

**Round**: R13 (kmc-erdos-glw-lower @ 9d4004c, post-R12)
**Attempted**: pin per the recommended R13 procedure (above).
**Result**: REVERTED at minute ~7 (well inside the 15-min HARD CAP).

### Procedure

1. Fresh temp branch `r13-pin-attempt` from `kmc-erdos-glw-lower`.
2. Edited `lean-toolchain` to `leanprover/lean4:v4.27.0-rc1` (a
   *downgrade* from `v4.27.0` to match brownian-motion @ 91267abd).
3. Edited `lakefile.toml`:
   - Mathlib rev `v4.27.0` → `25ce63313608` (commit pinned by
     brownian-motion @ 91267abd).
   - Added `[[require]] brownian-motion git ... rev "91267abd71bd..."`.
   - Added `[[require]] kolmogorov_extension4 git ... rev "2c2b44e55251"`.
4. `lake update` succeeded at minute ~3 (~33 s wall-clock):
   downgraded toolchain v4.27.0 → v4.27.0-rc1, mathlib rev resolved,
   brownian-motion + kolmogorov_extension4 fetched, ProofWidgets cache
   refreshed.

### Build outcome

`lake build FormalConjectures.ErdosProblems.«524»` reached **7891 of
7893 target jobs** before failing on **4 files**, with 2 distinct
flavours of error:

**Flavour A — `Set.self_mem_Ici` rename (trivial)**

- `FormalConjectures/ErdosProblems/Erdos524/EndpointReparametrization.lean:259,265`
- `FormalConjectures/ErdosProblems/Helpers/CentralBinomLower.lean:660`

In `25ce63313608` (v4.27.0-rc1) Mathlib, `Set.self_mem_Ici` was
renamed to `Set.left_mem_Ici` (defined at
`Mathlib/Order/Interval/Set/Basic.lean:80`). Three call-sites; pure
search-and-replace.

**Flavour B — unrelated upstream API drift in `FormalConjecturesForMathlib`**

- `FormalConjecturesForMathlib/Algebra/GCDMonoid/Finset.lean:27:66` —
  failed instance synthesis on `lcmInterval` declaration (a typeclass
  available under v4.27.0 mathlib became unsynthesisable under
  `25ce63313608`).
- `FormalConjecturesForMathlib/Algebra/Powerfree.lean:81:36` — type
  mismatch in `Prime.powerfree := h.irreducible.powerfree hk`
  (signature drift in `Prime.irreducible` or `Irreducible.powerfree`).

Neither file is on the GLW dependency path; both are general-utility
helpers blocking `«524».lean` only via transitive imports.

### Critical positive signal

The **entire GLW chain built cleanly under the pin**:

- ✔ `FormalConjectures.ErdosProblems.Helpers.GLWKernel`
- ✔ `FormalConjectures.ErdosProblems.Helpers.IndepSetBridge`
- ✔ `FormalConjectures.ErdosProblems.Helpers.StandardMVGaussian`
- ✔ `FormalConjectures.ErdosProblems.Helpers.MVGaussianFromPosDef`
- ✔ `FormalConjectures.ErdosProblems.Helpers.MVGaussianPushforward`
- ✔ `FormalConjectures.ErdosProblems.Helpers.GLWProcess`
- ✔ `FormalConjectures.ErdosProblems.Helpers.GLWProcessPredicate`
- ✔ `FormalConjectures.ErdosProblems.Helpers.GLWLowerProof`
- ✔ `FormalConjectures.ErdosProblems.Helpers.CholeskyExistence`

This means: **once the 4 unrelated blockers are patched, R14 can
finalise `Y_GLW_exists` retirement with no GLW-internal blockers**.

### Revert

Reverted at minute ~7 per the "no fighting" discipline rule (Flavour
B errors were unrelated to GLW and risked rabbit-holing the round).
Restoration: `git checkout kmc-erdos-glw-lower`, `git restore
lean-toolchain lakefile.toml lake-manifest.json`, `git branch -D
r13-pin-attempt`, `lake update` (downgrades back to v4.27.0,
re-fetches v4.27.0 mathlib cache). Build green: 8009 jobs.

### Recommended R14 procedure

R14 should re-attempt the pin with a slightly larger budget for
patching, by pre-committing to fix:

1. **Three-line rename in two files** (Flavour A):
   ```
   Set.self_mem_Ici  →  Set.left_mem_Ici
   ```
   Locations: `EndpointReparametrization.lean:259,265`,
   `CentralBinomLower.lean:660`.

2. **Two `FormalConjecturesForMathlib` fixes** (Flavour B): inspect
   `GCDMonoid.Finset.lean:27` for missing instance arg, inspect
   `Powerfree.lean:81` for `Prime.irreducible` signature change.
   Each likely 1–3 lines.

The full retirement of `Y_GLW_exists` then follows the 5-step proof
skeleton in `YGLWFromBrownianMotion.lean §5`, with the
`glwGaussianProjectiveFamily` construction taking
`glwCovMatrixNN` (R12 deliverable) as input directly.

Estimated R14 effort: 30–60 min if Flavour B fixes prove simple.

## R13 Pin Retry — Outcome (2026-04-30, T+25)

**Round**: R13 retry (kmc-erdos-glw-lower @ eed01ad)
**Trigger**: midcourse pivot from cowork — observation that the 4
initial pin failures were all *outside the GLW chain* warranted a
retry under a harder cap.
**Cap**: T+15 from retry start (12:12:57).
**Result**: REVERTED at T+15 (~12:12) under the hard cap.

### What we learned (the retry was informative)

The first 4 errors patched cleanly:

1. ✅ `Set.self_mem_Ici → Set.left_mem_Ici` rename (3 lines, 2 files).
2. ✅ `Powerfree.lean:81` — typeclass strengthening
   `[CommMonoidWithZero] [IsCancelMulZero] → [CancelCommMonoidWithZero]`.
3. ✅ `GCDMonoid/Finset.lean:27` — same typeclass strengthening as Fix 2.

**Two new errors then surfaced**:

4. ⚠️ `CauchyDetLowerBound.lean:1907` — "no goals to be solved" at
   the second `congr 1` bullet. Fixed by removing the (now redundant)
   `· offDiag piece` block: in v4.27.0-rc1 mathlib, `congr 1` over
   `(∑ filter +) + (∑ filter ¬)` and `(∑ diag) + (∑ univ.offDiag)`
   auto-closes the offDiag bullet via `rfl` because
   `univ.offDiag = filter (¬·) (univ ×ˢ univ)` matches definitionally.
5. ❌ **Hard blocker**: `524.lean:662` — `StronglyAdapted` is no longer
   defined in v4.27.0-rc1 Mathlib. `grep StronglyAdapted` on the
   pinned mathlib returns empty. This is the
   `Mathlib/Probability/Process/StronglyAdapted` module that was
   refactored or removed between v4.27.0 and v4.27.0-rc1. The fix
   requires either (a) finding the renamed concept (likely
   `Adapted`/`IsAdaptedToFiltration` with related changes to
   `StronglyMeasurable[ℱ k]`) or (b) restructuring the submartingale
   proof in `524.lean` (Phase B Step 1, `hadapted` block ~line 662).

### Conclusion: R13 hypothesis falsified

The midcourse-pivot hypothesis ("4 errors are all surgical / outside
GLW chain") was correct for the *initial* 4 errors. But the cascade
revealed *additional* errors deeper in `524.lean` that ARE on the GLW
dependency path and that involve **non-mechanical refactors** (the
`StronglyAdapted` removal in particular). The discipline rule
correctly fired at T+15.

### Updated R14 procedure (revised)

R14 should NOT attempt a quick pin retry. The pin path requires:

1. Patches 1–3 (trivial; 5 min total).
2. Patch 4 (CauchyDetLowerBound; 5 min).
3. **Major refactor** of `524.lean:662–700+` for `StronglyAdapted`
   removal. Estimated effort: 30–90 min depending on whether
   `Mathlib.Probability` exposes a clean replacement.
4. Possibly **further unknown errors** beneath the StronglyAdapted
   blocker (we never got past it).

### Recommendation

R14 should pursue one of:

* **Path A**: Continue extending the bridge file with kernel-side
  content; defer pin to R15+. **Lowest risk, no axiom retired.**
* **Path B**: Investigate the `StronglyAdapted` replacement *separately*
  on `kmc-erdos-glw-lower` (no pin) and prepare a refactor branch. Once
  ready, attempt the pin again with the refactor pre-staged. **Medium
  risk, possibly retires the axiom in 2 rounds.**
* **Path C**: Direct upstream coordination with Mathlib /
  brownian-motion to either (i) ask brownian-motion to track Mathlib
  v4.27.0 release tag, or (ii) wait for the next brownian-motion
  release that targets a Mathlib commit closer to v4.27.0. **Lowest
  marginal cost, but bottlenecked on external timing.**

### State at end of R13

* Branch `kmc-erdos-glw-lower` HEAD: post-revert, restored to
  `kmc-erdos-glw-lower` baseline (toolchain v4.27.0, mathlib pin
  `v4.27.0`, no brownian-motion / kolmogorov_extension4 deps).
* Build: green (8009 jobs).
* Axiom count: 2 (`Y_GLW_exists`, `two_dim_KMT_coupling`).
* Bridge file deliverables from R13 Tier 4: ~1260 lines added, 25
  sub-sections, all committed and pushed to fork.

### Critical R14 finding: StronglyAdapted is just a rename

Investigation of `Mathlib/Probability/Process/Adapted.lean` in current
v4.27.0 reveals (line 57 comment):

> "The definition known as `Adapted` before 2026-01-13 is now
>  `StronglyAdapted`."

So in v4.27.0 (current):
- `Adapted` := `∀ i, Measurable[f i] (u i)` (uses `Measurable`)
- `StronglyAdapted` := `∀ i, StronglyMeasurable[f i] (u i)` (uses `StronglyMeasurable`)

In v4.27.0-rc1 (the brownian-motion target, pre-2026-01-13):
- `Adapted` := the old definition (StronglyMeasurable-based)
- `StronglyAdapted` did not yet exist

**This means the R13-blocker `StronglyAdapted` in `524.lean:662` is a
mechanical rename**, NOT the deep refactor we feared.

A precise grep of `524.lean` reveals only **2 occurrences** of the
StronglyAdapted naming:

```
524.lean:662: have hadapted : StronglyAdapted ℱ f := by
524.lean:667:   (Filtration.stronglyAdapted_natural hm j).mono
```

For R14 (when pinned to v4.27.0-rc1), both need the rename:

```diff
-   have hadapted : StronglyAdapted ℱ f := by
+   have hadapted : Adapted ℱ f := by
        ...
-   (Filtration.stronglyAdapted_natural hm j).mono
+   (Filtration.adapted_natural hm j).mono
```

(In v4.27.0-rc1, the old name `Filtration.adapted_natural` was used;
mathlib renamed it to `Filtration.stronglyAdapted_natural` on
2026-01-13 alongside the `Adapted` → `StronglyAdapted` rename.)

The `StronglyMeasurable[ℱ k]` calls inside the block (e.g. line 664
`have hwalk_sm : StronglyMeasurable[ℱ k] (walk a k) := by`) **do not
need to change** — `StronglyMeasurable` is unchanged across the
rename, since the rename only swapped the *Adapted-level* names.

### Caveat: cannot pre-stage the rename on master

The rename `StronglyAdapted → Adapted` (and likewise
`stronglyAdapted_natural → adapted_natural`) **cannot** be applied as a
preparatory commit on `kmc-erdos-glw-lower` (or `main`) under v4.27.0,
because:

* In v4.27.0, `StronglyAdapted` is the StronglyMeasurable-based
  predicate (what we want).
* In v4.27.0, `Adapted` is the (new, post-2026-01-13)
  Measurable-based predicate (different concept).

Pre-staging the rename on master would change the SEMANTICS, not just
the name — the proof would be against a stricter measurability
hypothesis (just `Measurable`, not `StronglyMeasurable`). That could
break the build.

Therefore R14 must do the rename **atomically with the pin**:

1. Branch from `kmc-erdos-glw-lower`.
2. Apply pin (toolchain + lakefile).
3. Apply the 5 mechanical fixes (Set.left_mem_Ici × 2, Powerfree,
   GCDMonoid.Finset, CauchyDetLowerBound).
4. Apply the StronglyAdapted rename (in v4.27.0-rc1 mathlib, the
   StronglyMeasurable-based predicate IS called `Adapted`, so this is
   semantically correct under the pin).
5. Build, verify, retire `Y_GLW_exists`.
6. Cascade to consumers.

### Updated R14 procedure (revised again, with new finding)

R14 effort estimate revised DOWN to **30-45 min** total:

1. Patches 1-3 (typeclass strengthening + rename): 5 min.
2. Patch 4 (CauchyDetLowerBound offDiag bullet removal): 2 min.
3. **Patch 5 (StronglyAdapted → Adapted)**: 5-10 min mechanical
   sed-style refactor. May need to also revisit any
   `StronglyMeasurable[ℱ k]` references that depended on the old
   typing.
4. Possibly **further unknown errors** beneath StronglyAdapted (we
   didn't see past it in R13).
5. If clean: retire `Y_GLW_exists` via brownian-motion API (15-20
   min).

**The R13 hypothesis ("4 errors are surgical") was effectively
correct**, just incomplete (5th error existed). The discipline rule
firing at T+15 was still right; the StronglyAdapted finding only
becomes apparent post-revert via mathlib source inspection.

R14 should attempt the pin again with a higher T+25 cap and the
explicit fix list above.
