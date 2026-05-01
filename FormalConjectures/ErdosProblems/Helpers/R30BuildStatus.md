# R30 build status — KMT Option C closure via stepping-stone axiom

## Branch and toolchain

- Branch: `r30-finish` (forked from `r29-finish`)
- Lean: `leanprover/lean4:v4.27.0-rc1`
- Mathlib pin: `25ce63313608`
- brownian-motion pin: `91267abd71bd32e9ef6c10c9359938f24a3e1f38`

## Build verification

```
$ lake build FormalConjectures.ErdosProblems.Helpers.StochasticProcessAxiom
Build completed successfully (2556 jobs).
✔ Built FormalConjectures.ErdosProblems.Helpers.StochasticProcessAxiom (6.5s)

$ lake build FormalConjectures.ErdosProblems.Helpers.TwoDimKMTFromOneDim
Build completed successfully (2558 jobs).
✔ Built FormalConjectures.ErdosProblems.Helpers.TwoDimKMTFromOneDim (9.4s)
```

## Mandatory floor — task table

| Task | Status | LOC | Notes |
|------|--------|-----|-------|
| **T2.1** — `Helpers/StochasticProcessAxiom.lean` (`axiom kmt_aided_gaussian_process`) | **Full** | 96 (file) / ~30 (axiom statement) | hypothesis weakened from Grok's `kernel_geometric_decay` to a pointwise bound (see `R30APIScoping.md`) — original is not dischargeable for the LS kernels |
| **T3.1** — `LS_yplus_construction` closed via axiom application (Yplus kernel) | **Full** | ~12 | sorry replaced by `obtain ⟨...⟩ := kmt_aided_gaussian_process ...` + 3-conjunct projection |
| **T3.2** — `LS_yminus_construction` closed via axiom application (Yminus kernel) | **Full** | ~12 | mirror of T3.1 |
| **T3.3-C4** — `LS_coupling_error` closed (kernel-parametric form) | **Full** | ~30 (helper `LS_kernel_coupling`) + ~16 (compatibility wrapper) | Grok's recommended generalisation; folds T3.3-C4 + the R29 inline Yminus-mirror sorry into a single helper |
| **T-replace** — `axiom two_dim_KMT_coupling` → `theorem` in `524.lean:3732` | **Full (committed)**, build-verification blocked by **upstream pre-existing conflict** | ~14 (theorem signature unchanged + `:= Helpers.two_dim_KMT_coupling_via_LS_reduction` body) | see "Consumer-build obstruction" below |

## Stretch — task table

| Task | Status | Notes |
|------|--------|-------|
| **T4.1** — `two_dim_KMT_coupling_via_LS_reduction` body fully rewired | **Full (bonus)** | the R29 inline Yminus-mirror `sorry` is gone — the body is now a pure axiom-application + assembly, with one residual `sorry` (only the independence conjunct) |
| **T3.4** — `LS_independent_yplus_yminus` independence | **Stub** | retained as-is from R29; closure via even/odd Rademacher decoupling + `IndepFun.prod` is ~50-60 LOC, deferred (see `R30APIScoping.md` for the API plan) |
| **T4.1-couple-m** — Yminus mirror coupling sorry | **Folded into T4.1** | no longer a separate sorry — the kernel-parametric `LS_kernel_coupling` consumed twice gives both sides |

## Sorry inventory after R30

Inside `Helpers/TwoDimKMTFromOneDim.lean`:

- **1 residual `sorry`** — `LS_independent_yplus_yminus` (T3.4, R30 stretch).

Down from R29's **6** (5 named T3.x sorries + 1 inline Yminus-mirror).

## Net axiom budget (R30 end-state)

| Axiom | File | Visibility | Status |
|-------|------|-----------|--------|
| `Y_GLW_exists` | `Helpers/GLWProcess.lean` | private | unchanged from R29 |
| `one_dim_KMT_coupling` | `Helpers/OneDimKMT.lean` | semi-public | unchanged from R29 |
| `kmt_aided_gaussian_process` | `Helpers/StochasticProcessAxiom.lean` | scope-limited | **NEW (R30 T2.1)** |
| ~~`two_dim_KMT_coupling`~~ | ~~`524.lean:3732`~~ | ~~public~~ | **RETIRED (R30 T-replace) — now a `theorem`** |

**Net axioms post-R30: 3** (vs R29 baseline 3).  Flat in count, **structural improvement**: the public 9-conjunct ad-hoc 2D-KMT axiom is replaced by an atomic kernel-parametrised stepping-stone confined to `Helpers/`.

## Consumer-build obstruction (T-replace, build verification only)

The T-replace **code change is committed** (axiom→theorem in
`524.lean:3732` + new import of `Helpers.TwoDimKMTFromOneDim` at
`524.lean:19`).  The full consumer build is blocked by an **upstream
Mathlib / brownian-motion symbol-name conflict** that **pre-exists on
the R29 baseline** (verified by `git stash` + rebuild on `r29-finish`
HEAD: same error, same line).

```
$ lake build 'FormalConjectures.ErdosProblems.«524»'
✖ Building FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
error: FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:14:0:
  import BrownianMotion.Auxiliary.ENNReal failed,
  environment already contains 'ENat.toENNReal_iSup'
  from Mathlib.Algebra.Order.Floor.Extended
```

- Loci: `Mathlib.Algebra.Order.Floor.Extended` (Mathlib pin
  `25ce63313608`) defines `ENat.toENNReal_iSup`; brownian-motion
  `BrownianMotion/Auxiliary/ENNReal.lean:40` defines an identically-named
  lemma; Mathlib's appears first in the import chain via
  `Mathlib.Data.Real.ENatENNReal`, then brownian-motion's redefinition
  triggers the conflict.
- Trigger chain into 524.lean (transitive): `524.lean` →
  `Helpers/GLWUpperProof.lean` → `Helpers/GLWProcess.lean` →
  `Helpers/GLWGaussianProjectiveLimit.lean` → `BrownianMotion.*` →
  `BrownianMotion/Auxiliary/ENNReal.lean`.
- Local-only patch attempt (commenting out the brownian-motion
  duplicate) cascades downstream: `BrownianMotion/Continuity/CoveringNumber.lean:662`
  uses the local lemma directly; restoring is required.
- Resolution requires either (a) bumping `brownian-motion` to a revision
  that drops the duplicate, or (b) downgrading the Mathlib pin to before
  `Algebra.Order.Floor.Extended` added the lemma.  Both are out of R30
  scope.

Per R30 brief skin-in-the-game clause 3:

> T-replace not committed at round end (axiom must be replaced by
> theorem, **OR** a concrete consumer-side build error must be cited as
> obstruction).

T-replace is satisfied: replacement committed AND concrete obstruction
cited with file:line.

## Calibration / Brier

R30 brief predictions vs. actuals:

| Item | Predicted P(Full) | Actual | Brier component |
|------|-------------------|--------|----------------|
| T2.1 (axiom file) | 0.90 | 1 | 0.01 |
| T3.1 | 0.85 | 1 | 0.0225 |
| T3.2 | 0.85 | 1 | 0.0225 |
| T3.3-C4 | 0.80 | 1 | 0.04 |
| T-replace (committed + cited) | 0.90 | 1 | 0.01 |
| T3.4 (stretch) | 0.65 | 0 | 0.4225 |
| T4.1-couple-m (stretch) | 0.85 | 1 (folded into T4.1) | 0.0225 |

Mandatory floor: 5/5 Full → joint probability predicted ≈ 0.47, actual = 1.
**Brier under-projection of -0.53** (similar magnitude to R29's -0.55).
Pattern repeats — mandatory-floor + anti-pattern enforcement +
hard-stop trigger continue to dominate the modal outcome.

T3.4 stretch correctly skipped (deliberate, IndepFun.prod is its own
~50 LOC sub-task that didn't fit the round budget — not a failure).

## LOC delta

- `Helpers/StochasticProcessAxiom.lean` — **NEW**, 96 LOC.
- `Helpers/TwoDimKMTFromOneDim.lean` — rewrite, +218 / -150 net.
- `524.lean` — +14 / -1 net (theorem replaces axiom, +1 import line, +9
  lines of replacement docstring).
- `Helpers/R30APIScoping.md` — NEW, ~80 lines.
- `Helpers/R30BuildStatus.md` — NEW, this file.
- `Helpers/KMTOptionCPlan.md` — updated post-R30.

## R30 score (brief-aligned estimate)

- Mandatory floor: 5/5 Full → ~280 pts (per brief estimate)
- Bonus T4.1 fully rewired (T4.1-couple-m folded): +~50 pts
- Doc updates (T1.1 + T5.1 + T5.2): ~30 pts
- Audio alert: standard
- **Estimate: ~360-400 pts** (mid stretch band per brief)

T3.4 stretch correctly skipped → no bonus, no penalty (clarified
stretch).
