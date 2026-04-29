# Phase 2 Final Report

**Branch:** `kmc-erdos-gaussian-smallball` (fork: `kieranmcshane/formal-conjectures`)
**HEAD:** `46ab7fb feat: Phase 2 Node 1B — Y_GLW_exists axiom`
**Session date:** 2026-04-29 (autonomous push)

## Headline numbers

| Metric | Start of Phase 2 | End of session |
|---|---|---|
| Axioms in `524.lean` | 3 | 3 |
| Helper-side axioms in chain | 0 | **1** (`Y_GLW_exists`, materially smaller — see below) |
| **Net axiom count in `524.lean` chain** | **3** | **4** |
| `sorry` count anywhere in chain | 0 | **0** |
| `admit` count anywhere in chain | 0 | **0** |

The 4-axiom count is a temporary regression by design: per the brief's pre-approval 1, `Y_GLW_exists` is shipped as a stepping-stone whose intended downstream effect is to reduce `gao_li_wellner_small_ball_upper` and `_lower` to theorems at Node 6, dropping net axioms from `4` (3 GLW/KMT + 1 stepping-stone) to `2` (KMT + stepping-stone). **Node 6 was not reached this session** — see the blocker section.

## Per-Node status

| Node | File | Status | Commit | LOC |
|---|---|---|---|---|
| 1A | `FormalConjectures/ErdosProblems/Helpers/GLWKernel.lean` | **GREEN** | `65f786a` | 219 |
| 1B (proposal v1) | `Helpers/GLWProcess.md` | landed | `e84cbc8` | 107 |
| 1B (proposal v2) | `Helpers/GLWProcess.md` | landed | `bc2c260` | +10 |
| 1B (proposal v3) | `Helpers/GLWProcess.md` | landed | `0395824` | +43 |
| 1B (axiom code) | `Helpers/GLWProcess.lean` | **GREEN** | `46ab7fb` | 106 |
| 2 | `Helpers/GLWHierApprox.lean` | **GREEN** | `bbf213a` | 115 |
| 4 | `Helpers/GLWDiscretization.lean` | **GREEN** | `2d1774e` | 127 |
| 5 (KMT) | — | **DEFERRED** (per pre-approval 4) | — | — |
| 6 | `Helpers/GLWBoxProbInstance.lean` (not created) | **BLOCKED** | — | — |
| `.gitignore` hygiene | `.gitignore` | landed | `5a63623` | +18 |
| Helper closure | `Helpers/GaussianGridSmallBall.lean` | **untouched, locked** | `611b465` | — |

All 4 Phase 2 helper Lean files (`GLWKernel`, `GLWHierApprox`, `GLWDiscretization`, `GLWProcess`) build green locally; **zero sorry, zero admit anywhere in the chain**.

## Axiom inventory

Exact axioms currently in scope on the branch:

```
FormalConjectures/ErdosProblems/Helpers/GLWProcess.lean:
  axiom Y_GLW_exists  ← NEW this session, pre-approved per brief

FormalConjectures/ErdosProblems/524.lean:
  axiom gao_li_wellner_small_ball_upper   (line 3493, unchanged)
  axiom gao_li_wellner_small_ball_lower   (line 3521, unchanged)
  axiom two_dim_KMT_coupling              (line 3574, unchanged, deferred per pre-approval 4)
```

`Y_GLW_exists` materially-smaller justification (full table in `Helpers/GLWProcess.md` and the file docstring):

| Claim | GLW axiom (upper/lower) | `Y_GLW_exists` |
|---|---|---|
| Existence of `Y` | implicit | explicit |
| Quantifier over `(Ω, μ)` | universal (false on trivial Ω) | existential (consistent) |
| Integrability | unstated | conjuncted |
| Covariance kernel | unconstrained | fixed to `K_GLW` |
| Joint Gaussianity | unstated | conjuncted |
| Continuous sample paths | unstated | conjuncted |
| Sample-path tail decay | unstated | conjuncted |
| **Small-ball cubic bound** | **claimed** | **NOT claimed** |

## Sorry inventory

**Zero.** Verified by `grep -rE '^\s*(sorry|admit)\b'` over every helper Lean file shipped this session.

## Where I stopped and why

**Hard blocker reached:** Node 6 — V1-instance construction.

The Node 6 task per pre-approval 3 is to produce:
1. `gaussianBoxProbV1_of_GLW : (Y : ℝ → Ω → ℝ) → (bundle of Y-properties) → GaussianBoxProbV1 m`
2. `gao_li_wellner_small_ball_upper_thm` and `_lower_thm` with the hypothesis bundle, proved via the V1 instance + `gaussian_grid_smallball_upper_final` / `_lower_final`.
3. `524.lean` axiom-to-theorem replacement at six call sites.

The blocker is in step (1). The V1 structure has the field

```
cov_eq_hierCauchy : cov = hierCauchyG m
```

which forces `cov := hierCauchyG m` literally. The actual covariance of the GLW process sampled at `hierTimes m` is `K_GLW_matrix m`, which differs from `hierCauchyG m` entrywise by the Node 2 bound

```
|K_GLW_matrix m i j - hierCauchyG m i j| ≤ exp(-(g_i + g_j)) / (g_i + g_j).
```

The V1 instance's `anderson_upper` field requires

```
boxProb ε ≤ (2ε)^(m²) · (2π)^(-m²/2) · 1/√(cov.det).
```

If `cov := hierCauchyG`, the inequality must use `1/√(hierCauchyG.det)`. Anderson's inequality applied to the actual Gaussian distribution of `Y_GLW` at `hierTimes` gives the bound in terms of `1/√(K_GLW_matrix.det)`. To bridge, one needs

```
1/√(K_GLW_matrix.det) ≤ 1/√(hierCauchyG.det) · (1 + o(1)),
```

equivalently `K_GLW_matrix.det ≥ hierCauchyG.det · (1 - o(1))`. **This is matrix-perturbation work** (entrywise closeness → determinant closeness via Hadamard-Fischer / Weyl-style spectral bounds), and it is not derivable in the time-budget of this session.

The same structural issue propagates through every other V1 field (`anderson_lower`, `chain_rule_lower`, `relevant_block_bound`, `fine_blocks_combined_lower`, **`relevant_blocks_combined_lower`** — the new field added in `611b465`). Each requires either (a) re-proving the inequality at `hierCauchyG` with a `K_GLW_matrix → hierCauchyG` bridge, or (b) providing a deeper construction that admits the helper's contract.

**Why I did not attempt a partial Node 6 with sorries:** the brief is unambiguous — *"Zero new sorry or admit. Anywhere. Ever."* A partial construction with `sorry` in any field would violate this. I judged that an honest stop here was preferable to either (a) shipping sorries against the rules or (b) shipping a mathematically dishonest "vacuous-`ε₀`" Node 6 (option (c) of the universal-Y resolution, which the brief explicitly disapproves of).

## Consumer call sites that will need update at Node 6

Six call sites in `524.lean` referencing the GLW axioms; left unchanged this session:

```
3761  in polynomial_sup_small_ball_upper:        gao_li_wellner_small_ball_upper glw Yplus hYp_meas
3914  in polynomial_sup_small_ball_upper_uniform: gao_li_wellner_small_ball_upper glw Yplus hYp_meas
4061  in polynomial_sup_small_ball_lower:        gao_li_wellner_small_ball_lower glw Yplus hYp_meas
4063  in polynomial_sup_small_ball_lower:        gao_li_wellner_small_ball_lower glw Yminus hYm_meas
4435  in polynomial_sup_small_ball_lower_uniform: gao_li_wellner_small_ball_lower glw Yplus hYp_meas
4437  in polynomial_sup_small_ball_lower_uniform: gao_li_wellner_small_ball_lower glw Yminus hYm_meas
```

When Node 6 lands, each of these will need to be updated to provide the hypothesis bundle on `Yplus` / `Yminus`. There is a **secondary architecture question**: the bundle requires `Y` to satisfy the K_GLW covariance + joint Gaussianity, but the KMT axiom gives only measurability and continuity for `Yplus` / `Yminus`. The covariance / Gaussianity properties for those processes come from their **construction** (Itô integrals against the KMT-coupled Brownian motions) — which the existing `two_dim_KMT_coupling` axiom does not expose. Two options:

- **A.** Strengthen `two_dim_KMT_coupling` to assert covariance + Gaussianity for `Yplus` / `Yminus` directly. Net-axiom-friendly but inflates KMT.
- **B.** Have the consumers locally invoke `Y_GLW_exists` to produce a process `Y_GLW`, prove law-equality `Yplus =fdd Y_GLW` from the KMT construction, and transfer the bound. Cleaner but requires non-trivial law-equality plumbing.

Flagging for the user. Not an unilateral pick for an autonomous push.

## What would unblock Node 6 in a follow-up session

1. **Matrix determinant perturbation lemma** in `FormalConjecturesForMathlib/`:
   `‖A - B‖_∞ ≤ δ ∧ A.PosDef ∧ B.PosDef → |A.det - B.det| ≤ δ · m! · (max ‖A‖, ‖B‖)^(m-1)` (Hadamard-Fischer route).
   Once this is in place, the `K_GLW_matrix.det ≈ hierCauchyG.det` bridge unlocks every V1 field.

2. **Law-equality lemma** for centered Gaussian processes with the same finite-dim covariance:
   `(∀ u v, ∫ Y u Y v = ∫ Z u Z v) ∧ jointGaussian Y ∧ jointGaussian Z → Y =fdd Z`. This unlocks the `Yplus → Y_GLW` transfer for the call-site updates.

3. **(Optional)** Strengthening of `two_dim_KMT_coupling` to expose `Yplus.cov = K_GLW` directly (architecture option A above).

With (1) and (2), Node 6 becomes a long-but-tractable bookkeeping exercise: ~600–900 LOC across `Helpers/GLWBoxProbInstance.lean` + the consumer updates in `524.lean`. With (3), it shrinks further.

## What you can do now (suggestions for review)

- **Validate `Y_GLW_exists`** content. Specifically: check the `IsGaussian` conjunct on pushforward measures expresses joint Gaussianity in the way Mathlib's Anderson-inequality use will need.
- **Decide on architecture option A vs B** for the call-site updates (see above). This is your call, not mine.
- **Confirm or adjust the matrix-perturbation lemma scope** for Mathlib-side work.

## Commit log this session (chronological)

```
46ab7fb feat: Phase 2 Node 1B — Y_GLW_exists axiom (stepping-stone, materially smaller than GLW pair)
2d1774e feat: Phase 2 Node 4 — discrete vs continuous box probability comparison
0395824 docs: Phase 2 Node 1B — proposal v3 (existential Ω, explicit integrability, tail-decay rationale)
bbf213a feat: Phase 2 Node 2 — hierarchical Cauchy approximation of K_GLW matrix
bc2c260 docs: Phase 2 Node 1B — proposal v2 with joint-Gaussianity conjunct
e84cbc8 docs: Phase 2 Node 1B — propose stepping-stone axiom Y_GLW_exists
65f786a fix: Phase 2 Node 1A — Mathlib API drift round 3
d45a547 fix: Phase 2 Node 1A — div_sub_div lemma name + EventuallyEq form
325b0dd fix: Phase 2 Node 1A — correct slope import path
2fcd836 feat: Phase 2 Node 1A — GLW kernel definition + analytic properties
5a63623 chore: .gitignore — filter scratch, LaTeX artifacts, worktree symlinks
5e04591 wip: GaussianGridSmallBall — push to cloud build (predecessor session)
1b2db38 wip: Node 3 — solve h_rel_prod + schur scalar; close build errors  (predecessor session)
```

## Final state — outcome ranking

Per the brief's outcome ladder:

- **Best** (1B + 2 + 4 + 6 all green, GLW theorems shipped): **NOT REACHED.** Node 6 blocked.
- **Good** (1B + 4 green, Node 6 partial): **PARTIALLY MET.** 1B + 2 + 4 green, but no Node 6 partial — the no-sorry rule precluded a stub.
- **Acceptable** (1B green, Node 4 stuck): **EXCEEDED.** 1B + 2 + 4 all green, Node 4 not stuck.

**Net assessment:** above "Acceptable", below "Good" (since "Good" required some Node 6 partial which I could not honestly produce). All committed work is green, tested, axiom-clean except for the single pre-approved `Y_GLW_exists` stepping-stone.
