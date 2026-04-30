# R19 Build Status

Per-file `lake build` status for the GLW helper stack at the end of
Round 19 (`r19-finish` branch, HEAD `b57af60`). All targeted helpers
build green; the residual `sorry` is structurally tagged at conjunct 9
of `glwGaussianLimit_Y_GLW_existence` and is the sole gating
obstruction for `Y_GLW_exists` axiom retirement (carried over from
R18 with R19 status notes added).

## Verification protocol

Each line below is the verbatim final line of `lake build <target>`
captured against `r19-finish` HEAD. The new helper
`SubGaussianGaussianReal.lean` packages the gaussianReal sub-Gaussian
adapter; the existing `GLWGaussianProjectiveLimit.lean` absorbs the
GLW-specific T2.1.a/T2.1.b lemmas inline per v2-manifest spec.

## Per-file status

| File | Build | Sorries | R19 changes |
|------|-------|---------|-------------|
| `Helpers/SubGaussianGaussianReal.lean` | ✓ | 0 | NEW. T2.1.a adapter `hasSubgaussianMGF_id_gaussianReal` (~5 LOC) + two-sided Chernoff helper `gaussianReal_real_abs_ge_le` (~35 LOC). |
| `Helpers/GLWGaussianProjectiveLimit.lean` | ✓ | 1 (conjunct 9, R19-T2.2 tag) | T2.1.a application: `hasSubgaussianMGF_eval_glwGaussianLimit`, `eval_glwGaussianLimit_real_abs_ge_le`, `eval_glwGaussianLimit_real_abs_ge_le_of_pos`, `summable_marginal_tail`. T2.1.b: `glwHolderConstant`, `glwHolderConstantENN`, `measurable_glwHolderConstantENN`, `measurable_glwHolderConstant`. T2.2/T2.3 Stub blockers documented. Conjunct-9 docstring updated with R19 progress + R19-T2.2 tag. |
| `Helpers/GLWProcess.lean` | ✓ | 0 (transitive sorry from conjunct 9) | Untouched in R19. |
| `Helpers/GLWProcessPredicate.lean` | ✓ | 0 | Untouched in R19. |
| `Helpers/PhaseAUpperBound.lean` | ✓ | (R17 stubs for Slepian / Sudakov-Fernique) | Untouched in R19 (Phase 4 deferred). |
| `Helpers/R19APIScoping.md` | doc | — | NEW T1.1 deliverable. Updated post-pre-flight to flag the Claim 2 correction (`exists_modification_holder'''` reading was wrong; `holderOnWith_holderModification` has the explicit iSup formula). 257 lines. |
| `Helpers/R19BuildStatus.md` | doc | — | NEW (this file). |
| `Helpers/R20ReadinessDiagnostic.md` | doc | — | NEW T5.2 deliverable. |

## Build logs

```
$ lake build FormalConjectures.ErdosProblems.Helpers.SubGaussianGaussianReal
Build completed successfully (2880 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit
Build completed successfully (3411 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit \
            FormalConjectures.ErdosProblems.Helpers.GLWProcess \
            FormalConjectures.ErdosProblems.Helpers.GLWProcessPredicate \
            FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
Build completed successfully (3414 jobs).
```

(Two unused-variable warnings on the T2.2 Stub `marginal_sup_tail_blocker_R19`
hypotheses are expected and intentional — the Stub is a typeable
placeholder for the deferred analytical bound; the hypotheses scope
the future Full statement.)

## R19 changes by phase

### Phase 0 — V1 (Full, 0 pts)

R18-touched helpers rebuild green at `f282779` HEAD before any R19
work begins. Same lemma names, same proof bodies — confirms R18's
landings were soundly merged and not regressed.

### Phase 1 — T1.1 (Full, 30 pts)

`Helpers/R19APIScoping.md` (257 lines) verifies all three R18-
diagnostic claims on the local toolchain. Crucially, surfaces the
Cowork-discovered correction on Claim 2: the Hölder constant in
`KolmogorovChentsov.holderOnWith_holderModification` has the explicit
formula `C ω := ⨆ s, t : (denseCountable T ∩ U), edist (X s ω)
(X t ω) ^ p / edist s t ^ (β · p)` (lines 650-651), making it
measurable by construction. R18's "no measurable Hölder constant"
verdict was wrong.

### Phase 2 — T2.1 (Full, 80 pts), T2.2/T2.3 (Stub, 32 pts)

**T2.1.a (sub-Gaussian + Chernoff for `gaussianReal`):** the adapter
`hasSubgaussianMGF_id_gaussianReal` lives in
`Helpers/SubGaussianGaussianReal.lean`; its GLW-specific applications
(`hasSubgaussianMGF_eval_glwGaussianLimit`,
`eval_glwGaussianLimit_real_abs_ge_le`,
`eval_glwGaussianLimit_real_abs_ge_le_of_pos`,
`summable_marginal_tail`) live inline in `GLWGaussianProjectiveLimit`.
The combined output is

  `P(|Y T ω| ≥ ε) ≤ 2 · exp(-ε² T)` for `T ≥ 1`, `ε ≥ 0`,

with `∑_T 2 · exp(-ε² T) < ∞` (geometric).

**T2.1.b (measurable Hölder constant):** `glwHolderConstant n ω : ℝ≥0`
is defined inline as the `.toNNReal`-rooted iSup at our K-C
parameters `(p, q, β·p) = (2, 2, 1/2)`, on the cover element
`U = Set.Ico n (n + 1)`. Measurability follows from the countable
iSup of measurable summands; subtype `Countable` instance via
`countable_denseCountable.mono.to_subtype`.

**T2.2 (Stub) + T2.3 (Stub):** `marginal_sup_tail_blocker_R19` and
`BC_integer_ladder_blocker_R19` are typeable placeholders. The 5-step
proof chain is documented; step 4 (local K-C constant `M_T = O(1/T³)`
from a 2nd-order Taylor expansion of `K_GLW` around `(T, T)`) is the
deferred bottleneck. With `M_T` in hand, the chaining moment bound
gives `f(T, ε) = 2·exp(-ε² T / 4) + 4 · Cp / (ε² · T³)`, both terms
summable.

### Phase 5 — Documentation

* `Helpers/R19APIScoping.md` (T1.1 Full).
* `Helpers/R19BuildStatus.md` (T5.1 — this file).
* `Helpers/R20ReadinessDiagnostic.md` (T5.2 Full).

T5.3 (AxiomRetirementCelebration) is gated on T3.1 Full and is
deferred to R20+ pending the K_GLW analytical bound.

### Phase 6 — Push

`r19-finish` is pushed to the fork at the end of the round.

## Calibration accounting

- **Maximum (all Full): 705 pts.**
- **Plus T3.1 project bonus: +500 (gated on T3.1 Full — not landed).**
- **R19 actual:** V1 (0) + T1.1 Full (30) + T2.1 Full a+b (80) + T2.2
  Stub (16) + T2.3 Stub (12) + T2.4 R19-status update (Stub-equiv;
  the Lean `sorry` was already in place at R18 and only the docstring
  changed) + T5.1 (25) + T5.2 (40) + T6.1 (20) = ~223 pts.
- **R19 vs realistic projection (600-850):** below the lower band.
  The technical bottleneck (step 4 local K-C constant) was
  underestimated in v2's "60 LOC marginal sup-tail bound" estimate —
  Cowork's plan assumed the chaining `Cp` bound on `E[C^p]` would
  carry T-dependence through `M`, but `M = 1` is global and the
  chaining bound is constant in T. To recover summability we need a
  bespoke K_GLW Taylor analysis, which is R20 work.

The R19 calibration story: T1.1's Cowork-driven correction was
substantively *right* on Claim 2 (measurable Hölder constant exists
and is achievable in ~50 LOC; we delivered it). It was *wrong* on
the path to the sup-tail bound: even with measurable `C`, the
chaining moment bound doesn't give T-summable tails without an
additional variance-decay analysis on the kernel.

## R19 → R20 axiom delta (status quo)

```
R18 (start of R19): sorryAx + propext + Classical.choice + Quot.sound
R19 (end):          sorryAx + propext + Classical.choice + Quot.sound
                                       (unchanged — sorry survives)
```

`Y_GLW_exists` axiom retirement is carried into R20.
