# R20 Readiness Diagnostic

Closing-of-R19 diagnostic. R19 landed:

* T1.1 Full (R19APIScoping.md, with Claim 2 corrected mid-round).
* T2.1.a Full (gaussianReal sub-Gaussian + GLW marginal Chernoff
  tail at integer points).
* T2.1.b Full (measurable `glwHolderConstant` from explicit iSup).
* T2.2 Stub + T2.3 Stub (documented blockers).

`Y_GLW_exists` axiom retirement remains gated on a *single* analytical
bound: the local K-C constant `M_T = O(1/T³)` for the GLW kernel.

## Blocker A (priority A — round headline) — Local K-C constant for K_GLW

**State:** R19 closed both R18-flagged Mathlib gaps (sub-Gaussian
tail + measurable Hölder constant), but discovered a third gap that
neither R18 nor v2-manifest pre-flight surfaced:

> The chaining moment bound from
> `IsKolmogorovProcess.finite_set_bound_of_edist_le` carries the
> *global* K-C constant `M = 1`, which makes
> `E[(glwHolderConstant T ω)] ≤ Cp · M = Cp · 1 = Cp` — **constant in
> T** — not yielding a summable sup-tail bound when applied to a
> per-block chaining argument.

**Why it's hard:** to recover summability, R20 needs a *local* K-C
constant `M_T` decaying as `O(1/T³)` for the increment process on
`[T, T+1]`. This is the analytical bound

```
Var(Y_s - Y_t) ≤ M_T · (s - t)²,  s, t ∈ [T, T+1],
```

with `M_T = 1/(4T³) + O(1/T⁴)`. The Taylor expansion of `K_GLW(s, t)
= (1 - exp(-(s+t))) / (s+t)` around the diagonal `(T, T)` gives this
bound directly:

* Series expansion to order 2 in `(s - T)` and `(t - T)`.
* Cancellation of the constant term and first-order terms (via
  symmetry of `K_GLW`).
* Leading second-order term:
  `K_GLW(s,s) + K_GLW(t,t) - 2 K_GLW(s,t) = (s-t)² / (4T³) + ...`.

**Resolution path for R20 — Option A (recommended):**

1. Prove `K_GLW_increment_var_le_T_cube`: the bound above.
   ~80 LOC of Taylor-expansion + remainder estimation in
   `Helpers/YGLWConstruction.lean`.
2. Promote to `IsKolmogorovProcess`-shape on `[T, T+1]`:
   `glwGaussianLimit_isKolmogorovProcess_local T` with
   `(p, q, M_T) = (2, 2, M_T)`. ~30 LOC.
3. Apply `finite_set_bound_of_edist_le` with the local constant:
   chaining gives `E[glwHolderConstantENN T] ≤ Cp · M_T`. ~20 LOC.
4. Markov + step-2 of T2.2 documented chain → summable f(T, ε).
   ~30 LOC.

**Total for blocker A: ~160 LOC, 1-2 R20 waves.**

**Resolution path for R20 — Option B (fallback):** wait for upstream
Borell-TIS in either Mathlib or `brownian-motion`. Outside our
control timing-wise.

## Blocker B (priority A — assembly) — Conjunct 9 sup-tail + Borel-Cantelli

**State:** structurally identical to R18's blocker, but now with all
sub-prerequisites except blocker A in place.

**Resolution path:** sequential consumption of blocker A's output:

1. `marginal_sup_tail_le T hT ε hε`: `P(sup_{[T, T+1]} |Y u| ≥ ε)
   ≤ 2 exp(-ε² T / 4) + 4 Cp / (ε² T³)`. ~40 LOC after blocker A.
2. `summable_sup_tail`: both terms summable in T. ~10 LOC.
3. Borel-Cantelli via `MeasureTheory.measure_limsup_atTop_eq_zero`.
   ~20 LOC.
4. Quantifier interleaving over a countable rational ε-net to recover
   the conjunct-9 statement. ~20 LOC.

**Total for blocker B: ~90 LOC, 1 wave once blocker A lands.**

## Blocker C (priority B) — Phase A: Slepian comparison

Unchanged from R18. ~300 LOC / 3 waves. Independent of blocker A.

## Blocker D (priority B after C) — Phase A: Sudakov-Fernique

Unchanged from R18. ~150 LOC. Depends on blocker C.

## Blocker E (priority C) — Two-dim KMT retirement

Unchanged. ~1000+ LOC / 6+ waves.

## Summary table

| # | Blocker | Priority | Effort | Unblocks |
|---|---------|----------|--------|----------|
| A | Local K-C constant `M_T = O(1/T³)` for K_GLW | A | 160 LOC / 1-2 waves | T2.2 sup-tail |
| B | Conjunct 9 sup-tail + BC | A (after A) | 90 LOC / 1 wave | `Y_GLW_exists` retirement |
| C | Slepian comparison | B | 300 LOC / 3 waves | Phase A upper bound |
| D | Sudakov-Fernique | B (after C) | 150 LOC | Phase A upper bound |
| E | Two-dim KMT | C | 1000+ LOC / 6+ waves | A2-axiom retirement |

R20's natural focus is blockers A + B in sequence. Together they
deliver the first axiom retirement of the project (the +500 bonus
that has been gated since R13). The combined ~250 LOC is plausible
in 1-2 R20 waves.

## R19 → R20 axiom delta

```
R18 (current): sorryAx + propext + Classical.choice + Quot.sound
R19 (current): sorryAx + propext + Classical.choice + Quot.sound  ← unchanged
R20 target:    propext + Classical.choice + Quot.sound  ← clean
```

The two non-`sorry` axioms (`propext`, `Quot.sound`) are Lean's
unconditional kernel-level axioms. `Classical.choice` enters via
`exists_modification_holder'''`-style theorems and is unavoidable.

## Calibration notes

R19 actual ~223 pts vs. v2 manifest's projected 600-850 (37% of
midpoint). Two contributing factors:

1. **Cowork's pre-flight underestimated step 4 of T2.2.** The "60 LOC
   marginal sup-tail bound" estimate assumed the chaining `Cp` bound
   would carry T-dependence through `M`, but `M = 1` is global. R19
   discovered this *after* T2.1.a/b were landed, when assembling the
   sup-tail. The miss is now documented in
   `marginal_sup_tail_blocker_R19` and recovered in this diagnostic
   as Blocker A.

2. **No new Lean lemma was introduced for the K_GLW Taylor bound.**
   The analytical step (160 LOC) is large enough to be R20's
   headline, not a sub-task within R19.

R20 calibration target: 350-600 pts on a focused manifest with
blocker A as the centerpiece. T3.1 (axiom retirement) is genuinely
in play in R20 if blocker A + blocker B both land.

The structural-credit story is good: R19 landed concrete API
prerequisites (T2.1.a Full + T2.1.b Full) that are *re-usable across
the GLW project*. The work is not wasted; it just gates on one more
analytical bound to deliver the headline.

## R20 strategic ordering

1. **Phase 0 — V1**: rebuild check on `r19-finish` HEAD.
2. **Phase 1 — T1.1**: validate Blocker A's Taylor-expansion claim
   against `K_GLW`'s explicit form. ~10-15 min, low-risk pre-flight.
3. **Phase 2 — Blocker A** (the headline): land
   `K_GLW_increment_var_le_T_cube` Full, then promote to local
   `IsKolmogorovProcess`-shape, then apply chaining moment bound.
4. **Phase 3 — Blocker B**: assemble conjunct 9 from Blocker A's
   output + R19's T2.1.a/b prerequisites. Borel-Cantelli on the
   integer ladder.
5. **Phase 4 — T3.1**: `#print axioms Y_GLW_exists` should now be
   clean. **+500 project bonus.**
6. **Phase 5 — T5.x**: docs.

## Pivot rules for R20

1. **If the Taylor expansion has a higher-order remainder issue**:
   the remainder is `O((s-t)² · |s-T|/T⁴ + (s-t)² · |t-T|/T⁴)`,
   uniformly bounded by `(s-t)² / T⁴` for `s, t ∈ [T, T+1]`. If the
   bound is ugly, `M_T = 1/T² + 1/T³` is fine — both decay rates
   give summable bounds.
2. **If `IsKolmogorovProcess` doesn't accept a per-T constant cleanly**:
   restate as a local-Hölder-modulus bound directly, bypassing
   the K-C predicate.
3. **If the +500 bonus criterion (clean #print axioms)
   exposes any non-Classical/Quot/propext axiom**: investigate; the
   surface is small and we should be able to nail it.

R20 is the round where the project's first axiom retirement is
genuinely on the line. The path is mapped; one analytical bound
gates everything.
