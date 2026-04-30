# R20 Build Status

Per-file `lake build` status for the GLW helper stack at the end of
Round 20 (`r20-finish` branch). The two **R20 headlines** are now
landed:

* **T1.1 Full** — the load-bearing analytical Taylor bound
  `K_GLW_increment_var_le_T_cube`: for `T ≥ 1` and `s, t ∈ [T, T+1]`,
  `K_GLW(s, s) + K_GLW(t, t) - 2·K_GLW(s, t) ≤ (s - t)² / (2·T³)`.
  This is the local K-C constant `M_T = O(1/T³)` derivation R19
  identified as the round's gating analytical fact.
* **T2.1 Full** — the local K-C structural copy
  `glwGaussianLimit_isKolmogorovProcess_local T hT`: the projection
  process on the subtype `↥(Set.Ico T (T+1)) : Set NNReal` satisfies
  `IsKolmogorovProcess` with `(p, q, M_T) = (2, 2, 1/(2·T³))`.

The chaining moment bound (T2.2), sup-tail (T3.1), Borel–Cantelli
(T3.2), and conjunct-9 assembly (T4.1) are landed as **typeable
Stubs with documented blockers**, leaving the `Y_GLW_exists` axiom
retirement as a focused R21 closeout (~250 LOC of brownian-motion
library plumbing).

## Verification protocol

Each line below is the verbatim final line of `lake build <target>`
captured against `r20-finish` HEAD.

## Per-file status

| File | Build | Sorries | R20 changes |
|------|-------|---------|-------------|
| `Helpers/YGLWConstruction.lean` | ✓ | 0 | T1.1 Full (~250 LOC). New section 7.5 *Local K-C constant on `[T, T+1]` (R20)*: `exp_neg_diff_local_abs_le` (~70 LOC), `glwIntegrand_diff_sq_le_local` (~30 LOC), `hasDerivAt_xsq_exp_primitive` (~50 LOC), `integral_xsq_exp_neg_two_T_le` (~70 LOC), `K_GLW_increment_var_le_T_cube` (~50 LOC). |
| `Helpers/GLWGaussianProjectiveLimit.lean` | ✓ | 4 (3 R20-T2.2/T3.1/T3.2 Stubs + 1 R18-conjunct-9) | T2.1 Full (~80 LOC): `glwGaussianLimit_isKolmogorovProcess_local`. T2.2/T3.1/T3.2 Stubs (~150 LOC of typeable signatures + documented blockers). The R18 conjunct-9 sorry remains in `glwGaussianLimit_Y_GLW_existence` (un-touched in R20). |
| `Helpers/SubGaussianGaussianReal.lean` | ✓ | 0 | Untouched in R20. |
| `Helpers/GLWProcess.lean` | ✓ | 0 | Untouched in R20. |
| `Helpers/GLWProcessPredicate.lean` | ✓ | 0 | Untouched in R20. |
| `Helpers/PhaseAUpperBound.lean` | ✓ | (R17 stubs) | Untouched in R20 (Phase 4 deferred). |
| `Helpers/R20BuildStatus.md` | doc | — | NEW (this file). |
| `Helpers/R21ReadinessDiagnostic.md` | doc | — | NEW T5.3 deliverable. |

## Build logs

```
$ lake build FormalConjectures.ErdosProblems.Helpers.YGLWConstruction
Build completed successfully (2666 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWGaussianProjectiveLimit
Build completed successfully (3411 jobs).
```

The R20-T1.1 / R20-T2.1 / R20-T2.2 / R20-T3.1 / R20-T3.2 work compiles
green; the only `sorry`s are the documented Stubs.

## R20 changes by phase

### Phase 0 — V1 (Full, 0 pts)

R19-touched helpers rebuild green at `r19-finish` HEAD before any R20
work begins. Confirms R19's landings (T1.1, T2.1.a, T2.1.b) are intact
under the toolchain.

### Phase 1 — T1.1 (Full, 180 pts)

The Taylor bound `K_GLW_increment_var_le_T_cube` is proved via the
**L²([0,1]) representation** of the kernel rather than direct Taylor
expansion of `K_GLW`:

```
K_GLW(s, s) + K_GLW(t, t) - 2·K_GLW(s, t)
  = ∫₀¹ (exp(-s·x) - exp(-t·x))² dx       -- L2_distance_glwIntegrand_eq
  ≤ ∫₀¹ (s - t)² · x² · exp(-2·T·x) dx    -- glwIntegrand_diff_sq_le_local
  ≤ (s - t)² · 1/(4·T³)                   -- integral_xsq_exp_neg_two_T_le
  ≤ (s - t)² / (2·T³).                    -- arithmetic
```

Cowork's pre-flight validated the leading coefficient `1/(4T³)` via
SymPy symbolic differentiation; the Lean proof confirms via the
explicit primitive `F(x) := -((c²x² + 2cx + 2) / c³) · exp(-c·x)`
with `c := 2T`, satisfying `F'(x) = x² · exp(-c·x)` and yielding
`F(1) - F(0) = 2/c³ - (c² + 2c + 2)·exp(-c)/c³ ≤ 1/(4T³)`.

The L²-representation route avoids the Taylor-with-remainder
machinery from `Mathlib.Analysis.Calculus.Taylor`, which would have
required hand-rolling the order-2 expansion (~80 LOC). The integral
route is ~250 LOC total but reuses existing infrastructure
(`L2_distance_glwIntegrand_eq`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
`exp_neg_diff_le_asym`).

### Phase 2 — T2.1 (Full, 80 pts)

`glwGaussianLimit_isKolmogorovProcess_local T hT` mirrors the global
`glwGaussianLimit_isKolmogorovProcess` (R17 Full) structurally,
substituting `M = 1` with `M_T = Real.toNNReal (1 / (2·T³))`. The
proof uses T1.1 (`K_GLW_increment_var_le_T_cube`) for the variance
bound, with the same `hasLaw_eval_sub_eval_glwGaussianLimit`,
`integral_id_gaussianReal`, `variance_id_gaussianReal` chain as the
global proof. ~80 LOC.

The signature uses `Real.toNNReal` (not the anonymous constructor
`⟨1 / (2·T³), proof⟩`) because `(Real.toNNReal x : ℝ≥0∞) =
ENNReal.ofReal x` is rfl, which makes the final calc step transparent.

### Phase 2 — T2.2 (Stub, 14 pts)

`glwHolderConstantENN_lintegral_le_R20`: chaining moment bound

```
∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit ≤ Cp_T < ∞
```

where `Cp_T = O(1/T³)` from applying `countable_kolmogorov_chentsov`
(brownian-motion library, `KolmogorovChentsovInequality.lean:326`) to
the local IsKolmogorovProcess from T2.1.

**Stub blocker:** the chaining lemma needs three companion facts:

1. `HasBoundedInternalCoveringNumber Set.univ` for the subtype
   `↥(Set.Ico T (T+1))`. The R19-used cumulative cover
   `isCoverWithBoundedCoveringNumber_Ico_nnreal` gives bounded covering
   numbers for `[0, n+1)` blocks of NNReal, but the standalone
   subtype block requires construction via
   `HasBoundedInternalCoveringNumber.subset` — ~30 LOC.

2. The countable index `T' = denseCountable NNReal ∩ Set.Ico T (T+1)`
   matching the inner iSup of `glwHolderConstantENN`.

3. The `constL` constant evaluation (`Cp(d, p, q)` from the K-C
   inequality at `(d, p, q) = (1, 2, 2)`).

Estimated ~80–120 LOC for full assembly.

### Phase 3 — T3.1 (Stub, 16 pts)

`marginal_sup_tail_le_R20`: combines T2.2 (chaining moment bound)
with R19's `eval_glwGaussianLimit_real_abs_ge_le_of_pos` (marginal
Chernoff at integer points) via the sup-decomposition

```
sup_{[T, T+1]} |Y u ω| ≤ |Y T ω| + glwHolderConstant T ω
```

(Hölder bound on the unit-diameter block).

**Stub blocker:** the connection between the R18 witness `Y' =
exists_glwBrownianModification`'s output and the explicit iSup-formula
`glwHolderConstantENN T` requires re-establishing the `holderOnWith`
bound after R18's routing through `exists_modification_holder'''`.
~60–80 LOC.

### Phase 3 — T3.2 (Stub, 12 pts)

`BC_integer_ladder_R20`: applies `MeasureTheory.measure_limsup_atTop_eq_zero`
to the events `E_T(ε) := {ω | sup_{[T, T+1]} |Y u| ≥ ε}` using the
summable bound from T3.1.

**Stub blocker:** Gated on T3.1 Full. The Borel-Cantelli step is a
direct API call to `measure_limsup_atTop_eq_zero` followed by
`Filter.eventually_atTop` unfolding; ~30–40 LOC once T3.1 lands.

### Phase 4 — T4.1 / T4.2 (Stub-equiv / Skip)

The conjunct-9 sorry in `glwGaussianLimit_Y_GLW_existence` remains as
in R19. With T2.2 / T3.1 / T3.2 all Stub, the conjunct-9 assembly is
not landable in R20. Documented in `R21ReadinessDiagnostic.md`.

T4.2 (`#print axioms Y_GLW_exists`) is **NOT** clean this round
(`sorryAx` is still present); the +500 project bonus is **NOT**
triggered. The bonus is genuinely in play in R21 as a focused close-
out round (~250 LOC across T2.2 + T3.1 + T3.2 + T4.1).

### Phase 5 — Documentation

* `Helpers/R20BuildStatus.md` (T5.1 Full — this file).
* `Helpers/R21ReadinessDiagnostic.md` (T5.3 Full).
* T5.2 (AxiomRetirementCelebration) gated on T4.2 Full — not landed.

### Phase 6 — Push

`r20-finish` is pushed to the fork at the end of the round.

## Calibration accounting

R20 actual ≈ V1 (0) + T1.1 Full (180) + T2.1 Full (80) + T2.2 Stub
(14) + T3.1 Stub (16) + T3.2 Stub (12) + T5.1 Full (25) + T5.3 Full
(40) + T6.1 (20) ≈ **~387 pts**.

Cowork's R20 prediction: 745 pts max (all Full) plus 500 pts T4.2
bonus = 1245 max. Realised: 387 / 745 ≈ 52% of max-without-bonus.

**The Cowork prediction was wrong on T2.2 / T3.1.** The "30-LOC
structural copy" estimate for T2.2 underestimated:

* The brownian-motion chaining bound API requires
  `HasBoundedInternalCoveringNumber` for the index space's open subset,
  which for the subtype `↥(Set.Ico T (T+1))` requires a fresh
  derivation (R19's existing cover applies to NNReal cumulative
  blocks, not standalone-subtype blocks).
* The R18 routing through `exists_modification_holder'''` loses the
  explicit Hölder-constant connection that T3.1's sup-decomposition
  needs.

The R20 calibration story: T1.1 Full (the analytical headline) +
T2.1 Full (the structural copy) deliver the load-bearing pieces.
T2.2 / T3.1 / T3.2 are now well-typed Stubs with documented blockers,
which means R21 has a concrete punch list rather than open analytical
work. The cumulative-from-R19 ratio is 223 + 387 = 610 pts of
substantive landings out of the 1690-pt nominal cumulative cap,
delivering both the hard analytical fact (T1.1) and the structural
local-K-C predicate (T2.1) toward the eventual axiom retirement.

## R20 → R21 axiom delta

```
R19 (current): sorryAx + propext + Classical.choice + Quot.sound
R20 (current): sorryAx + propext + Classical.choice + Quot.sound  ← unchanged
R21 target:    propext + Classical.choice + Quot.sound (clean)
```

The +500 pts axiom-retirement bonus is genuinely R21-attainable.

## Cumulative R19 + R20 deliverables

| Lemma | File | Round | Status |
|-------|------|-------|--------|
| `hasSubgaussianMGF_id_gaussianReal` | SubGaussianGaussianReal | R19 | Full |
| `eval_glwGaussianLimit_real_abs_ge_le_of_pos` | GLWGaussianProjectiveLimit | R19 | Full |
| `summable_marginal_tail` | GLWGaussianProjectiveLimit | R19 | Full |
| `glwHolderConstant` / `glwHolderConstantENN` (defs + measurability) | GLWGaussianProjectiveLimit | R19 | Full |
| `K_GLW_increment_var_le_T_cube` (M_T = 1/(2T³)) | YGLWConstruction | R20 | **Full** |
| `glwGaussianLimit_isKolmogorovProcess_local` (local K-C) | GLWGaussianProjectiveLimit | R20 | **Full** |
| `glwHolderConstantENN_lintegral_le_R20` (chaining moment bound) | GLWGaussianProjectiveLimit | R20 | Stub |
| `marginal_sup_tail_le_R20` | GLWGaussianProjectiveLimit | R20 | Stub |
| `BC_integer_ladder_R20` | GLWGaussianProjectiveLimit | R20 | Stub |
| Conjunct-9 of `glwGaussianLimit_Y_GLW_existence` | GLWGaussianProjectiveLimit | R18 | sorry (R20-blocked on T2.2-T4.1) |

The two **R20 Full** entries (`K_GLW_increment_var_le_T_cube` + the
local IsKolmogorovProcess) are the load-bearing pieces; T2.2-T4.1 are
mechanical assembly with the brownian-motion library API.
