# R21 Readiness Diagnostic

Closing-of-R20 diagnostic. R20 landed:

* **T1.1 Full** (`K_GLW_increment_var_le_T_cube`): the load-bearing
  analytical Taylor bound for the local K-C constant `M_T = 1/(2T³)`.
* **T2.1 Full** (`glwGaussianLimit_isKolmogorovProcess_local`): the
  local IsKolmogorovProcess on the unit block `↥(Set.Ico T (T+1))`
  with `(p, q, M_T) = (2, 2, 1/(2T³))`.
* **T2.2 Stub + T3.1 Stub + T3.2 Stub** (typeable signatures + documented
  blockers): chaining moment bound, sup-tail bound, Borel–Cantelli.

`Y_GLW_exists` axiom retirement remains gated on **the chaining-API
plumbing**: applying `countable_kolmogorov_chentsov` (brownian-motion
library, `KolmogorovChentsovInequality.lean:326`) to T2.1's local
IsKolmogorovProcess and re-establishing the Hölder-constant connection
post-R18-routing.

## Blocker A (priority A — round headline) — Apply chaining moment bound

**State:** R20 closed the *analytical* gap (T1.1 Full + T2.1 Full),
delivering the local K-C constant `M_T = 1/(2T³)`. The remaining gap
is API-level: hooking the local IsKolmogorovProcess into the
brownian-motion chaining bound.

**Resolution path for R21 — T2.2 Full:**

1. **Construct `HasBoundedInternalCoveringNumber Set.univ` for the
   subtype `↥(Set.Ico T (T+1))`.** The cumulative cover
   `isCoverWithBoundedCoveringNumber_Ico_nnreal` gives bounded covering
   numbers for `[0, n+1)` blocks of NNReal. For the standalone subtype
   block, derive via `HasBoundedInternalCoveringNumber.subset` (the
   block has diameter 1 and internal covering number `≤ ⌈1/ε⌉` at
   scale ε, hence `c = 1, d = 1` works). ~30 LOC.

2. **Apply `countable_kolmogorov_chentsov` with the local K-C.** The
   countable index `T' = denseCountable NNReal ∩ Set.Ico T (T+1)` (or
   its image in the subtype). The bound becomes
   `∫⁻ ω, glwHolderConstantENN T ω ≤ M_T · constL T 1 1 2 2 (1/4) U`
   where `constL` is the explicit chaining constant. ~30 LOC.

3. **Evaluate `constL` explicitly.** The R20 definition of
   `glwHolderConstantENN T ω` uses `(p, β·p) = (2, 1/2)` (β = 1/4),
   matching the K-C structure. The constant `constL 1 1 2 2 (1/4)` is a
   finite ENNReal; the value matters less than its finiteness. ~10 LOC.

**Total for blocker A: ~70 LOC, 1 wave.**

## Blocker B (priority A — assembly) — Sup-tail + BC + conjunct-9

**State:** structurally identical to R19's blocker, but now with all
sub-prerequisites gated only on Blocker A.

**Resolution path for R21 — T3.1, T3.2, T4.1 Full sequencing:**

1. **T3.1 Full** (~60 LOC): sup-decomposition
   `sup_{[T, T+1]} |Y' u ω| ≤ |Y'(T) ω| + glwHolderConstant T ω`
   via the `holderOnWith_holderModification` connection (R18 routing
   through `exists_modification_holder'''` needs the Hölder constant
   re-attached — see Pivot Rule 1 below). Then union bound + Markov on
   the moment bound from T2.2 + R19's Chernoff at integer points.

2. **T3.2 Full** (~30 LOC): direct `MeasureTheory.measure_limsup_atTop_eq_zero`
   on the events `E_T(ε)` with summable `f(T, ε)` from T3.1.

3. **T4.1 Full** (~30 LOC): a.s. event from T3.2 + integer-vs-real
   ceiling argument to convert `T : ℕ` ladder to `T₀ : ℝ` for u ≥ T₀.

**Total for blocker B: ~120 LOC, 1 wave once Blocker A lands.**

## Blocker C (priority A — finalisation) — `#print axioms` clean

**State:** Once T4.1 is sorry-free (and the only sorry in the whole
GLW helper stack on the conjunct-9 path), `#print axioms
Y_GLW_exists` should report only `[propext, Classical.choice,
Quot.sound]` — the unconditional Lean kernel + standard probability
library axioms.

**Resolution path:** mechanical. After T4.1 Full, run
`#print axioms Y_GLW_exists`, capture the output, and document in
`AxiomRetirementCelebration.md`. **+500 pts project bonus.**

## Blocker D (priority B) — Phase A: Slepian + Sudakov-Fernique

Unchanged from R19/R20. ~450 LOC / 4 waves. Independent of the GLW
conjunct-9 path.

## Blocker E (priority C) — Two-dim KMT

Unchanged. ~1000+ LOC / 6+ waves.

## Summary table

| # | Blocker | Priority | Effort | Unblocks |
|---|---------|----------|--------|----------|
| A | Chaining moment bound API plumbing | A | 70 LOC / 1 wave | T2.2 Full |
| B | Sup-tail + BC + conjunct-9 assembly | A (after A) | 120 LOC / 1 wave | T4.1 Full |
| C | `#print axioms` celebration | A (after B) | 5 LOC | Y_GLW_exists axiom retirement |
| D | Slepian + Sudakov-Fernique | B | 450 LOC / 4 waves | Phase A upper bound |
| E | Two-dim KMT | C | 1000+ LOC / 6+ waves | A2-axiom retirement |

R21's natural focus is blockers A + B + C in sequence. Together they
deliver **the first project axiom retirement** (the +500 bonus that
has been gated since R13).

The combined ~190 LOC is plausible in a single R21 wave, modulo the
brownian-motion library API navigation.

## R20 → R21 axiom delta

```
R19 (start of R20): sorryAx + propext + Classical.choice + Quot.sound
R20 (current):       sorryAx + propext + Classical.choice + Quot.sound  ← unchanged
R21 target:          propext + Classical.choice + Quot.sound  ← clean
```

The two non-`sorry` axioms (`propext`, `Quot.sound`) are Lean's
unconditional kernel-level axioms. `Classical.choice` enters via
`exists_modification_holder'''`-style theorems and is unavoidable.

## R20 calibration notes

R20 actual ≈ 387 pts vs. Cowork's max-without-bonus 745. **52% of
max-without-bonus.** The miss is concentrated on T2.2 / T3.1 / T3.2 /
T4.1 — the chaining-API plumbing that Cowork's pre-flight estimated
at ~30 LOC each but in practice requires:

1. **R20 Pivot Rule 1 (validated):** Mathlib's Taylor expansion
   infrastructure was bypassed in favour of the L²([0,1]) integral
   representation. The hand-rolled order-2 expansion was avoided
   entirely; instead, the explicit primitive
   `F(x) = -((c²x² + 2cx + 2)/c³)·exp(-cx)` for `∫₀¹ x²·exp(-cx) dx`
   delivered the analytical bound in ~70 LOC of derivative-bookkeeping.

2. **R20 Pivot Rule 2 (NEW for R21):** The R18-witness `Y' :=
   exists_glwBrownianModification`'s output loses the explicit Hölder
   constant when going through `exists_modification_holder'''`'s
   indicator-process construction. To use the iSup-formula
   `glwHolderConstantENN T` in T3.1's sup-decomposition, the
   `holderOnWith` bound must be re-established **on the modification
   `Y'` directly** rather than on the underlying Z-construction. This
   is ~30 LOC of `HolderOnWith.congr_edist`-style transport.

3. **R20 Pivot Rule 3 (NEW for R21):** The `constL` chaining constant
   from `KolmogorovChentsovInequality.lean` carries opaque parameter
   dependence; T2.2 Full only needs `constL < ∞`, not its explicit
   value. The Stub already wraps `Cp_T < ∞` as the existential output,
   matching the actual API shape.

R21 calibration target: **800–1100 pts** on a focused manifest with
blockers A + B + C as the centerpiece. T4.2 (axiom retirement) is
genuinely R21-landable; the +500 pts project bonus is in play.

The structural-credit story for R20: T1.1 Full + T2.1 Full deliver the
analytical and structural pieces that **enable** R21's mechanical
closeout. The cumulative R19 + R20 deliverables are 5 Full new lemmas
(2 R19 + 2 R20 + the `glwHolderConstant` definition stack) and 3 R20
Stubs with concrete next-wave hooks.

## R21 strategic ordering

1. **Phase 0 — V1**: rebuild check on `r20-finish` HEAD.
2. **Phase 1 — Blocker A**: `HasBoundedInternalCoveringNumber` for the
   subtype block + `countable_kolmogorov_chentsov` application = T2.2
   Full.
3. **Phase 2 — Blocker B step 1**: Hölder-constant transport from `Y'`
   to `glwHolderConstant T` (~30 LOC).
4. **Phase 3 — Blocker B step 2**: T3.1 sup-decomposition + Markov +
   Chernoff (~50 LOC).
5. **Phase 4 — Blocker B step 3**: T3.2 Borel-Cantelli (~30 LOC).
6. **Phase 5 — Blocker B step 4**: T4.1 conjunct-9 assembly (~30 LOC).
7. **Phase 6 — Blocker C**: `#print axioms Y_GLW_exists` capture,
   `AxiomRetirementCelebration.md` documentation.
8. **Phase 7 — docs + push**.

## Pivot rules for R21

1. **If `HasBoundedInternalCoveringNumber.subset` doesn't compose
   cleanly with the subtype:** prove the bound directly from the
   1-dimensional internal covering number formula (the unit interval
   has internal covering number ≤ ⌈1/(2ε)⌉ + 1 at scale ε).

2. **If the `holderOnWith` connection from `Y'` loses information:**
   re-do the R18 witness as a direct `holderModification`
   construction rather than via `exists_modification_holder'''`,
   capturing the Hölder constant explicitly in the witness.

3. **If `#print axioms Y_GLW_exists` reveals an extra axiom:** likely
   from `Classical.someSpec` in `IsLimitOfIndicator.measurable`. If
   that's the only extra it's still acceptable; document and proceed.

R21 is the round where the project's first axiom retirement is
genuinely reachable. The path is mapped; the analytical work (T1.1)
and structural copy (T2.1) are landed; what remains is brownian-motion
library API plumbing.
