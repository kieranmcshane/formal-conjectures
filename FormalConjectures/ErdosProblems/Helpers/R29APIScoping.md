# R29 API Scoping

**Round:** 29 — KMT Option C, 1D axiom + LS bridge skeleton.
**Date:** 2026-05-01.
**Branch:** `r29-finish` (off `r28-finish` HEAD `66a3208`).

This document records the upstream-API and predicate state at the time the
R29 mandatory floor (T2.1 + T4.1) was landed. Captured pre-implementation.

## 1. `Erdos524.IsRademacherSequence` — relocation (R29 V1b)

The structure was originally declared at `524.lean:124-134`, in
`namespace Erdos524`, with fields `indep`, `measurable`, `prob_pos`,
`prob_neg` (all unchanged).

**Cyclic-import discovery.** The R29 mandatory-floor skeleton
`Helpers/TwoDimKMTFromOneDim.lean` must mention `IsRademacherSequence` in
its statement (matching `524.lean:3741`'s axiom verbatim) **and** be
imported by `524.lean` to retire the axiom — which is impossible while
`IsRademacherSequence` lives in `524.lean` (the helper would have to
import 524 to see the predicate).

**Resolution.** Predicate moved verbatim to a new minimal helper file
`FormalConjectures.ErdosProblems.Helpers.RademacherSequence` (56 LOC, two
imports: `Mathlib.Probability.Independence.Basic` and
`Mathlib.Probability.Notation` for the `ℙ` scoped notation). 524.lean now
imports the helper and removes the local structure declaration; the
`Erdos524` namespace is unchanged from the consumer's perspective, so
none of 524.lean's lemmas (`isRademacherSequence_neg_mul`,
`isRademacherSequence_neg`, `rademacher_ae_mem_pm_one`, etc.) require
modification.

**Build verification.**
`lake build FormalConjectures.ErdosProblems.Helpers.RademacherSequence` →
"Build completed successfully (2555 jobs)".

## 2. `ProbabilityTheory.IndepFun` — Mathlib API state

Located at `Mathlib.Probability.Independence.Basic` and friends. The
relevant constructors / instances consumed by `LS_independent_yplus_yminus`
(T3.4) are:

* `ProbabilityTheory.IndepFun` — the predicate itself.
* `ProbabilityTheory.IndepFun_iff_pi_map_eq` — the standard product-space
  characterisation (joint pushforward = product of marginals). Brief lookup
  at the current pin (mathlib `25ce63313608`) shows this lemma exists
  under the name `ProbabilityTheory.indepFun_iff_map_prod_eq` (camelCase
  convention; the brief's name is slightly off but resolves to the same
  lemma).
* `ProbabilityTheory.IndepFun.const_left` / `const_right` — trivial
  constants are independent of everything; not directly applicable here
  but useful for degenerate testing.

R30 closure of T3.4 will use the joint-pushforward characterisation on a
product-space construction with two independent Brownian motions.

## 3. Stochastic-integral API — `brownian-motion` package

Status (pin `91267abd71bd`): the package's `BrownianMotion.StochasticIntegral`
namespace contains only the `Komlos` lemma (L¹-convex Komlós, *not* the
KMT coupling) and basic `IntegralWrt` infrastructure for piecewise-constant
processes against Brownian motion. The L²-kernel stochastic-integral API
needed by T3.1 / T3.2 (Itô isometry on `s ↦ e^{-us}`) is **not present**
at this pin.

This matches the Phase 2 Plan's "Node 1B swing factor" identification.

**Implication for R30.** T3.1, T3.2, and the C4 conjunct of T3.3 cannot
close until the upstream `brownian-motion` API gains the L²-deterministic-
kernel construction. The remaining R30 work that *can* be done at the
current pin:

* T3.4 (independence) — closes via `indepFun_iff_map_prod_eq` +
  product-construction.
* The strengthened-hypothesis input to T3.5 (Borell-BC argument
  producing `∀ ε > 0, ∃ T, ∀ᵐ ω, ∀ u ≥ T, …`) — closes inside T3.1 / T3.2
  *only* if the underlying Gaussian limits are constructed; currently
  blocked by the same gate.

T3.5's *swap* step (the actual T3.5 body) is fully closed in R29.

## 4. R29 mandatory-floor outputs

| File | LOC | Build | Sorries |
|------|----:|:-----:|:-------:|
| `Helpers/RademacherSequence.lean` | 56 | ✔ | 0 |
| `Helpers/OneDimKMT.lean` | 110 | ✔ | 0 (axiom only) |
| `Helpers/TwoDimKMTFromOneDim.lean` | 239 | ✔ | 5 |

**Sorry inventory in `TwoDimKMTFromOneDim.lean` (post-R29 close):**

| Sub-sorry | Status | TAG | R30 plan |
|-----------|:------:|-----|----------|
| T3.1 (`LS_yplus_construction`) | open | `[R29-T3.1-LS-yplus]` | gated on stochastic-integral API |
| T3.2 (`LS_yminus_construction`) | open | `[R29-T3.2-LS-yminus]` | gated on stochastic-integral API |
| T3.3 C4 (`LS_coupling_error`) | open | `[R29-T3.3-coupling-error]` | C3 closed via `Δ := log(n+1)/√n`; C4 gated on T3.1 |
| T3.4 (`LS_independent_yplus_yminus`) | open | `[R29-T3.4-indep-product-space]` | tractable in R30 (independence of stochastic-integral API) |
| T4.1 inline (Yminus mirror) | open | `[R29-T4.1-coupling-minus]` | folds away once T3.3 generalises to take both kernels |
| T3.5 (`LS_tail_decay_skeleton`) | **closed** | — | swap-only; full proof shipped in R29 |

R30 priority order (highest tractability first): T3.4 → T3.5 strengthened
input via R30-extra Borell-BC helper → T3.1 / T3.2 / T3.3-C4 (all gated on
upstream).

## 5. Net-axiom budget (Refinement 2)

| Round | Axioms | Count | Notes |
|-------|--------|:-:|------|
| End R28 | `two_dim_KMT_coupling` (public) + `Y_GLW_exists` (private, transitive `sorryAx`) | 2 | baseline |
| End R29 | + `one_dim_KMT_coupling` (new public) | **3** | transitional, paired with `two_dim_KMT_coupling_via_LS_reduction` skeleton |
| Target end-R30 | unchanged; ≥ 3 of 5 sub-sorries closed | 3 | toward replacing `two_dim_KMT_coupling` axiom by theorem in R31+ |
| Target end-R31 | `Y_GLW_exists` (private) + `one_dim_KMT_coupling` (public) | 2 | `two_dim_KMT_coupling` retired, KMT Option C complete |

If R30 closes < 3 of 5 sub-sorries, R29's 1D axiom and skeleton are
reverted (Refinement 2).

## 6. Cross-references

* `Helpers/OneDimKMTSketch.md` — exploratory sketches for upstream 1D KMT
  (Skorokhod, dyadic Tusnády, direct quantile).
* `Helpers/TwoDimKMTRetirement.md` — the original retirement-roadmap
  document, written when 1D KMT was treated as upstream-only.
* `Helpers/KMTOptionCPlan.md` — the R28-authored plan that R29 implements
  the mandatory floor of.
* `Helpers/Phase2Plan.md` Node 1B — the upstream stochastic-integral gate.
