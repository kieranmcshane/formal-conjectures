# Phase A upper-bound: Mathlib gap diagnostic

**Date**: 2026-04-30
**Round**: R14
**Goal**: enumerate the Mathlib (and `brownian-motion` / `kolmogorov_extension4`)
gaps that block a fully proved Phase A *upper bound* on the GLW small-ball
event. Phase A complement of the existing GLW lower bound; together they
pin down the small-ball asymptotics that feed the limiting maximum law in
`524.lean`.

This file is the analogue of `ToolchainBumpDiagnostic.md` for the
upper-bound side. It is intentionally non-exhaustive: each gap below is
*known* to block a proof we have already attempted on paper. New gaps
will surface as the scaffold in `Helpers/PhaseAUpperBound.lean` is
expanded.

---

## Gap A1 — Slepian's lemma (Gaussian comparison by covariance domination)

**Statement we need.** For two centred Gaussian vectors `X, Y` on a
finite index set `I` with `Cov(Xᵢ, Xⱼ) ≤ Cov(Yᵢ, Yⱼ)` for all `i ≠ j` and
`Var(Xᵢ) = Var(Yᵢ)`, and any thresholds `(λᵢ)`,
`ℙ(∀ i, Xᵢ ≤ λᵢ) ≤ ℙ(∀ i, Yᵢ ≤ λᵢ)`. Equivalently, in supremum form:
`𝔼 sup_i Xᵢ ≤ 𝔼 sup_i Yᵢ`.

**Why we need it.** Phase A's upper bound reduces (via `endpoint_reparametrization`)
to comparing the GLW Gaussian process `Y±(u)` to a *reference*
Ornstein–Uhlenbeck process whose small-ball probabilities are explicitly
computable. The reference process has *larger* off-diagonal covariances at
the matched variances, so Slepian gives the desired upper bound on the
sup small-ball probability.

**Mathlib status.** Not present at `mathlib4 @ 25ce63313608`. Closest:
`Mathlib.Probability.GaussianRealVar` has covariance manipulations but no
comparison principle. `brownian-motion` has the `gaussianProjectiveFamily`
machinery but no Slepian-type inequality.

**Workaround sketch.** Could be derived elementarily from Gaussian density
sign-comparison + dominated convergence on the half-space indicator, but
this is non-trivial (≈ 200 lines) and not currently a supported route.

---

## Gap A2 — Sudakov–Fernique inequality

**Statement we need.** For centred Gaussian processes `(X_t)_{t ∈ T}` and
`(Y_t)_{t ∈ T}` on a (possibly infinite) index set `T` with
`𝔼 (X_s − X_t)² ≤ 𝔼 (Y_s − Y_t)²` for all `s, t`, the suprema satisfy
`𝔼 sup_t X_t ≤ 𝔼 sup_t Y_t`.

**Why we need it.** When the index set is *uncountable* (as is the case for
`u ∈ [0, T]` after reparametrization), Slepian's pointwise statement is
not enough — we need the supremum-version Sudakov–Fernique to control
expected suprema over compact intervals before applying concentration.

**Mathlib status.** Not present. `brownian-motion`'s
`KolmogorovChentsov` gives sample-path continuity (which lets us reduce
`sup` over the interval to `sup` over a countable dense set), but the
final comparison step still requires Slepian (Gap A1) plus a dominated
convergence pass — itself blocked on `Mathlib.MeasureTheory.Convergence`
having dominated convergence for *suprema* of conditionally bounded
families.

---

## Gap A3 — Borell–TIS / Gaussian concentration on the supremum

**Statement we need.** If `X` is a centred Gaussian process with
`σ² := sup_t Var(X_t) < ∞` and finite expected supremum `m := 𝔼 sup_t X_t`,
then for all `λ > 0`,
`ℙ(|sup_t X_t − m| > λ) ≤ 2 exp(−λ² / (2 σ²))`.

**Why we need it.** Together with Sudakov–Fernique (Gap A2), Borell–TIS
converts an *expectation* upper bound on `sup` to a *probability* upper
bound (the small-ball / large-deviation form actually used in Chojecki
Lemma 13). Without Borell–TIS the upper bound is asymptotically the right
shape but loses constants.

**Mathlib status.** Not present at the current pin. There is a partial
formalization in `Mathlib.Probability.IdentDistrib` of the *isoperimetric*
content but no end-user statement for Gaussian processes. The
`brownian-motion` dependency does *not* package this either; it's a known
gap on Degenne's roadmap.

**Workaround sketch.** Borell–TIS reduces to log-Sobolev for the standard
Gaussian (which Mathlib has, in `Mathlib.Analysis.SpecialFunctions.Log`)
plus Herbst's argument; the Herbst step requires a Gaussian-tail bound on
exponential moments that we can derive from
`Mathlib.Probability.Gaussian.IndepFun` but the chain is ≈ 400 lines of
unstated infrastructure. Not feasible without a dedicated PR upstream.

---

## Gap A4 — quantitative Kolmogorov–Chentsov in 1D

**Status.** This is *partially* available in `brownian-motion` via
`kolmogorov_chentsov_continuity`, but the Hölder-exponent quantitative
form (which we need to feed Borell–TIS with explicit constants) is not.
The qualitative form ("there exists a continuous version") is present;
the quantitative form ("the Hölder seminorm is integrable with explicit
moment bound depending on `α, β`") is the missing piece.

**Severity.** Lower than A1–A3 — we *can* dispense with quantitative
Hölder by accepting a slightly weaker upper bound (off by a logarithmic
factor in the rate). This would still close the GLW two-sided estimate at
the leading-order level required by `524.lean`.

---

## Path forward

Phase A is **blocked at the leading-order level** by gaps A1 + A2 + A3
acting jointly. None of the three is independently the bottleneck — all
three together form the standard "Slepian → Sudakov–Fernique →
Borell–TIS" pipeline that produces sharp upper bounds for Gaussian sup
small-ball estimates.

R15 plan options (decreasing order of feasibility):

1. **Wait for upstream.** Track Degenne's `brownian-motion` repo for
   Slepian / Sudakov–Fernique additions (his PhD thesis covers these).
   Lowest engineering cost, highest schedule risk.
2. **Bespoke elementary route.** Bypass Gaussian-process machinery by
   reducing Phase A to a *direct* covariance computation on the OU
   process; quote Borell–TIS as an *axiom* for now. Cost: ~300 lines for
   the reduction; deferred axiom analogous to `two_dim_KMT_coupling`.
3. **Half-step.** Prove the upper bound up to a logarithmic slack
   (skipping A3, accepting weaker concentration). Cost: ~150 lines but
   the constant in `524.lean` becomes off by `O(log n)`, which would
   require revising the limiting law statement in §11.

Option 2 is the recommended R15 starting point. Option 3 is a useful
fallback if `brownian-motion` API surface is more limited than expected.

---

## R16 update (2026-04-30)

**Status table:**

| Blocker | R14/R15 status | R16 status | Priority for R17 |
|---------|----------------|------------|------------------|
| A1 — Slepian | `True` placeholder | Stub signature + 30-line proof outline (`PhaseAUpperBound.slepian_comparison_GLW`) | **HIGH** — load-bearing for A2 |
| A2 — Sudakov–Fernique | `True` placeholder | Stub signature + countable-dense-set proof outline | MEDIUM — derives from A1 |
| A3 — Borell–TIS | `True` placeholder | Stub signature + log-Sobolev/Herbst proof outline | MEDIUM — independent of A1/A2 |
| A4 — quantitative K-C | partial via `brownian-motion` | unchanged | LOW — can accept log-slack |

**R16 narrowing:** the proof outlines committed in R16 each identify a
specific Mathlib gap (not just a generic "Slepian missing" diagnosis).
The narrowed gaps are:

* **A1.** Differentiability of the multivariate-Gaussian distribution
  function w.r.t. the covariance matrix (`Mathlib.Probability.
  Distributions.Gaussian.*` does not have this; the closest is
  `multivariateGaussian_density_eq` in `brownian-motion`). A 30-50 LOC
  Mathlib PR could close this.
* **A2.** Countable-dense-set reduction — relies on
  `KolmogorovChentsov.continuousModification` (already in
  `brownian-motion`) plus a missing "sup over interval = sup over
  countable dense subset a.s." lemma. ~20 LOC PR.
* **A3.** Probabilistic log-Sobolev inequality for the standard
  Gaussian. This is the actual upstream gap; the analytic log-Sobolev
  in `Mathlib.Analysis.SpecialFunctions.Log` is unrelated. Requires a
  dedicated PR.

**Path forward (R17 priority order):**

1. PR A2-reduction lemma (smallest, isolated).
2. PR A1 differentiability (medium, well-defined statement).
3. PR A3 log-Sobolev (largest, but unblocks all of Phase A).

**Bypass option (R17 fallback):** Option 2 from R14/R15 — accept Borell–TIS
as a deferred `axiom` analogous to the still-pending
`two_dim_KMT_coupling`. This re-axiomatises A3 but lets us close A1+A2
honestly within the toolchain. R16 R17ReadinessDiagnostic argues this
is the correct trade given the relative cost of A3 vs A1+A2.
