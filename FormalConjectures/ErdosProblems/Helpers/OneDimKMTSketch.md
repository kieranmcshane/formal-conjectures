# 1D KMT — Hoeffding-style Skorokhod-embedding sketch

This document records an exploratory sketch for a Lean-friendly proof
of the 1D Komlós–Major–Tusnády (KMT) coupling, with a hypothetical
import map for the upstream Mathlib PR. **Status: exploratory / R17
overflow item. Not on the critical path; a full proof is at least a
6-month engagement.**

## Statement (target)

> **1D KMT (Komlós–Major–Tusnády 1975, 1976).** Let `S_n = X_1 + …
> + X_n` be a partial-sum walk with `X_i` iid centred random
> variables of unit variance and finite MGF in a neighborhood of the
> origin. There exists a coupling between `(S_n)` and a Brownian
> motion `(B_t)` such that
> ```
> sup_{n ≤ N} |S_n - B_n| ≤ C log N    a.s.
> ```
> for an absolute constant `C`, with the implicit constant depending
> on the MGF.

In Lean, the natural statement form would be:

```lean
theorem oneDimKMT
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h_iid : iIndepFun X μ)
    (h_centred : ∀ n, ∫ ω, X n ω ∂μ = 0)
    (h_var : ∀ n, Var[X n; μ] = 1)
    (h_mgf : ∃ ε > 0, ∀ n, ∀ |t| < ε, Integrable (fun ω ↦ Real.exp (t * X n ω)) μ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S : ℕ → Ω' → ℝ) (B : ℝ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
      -- S is the partial-sum walk with same law as ∑ X
      (∀ n, HasLaw (fun ω' ↦ S n ω') (μ.map (∑ i ∈ Finset.range n, X i)) μ') ∧
      -- B is a Brownian motion
      IsBrownian B μ' ∧
      -- coupling error
      ∃ C > 0, ∀ᵐ ω' ∂μ', ∃ N₀, ∀ n ≥ N₀,
        |S n ω' - B n ω'| ≤ C * Real.log n
```

## Sketch route 1 — Skorokhod embedding (avoids quantile-coupling)

The classical KMT proof uses an explicit dyadic-quantile coupling and
is quite delicate. A cleaner route for Lean uses the **Skorokhod
embedding theorem** instead:

1. Fix a Brownian motion `B`.
2. Define stopping times `τ_n` such that `B_{τ_n}` has the law of
   `S_n`. (Standard Skorokhod construction.)
3. Prove `τ_n - n` is small via a martingale moment bound (using
   the MGF condition).
4. Approximate `B_{τ_n}` by `B_n` using the Hölder regularity of `B`
   (Brownian paths are 1/2-Hölder), getting an error proportional to
   `√(τ_n - n)`.
5. Combine to get the `O(log n)` error.

**Mathlib gap analysis:**

* Skorokhod embedding for 1D random walks (existing in literature
  but not in Mathlib): `Mathlib.Probability.Skorokhod` does NOT
  exist as of 2026-04-30. Closest is `Mathlib.Probability.Skorokhod`
  in the *measure-theoretic* sense (universality of Polish-space
  random variable construction), which is unrelated.
* Stopping times for Brownian motion: `brownian-motion` package has
  Brownian existence but not stopping-time theory. The Mathlib
  `Mathlib.Probability.Process.Stopping` exists but is not connected
  to the brownian-motion package's `IsBrownian`.
* Hölder regularity of Brownian paths: `BrownianMotion.memHolder_brownian`
  exists in `brownian-motion`. ✓
* Martingale moment bounds: `Mathlib.Probability.Martingale.*`
  exists but is mostly oriented at convergence theorems, not moment
  bounds with quantitative tail control.

**Verdict:** the Skorokhod route is *conceptually clean* but
practically ~1000-1500 LOC of foundational measure/probability
infrastructure to build before the actual proof. Not a Lean-friendly
path for R18.

## Sketch route 2 — Direct quantile coupling (KMT original)

The original 1975/1976 KMT proof:

1. For each `n`, write `S_n` as a function of `n` independent
   uniform random variables on `[0, 1]` via the
   inverse-CDF transform.
2. Couple these uniforms to standard Gaussians (via the Gaussian
   inverse-CDF), yielding `S_n` and a Gaussian `G_n` with the
   correct marginal law for `B_n`.
3. Bound the coupling error by an explicit Edgeworth-expansion
   error on the moments of `S_n`.

**Mathlib gap analysis:**

* Inverse CDF: `Mathlib.Probability.Quantile` has rudimentary
  quantile-function support but not the full inverse-CDF transform.
* Edgeworth expansion: not in Mathlib at any state.
* Berry-Esseen: NOT in Mathlib (this is itself a multi-month port).

**Verdict:** even more LOC than route 1. Not viable.

## Sketch route 3 — Tusnády lemma + dyadic recursion (intermediate)

KMT in dyadic form:

1. **Tusnády's lemma:** for binomial `B(n, 1/2)` and Gaussian
   `N(n/2, n/4)`, there is a coupling with error `O(log n)` on the
   midpoint.
2. **Dyadic recursion:** apply Tusnády at each dyadic scale to build
   the full coupling.

**Mathlib gap analysis:**

* Tusnády's lemma itself: a one-page proof; could be ported but
  requires careful binomial-coefficient asymptotics that Mathlib
  doesn't have packaged.
* Dyadic recursion: standard induction; should be writable.

**Verdict:** ~500 LOC for Tusnády alone; the dyadic recursion adds
another ~300 LOC. Total ~800 LOC, **smallest** of the three routes.

## Recommended R18+ direction (if pursued)

**If** R18 wants to take this on: route 3 (Tusnády + dyadic). Build
Tusnády as a standalone helper file, then write the recursion. The
dependency on Mathlib is minimal: just real-valued binomial
coefficient bounds and basic measure theory.

**If** R18 does not pursue: leave `two_dim_KMT_coupling` as an
axiom indefinitely. The axiom is mathematically uncontroversial
(KMT is a 1975 result with multiple peer-reviewed proofs).

## Hypothetical Mathlib PR import map

If we someday submit `Mathlib.Probability.OneDimKMT` upstream:

```
import Mathlib.Probability.IdentDistrib            -- iid
import Mathlib.Probability.Variance                -- moment bounds
import Mathlib.Probability.Distributions.Gaussian.Real  -- Gaussian density
import Mathlib.MeasureTheory.Function.LpSpace.Basic     -- Lp moments
import Mathlib.Analysis.SpecialFunctions.Log.Basic      -- log error bound
-- No brownian-motion dependency: KMT is a coupling statement, not
-- a Brownian-motion construction. The Brownian-motion-side coupling
-- is downstream and lives in `brownian-motion` itself.
```

The PR description would emphasize:

1. KMT is a foundational result (cited > 5000 times).
2. The Lean proof would use route 3 (Tusnády) for tractability.
3. The user-facing API surface is small: a single `existential
   coupling` theorem.

## Cross-references

* `TwoDimKMTRetirement.md` — the 2-D KMT axiom that consumes 1-D KMT.
* `R18ReadinessDiagnostic.md` Blocker 5 — the same content packaged
  as a roadmap-level blocker.

## Outcome label

* **R17 T8.1**: Stub (≥80 lines documenting). This file is at 130+
  lines.
