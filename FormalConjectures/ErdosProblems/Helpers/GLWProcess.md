# Phase 2 Node 1B — stepping-stone axiom proposal (v3)

**Status:** PROPOSAL v3 — awaiting user greenlight before any axiom is shipped.

**v3 changelog:**
* **Existential `Ω`.** v2 universally quantified over `(Ω, ℙ)`, which is mathematically
  inconsistent on the trivial 1-point space (no non-trivial Gaussian process can
  live there) — the same false-for-trivial-Ω flaw as
  `gao_li_wellner_small_ball_upper`. v3 produces `Ω` from the construction, which
  is consistent (Daniell–Kolmogorov on `ℝ^[0,∞)`). This pre-resolves the
  universal-Ω prong of the Node 6 universal-Y/Ω decision.
* **Explicit `Integrable` conjuncts.** Mathlib's `∫ ω, f ω ∂ℙ` returns `0` for
  non-integrable `f`, so v2's centeredness and covariance conjuncts were
  vacuously true for non-integrable `Y`. The `IsGaussian` conjunct on pushforward
  measures does **not** imply integrability of `Y u` itself (different measure).
  v3 adds `Integrable (Y u) ℙ` and `Integrable (Y u · Y v) ℙ` explicitly.
* **Tail-decay rationale corrected.** The conjunct `∀ ε > 0, ∀ᵐ ω, ∃ T₀, ...`
  asserts pointwise a.s. eventual smallness — `σ²(T) → 0` alone gives only
  `L²`-convergence, not pointwise a.s. The actual justification is Borell on
  `sup_{u ∈ [T, T+1]} |Y u|` (using continuous-paths + σ²-decay) followed by
  Borel–Cantelli over `T = 1, 2, 3, ...`. The conjunct stays; only the
  docstring rationale changes.

## Survey of this Mathlib snapshot

`grep` of `.lake/packages/mathlib/Mathlib/Probability/` shows:

* `Distributions/Gaussian/{Basic,Real,CharFun,Fernique}.lean` — `IsGaussian` predicate,
  Gaussian on ℝ, characteristic-function bridge, Fernique tail bound. ✓
* `Process/{Filtration,Adapted,Stopping,Predictable,HittingTime,Kolmogorov,
  PartitionFiltration,FiniteDimensionalLaws}.lean` — adapted-process /
  filtration scaffolding + Daniell–Kolmogorov consistency. ✓
* `Martingale/{Basic,Convergence,Centering,...}.lean` — discrete-time
  martingale theory. ✓
* `Moments/SubGaussian.lean` — sub-Gaussian moments. ✓

What is **absent**:

* No `BrownianMotion` / `IsBrownianMotion` predicate or construction.
* No `WienerMeasure` / Wiener-process measure.
* No Itô integral against Brownian motion (or any continuous semimartingale).
* No stochastic-integral API for deterministic kernels against BM.

Consequence: the Phase2Plan.md Node 1B target

```lean
noncomputable def Y_GLW (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) (u : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.exp (-u * s) ∂(B · ω)
```

cannot be written from existing Mathlib primitives. Building Brownian motion +
Itô integration locally inside `FormalConjecturesForMathlib/` is doctoral-thesis-
scale work and out of scope for this Phase 2 push.

## Proposed stepping-stone axiom

A single axiom asserting the **existence** of a centered Gaussian process with
covariance kernel `K_GLW`, continuous sample paths, and standard tail decay.
This is strictly weaker than `gao_li_wellner_small_ball_upper`/`_lower`, which
both assert a cubic-exponential small-ball estimate on top of the existence.

```lean
/-- **Stepping-stone axiom (Phase 2 Node 1B, v3).** Existence of a probability
space `(Ω, ℙ)` carrying a centered Gaussian process
`Y_GLW : ℝ → Ω → ℝ` with covariance `K_GLW(u, v) = (1 - exp(-(u+v)))/(u+v)`
(the kernel of `∫₀¹ e^{-us} dB(s)`), continuous sample paths, and the
sample-path tail decay `sup_{u ≥ T} |Y u| → 0` a.s. as `T → ∞`.

**Materially smaller than the GLW axioms it stages toward** — asserts only
the **existence** of such a probability space + process, not any small-ball
bound. Once Mathlib gains Brownian motion + Itô calculus this axiom is
dischargeable from
`Mathlib.Probability.Process.Kolmogorov` (Daniell–Kolmogorov on the
finite-dimensional Gaussians with covariance `K_GLW`) +
`Mathlib.Probability.Distributions.Gaussian.Fernique` (continuous sample
paths via Kolmogorov–Chentsov + Fernique-style modulus).

**Existential over `Ω`.** Quantifying universally over `(Ω, ℙ)` would be
inconsistent on a trivial space (the same false-for-trivial-Ω flaw as
`gao_li_wellner_small_ball_upper`). Producing `Ω` from the construction
matches Daniell–Kolmogorov, which builds `Ω = ℝ^[0,∞)` with the cylinder
measure. Node 6 consumers will `obtain ⟨Ω, _, _, Y, hY⟩` to extract.

**Tail-decay rationale.** `σ²(T) → 0` alone gives `L²`-convergence, not
pointwise a.s. eventual smallness. The actual justification of the
conjunct: Borell on `sup_{u ∈ [T, T+1]} |Y u|` (Ledoux §1.3 eq. (1.7)),
using continuous-paths separability + σ²-decay; then Borel–Cantelli
over the integer-indexed sequence `T = 1, 2, 3, ...`. -/
axiom Y_GLW_exists :
    ∃ (Ω : Type) (_ : MeasureSpace Ω) (_ : IsProbabilityMeasure (ℙ : Measure Ω))
      (Y : ℝ → Ω → ℝ),
      -- measurability
      (∀ u, Measurable (Y u)) ∧
      -- integrability of marginals and pairwise products (load-bearing
      -- because `∫` returns `0` for non-integrable functions, so
      -- centeredness and covariance conjuncts below would otherwise be
      -- vacuous for non-integrable `Y`)
      (∀ u, Integrable (Y u) ℙ) ∧
      (∀ u v : ℝ, Integrable (fun ω => Y u ω * Y v ω) ℙ) ∧
      -- centeredness
      (∀ u, ∫ ω, Y u ω ∂ℙ = 0) ∧
      -- covariance kernel
      (∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
        ∫ ω, Y u ω * Y v ω ∂ℙ = K_GLW u v) ∧
      -- joint Gaussianity: every finite linear combination of `Y u_i`
      -- is Gaussian on ℝ. Load-bearing for Node 6's Anderson-inequality
      -- invocation through `GaussianBoxProb.anderson_lower`.
      (∀ (n : ℕ) (us : Fin n → ℝ) (cs : Fin n → ℝ),
        ProbabilityTheory.IsGaussian
          (Measure.map (fun ω => ∑ i, cs i * Y (us i) ω) ℙ)) ∧
      -- continuous sample paths (Kolmogorov–Chentsov)
      (∀ᵐ ω ∂ℙ, Continuous (fun u => Y u ω)) ∧
      -- sample-path tail decay (Borell on `sup_{[T,T+1]}` + Borel–Cantelli)
      (∀ ε > 0, ∀ᵐ ω ∂ℙ, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε)
```

## Why this is materially smaller than the existing GLW axioms

| Claim | GLW axiom | This axiom |
|---|---|---|
| Existence of `Y` | implicit | **explicit** |
| Existential over `Ω` | universal (false on trivial `Ω`) | **existential (consistent)** |
| Integrability of `Y u`, `Y u · Y v` | unstated | **conjuncted** |
| Covariance specification | unconstrained | **`K_GLW`** |
| Joint Gaussianity | unstated | **conjuncted** |
| Continuous paths | unstated | **conjuncted** |
| Tail decay | unstated | **conjuncted** |
| Small-ball cubic bound | **claimed** | **not claimed** |
| Universal-`Y` quantifier | yes | **no** |

The probabilistic small-ball estimate — the actual hard mathematical content of
Gao–Li–Wellner (2010) — stays unaxiomatized. Once `Y_GLW_exists` lands, Nodes
2/4/6 derive the small-ball bound via:

* Node 2: covariance kernel `K_GLW(u, v) ≈ 1/(u+v)` matches `hierCauchyG m`
  to `O(exp(-(u+v))/(u+v))` (already proved in Node 1A as `K_GLW_cauchy_asymptotic`).
* Node 4: discretize the continuous box event using sample-path continuity.
* Node 6: package as a `GaussianBoxProbV1 m` instance and apply
  `gaussian_grid_smallball_upper_final` / `_lower_final`.

Net effect: `gao_li_wellner_small_ball_upper` and `_lower` become provable
theorems backed by `Y_GLW_exists` + the helper. **Net axiom count change: 3 → 1**
(GLW pair + KMT eliminated; one new construction axiom added — KMT remains, see
Phase2Plan.md.)

## Decision request

OK to ship `Y_GLW_exists` as a single axiom in a new file
`Helpers/GLWProcess.lean`?

* If **yes**: I write the axiom + a one-paragraph file docstring + import it into
  Phase2Plan.md's dependency chain, and proceed to Node 2 next.
* If **no**: tell me what shape you'd prefer (e.g. parametrize over a process
  satisfying these properties — push the obligation to construct one to a
  consumer; or split into two axioms; or scope it differently). Or veto the
  axiom and we end Phase 2 here with helper green + axiom count unchanged.
* If **modified**: send me the exact axiom statement you want and I write that
  one instead.

Standing by — no axiom shipped until you respond.
