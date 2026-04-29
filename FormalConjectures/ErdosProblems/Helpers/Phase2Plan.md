# Phase 2 Bridging Plan — GLW/KMT axioms → helper-backed theorems

**Date:** 2026-04-29 (post-Helper Round 2)
**Branch:** `kmc-erdos-gaussian-smallball`
**Helper status:** `GaussianGridSmallBall.lean` is zero-sorry, zero-axiom on commit `611b465`. `GaussianBoxProbV1` carries the new additive field `relevant_blocks_combined_lower`; `h_assembly` closes via `mul_le_mul + ring`.

## Goal of Phase 2

Drive the axiom count in `FormalConjectures/ErdosProblems/524.lean` from **3 → 0**:

| # | Axiom | Line | Eliminated by Nodes |
|---|---|---|---|
| 1 | `gao_li_wellner_small_ball_upper` | 3493 | 1A, 1B, 2, 4, 6 |
| 2 | `gao_li_wellner_small_ball_lower` | 3521 | 1A, 1B, 2, 4, 6 (+ tail bridge) |
| 3 | `two_dim_KMT_coupling` | 3574 | 5 |

The 3 axioms quantify universally over arbitrary measurable `Y : ℝ → Ω → ℝ` and arbitrary Rademacher couplings; the helper proves a finite-dim hierarchical-Cauchy box-probability bound. Closing the gap means constructing, for the specific GLW process `Y(u) = ∫₀¹ e^{-us} dB(s)`, a `GaussianBoxProbV1 m` instance whose `boxProb` matches the continuous box probability the axiom quantifies over. The KMT axiom is independent — it concerns the Rademacher → Brownian coupling, upstream of the GLW process.

## Node inventory — Lean signatures, dependencies, scope

### Node 1A — GLW kernel: definition + analytic properties [LEAF]

The deterministic kernel `K_GLW(u, v) = (1 - exp(-(u+v)))/(u+v)`, extended to `u + v = 0`. Pure real analysis on `ℝ × ℝ → ℝ`; no probability.

```lean
namespace Erdos524.Helpers

noncomputable def K_GLW (u v : ℝ) : ℝ :=
  if h : u + v = 0 then 1 else (1 - Real.exp (-(u + v))) / (u + v)

theorem K_GLW_pos : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → 0 < K_GLW u v
theorem K_GLW_le_one : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → K_GLW u v ≤ 1
theorem K_GLW_continuous : Continuous (Function.uncurry K_GLW)
theorem K_GLW_symm : ∀ u v : ℝ, K_GLW u v = K_GLW v u
/-- Large-(u+v) asymptotic: K_GLW u v - 1/(u+v) = O(exp(-(u+v))/(u+v)). -/
theorem K_GLW_cauchy_asymptotic :
    ∀ u v : ℝ, 0 < u + v →
      |K_GLW u v - 1 / (u + v)| ≤ Real.exp (-(u + v)) / (u + v)

end Erdos524.Helpers
```

**Dependencies:** Mathlib only (`Real.exp`, `Real.exp_pos`, `div_pos`, `Continuous.div`, `Real.exp_le_one_iff`).
**Scope:** Pure Mathlib API. ~80–120 lines. Very low risk.
**Target file:** `FormalConjectures/ErdosProblems/Helpers/GLWKernel.lean`.

### Node 1B — GLW process Y_GLW + covariance formula

Define the Itô integral `Y_GLW B u ω = ∫₀¹ e^{-us} dB(s)(ω)` and prove its first-and-second moments give exactly `K_GLW`.

```lean
namespace Erdos524.Helpers

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The GLW Itô-integral process. -/
noncomputable def Y_GLW (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) (u : ℝ) (ω : Ω) : ℝ :=
  -- pending Mathlib's Itô integral; placeholder is `∫ s in Set.Icc 0 1, e^{-us} dB(s)(ω)`
  sorry

theorem Y_GLW_measurable (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) :
    ∀ u : ℝ, Measurable (Y_GLW B hB u)

theorem Y_GLW_integrable (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) (u : ℝ) :
    Integrable (Y_GLW B hB u) ℙ

theorem Y_GLW_mean_zero (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) (u : ℝ) :
    ∫ ω, Y_GLW B hB u ω ∂ℙ = 0

theorem Y_GLW_covariance (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ ω, Y_GLW B hB u ω * Y_GLW B hB v ω ∂ℙ = K_GLW u v

theorem Y_GLW_continuous_paths (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) :
    ∀ᵐ ω ∂ℙ, Continuous (fun u => Y_GLW B hB u ω)

end Erdos524.Helpers
```

**Dependencies:** Node 1A (`K_GLW`); Mathlib's stochastic integral / `MeasureTheory.Integral.IntegralEqImproper` and Brownian motion API.
**Scope:** **Largest open question of the plan.** Mathlib's Itô-against-Brownian-motion is partial (cumulative Itô integrals exist for `L²`-progressively-measurable integrands, but the API for deterministic-kernel integrals against BM is thin and lemmas about its covariance are not packaged). Honest estimate: 300–700 lines of Mathlib gymnastics + 1 stepping-stone axiom for the Itô isometry on the specific kernel `s ↦ e^{-us}` *if* the Mathlib API can't be assembled in reasonable time. Stepping-stone axiom would be strictly weaker than `gao_li_wellner_small_ball_upper` (one specific kernel, one identity, no small-ball claim).
**Target file:** `FormalConjectures/ErdosProblems/Helpers/GLWProcess.lean`.

### Node 2 — Hierarchical-Cauchy approximation of the discrete GLW covariance

Sample `Y_GLW` at the hierarchical times `hierTimes m i := Real.log (hierGrid m i)` (equivalently `e^{-u s}` evaluated at the hierGrid scales) and compare the resulting `m × m` covariance matrix `K_GLW(hierTimes m i, hierTimes m j)` to `hierCauchyG m i j = 1/(hierGrid m i + hierGrid m j)`.

```lean
namespace Erdos524.Helpers

noncomputable def hierTimes (m : ℕ) : Fin m × Fin m → ℝ := fun ij => Real.log (hierGrid m ij)

noncomputable def K_GLW_matrix (m : ℕ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  Matrix.of fun i j => K_GLW (hierTimes m i) (hierTimes m j)

/-- Spectral approximation: `K_GLW_matrix m` and `hierCauchyG m` are close in
    operator norm, with error decaying in `m`. -/
theorem K_GLW_matrix_close_hierCauchy (m : ℕ) (hm : 1 ≤ m) :
    ∀ i j : Fin m × Fin m,
      |K_GLW_matrix m i j - hierCauchyG m i j| ≤
        Real.exp (-(hierGrid m i + hierGrid m j)) / (hierGrid m i + hierGrid m j)

/-- The discrete GLW covariance matrix is positive-definite. -/
theorem K_GLW_matrix_posDef (m : ℕ) (hm : 1 ≤ m) : (K_GLW_matrix m).PosDef
```

**Dependencies:** Node 1A (kernel definition + asymptotic); `Helpers.CauchyDetLowerBound` (already in tree, provides `hierGrid`, `hierCauchyG`).
**Scope:** Pure linear algebra + `K_GLW_cauchy_asymptotic`. ~150–250 lines. Low–medium risk.
**Target file:** `FormalConjectures/ErdosProblems/Helpers/GLWHierApprox.lean`.

### Node 4 — Discrete-vs-continuous box-probability comparison

Let `T(ε) = -C log ε` for some `C > 0`. Compare the continuous event `{∀ u ∈ [0, T(ε)], |Y_GLW u| ≤ ε}` to the discrete event `{∀ i ∈ Fin m, |Y_GLW (hierTimes m i)| ≤ (1-δ)·ε}` for appropriate `m = m(ε)` and small `δ`.

```lean
namespace Erdos524.Helpers

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Discretization upper bound: continuous box ⊆ slightly-larger discrete box. -/
theorem Y_GLW_box_disc_upper
    (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) (ε : ℝ) (hε : 0 < ε)
    (m : ℕ) (hm : 1 ≤ m)
    (T : ℝ) (hT_le : T ≤ -2 * Real.log ε) (hT_pos : 0 < T) :
    {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, |Y_GLW B hB u ω| ≤ ε} ⊆
    {ω | ∀ i : Fin m × Fin m, |Y_GLW B hB (hierTimes m i) ω| ≤ ε}

/-- Discretization lower bound: small enough discrete box ⊆ continuous box. -/
theorem Y_GLW_box_disc_lower
    (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B) (ε : ℝ) (hε : 0 < ε)
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ_lt_one : δ < 1) :
    {ω | ∀ i : Fin m × Fin m, |Y_GLW B hB (hierTimes m i) ω| ≤ (1 - δ) * ε} ∩
    {ω | ∀ i ∈ Fin m × Fin m, ∀ u ∈ ⋃ i, Set.Ioo ... -- modulus of continuity event
         |Y_GLW B hB u ω - Y_GLW B hB (hierTimes m i) ω| ≤ δ * ε} ⊆
    {ω | ∀ u ≥ (0 : ℝ), |Y_GLW B hB u ω| ≤ ε}
```

**Dependencies:** Node 1B (`Y_GLW_continuous_paths`).
**Scope:** Modulus-of-continuity + Borell-type concentration. ~200–400 lines. Medium risk.
**Target file:** `FormalConjectures/ErdosProblems/Helpers/GLWDiscretization.lean`.

### Node 5 — 2D KMT coupling (Rademacher → twin Brownian motions)

Statement: for `(a_k)` a Rademacher sequence, there exist twin Brownian motions `B⁺, B⁻` (independent) such that the partial-sum processes `Z_n^±(u) = n^{-1/2} Σ_k a_k (±e^{-u/n})^k` satisfy `sup_u |Z_n^±(u) - Y_GLW B^± u| ≤ Δ_n` a.s. with `Δ_n = O(log n / √n)`. This is the actual content of `axiom two_dim_KMT_coupling`.

```lean
-- Same shape as the existing axiom, restated as a theorem:
theorem two_dim_KMT_coupling_thm :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∃ (Yplus Yminus : ℝ → Ω → ℝ) (Δ : ℕ → ℝ), <full conjunction from axiom>
```

**Dependencies:** Mathlib 1D KMT (does not exist).
**Scope:** **Out of scope for this session.** 1D KMT is a multi-year Mathlib formalization target; building it locally is on the order of a doctoral thesis. The Chojecki Lemma 13 wrapper around it (independence of the two limits, sample-path regularity) is much shorter, but only after 1D KMT is in place. Honest move: leave this axiom untouched in this session, OR introduce **one** materially-smaller stepping-stone axiom of the shape "1D KMT for Rademacher partial sums against the specific kernel `s ↦ e^{-us}`" that strictly weakens the universally-quantified axiom into the only kernel we actually use. Net axiom count on the path through Node 5: 1.
**Target file:** `FormalConjectures/ErdosProblems/Helpers/KMTCoupling.lean`.

### Node 6 — GaussianBoxProbV1 instance assembly

The capstone. Construct, for each `m`, a `GaussianBoxProbV1 m` instance whose `cov = hierCauchyG m`, whose `boxProb ε` is the continuous-process box probability `(ℙ {ω | ∀ u ∈ [0, T(ε)], |Y_GLW u ω| ≤ ε}).toReal`, and which discharges every V1 field — including the new `relevant_blocks_combined_lower`.

```lean
namespace Erdos524.Helpers

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

noncomputable def gaussianBoxProbV1_of_GLW
    (B : ℝ → Ω → ℝ) (hB : IsBrownianMotion B)
    (m : ℕ) (hm : 1 ≤ m) (T : ℝ) (hT : 0 < T) :
    GaussianBoxProbV1 m
```

**Dependencies:** Nodes 1A, 1B, 2, 4. Crucially: discharging `relevant_blocks_combined_lower` for the GLW instance is the math content that this Node owes — Node 6 has to *prove* the cubic-aggregate bound for the relevant-block product in the GLW context (not just assume it as in the V1 contract). This is essentially Anderson + KL spectral estimates restricted to the relevant-frequency band.
**Scope:** ~300–500 lines of bookkeeping + the relevant-block lower bound proof. Medium–high risk concentrated in `relevant_blocks_combined_lower`.
**Target file:** `FormalConjectures/ErdosProblems/Helpers/GLWBoxProbInstance.lean`.

### Replacement of the GLW axioms (final)

Once Node 6 exists, the GLW axioms become consequences:

```lean
theorem gao_li_wellner_small_ball_upper_thm (glw : GaoLiWellnerConstants) :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (Y : ℝ → Ω → ℝ), (∀ u, Measurable (Y u)) →
      ∃ (ε₀ : ℝ) (T : ℝ → ℝ), <upper bound> := by
  -- caveat: the existing axiom universally quantifies over Y. The honest theorem
  -- has the GLW-shape Y baked into its construction, then is wrapped into the
  -- universally-quantified statement by choosing ε₀ small enough that the bound
  -- holds vacuously for non-GLW Y, OR by repackaging the axiom signature with
  -- a hierarchical-Cauchy hypothesis on Y. The latter changes the consumer
  -- contract; will be settled when Node 6 lands.
  ...
```

(See "Open issue with the universal-Y axiom signature" below.)

## Dependency DAG

```
       ┌──────────────┐
       │  Node 1A     │  ← LEAF (pure analysis, ~80-120 LOC, low risk)
       │  GLW kernel  │
       └──────┬───────┘
              │
        ┌─────┴─────┐
        │           │
        ▼           ▼
  ┌──────────┐  ┌──────────────┐
  │ Node 1B  │  │   Node 2     │
  │ Y_GLW +  │  │ Hierarchical │
  │ cov      │  │ Cauchy approx│
  └──────┬───┘  └──────┬───────┘
         │             │
         ▼             │
  ┌──────────┐         │
  │ Node 4   │         │
  │ Disc/cont│         │
  │ box prob │         │
  └──────┬───┘         │
         │             │
         └──────┬──────┘
                │
                ▼
        ┌─────────────┐
        │   Node 6    │
        │ V1 assembly │
        └──────┬──────┘
               │
               ▼
   ╔══════════════════════════╗
   ║ Replace GLW upper/lower  ║
   ║ (eliminates 2 of 3 axiom)║
   ╚══════════════════════════╝

   ┌──────────────────────┐
   │      Node 5          │  ← INDEPENDENT branch, no Phase 2 deps
   │   2D KMT coupling    │     but blocked by missing Mathlib 1D KMT
   └──────────┬───────────┘
              │
              ▼
   ╔════════════════════════╗
   ║ Replace KMT axiom      ║
   ║ (eliminates 3rd axiom) ║
   ╚════════════════════════╝
```

## Honest reachable target this session

| Path | Axioms removed | Total axioms after | Feasibility |
|------|----------------|---------------------|-------------|
| Nodes 1A → 1B → 2 → 4 → 6 | GLW upper, GLW lower | **1** (KMT remains) | Plausible, but Node 1B is the swing factor — may need a one-line stepping-stone axiom for Itô isometry on `e^{-us}`. |
| Nodes 1A → ... → 6 + Node 5 | All 3 | **0** | Not in scope: Node 5 needs Mathlib 1D KMT, which is doctoral-thesis-scale work. |
| Nodes 1A → ... → 6 + Node 5 with stepping-stone axiom | All 3 by name; net axiom = "1D KMT for `e^{-us}` kernel" | **1 net** | Honest. Net count unchanged from path 1, but axiom is in a different layer (statistical vs functional-analytic). |

**Concrete recommendation for this session:** drive the count from 3 → 1 by executing path 1 (Nodes 1A → 1B → 2 → 4 → 6, eliminating both GLW axioms). Leave the KMT axiom as the single residual, with a clear note that closing it requires upstream Mathlib KMT or a stepping-stone axiom of strictly smaller statement.

## Recommended starting point

**Node 1A** — the true leaf. Pure real analysis on `(1 - exp(-x))/x`, no probability, no Mathlib gaps. Smallest unit of useful progress; ~80–120 lines; should land in a single commit.

After Node 1A is green, the dependency DAG opens up Nodes 1B and 2 in parallel. Node 1B is the swing — it's the only Node that may need a stepping-stone axiom for Mathlib's stochastic-integral API gaps. Tackling it second exposes the only major risk early.

## Open issue with the universal-Y axiom signature (flag, not a blocker)

The existing `gao_li_wellner_small_ball_upper` axiom universally quantifies over **arbitrary** measurable `Y : ℝ → Ω → ℝ`. As stated, it is mathematically false for trivial `Y` (e.g. `Y = 0` makes the box probability `1`, while the RHS `exp(-c|log ε|^3) → 0`). The axiom is **inconsistent in its universal form** but has been usable so far because no consumer instantiates it at a counterexample `Y`. When the axiom is replaced by a theorem, we must either:

1. Add a hierarchical-Cauchy / Gaussianity hypothesis on `Y` (changes the signature; breaks `polynomial_sup_small_ball_*` callers — they pass arbitrary `Yplus`).
2. Choose `ε₀` via the construction in a way that makes the bound hold vacuously for non-GLW `Y` (mathematically dishonest if not justified).
3. Rephrase the universally-quantified statement to existentially produce its own `Y` from the construction (changes the consumer contract).

This is **not** a blocker for Phase 2 itself — it surfaces only at the moment of axiom-to-theorem replacement (post-Node 6). Flagging now so we can decide together when we get there.

## Workflow

Per the cloud-build protocol: each Node lands as one commit on `kmc-erdos-gaussian-smallball`, pushed to `fork`, verified by `gb` on the codespace, then we move to the next. No local `lake build`. After this audit-only commit, request greenlight before starting Node 1A.
