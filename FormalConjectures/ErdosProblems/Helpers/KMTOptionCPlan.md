# KMT Option C Retirement Plan — R28 Stub + Roadmap

**Round:** R28 (`r28-finish` branch)
**Status:** Stub (load-bearing LS-reduction Lean transcription deferred; net-axiom-count guardrail enforces no-regression).
**Pre-authorisation:** 7h-session-brief §"Branch C R28" lines 41-46; §"R27 Branch A KMT Option C spec" lines 105-127; Grok-validated D2 + Option C combination.

## Current state at R28

After R27's Option D bascule:
- `Y_GLW_exists` axiom inventory: `[propext, Classical.choice, Quot.sound, Cp_T_explicit_pointwise_axiom (private)]` — `sorryAx` retired.
- `two_dim_KMT_coupling` (`524.lean:3741`) remains as public axiom (5 consumers in `524.lean`).
- Net axiom count: 2 (1 private D2 + 1 public 2D KMT).

R28 candidate path (per brief, Branch C continuation):
1. Introduce `axiom one_dim_KMT_coupling` in new file `Helpers/OneDimKMT.lean`.
2. Transcribe LS reduction `TwoDimKMTRetirement.md:84-92` into new file `Helpers/TwoDimKMTFromOneDim.lean`.
3. Replace `axiom two_dim_KMT_coupling` in `524.lean:3741` with `theorem two_dim_KMT_coupling := ...` proved via the LS bridge.
4. Verify net axiom count remains 2.

## Why R28 lands at Stub

**Honest scope assessment (post-R26/R27 context-budget review):**

The 2D form `two_dim_KMT_coupling` has **9 conjuncts** quantifying jointly over Yplus, Yminus, Δ, and a Rademacher sequence `a`, including:
- Two kernel-tested coupling bounds with kernels `f₁(u,k) = exp(-u·k/n)` and `f₂(u,k) = (-exp(-u/n))^k`.
- `ProbabilityTheory.IndepFun` between Yplus and Yminus over the joint product space.
- Continuous sample paths for both.
- Tail decay (`∀ε > 0, ∀ᵐω, ∃T₀, ∀u ≥ T₀, |Y u ω| ≤ ε`) for both.

A 1D axiom of the classical Komlós–Major–Tusnády form (`|S_n - B(n)| ≤ C log(n+1)`) does not directly produce kernel-tested couplings. The LS reduction must:

1. **Apply 1D KMT to derive a Brownian motion `B` such that `S_n ≈ B(n)`.**
2. **Use `B` to construct `Yplus(u, ω)`** as a stochastic integral against the kernel `e^{-u s}`. This requires the brownian-motion package's stochastic-integral API at deterministic-kernel parameters — exactly the gap that `Phase2Plan.md` Node 1B identified as the "swing factor" (300-700 LOC of Mathlib gymnastics or one stepping-stone axiom for the Itô isometry on `s ↦ e^{-us}`).
3. **Compute the coupling error** `|((1/√n) ∑ a_k e^{-uk/n}) - Yplus u| ≤ Δ_n` uniformly in `u ≥ 0` and `ω` from the partial-sum coupling. This is the kernel-tested form of the strong invariance principle restricted to our kernel — non-trivial.
4. **Repeat for Yminus** with the second kernel.
5. **Construct the joint product space** carrying two independent BMs `B⁺, B⁻` to satisfy the `IndepFun` conjunct.
6. **Continuous sample paths and tail decay** transfer from the BM construction via Kolmogorov-Chentsov + martingale tail estimates.

**Realistic LOC estimate to land this in Lean:** 300-600 LOC, in the post-`brownian-motion`-stochastic-integral-API world. R28's remaining context budget cannot cover this.

## Net-axiom-count guardrail (Refinement 2) decision

If R28 lands `axiom one_dim_KMT_coupling` *without* successfully replacing `axiom two_dim_KMT_coupling`, the project's net axiom count goes to **3** = `Cp_T_explicit_pointwise_axiom` + `two_dim_KMT_coupling` + `one_dim_KMT_coupling`. This is a **regression** vs the R25 baseline of 2.

Per the brief lines 152-153:
> "**NET AXIOM CHECK at R28 end (failure case):** if KMT Option C also fails AND R28 ends with net = 3 (Y_GLW under D2 + two_dim_KMT_coupling unchanged + one_dim_KMT_coupling introduced but theorem not landed) → REVERT R28 changes (drop one_dim_KMT_coupling and the partial theorem). Net at session end = 2. NO REGRESSION VS BASELINE."

**Therefore: R28 lands at honest Stub** without introducing any new Lean axioms or theorems. Net axiom count remains 2.

## Pre-authorised axiom forms (for future rounds)

When the brownian-motion stochastic-integral API for deterministic L²-kernels lands (or a stepping-stone axiom for it is introduced), the following Lean signatures are pre-authorised:

### `Helpers/OneDimKMT.lean` (Grok-validated form, adapted)

```lean
namespace Erdos524.Helpers

/-- **R28+ / KMT Option C primary axiom.**

The classical Komlós–Major–Tusnády 1975 strong invariance principle
specialised to Rademacher partial sums: there exist Brownian motions
coupling the partial sums `S_n = ∑_{k=1..n} a_k` to `B(n)` with error
`|S_n - B(n)| ≤ C log(n+1)` uniformly in `n` and `ω`.

This is a single peer-reviewed 1D theorem (Komlós–Major–Tusnády
*Studia Sci. Math. Hungar.* 1975). The full Lean formalisation is a
multi-year project; pending that, we axiomatise the statement.

`O(log n)` rate is necessary for the polynomial-small-ball downstream
consumer (Grok-validated; cannot be weakened to `o(√n)` without losing
the cubic-subseq absorption). -/
axiom one_dim_KMT_coupling :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), Erdos524.IsRademacherSequence a →
      ∃ (B : ℕ → Ω → ℝ) (C : ℝ),
        0 < C ∧ (∀ n, Measurable (B n)) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω,
          |∑ k ∈ Finset.Icc 1 n, a k ω - B n ω| ≤ C * Real.log (n + 1))

end Erdos524.Helpers
```

### `Helpers/TwoDimKMTFromOneDim.lean` (LS reduction theorem)

```lean
namespace Erdos524.Helpers

/-- **R28+ / Two-dim KMT via LS reduction.**

The 2D coupling `two_dim_KMT_coupling` follows from `one_dim_KMT_coupling`
applied twice + product-space construction for independence + KC continuity
and tail-decay transfer. Per `TwoDimKMTRetirement.md:84-92` — body remains
~150-300 LOC pending stochastic-integral API for `s ↦ e^{-us}` kernel. -/
theorem two_dim_KMT_coupling_via_LS_reduction :
    -- 9-conjunct statement (matches 524.lean:3741) ...
    sorry  -- TAG[R28-LS-reduction-load-bearing]: kernel-tested coupling for e^{-us}

end Erdos524.Helpers
```

### `524.lean:3741` replacement (gated on LS reduction theorem)

```lean
-- Replace `axiom two_dim_KMT_coupling :=` with:
theorem two_dim_KMT_coupling := Erdos524.Helpers.two_dim_KMT_coupling_via_LS_reduction
```

This theorem has the same signature as the current axiom; consumers (`524.lean:3925, 4080, 4228, 4604, ...`) need no changes.

## Future round budget

| Round | Task | LOC budget | Risk |
|-------|------|:-----------:|------|
| R29 | Land 1D axiom + structured 2D theorem stub (private helper) | 50-80 | Low |
| R30 | Itô isometry stepping-stone axiom for `s ↦ e^{-us}` (or Mathlib BM API arrival) | 30 (axiom) | Medium (depends on upstream) |
| R31 | Yplus, Yminus stochastic-integral construction | 100-150 | Medium |
| R32 | Coupling error bound (uniform in u, ω) | 80-120 | Medium-High |
| R33 | Product-space + IndepFun + sample-path continuity transfer | 60-100 | Medium |
| R34 | KC tail decay for Y± | 40-60 | Medium |
| R35 | Compose to final 2D theorem; replace 524.lean axiom | 30-50 | Low (mechanical) |

**Cumulative: ~400-560 LOC across 7 rounds**, in the post-Itô-isometry-axiom world. Net axiom delta: -1 (2D out) +1 (1D in) +1 (Itô isometry axiom, if used) = +1 net. Manageable.

## Skin-in-the-game

If the math content of the LS reduction turns out to have a hidden gap (e.g., the kernel-tested coupling cannot be derived from classical 1D KMT alone), this MD captures the assumption. Grok-validated the structural soundness in the 7h-session pre-flight (brief lines 117-118: "Grok confirmed: two independent 1D KMT applications + triangle inequality coordinate-wise + KC sample-path regularity transfer via independence — no hidden trap"). Should that validation prove wrong, the design-failure clause kicks in (brief lines 261-267).

## Cross-references

- `R26BuildStatus.md` — Y_GLW Partial outcome, Branch C trigger.
- `R27BuildStatus.md` — D2 bascule (R23-bound-pointwise sorry retired).
- `CpTExplicitAxiom.md` — D2 axiom math derivation.
- `KMTStatusInventory.md` — Option A/B/C/D comparison.
- `TwoDimKMTRetirement.md` — original LS reduction sketch (R14, R17).
- `OneDimKMTSketch.md` — 1D KMT proof routes (R17).
- `SubGaussianMomentScoping.md` — Mathlib sub-Gaussian gaps.
