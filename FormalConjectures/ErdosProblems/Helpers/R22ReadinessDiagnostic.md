# R22 Readiness Diagnostic

**Round to plan:** R22 (Y_GLW_exists axiom retirement closeout).
**Predecessor:** `r21-finish` (commits `30eaa83`, `ea2615d`, plus T5.* docs).
**Pins after R21:** `formal-conjectures @ r21-finish`, `brownian-motion @ 91267ab`, `mathlib @ 25ce633136`.

## R21 leftover

The single open sorry is at `Helpers/GLWGaussianProjectiveLimit.lean:1392`,
inside conjunct 9 of `glwGaussianLimit_Y_GLW_existence`. R22's job is to
close this gap and retire the `Y_GLW_exists` (transitive) `sorryAx`,
which then triggers the +500 project bonus (first axiom retirement of
the project).

R22 inherits a clean foundation: T2.2 (chaining moment bound) is
sorry-free, T3.1/T3.2 are sorry-free in their reformulated (weaker)
forms, and the `HasBoundedInternalCoveringNumber.subtype_univ` helper
is reusable for any block-K-C application.

## Prioritised blockers (R22 attack order)

### Blocker A (load-bearing) — modification sup-tail bound

**Statement to prove**:
```lean
lemma modification_block_sup_tail
    (T : ℕ) (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    glwGaussianLimit
      {ω | ε ≤ ⨆ u : ↥(denseCountable NNReal ∩ Set.Ico (T : NNReal) (T+1)),
                |ω u.1.1|}
      ≤ ENNReal.ofReal (sub_gaussian_term T ε) + chaining_term T ε
```

with both RHS terms summable in `T`. The `sub_gaussian_term` comes from
the marginal Chernoff (R19 `eval_glwGaussianLimit_real_abs_ge_le_of_pos`)
applied at a grid point near `T`. The `chaining_term` comes from Markov
on T2.2's chaining bound combined with `Cp_T = O(1/T²)` summability.

**Why this is the bridge.** T3.1's reformulation (Markov on
`glwHolderConstantENN T`) is the chaining piece. Combining with
marginal Chernoff at a grid anchor, plus block-diameter ≤ 1, gives the
sup-tail bound on the *projection's countable iSup*. The modification's
continuous sup equals the projection's countable iSup almost surely
(continuity of `Y' · ω` + a.s.-equality on a countable index — the
intersection of countably many a.s.-events is a.s.).

**Estimated LOC**: 200–300. Touches: `eval_glwGaussianLimit_real_abs_ge_le_of_pos`,
`glwHolderConstantENN_lintegral_le_R20` (T2.2), `meas_ge_le_lintegral_div`
(Markov), `exists_glwBrownianModification` (continuity).

**Sub-blocker A.1**: define `subGaussian_term T ε` explicitly via the
marginal at a specific grid point inside `denseCountable ∩ Set.Ico T (T+1)`.
Choose: pick the smallest `u_T ∈ denseCountable ∩ Set.Ico T (T+1)` (use
`Dense.exists_mem` of `denseCountable NNReal` in the open neighbourhood
`(T, T + 1/2)`). Then `|ω u_T| ≤ ε/2` event has probability `≤ 2 exp(-ε²·T/4)`
via R19 marginal Chernoff (factor of 4 absorbing the slack).

**Sub-blocker A.2**: extract a *quantitative* `Cp_T` from T2.2 instead
of the existential one. The existing `glwHolderConstantENN_lintegral_le_R20`
returns `∃ Cp_T < ∞, ...`; refactor to return the explicit
`(Real.toNNReal (1/(2*T^3)) : ℝ≥0∞) * constL ↥S c_T 1 2 2 (1/4) Set.univ`
so that summability of `∑_T Cp_T / ε²` can be checked term-wise.

### Blocker B — modification ↔ projection a.s.-bridge

**Statement to prove**:
```lean
lemma modification_sup_eq_projection_iSup_ae (T : ℕ) :
    ∀ᵐ ω ∂glwGaussianLimit,
      (⨆ u : ↥(denseCountable NNReal ∩ Set.Ico (T : NNReal) (T+1)),
          |Y' u.1.1 ω|)
        =
      (⨆ u : ↥(denseCountable NNReal ∩ Set.Ico (T : NNReal) (T+1)),
          |ω u.1.1|)
```

Where `Y'` is the modification from `exists_glwBrownianModification`.
For each fixed `u`, `Y' u =ᵐ ω u` (R18). The countable iSup over a
countable index, combined with `ae_all_iff`, gives the equality on a
common a.s.-set.

**Estimated LOC**: 30–50. Standard `Filter.Eventually.all` reasoning.

### Blocker C — continuous sup ↔ countable iSup

**Statement to prove**:
```lean
lemma continuous_sup_eq_countable_iSup
    {f : NNReal → ℝ} (hf : Continuous f) (T : ℕ) :
    (⨆ u : ↥(Set.Ico (T : NNReal) (T+1)), |f u.1|)
      =
    (⨆ u : ↥(denseCountable NNReal ∩ Set.Ico (T : NNReal) (T+1)), |f u.1|)
```

Continuous functions on a connected dense subset of an interval attain
their supremum on the closure. The denseCountable subset is dense; on
the open `Set.Ico T (T+1)` the iSup of `|f|` over the dense subset
equals the iSup over the full block (modulo measure-zero boundary
issues handled by `Set.Ico` vs `Set.Icc`).

**Estimated LOC**: 40–60. Mathlib has `Dense.iSup_eq` style lemmas for
continuous monotone, but `|·|` requires a small adapter.

**Caveat**: Set.Ico is half-open, so the right endpoint `T+1` is excluded.
For `Y' · ω` continuous on NNReal, `sup_{u ∈ [T, T+1]} |Y' u ω|` (closed)
and `sup_{u ∈ [T, T+1)} |Y' u ω|` (half-open) may differ at u = T+1.
Conjunct 9's quantification `∀ u ≥ T₀` covers all real u, including
half-open block boundaries; the integer ladder `T → T₀` covers the
endpoints by the next block's iSup. Resolve by using closed `Icc` blocks
or explicit boundary handling.

### Blocker D (cosmetic, ~30 LOC) — quantifier interleaving

**Statement to prove**:
```lean
lemma conjunct_9_from_block_BC :
    (∀ ε > 0, ∀ᵐ ω ∂glwGaussianLimit, ∃ T₀ : ℕ,
       ∀ T : ℕ, T₀ ≤ T → ¬(ε ≤ ⨆ u : ↥(denseCountable NNReal ∩ Set.Ico (T : NNReal) (T+1)),
                              |ω u.1.1|))
    →
    (∀ ε > 0, ∀ᵐ ω ∂glwGaussianLimit, ∃ T₀ : ℝ,
       ∀ u ≥ T₀, |Y' u.toNNReal ω| ≤ ε)
```

For real `u ≥ T₀ + 2` (with `T₀ : ℕ`), let `T := ⌊u⌋ : ℕ`, then `T ≥ T₀ + 1 ≥ T₀`,
and `u.toNNReal ∈ [T, T+1)` (or `[T, T+1]`). Apply the block iSup bound at
`T` (and `T-1` for the left boundary). Combined with Blockers B + C, the
conjunct-9 statement falls out.

**Estimated LOC**: 30–50.

### Blocker E (alternative route — Borell-TIS) — DO NOT pursue this round

Mathlib does not yet have Borell-TIS. The Cowork-direct sup-tail bound
via Borell would be `P(sup ≥ ε) ≤ 2 exp(-ε²/(2σ²))` where `σ² = sup_u Var[Y u]`.
For `Var[Y u] ≤ 1/(2T)` on `[T, T+1]`, `σ² ≤ 1/(2T)`, giving
`P(sup ≥ ε) ≤ 2 exp(-ε²·T)`. This is much sharper than the chaining route
but requires Borell-TIS which is not in Mathlib at HEAD. **Skip until
Borell-TIS lands upstream.**

## Estimated R22 effort

| Blocker | LOC | Build iterations | Difficulty |
|---------|-----|-------------------|------------|
| A.1 (subGaussian_term) | 60 | 3-4 | Medium (grid-point picking) |
| A.2 (quantitative Cp_T) | 80 | 4-6 | Medium (refactor + finiteness re-derivation) |
| A (compose A.1 + A.2 + Markov) | 100 | 6-8 | Hard (sup decomposition algebra) |
| B (modification a.s. bridge) | 40 | 2-3 | Easy |
| C (continuous = countable iSup) | 50 | 3-4 | Medium (Mathlib API hunt) |
| D (quantifier assembly) | 40 | 2-3 | Easy |
| **Total** | **370** | **20-28 builds** | **Hard overall** |

R22 should target ~370 LOC of new Lean and ~25 build iterations.
Realistic if R22's plan grades A as a single "Full" task at 200 pts;
B+C+D as a single "Full" task at 100 pts; final conjunct-9 retire as
a single "Full" task at 100 pts; T4.2 axiom retirement headline +500.

## Other open project frontiers (parallel, unblocked by R22)

* **`two_dim_KMT_coupling`** axiom in `524.lean:3741` — independent of
  GLW; awaits one-dim KMT scaffolding (see `OneDimKMTSketch.md`,
  `TwoDimKMTRetirement.md`).
* **Phase 2 / Node 3 (Gaussian-grid small-ball)** — sub-grid BB1 retired
  at commit `2afe1b8` on `add-erdos-524`. Two sorries remain (Schur,
  lower assembly). Future-blocker for axiom A1 retirement (independent
  axiom branch, not the GLW one).

## R22 success criteria

1. `Helpers/GLWGaussianProjectiveLimit.lean` builds with **0 sorries**.
2. `#print axioms Y_GLW_exists` shows ONLY `propext / Classical.choice / Quot.sound`.
3. The `Y_GLW_exists` declaration in `Helpers/GLWProcess.lean` (currently a `theorem` with transitive sorryAx) becomes a fully-discharged theorem with no sorryAx dependency.
4. `Helpers/AxiomRetirementCelebration.md` documents the closure, with full citation chain `Y_GLW_exists → glwGaussianLimit_Y_GLW_existence → conjuncts 1-9 → modification → glwCovMatrixNN → R13/R14/R15/R16/R17/R18/R19/R20/R21/R22`.

## Calibration suggestion for R22 manifest

R21 manifest projected 600-900 pts (69-103% of 870 base) but landed at
~421 pts (48%). The shortfall traces specifically to T3.1/T4.1 plumbing
that the manifest underestimated. R22 should:

* **Pre-flight**: dispatch a Problem-asker to verify whether Mathlib has
  the Dense.iSup_eq / continuous-sup-equals-dense-sup lemma (Blocker C).
  If yes, ~50 LOC saved. If no, allocate +1 build iteration budget.
* **Cap A as 1 task at 250 pts** (subBlockers A.1, A.2, A combined).
  Realistic Full probability: 0.6.
* **Cap B+C+D as 1 task at 150 pts** (mostly mechanical). Realistic
  Full probability: 0.85.
* **Final retire (conjunct 9 + T4.2) at 100 pts**. Gated; realistic Full
  probability conditional on A and B+C+D: 0.95.
* **Joint probability headline**: 0.6 × 0.85 × 0.95 ≈ 0.48. Plus +500
  bonus on retirement.
* **Realistic R22 ceiling**: 500 pts base + 500 bonus = 1000 pts.
  Realistic outcome: 350-700 pts. Over-projection is the historical
  failure mode; 50% is the realistic landing.

End of R22 readiness diagnostic.
