# R17 readiness diagnostic

**Date:** 2026-04-30
**Round closing:** R16
**Goal:** punch list of blockers and recommended R17 work order, with
explicit success criteria for each.

## Outcome status from R16

| Outcome | Tier achieved | Notes |
|---------|---------------|-------|
| O1 — `glwGaussianLimit_isKolmogorovProcess` | **Partial** (R15 → R16) | `measurablePair` Full; `kolmogorovCondition` structured-sorry with detailed reduction chain documented in-line. `(p, q, M) = (2, 2, 1)` chosen over the brief's `(4, 2, 3)` — see "Calibration note" below. |
| O2 — `glwGaussianLimit_Y_GLW_existence` | **Partial** | 2 of 9 conjuncts Full (`IsProbabilityMeasure`, `Measurable`); 7 structured sorries each tagged with the precise brownian-motion-shaped helper port required. |
| O3 — `#print axioms Y_GLW_exists` | **Deferred** | Skipped due to 90-min budget vs. 7900+-job lake build. Inherited transitive sorry from O2 means the axiom audit is not yet meaningful. |
| O4 — `isGLWProcess_from_existence` | **Full** | Generic re-wrap corollary added; `isGLWProcess_exists_full` rewritten to use it. |
| O5 — 1D KMT pre-flight | **Full** | **Finding: 1D KMT is NOT in mathlib (`25ce63313608`) or `brownian-motion` (`91267abd71bd`).** Branch B applies. |
| O6, O7 — `two_dim_KMT_coupling` retirement | **Stub** | Brief's branch B: documented in `Helpers/TwoDimKMTRetirement.md`. Axiom remains in 524.lean. |
| O8 — 524.lean cascade | **N/A** | No consumer-facing change. |
| O9, O10, O11 — Phase A scaffold | **Stub** | `True` placeholders replaced with proof-outline-bearing stubs. Each has ≥ 30-line proof outline in docstring. |
| O12 — `TwoDimKMTRetirement.md` | **Full** | 100+ line doc with arXiv cite, import map, branch-B justification. |
| O13 — `PhaseADiagnostic.md` R16 update | **Full** | Status table + narrowed Mathlib gaps + R17 PR priority order. |
| O14 — Mathlib-PR-shaping refactor | **Stub** | Skipped due to budget; recommendation moved to R17 priority list below. |
| O15 — this file | **Full** | |
| O16 — Push branch | (this round) | Pushed at end of R16. |

## R17 priority list

### Tier 1 — Headline (close O2 to Full)

**Goal:** retire the 7 structured sorries in
`glwGaussianLimit_Y_GLW_existence` so that `Y_GLW_exists` is fully
sorry-free.

The 7 sorries fall into 3 dependency tiers:

* **Tier 1a (independent, easy):** Conjuncts 3, 4, 5, 6 — port the
  brownian-motion `hasLaw_eval_*`, `integral_id_*`,
  `covariance_eval_*` lemmas verbatim with `glw` prefix and
  `glwCovMatrixNN_PosSemidef` substituted for `posSemidef_brownianCovMatrix`.
  Estimated 100-150 LOC; mechanical port.

* **Tier 1b (linearity argument):** Conjunct 7 — joint Gaussianity. Use
  `IsGaussian.map_continuousLinearMap` with the linear functional
  `(ω : (J → ℝ)) ↦ ∑ i, cs i * ω ⟨(us i).toNNReal, _⟩` where
  `J = Finset.image (fun i ↦ (us i).toNNReal) Finset.univ`. ~50 LOC.

* **Tier 1c (depends on O1 Full):** Conjunct 8 — continuous paths.
  Requires `glwGaussianLimit_isKolmogorovProcess` to be sorry-free (O1
  Full), then `IsAEKolmogorovProcess.mk` plus brownian-motion's
  `IsKolmogorovProcess.continuousModification` give the a.e. continuous
  modification. The Y in conjunct 8 must then be replaced by this
  modification (Y_mod) which still satisfies conjuncts 1-7 mod a.e.
  equality. ~80 LOC.

* **Tier 1d (independent, hard):** Conjunct 9 — tail decay. Needs
  Borell on `sup_{u ∈ [T, T+1]} |Y u|` plus Borel-Cantelli over
  `T = 1, 2, …`. Borell is the same A3 gap as in Phase A. **Block:**
  pending the Borell PR. Cost without Borell: 200+ LOC plus
  re-axiomatising the concentration step.

**Recommendation:** R17 closes Tier 1a + 1b + 1c (Full O2 modulo
conjunct 9), then ships conjunct 9 as a **structured sub-axiom**
(`Y_GLW_tail_decay_axiom`, parallel to `two_dim_KMT_coupling`) until
Borell lands.

### Tier 2 — Fully retire O1 (close to Full)

`glwGaussianLimit_isKolmogorovProcess.kolmogorovCondition`: the
reduction is documented in-line in `Helpers/GLWGaussianProjectiveLimit.lean`.
Needs the `hasLaw_eval_sub_eval_glwGaussianLimit` port (analog of
brownian-motion's line 130) plus a 2-D variance computation. Estimated
~100 LOC after Tier 1a is in (it shares the port helpers).

### Tier 3 — Mathlib-shaping (deferred from R16 O14)

Once Tier 1 + 2 are in, the projective-limit infrastructure is a
**kernel-generic helper**: it works for any continuous, PSD,
sub-grid-consistent kernel on `ℝ ≥ 0`, not just K_GLW. Refactor
`glwGaussianProjectiveFamily` → `gaussianProjectiveFamilyOfKernel K`
upstream-style; then GLW becomes a 1-line specialisation
`gaussianProjectiveFamilyOfKernel K_GLW`. This is a sister
contribution to `brownian-motion`'s existing `gaussianProjectiveFamily`
(which is hardcoded to `brownianCovMatrix`).

### Tier 4 — Phase A (after Borell upstream)

Per `PhaseADiagnostic.md` R16 update, the priority order is:

1. PR A2-reduction lemma (smallest, isolated, ~20 LOC).
2. PR A1 Slepian (medium, ~50 LOC after the differentiability gap).
3. PR A3 Borell–TIS / log-Sobolev (largest, dedicated PR).

After A1+A2+A3 land upstream, all four Phase A steps become genuine
proofs, not just signature stubs.

### Tier 5 — `two_dim_KMT_coupling` retirement (long-term)

Per `Helpers/TwoDimKMTRetirement.md`: 1D KMT is the upstream blocker.
Estimated upstream effort 800-1500 LOC for 1D KMT (via Skorokhod
embedding). Once 1D KMT is in mathlib, our Lean 30-50 LOC Letwin-Sawhney
2-D reduction lands in a single PR.

## Calibration notes

**On the brief's `(4, 2, 3)` choice for O1.** Arithmetic check:

* Brownian-motion uses `IsKolmogorovProcess preBrownian gaussianLimit (2*n) n …`
  (BrownianMotion.lean:705); for `n = 2` this is `(4, 2, …)`, but the
  constant is `Nat.doubleFactorial 3 = 3`, so the brief's `(4, 2, 3)`
  matches the brownian template at `n = 2` exactly.
* For GLW the L²-Hölder bound is `Var ≤ |s − t|²` (one power stronger
  than brownian's `Var = |s − t|`), so the analog at `n = 2` is
  `(p, q, M) = (4, 4, 3)` not `(4, 2, 3)`.
* R16 selected the L²-Hölder form `(2, 2, 1)` directly because (a) it
  is the natural shape of the bridge fact
  `glwCovMatrixNN_pairwise_diff_quadratic_le_sq` and (b) it is the
  smallest-effort path to a sorry-free O1.

The K-C threshold for continuous modification is `q > 1` on a 1-D
index, so `(2, 2, 1)` and `(4, 4, 3)` both unlock conjunct 8 of O2 via
`IsAEKolmogorovProcess.mk`. The `(4, 2, 3)` form would not be
arithmetically true for GLW, so the deviation is mathematically
necessary.

**On the 90-min vs 830-pt manifest.** R16's manifest at 267% surplus
relative to expected throughput yielded ~38% Full + 30% Partial +
20% Stub + 12% Deferred. Estimated points: ~330-380 of 830 = 40-46%
band. **Below the calibration band [50%, 70%].** Calibration finding:
**the 267% surplus is too high; back to ~150-180% for R17.**

The dominant time sinks in R16 were:

* O1 + O2 polishing (≈ 25 min) — value/time good but per-conjunct
  proof costs were higher than expected.
* O5 pre-flight scan (≈ 10 min) — value high (Branch B decision).
* Phase 4 doc writing (≈ 30 min) — high LOC throughput, lower
  rigor-impact than expected.

**Recommended R17 manifest size:** target 500-600 pts, prioritising
Tier 1a-c (the O2 retirement) which is ~250 pts at Full and is the
load-bearing piece for a future R18 axiom-clean GLW chain.
