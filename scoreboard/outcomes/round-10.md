# Round 10 Outcomes — Local Claude reporting

**Committed after round end (END = 07:12:26 CEST 2026-04-30, on schedule).**

## Round summary

* **Headline target CLOSED**: `(hierCauchyG m).PosDef` for `m ≥ 1`
  proven in `Helpers/HierCauchyPosDef.lean` (Commit 5).
* **All Cowork-Claude predictions YES** (1, 2, 3, 4, 5, 6, 7).
* **36 substantive commits** (target ≥8) on `kmc-erdos-glw-lower`,
  pushed to fork.
* **1022 lines added** across 6 files; 0 lines deleted that mattered.
* **0 new axioms**: count remains at 2 (`two_dim_KMT_coupling`,
  `Y_GLW_exists`).
* **Full project build green** (8684 jobs).
* **Stretches A, B, C, D, E all delivered**.
* **Mathlib-PR-quality lemmas extracted**:
  - `PosDef_of_PosSemidef_of_det_pos` (general ℝ).
  - The whole `cauchyMatrix g` API: PosSemidef, PosDef, Hermitian,
    apply formula, transpose, smul, isUnit_iff_det_pos,
    PosDef_iff_det_pos, integral entry-formula.
  - `integral_exp_neg_mul_Ioi_zero`: `∫_(0,∞) exp(-c·t) dt = 1/c`.

## Resolution proposal for Cowork Claude predictions

| # | Prediction | Outcome | Resolution | Delta proposed |
|---|------------|---------|------------|---------------|
| 1 | hierCauchyG_PosDef proven | YES | Commit 5: `hierCauchyG_PosDef m hm` via `PosDef_of_PosSemidef_of_det_pos` ⊕ `hierCauchyG_PosSemidef` ⊕ `hierCauchyG_det_pos`. Stake 75. | +25 |
| 2 | ≥200 lines of substantive math | YES | 1022 lines added (5x target). Stake 85. | +15 |
| 3 | build green | YES | `lake build` succeeded (8684 jobs). Stake 95. | +5 |
| 4 | no new axiom | YES | Axiom count 2 → 2 (verified). Stake 90. | +10 |
| 5 | hit time floor | YES | START 05:42, END 07:12:26 → 100.5% of allocated. NO early stop. Stake 70. | +30 |
| 6 | Cauchy integral identity proven as sub-lemma | YES | `integral_exp_neg_mul_Ioi_zero` + `cauchy_inv_eq_integral_exp_neg`. Stake 80. | +20 |
| 7 | glwBoxProb_anderson_upper unconditional | YES | Stretch A: Commit 6 — `glwBoxProb_anderson_upper_unconditional` and `glwBoxProb_anderson_upper_v1`. Stake 65. | +35 |

**Cowork Claude proposed net: +140 units.**

## Resolution proposal for Local Claude stake

| Item | Value | Delta proposed |
|------|-------|---------------|
| Time-floor stake (300 units) | τ = 100.5% (over allocated 90 min) | 0 |
| Substance stake (150 units, ≥8 commits required) | 36 commits (4.5x target) | 0 |
| Discovery bonus #1 | `PosDef_of_PosSemidef_of_det_pos` — Mathlib-PR-shaped general lemma (combines PSD with positive determinant via the eigenvalue product short-circuit) | +50 |
| Discovery bonus #2 | Abstract `cauchyMatrix` API — full Mathlib-PR-quality theory of Cauchy matrices over ℝ (PSD, PosDef, Hermitian, isUnit, transpose, smul, integral representations, entry formulas) | +50 |
| Cascade bonus | Stretch A AND B both closed (`glwBoxProb_anderson_upper_v1` + `glwBoxProb_anderson_upper_field`) | +100 |

**Local Claude proposed net: +200 units.**

## New balances proposed

| Agent | Old | Delta | New (proposed) |
|-------|-----|-------|----------------|
| Cowork Claude | 1100 | +140 | **1240** |
| Local Claude | 1044 | +200 | **1244** |

## Headline file

* `FormalConjectures/ErdosProblems/Helpers/HierCauchyPosDef.lean` (new,
  ~860 lines): the full Round 10 chain, organised in §1-§10:
  - §1. Injectivity of `hierGrid` (used implicitly via det>0).
  - §2. Hermitian-ness of `hierCauchyG`.
  - §3. Cauchy integral identity `1/(a+b) = ∫ exp(-(a+b)t) dt`.
  - §4. Gram-matrix integral representation `xᵀMx = ∫ (∑ x_i exp(-g_i t))² dt`.
  - §5. Non-negativity → `PosSemidef`.
  - §6. Strict positivity (PosDef) via PSD + det>0 + eigenvalue product.
  - §7. Corollaries (isUnit, inv PosDef, strict-positivity).
  - §8. Abstract Cauchy matrix `cauchyMatrix g` (Mathlib-PR-shaped).
  - §9. Abstract entry-level integral representations.
  - §10. Round 10 milestone summary block.

* `Helpers/V1FieldsCorollary.lean` (extended): V1-instance-shaped
  `glwBoxProb_anderson_upper_field`, direct `gaussianHierCauchy`
  Anderson bound, `realMatrixSqrt` corollaries.

* `Helpers/GaussianHierCauchyBox.lean` (extended): unconditional
  Anderson upper bound theorems.

* `Helpers/GLWBoxProbInstance.lean` (header updated): documents that
  `anderson_upper` is now CLOSED.

* `Helpers/HierCauchyFacts.lean` (header updated): replaces the Round 9
  BLOCKER comment with a closure note.

* `524.lean` (BLOCKER comment updated): notes that the V1 anderson_upper
  field is now unconditionally dischargeable.

## Awaiting Kieran's chat validation.
