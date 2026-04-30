# Round 9 Outcomes — Local Claude reporting

**Committed after round end.**

## Resolution proposal for Cowork Claude predictions

| # | Prediction | Outcome | Resolution | Delta proposed |
|---|------------|---------|------------|---------------|
| 1 | central sorry CLOSED | YES | `mvGaussian_box_density_at_mode_bound` is fully proven (no sorry), via new chain: `mvGaussianFromPosDef_apply_eq` → `standardMVGaussian_le_volume_smul` → `volume_realMatrixSqrt_mulVec_preimage` → `volume_anisotropic_box`. Sub-sorry on `standardMVGaussian_le_volume_smul` was also closed using new Tonelli lemma `lintegral_fintype_prod_eq_prod`. | +30 |
| 2 | ≥250 lines substantive | YES | actual: +639 / −59 (net +580) lines across 10 files; main file `Helpers/MVGaussianDensityBound.lean` grew from 207 to 719 lines. | +20 |
| 3 | full 524 build green | YES | `lake build FormalConjectures.ErdosProblems.«524»` succeeds in 8009 jobs. | +5 |
| 4 | no new axiom | YES | axiom count unchanged at 2 (`two_dim_KMT_coupling`, `Y_GLW_exists`). | +10 |
| 5 | hit time floor | PARTIAL | START 01:43:11, END_TARGET 03:13:11, actual STEP-N completion 03:10:17 (~2 min 54 sec early, 96.8% of allocated time). 29 substantive commits, +580 net lines, no Round 8-style early stop — but did not strictly reach END_TARGET wall-clock. Honest reporting per stake protocol. | +20 (partial credit) |
| 6 | new Mathlib lemma identified | YES | Multiple: `Matrix.PosSemidef.det_sqrt`, `RCLike.sqrt_real`, `Real.map_matrix_volume_pi_eq_smul_volume_pi`, `Matrix.PosDef.diagonal`, `MeasureTheory.lintegral_prod_mul`, `MeasureTheory.measurePreserving_piFinSuccAbove`, `MeasureTheory.measurePreserving_piCongrLeft`. | +25 |

**Total Cowork Claude delta: +30 +20 +5 +10 +20 +25 = +110 units gained.**

## Resolution proposal for Local Claude stake

- **Time-floor stake (200 units)**: actual session τ = 96.8% of allocated time (~3 min early). Per linear interpolation of the stake schedule (100% → 0, 70% → −60), penalty ≈ −6 units for 3.2% early. Delta proposed: **−6**.
- **Substance stake (100 units)**: actual commits = 29 (>> 6 required); each commit ≥15 lines or substantive content. Delta proposed: **0** (no penalty).
- **Discovery bonus**: claimed for closing `pi_withDensity_eq_withDensity_pi` — a genuine Mathlib gap that the Round 9 prompt explicitly suggested as a stretch goal. Delta proposed: **+50**.

**Total Local Claude delta: −6 + 0 + 50 = +44 units gained.**

## New balances proposed

- Cowork Claude: 1000 + 110 = **1110**
- Local Claude: 1000 + 44 = **1044**

## Round 9 substantive deliverables

Closed `sorry`s:

* `mvGaussian_box_density_at_mode_bound` (was Round 6 residual sorry, headline target).
* `standardMVGaussian_le_volume_smul` (intermediate sub-sorry introduced in Commit 4 to localize the gap, then closed in Commit 6).

New consumer-facing API (all sorry-free):

* `mvGaussian_box_density_at_mode_bound` — anisotropic, `(√(2π))⁻¹^n` form.
* `mvGaussian_box_density_at_mode_bound_rpow` — anisotropic, `(2π)^(-n/2)` form.
* `mvGaussian_isotropic_box_density_at_mode_bound` — isotropic ε.
* `mvGaussian_isotropic_box_density_at_mode_bound_rpow` — isotropic ε, `(2π)^(-n/2)` form (V1 instance shape).
* `mvGaussian_box_density_at_mode_bound_one` — identity covariance specialisation.
* `glwBoxProb_anderson_upper_via_round9_mm` — V1-instance-shaped Anderson upper for `glwBoxProb`, conditional on `(hierCauchyG m).PosDef`.

New Mathlib-PR-ready lemmas (all sorry-free):

* `lintegral_fin_nat_prod_eq_prod_aux` — Fin n Tonelli for ENNReal integrands on `Measure.pi μ`.
* `lintegral_fintype_prod_eq_prod` — Fintype version.
* `setLIntegral_fintype_prod_pi_eq_prod` — rectangle-restricted form.
* `pi_withDensity_eq_withDensity_pi` — pi/withDensity commutation.

New PosDef constructors / scalar identities:

* `realMatrixSqrt_det` (= `Real.sqrt M.det`).
* `realMatrixSqrt_det_pos`, `realMatrixSqrt_det_ne_zero`, `realMatrixSqrt_isUnit`.
* `volume_mulVec_preimage`, `volume_realMatrixSqrt_mulVec_preimage` — Lebesgue Jacobian under `mulVec`.
* `mvGaussianFromPosDef_apply_eq`, `mvGaussianFromPosDef_box_apply_eq` — change of variables.
* `anisotropic_box_measurable`, `volume_anisotropic_box`, `volume_anisotropic_box_lt_top`.
* `smul_one_PosDef` — `(c • 1).PosDef` for `c > 0`.
* `measurable_prod_gaussianPDF`, `prod_gaussianPDF_le`, `standardMVGaussian_eq_withDensity`.

Cleanup commits (no behaviour change):

* Linter warnings cleaned in `MVGaussianRotation.lean`, `StandardMVDensityBound.lean`, `GLWBoxProbInstance.lean`, `GLWUpperProof.lean`, `CentralBinomWindowSum.lean`, `524.lean`.
* BLOCKER docblocks updated in `GLWLowerProof.lean`, `524.lean`, `GLWBoxProbInstance.lean`, `HierCauchyFacts.lean` to reflect that the Round 6 PosDef Anderson sorry is now closed.

## Awaiting Kieran's chat validation.
