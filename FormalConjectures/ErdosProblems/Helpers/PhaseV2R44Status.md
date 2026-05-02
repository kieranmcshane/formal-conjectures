# Phase V2 — R44 Status Doc (V2 round 6: MGI Full close + MGE diagnostic strengthen)

**Round R44 (2026-05-02) — sixth round of V2 axiom-reduction program.**

Branch: `track-b-r33cd-gaps` (descendant of `r33-c-helpers-consolidation`).
Parent commit: `37c671f` (R43-T2.4 build verification + status doc +
AXIOM_INVENTORY).

This round commits:

1. `6cfe27e` — R44-T1.1: brief-vs-reality reconciliation + body-close audit
   (`Helpers/R44_T1_BodyCloseAudit.md`).
2. `6783d38` — R44-T2.2: MGI body Full close (orthant CDF as Lebesgue
   integral via `withDensity` bridge).
3. `313507c` — R44-T2.1: MGE diagnostic strengthen (single TAG'd Stub
   retained, decomposed (a)+(b)+(c) recipe + LOC estimates).

This file (R44-T2.3): build verification + status doc + AXIOM_INVENTORY
update.

---

## TL;DR

R44 lands the **mid-distribution** outcome of the brief's confidence
prediction (joint mandatory floor estimated P~0.45 for "both Full" vs
realistic P~0.50 for "MGI Full + MGE strengthened"; T1.1 audit revised
estimates downward given the brief's misframed Q1/Q2 scope). Concretely:

* **MGI body Full close.** R43-T2.1 Stub
  `multivariateGaussianOrthantCDF_eq_lebesgue_integral` retired to a Full
  Lean proof (~50 LOC, no `sorry`). Closure routes through MGE as a
  black-box hypothesis via `Measure.real_def` + `withDensity_apply` +
  reverse `integral_eq_lintegral_of_nonneg_ae`. Continuity of the
  integrand `y ↦ pdf S (fun i => y i)` proved inline via
  `PiLp.continuous_apply`, `Continuous.dotProduct`, and
  `Continuous.matrix_mulVec`.

* **MGE diagnostic strengthen.** Brief's Grok Q1 "Jacobi formula" close
  is structurally misframed (the file's MGE is a measure-theoretic
  pushforward equality, not a det-derivative). T1.1 audit reconciles
  this. The MGE body is left as a TAG'd Stub (single `sorry`,
  debt-neutral) with a decomposed (a)+(b)+(c) recipe for closure
  (~180-300 LOC across the three measure-theoretic gaps), each gap with
  concrete Mathlib API lookup evidence at pin `25ce63313608`.

* **Audit + status docs.** `R44_T1_BodyCloseAudit.md` (221 lines)
  + this file (R44-T2.3).

**Total R44 LOC**: ~340 LOC across audit + theorem code +
diagnostic strengthening + status. Within Grok Q5 budget (250-450 LOC
for split delivery).

---

## R44 deliverables

### T1.1 (mandatory) — audit
**File**: `Helpers/R44_T1_BodyCloseAudit.md`
**Status**: complete (221 lines).
**Content**: brief-vs-reality reconciliation (Grok Q1/Q2 misframing
documented), realistic R44 scope per file content + R43 trajectory,
revised confidence estimates per stub, MGI-first ordering rationale
+ R59 ceiling impact analysis.

### T2.2 (mandatory, prioritized first) — MGI body Full close
**File**: `Helpers/MultivariateGaussianPdf.lean:226-282`
**Status**: Full Lean proof, no `sorry`. ~50 LOC body.

```lean
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) (x : ι → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i} =
      ∫ y in {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i},
        multivariateGaussianPdf S (fun i => y i)
```

Proof composes:
* Orthant `{z | ∀ i, z i ≤ x i} = ⋂ i, (proj i)⁻¹' Iic (x i)` measurable
  via `MeasurableSet.iInter` + `(PiLp.continuous_apply 2 i).measurable`.
* Apply MGE (TAG'd Stub) to rewrite measure as `volume.withDensity (...)`.
* Unfold `Measure.real` to `(...).toReal` via `Measure.real_def`.
* Apply `withDensity_apply _ h_meas` to convert measure-of-set to
  `∫⁻ y in orthant, ENNReal.ofReal (pdf …) ∂volume`.
* Reverse `integral_eq_lintegral_of_nonneg_ae` using
  `multivariateGaussianPdf_nonneg` + continuity-derived
  `AEStronglyMeasurable`.

Continuity of `y ↦ pdf S (fun i => y i)`:

```lean
unfold multivariateGaussianPdf
refine Continuous.mul (continuous_const.mul continuous_const) ?_
refine Real.continuous_exp.comp ?_
refine continuous_const.mul ?_
-- Continuity of `y ↦ y ⬝ᵥ S⁻¹ *ᵥ y`.
have h_y_pi : Continuous (fun y : EuclideanSpace ℝ ι => fun i : ι => y i) :=
  continuous_pi (fun i => PiLp.continuous_apply (β := fun _ : ι => ℝ) 2 i)
exact h_y_pi.dotProduct (continuous_const.matrix_mulVec h_y_pi)
```

### T2.1 (mandatory, attempted second) — MGE diagnostic strengthen
**File**: `Helpers/MultivariateGaussianPdf.lean:183-279`
**Status**: TAG'd Stub retained (single `sorry`, debt-neutral). Body
comment expanded with R44 verification + decomposed closure recipe.

R44-specific additions to body comment:

* **Verification at pin `mathlib4 @ 25ce63313608` + `brownian-motion` HEAD**:
  - `det_CFC_sqrt`, `det_sqrt`, `Matrix.det.*sqrt`: 0 hits.
  - `stdGaussian.*=.*withDensity`, `stdGaussian.*lebesgue`: 0 hits in
    `BrownianMotion/Gaussian/`. Only special-case
    `multivariateGaussian_zero_one`.
  - General non-linear C¹ change-of-variables packaged
    (`integral_image_eq_integral_abs_det_jacobian_smul_of_injOn`); no
    constant-Jacobian linear specialisation for
    `T = toEuclideanCLM (CFC.sqrt S)`.

* **Decomposed closure recipe (R45+ scope)**:
  - (a) `det_CFC_sqrt_eq_sqrt_det`: `(CFC.sqrt S).det = Real.sqrt S.det`
    via `CFC.sqrt_mul_sqrt_self` + `Matrix.det_mul`. Estimated
    ~30-50 LOC.
  - (b) `stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace ℝ ι`
    via `Measure.pi` + `gaussianReal_of_var_ne_zero` + basis-sum
    unwinding. Estimated ~80-120 LOC.
  - (c) Constant-Jacobian linear pushforward via
    `MeasurePreserving.set_lintegral_comp` + `addHaar_smul`. Estimated
    ~40-80 LOC.
  - Composition: ~30-50 LOC.
  - **Total**: ~180-300 LOC.

The R44 brief's Grok-derived 80-120 LOC + P~0.75 estimate was based on
the misframed Jacobi-formula scope (referring to `Matrix.det.hasFDerivAt`
in `MatrixDetDifferentiable.lean`) and does not apply.

### T2.3 — Build verification (this commit)
`lake env lean` clean on:
* `Helpers/MultivariateGaussianPdf.lean`: 1 sorry warning (MGE @ 183)
  — was 2 (MGE @ 183 + MGI @ 226), MGI retired Full.
* `Helpers/MultivariateGaussianCDF.lean`: 2 sorry warnings (R41-T2.1
  @ 160, R35-T2.1 @ 274) — unchanged.
* `Helpers/MatrixDetDifferentiable.lean`: 2 sorry warnings (R40-T2.1
  @ 124, 141) — unchanged.
* `Helpers/PhaseAUpperBound.lean`: 1 sorry warning
  (`slepian_comparison_finite` @ 363) — unchanged.
* `Helpers/GLWUpperProof.lean`: 1 sorry warning (R39 @ 302) — unchanged.
* `Helpers/GLWLowerProof.lean`: 2 sorry warnings (Karhunen-Loève gaps
  @ 357, 381) — unchanged.

All R38 + R39 + R40 + R41 + R42 + R43 milestones preserved. The
R33-D-T2.2 form-β-to-full-sum bridge `sorry` at 524.lean:3889 (per
R43 build log; under uncommitted local edits inherited from prior
session, no R44 modifications) remains unchanged.

---

## Net debt

| Metric | Pre-R44 | Post-R44 | Δ |
|---|---|---|---|
| User-defined axioms | 5 | 5 | 0 |
| TAG'd `sorry` sites | 13 | 12 | **−1** |

**Δ breakdown**:
- T2.2 MGI Full close: -1 sorry (`MultivariateGaussianPdf.lean:226`
  retired). **−1 sorry**.
- T2.1 MGE diagnostic strengthen: 0 net change (single sorry
  retained). **0 sorries**.
- T1.1 + T2.3: doc-only, no code modification. **0 sorries**.
- **Net: −1 sorry**.

This matches the T1.1 audit's "realistic forecast" P~0.50 outcome
("MGI Full + MGE strengthened diagnostic") and falls below the brief's
optimistic "−2 sorries" forecast (P~0.05 in audit's revised estimate
given Grok Q1/Q2 misframing).

---

## R45 trajectory

R44 closes only MGI (the cheap consumer wrapper); MGE remains the
load-bearing measure-theoretic gap. R45 picks up either:

**Option A (per brief's prior R45 plan):** R45 = Phase 2 only (CDF
differentiability Full body via diff-under-integral + MGE+MGI). Now
that MGI is Full, this route still depends on MGE Stub as a black-box.

**Option B (revised per R44 reality):** R45 = MGE body close (gap (a)
+ gap (b)). Each gap is independently formalisable in ~30-120 LOC; the
joint sub-round is ~110-170 LOC and within Grok's 200-400 LOC empirical
hard-math single-round ceiling.

**Option C (split):** R45 = gap (a) + gap (c) (Jacobian + change-of-
variables, ~70-130 LOC); R46 = gap (b) (stdGaussian density, ~80-120
LOC) + composition (~30-50 LOC) ⇒ MGE body Full closes in R46.

Recommendation: Option B for R45 if R44 momentum holds; otherwise
Option C with explicit BTIS-merge buffer claim.

R59 ceiling check (post-R44):

| Phase | Round range | Total | Δ sorry / axioms |
|---|---|---|---|
| **R44** (this round) | 1 | 1 | -1 sorry |
| R45 (MGE body close, Option B preferred) | 1 | 1 | -1 sorry (MGE → Full) |
| R46 (Phase 2 — CDF Full body via MGE+MGI black-box) | 1 | 1 | -1 sorry (R35-T2.1 → Full) |
| R47 (Slepian body close) | 1 | 1 | -1 sorry |
| R48 (SF + truncation) | 1 | 1 | -1 sorry |
| **R49 BTIS-merge** | 1 | 1 | +1 axiom (BTIS), -2 sorries (Phase A upper consolidation) |
| R50–R54 (1D KMT cluster + R33-C/D Mathlib gaps) | 5 | 5 | -3 sorries, -2 axioms |
| R55–R58 (BTIS honest body) | 4 | 4 | -1 axiom |
| R59 buffer | 1 | 1 | (slack) |
| **Total** | 16 rounds | 16 rounds | sorries → 0; axioms → 0 |

Tighter than R43 status's 17-round forecast (R44 -1 instead of -3
sorries shifts +1 round demand). Buffer reduces from 1 round to 0
rounds at R59 (boundary case). Q5 BTIS-merge compression option
absorbs slip if Phase A upper pieces compress in R49.

If MGE body close at R45 is Full (Option B): trajectory closes
cleanly at R58 (1 round buffer recovered).

If MGE body close at R45 is partial / Option C split: trajectory
closes exactly at R59 with zero buffer.

---

## Skin-in-the-game ledger (R44 outcome vs T1.1 audit's revised confidence)

T1.1 audit's R44 confidence prediction (revised per brief misframing):

| Outcome | P(Full) audit | R44 actual |
|---|---|---|
| T1.1 audit | 0.95 | ✅ Full (221 lines) |
| T2.2 MGI body Full close | 0.50 | ✅ Full |
| T2.1 MGE body Full close | 0.10-0.15 | ✘ TAG'd Stub (debt-neutral diagnostic strengthen) |
| T2.3 build + status | 0.95 | ✅ Full |

**Joint mandatory floor**: T1.1 audit estimate "at least −1 sorry"
P~0.50, "−2 sorries" P~0.05. R44 actual: −1 sorry (MGI Full + MGE
strengthened). This matches the audit's mid-distribution prediction
and the brief's discipline rule for "TAG'd partial accepted as honest
outcome".

**Brief's confidence (pre-audit-revision)**: P~0.45 for joint Full
across T2.1 + T2.2. The brief's estimate reflected the misframed Q1
scope (Jacobi formula ~80-120 LOC instead of measure-theoretic
pushforward ~150-200 LOC); not applicable to actual scope.

---

## Conclusion

R44 lands MGI Full close + MGE diagnostic strengthen — the
realistic-forecast mid-distribution outcome of the T1.1 audit. The
brief's optimistic "both Full" target was based on misframed Grok Q1/Q2
scope and was unreachable in single-round work given the 3 measure-
theoretic Mathlib gaps. The R44-T1.1 audit + R44 build verify lock the
audit-trail honestly:

* MGI is now Full Lean (no `sorry`); the consumer-facing alternative
  spelling for the orthant CDF is unblocked for R45+ work.
* MGE retains a single TAG'd Stub with decomposed (a)+(b)+(c) recipe,
  each gap with concrete LOC estimate and Mathlib API search citation
  — substantially advancing the audit-trail without inflating sorry
  count.

R59 ceiling preserved at boundary (zero buffer if MGE Option C splits
across R45+R46; one round buffer if Option B Full at R45). Q5
BTIS-merge compression option reserved for Phase A upper consolidation
at R49.

Next round (R45): MGE body close attempt (Option B preferred —
~110-170 LOC for joint (a)+(b)+(c)+composition, within hard-math
single-round ceiling). If split needed, Option C via gap (a)+(c) at
R45 + gap (b)+composition at R46.
