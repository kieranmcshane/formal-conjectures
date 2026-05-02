# R46 pre-flight Grok prompt — MGE Full close + Phase 2 sub-gap (A)

**Round R46, Cowork Claude V2 axiom-reduction program (Erdős 524).**

This file is a ready-to-paste validation prompt for Grok / external
oracle review prior to R46. Use it after R45 round closure (commits
`faf3d8d` + `737a831` + `47618db` on branch `track-b-r33cd-gaps`).

---

## Context (binding)

* **Project:** Erdős Problem 524 sorry-free + axiom-free Lean 4
  formalization (`~/Documents/formal-conjectures/`,
  branch `track-b-r33cd-gaps` HEAD `47618db`).
* **R45 outcome:** mid-distribution (-0 sorries, 12 → 12). Phase 2
  body sorry preserved with diagnostic-quality enhancement
  (Path γ skeleton + 3 named sub-gaps). MGE Full close stretch NOT
  attempted (decision per brief's hard-stop rule).
* **R45 audit residual:** the R45-T1.1 framing-verification audit
  caught Q1.a misframing (Grok claimed `Matrix.PosSemidef.det_sqrt`
  in `Mathlib.Analysis.Matrix.Order`; 0 grep hits). Recipe revised
  from ~20-40 LOC bridge to ~30-50 LOC.
* **Current debt:** 5 user-defined axioms + 12 TAG'd sorry sites = 17
  items. Trajectory: R59 ceiling boundary case (zero buffer),
  Q5 BTIS-merge compression option intact for R49.
* **User priority #1:** sorry-free + axiom-free 524.lean. Active.

## R46 mandatory-floor candidate plan (Option C from R45 status doc)

### T1.1 (mandatory): R45 + R46 framing reconciliation audit

* Read R45-T1.1 audit (`R45_T1_FramingVerificationAudit.md`,
  ~353 lines) + R45 status doc (`PhaseV2R45Status.md`, ~297 lines).
* Verify R46 plan's MGE close recipe + Phase 2 sub-gap (A) cost
  estimates against current codebase state.
* Output `R46_T1_PlanVerificationAudit.md` (~30-50 lines).

### T2.1 (mandatory): MGE body Full close (Option C primary)

* Target: `MultivariateGaussianPdf.lean:183`
  (`multivariateGaussian_eq_lebesgue_withDensity`).
* Recipe (per Grok Q1 + R45-T1.1 audit revision):
  * (a) `det_CFC_sqrt_eq_sqrt_det : (CFC.sqrt S).det = Real.sqrt S.det`
    via `CFC.sqrt_mul_sqrt_self` + `Matrix.det_mul` +
    `Real.sqrt_eq_iff_sq_eq`. **~30-50 LOC bridge** (NOT Grok Q1.a's
    20-40; T1.1 audit correction).
  * (b) `stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace ℝ ι`
    via `Measure.pi` + `gaussianReal_of_var_ne_zero` (Mathlib
    `Probability/Distributions/Gaussian/Real.lean:204`) +
    `withDensity_limRatioMeas_eq` (Mathlib
    `MeasureTheory/Covering/Differentiation.lean:642`). ~60-100 LOC.
  * (c) Constant-Jacobian linear pushforward for
    `T = toEuclideanCLM (CFC.sqrt S)` via
    `lintegral_abs_det_fderiv_eq_addHaar_image` (Mathlib
    `MeasureTheory/Function/Jacobian.lean:1100`) + `HasFDerivAt_const`
    + `simp [Matrix.det_const]`. ~40-80 LOC.
  * Composition: ~30-50 LOC.
  * **Total: ~160-280 LOC.** Within hard-math 200-400 LOC single-round
    budget. P~0.50 for full close (Mathlib API verified at all three
    sub-gaps), P~0.35 for partial close (one sub-gap completes).
* Net: -1 sorry if Full (12 → 11).

### T2.2 (mandatory): Phase 2 sub-gap (A) `Matrix.PosDef.isOpen` stretch

* Target: introduce a Full helper lemma in
  `Helpers/MatrixDetDifferentiable.lean` (or a new file
  `Helpers/MatrixPosDefOpen.lean`):
  ```lean
  theorem Matrix.PosDef.isOpen {n : Type*} [Fintype n] [DecidableEq n] :
      IsOpen {S : Matrix n n ℝ | S.PosDef}
  ```
* Closure recipe:
  * `S.PosDef ↔ S.IsHermitian ∧ ∀ x ≠ 0, 0 < x ⬝ᵥ S *ᵥ x`.
  * `IsHermitian` is closed (`{S | S.IsHermitian}` is a closed set:
    intersection over `i, j` of closed `{S | S i j = S j i}`).
  * Wait — `IsHermitian` closed makes `PosDef` set the intersection
    of a closed set with an open set (positive eigenvalues), so
    PosDef is locally closed but NOT open in the full matrix space.
  * **Correct closure**: `Matrix.PosDef` is open in the **affine
    subspace of Hermitian matrices** (not in the full
    `Matrix n n ℝ`). The condition needed for Phase 2 differentiation
    is open-ness in `Matrix n n ℝ` itself — which DOES NOT HOLD.
  * **Subtlety**: the differentiation-under-integral framework
    requires a ball in `Matrix n n ℝ` around `S₀`. Within this ball,
    `S` may not be Hermitian (let alone PosDef). MGI's signature
    requires `S.PosDef`, so the rewrite cannot be transferred via
    `EventuallyEq` on a ball.
  * **Structural fix**: differentiate in the Hermitian subspace, not
    the full matrix space — i.e., restrict the parameter to
    `{S | S.IsHermitian}` (or the symmetric matrix subspace
    `Matrix.SymmetricMatrices` if available). This narrows the
    scope of the Phase 2 statement.
* Estimated LOC: ~30-80 (if Hermitian-subspace route) OR triggers a
  signature change to Phase 2 theorem.
* **Pre-flight question for Grok**: should Phase 2's signature be
  restricted to symmetric/Hermitian matrices? Or is there a way to
  construct the differential in the full matrix space using a
  smooth extension off the PosDef cone?

### T2.3 (mandatory): Build verification + status doc + AXIOM_INVENTORY

* Standard format (~25 LOC).

## R46 pre-flight questions for Grok

**Q1 (high priority):** Is the proposed (a)+(b)+(c) recipe for MGE
Full close still the right path post-R45-T1.1 audit revision? In
particular, does the corrected Q1.a closure
(`CFC.sqrt_mul_sqrt_self` + `Matrix.det_mul` +
`Real.sqrt_eq_iff_sq_eq`) actually compose cleanly, or does it run
into a `Real.sqrt_eq_iff_sq_eq` precondition (`0 ≤ a`) issue
requiring a separate PSD-of-`CFC.sqrt` argument?

**Q2 (CRITICAL):** Phase 2 sub-gap (A) — is `Matrix.PosDef`
open-as-a-subset-of `Matrix n n ℝ`? Or only as a subset of the
Hermitian matrix subspace? If only the latter, does Phase 2's
signature need restriction to `IsHermitian S₀` (or to the symmetric
subspace), and what's the impact on downstream consumers
(`slepian_comparison_finite` in `PhaseAUpperBound.lean`)?

**Q3:** Path γ Phase 2 dominator construction (sub-gap C from R45-T1.1
audit, ~150-300 LOC). Is there a Mathlib API for "Gaussian density on
a positive-definite covariance is uniformly bounded above by a
fixed Gaussian on a neighborhood of the parameter"? Searches at
`Probability/Distributions/Gaussian/` returned only the abstract
`IsGaussian.integrable_id` form, not the closed-form PDF version.

**Q4:** R46 path election. Given the joint MGE close + Phase 2
sub-gap (A) candidate, what's the recommended R46 trajectory?
* (α) MGE only (~180-290 LOC, P~0.50 Full).
* (β) MGE + Phase 2 sub-gap (A) joint (~210-370 LOC, P~0.40 joint Full).
* (γ) MGE only as primary; defer sub-gap (A) to R47.

**Q5:** R46 fallback if MGE close lands as partial. What's the
honest minimum-viable diagnostic enhancement for the MGE Stub that
preserves -0 sorries while advancing audit-trail quality? E.g., port
the (a) sub-gap as a separately-proved Full helper lemma without
inflating the MGE Stub's sorry count.

**Q6 (calibration):** Post-R45 calibration. The hard-math V2
trajectory (R39-R45) has delivered ~0.7 sorries/round on average
(R39: -3, R40-R44: -0,-1,-1,+2,-1, R45: -0). Should Grok recommend
adjusting the R59 ceiling to allow +1-2 round buffer, OR is the
current Q5 BTIS-merge compression option sufficient slack?

---

## Skin-in-the-game framing for R46

* R46 mandatory floor caps at 0 pts if T2.1 MGE body Full close is
  not committed (allowing partial close with TAG'd sub-Stub
  diagnostic).
* R46 caps at 50% if MGE close lands as Stub-quality (no -1 sorry).
* R59 ceiling: 14 rounds remaining post-R46. Trajectory remains
  feasible with Q5 BTIS-merge compression option.
* **Discipline check**: T1.1 audit must again verify framing
  before T2.1 work. Grok-claims-vs-codebase mismatch MUST be caught
  pre-T2.1, not post-T2.1.

---

## Recommended invocation

Paste the prompt above into Grok-4-mini-thinking or Grok-4-think with
the codebase state described.

Expected output: 6 verdicts on Q1-Q6 + recommended R46 trajectory.

---

**File created**: `Helpers/R46_PreFlight_GrokPrompt.md` (~140 lines).
**Status**: ready for R46 pre-flight session.
