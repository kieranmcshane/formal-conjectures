# R47 Track A pre-flight Grok prompt — math-reasoning validation

**Round:** R47 Track A (mainline). **Drafted at:** R46 close (T3.2 stretch).

**Process Q4 ii binding:** Local Claude T1.1 grep audit comes FIRST in
R47; this Grok prompt provides math-reasoning recipes that Local Claude
will VERIFY against pinned Mathlib state independently.

---

## Round-context summary (paste-ready for Grok)

We are formalising Erdős Problem 524 in Lean 4. Project state at R47
start:

* **5 user-defined axioms** (unchanged across R44-R46).
* **12 TAG'd sorries** (unchanged across R44-R46).
* **Total debt:** 17 items.
* **Hybrid (c) gate:** R52 milestone — if debt > 8 items, lock R54 +
  BTIS axiom (Path A pragmatic ship). Required pace R47-R50:
  1.875-2.5/round (recovery from R46 0/round below pace).
* **Aspirational target:** R59 pure axiom-free.

R46 Track A (last round) landed:
* T1.1 grep audit catching Grok Q2 framing error.
* MGE sub-gap (a) `det_CFC_sqrt_eq_sqrt_det` Full close (~30 LOC).
* MGE sub-gap (c) constant-Jacobian linear pushforward verified as
  DIRECT application of `map_linearMap_addHaar_eq_smul_addHaar`
  (`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:234`).
* PosDef minimum-eigenvalue helpers Full close (~40 LOC; correct
  framing of "Matrix.PosDef.isOpen" claim).
* GaussianParametricAnalysis cross-track synergy library extracted.

Net R46 retirement: 0 sorries (foundational infrastructure round).

---

## Grok consultation questions (R47 scope decision)

### Q1 — R47 scope candidate selection

Three plausible R47 scopes:

(a) **MGE sub-gap (b) Full close** — `stdGaussian_eq_lebesgue_withDensity`
    on EuclideanSpace ℝ ι, composing with sub-gap (a) Full + sub-gap
    (c) ApplyDirect to retire MGE main Stub. Estimated ~80-120 LOC for
    (b) + ~50 LOC composition. **Retires 1 sorry**: MGE Stub Full close.
    Side-effect: enables Phase 2 body close (R48 candidate) by
    completing the dependency chain.

(b) **Phase 2 body Full close** — `multivariateGaussianOrthantCDF_differentiableAt_along_Sα_path`
    Full close via diff-under-integral `hasFDerivAt_integral_of_dominated_loc_of_lip`.
    Requires three sub-gaps:
    - (A) PosDef "isOpen" — R46 partially addressed via min-eigenvalue
      helpers; full local-stability still needed (~50-80 LOC).
    - (B) Integrability of `multivariateGaussianPdf S` on `orthant x` —
      uses uniform Gaussian tail (~50-100 LOC).
    - (C) Lipschitz envelope on PosDef neighborhood (~150-300 LOC,
      load-bearing).
    Estimated ~300-450 LOC total. **Retires 1 sorry**: Phase 2 Stub
    Full close.

(c) **Both (a) and (b) in R47** — combined scope ~430-620 LOC.
    **Retires 2 sorries** in single round, recovering pace target.
    Risk: combined scope is large for single round.

**Question 1**: which R47 scope is highest-leverage given:
* Hybrid (c) gate at R52 needs 1.875-2.5 retirements/round average.
* R46 was at 0/round below pace; recovery pressure on R47.
* Sub-gap (b) for MGE is a Bottleneck per Grok R46 Q1 verdict.
* Phase 2 (B)+(C) require uniform Gaussian tail (T3.1 R46 stretch
  documented but not landed as Full).
* MGE composition does NOT depend on Phase 2 helpers; independent.

Single best recommendation + reasoning chain.

### Q2 — sub-gap (b) `stdGaussian_eq_lebesgue_withDensity` recipe verification

R45-T1.1 verified the recipe outline at-Mathlib:
* `stdGaussian (EuclideanSpace ℝ ι) = (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (basis-sum)`
  via `BrownianMotion/Gaussian/MultivariateGaussian.lean:145`
  (`stdGaussian_eq_pi_map_orthonormalBasis`).
* `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)` via
  `Mathlib/Probability/Distributions/Gaussian/Real.lean:202`
  (`gaussianReal_of_var_ne_zero`).

The remaining gap is composition: `Measure.pi (fun _ ↦ μ.withDensity (f ·))
= (Measure.pi (fun _ ↦ μ)).withDensity (∏ i, f i ·)` (product-measure
factorization through density).

**Question 2**: confirm:
(i) The product-measure-density factorization is the right route.
(ii) Whether Mathlib has `Measure.pi.withDensity_pi` or equivalent
     (R46 grep audit was inconclusive; verify at pin).
(iii) Estimated LOC if NOT in Mathlib (~30-50 bridge?). Net (b) close
      then ~80-150 LOC.
(iv) Alternative routes: does `MeasureTheory.integral_prod` +
     `integral_eq_lintegral_of_nonneg_ae` provide a shortcut?

### Q3 — Phase 2 body sub-gap (C) Lipschitz envelope

Sub-gap (C) (Lipschitz-on-PosDef-neighborhood with integrable Lipschitz
envelope) is the load-bearing part of Phase 2 body. R45-T1.1 estimated
~150-300 LOC alone, citing requirements:
* Explicit Fréchet derivative formula chain for `S ↦ pdf S y` (chain
  rule on the closed-form formula).
* Uniform Gaussian-tail bound on the derivative norm (uniform across
  `S` in a PosDef neighborhood).

The Fréchet derivative formula for `(2π)^(-n/2) (det S)^(-1/2) exp(-x^T
S^(-1) x / 2)` involves:
* `Matrix.det.differentiable` (R40 Stub, MatrixDetDifferentiable.lean).
* `Matrix.PosDef.inv_hasFDerivAt` (R41 Full,
  `MatrixDetDifferentiable.lean:200`).
* `Real.sqrt` differentiability at positive args (Mathlib).
* `Real.exp.differentiable` (Mathlib).
* Bilinear form `x^T A x` differentiability in A.

**Question 3**: is there a more concise route to the Lipschitz envelope
that BYPASSES the explicit Fréchet derivative? E.g., a direct
`LipschitzOnWith` argument from operator-norm bounds on the inverse
covariance + Cauchy-Schwarz on the quadratic form? This could shave
~100 LOC and accelerate R47 closure.

### Q4 — R47 retirement target alignment

Given:
* R46 actual: 0 retirements.
* Required pace R47-R50: 1.875-2.5/round to keep R52 gate viable.
* Hybrid (c) Path B aspirational target: R59 pure axiom-free.

If R47 scope = (a) only (1 retirement): R47-R50 must average
2.33-3.0/round. Realistic?

If R47 scope = (c) combined (2 retirements): R47-R50 must average
1.5-2.17/round. More feasible per-round but R47 itself becomes high-risk
(P~0.30 single-round Full close per audit precedent for ~500 LOC
scopes).

If R47 scope = (a) + Track B retry (post-MGE-completion): MGE Full
unlocks 2-3 R33-C/D Mathlib gaps in Track B parallel work. Combined
1+2 = 3 retirements feasible in single round?

**Question 4**: best R47 strategic choice given retirement constraints?

### Q5 — Cross-track synergy followup

R46-T3.1 extracted `GaussianParametricAnalysis.lean` library with R46
Full helpers. Track C (1D KMT) and Track D (BTIS honest) round 2 are
candidates to consume this library.

**Question 5**: 
(i) For Track C round 2 quantile measurability, which R46 helpers are
    DIRECTLY consumed vs which are foundation-only?
(ii) For Track D round 2 Herbst density chain rules, which?
(iii) Should Track C/Track D round 2 wait for R47 closure (MGE Full)
      to consume `multivariateGaussianPdf` properly, or proceed
      independently with current helpers?
(iv) Is there cross-track synergy compression that would help R47 +
     Track C round 2 + Track D round 2 land together (e.g., via a
     parallel R47 + Track C/D round 2 dispatch)?

---

## Validation expectations

For each Q1-Q5:
- A single best recommendation.
- A short reasoning chain (≤ 5 steps).
- Concrete cost estimate (LOC) + Brier-honest Full-close probability.
- Identification of any speculative claims (formal-Mathlib API, etc.) for
  Local Claude T1.1 to verify independently before R47 begins.

**Format**: response under 1500 words, structured by question.

**Process Q4 ii reminder**: ANY claim about Mathlib API at the pin
(`mathlib4 @ 25ce63313608`) MUST be flagged for T1.1 verification.
Three consecutive rounds (R44, R45, R46) caught misframed claims:
- R44: Jacobi-formula description of MGE.
- R45: `PosSemidef.det_sqrt` claimed in Mathlib.
- R46: `Matrix.PosDef.isOpen` in full matrix space.

Pre-flight pattern shows Grok reliable for math reasoning, less reliable
for formal-Mathlib API claims. Flagging speculative formal claims keeps
the audit pipeline efficient.

---

**End R47 pre-flight prompt.** To be sent to Grok at R47 round start.
Local Claude T1.1 grep audit commences IMMEDIATELY upon Grok response,
verifying every formal-Mathlib API claim independently.
