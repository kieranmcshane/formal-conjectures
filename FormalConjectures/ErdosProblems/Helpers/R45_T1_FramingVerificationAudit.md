# R45-T1.1 — Framing verification audit (Path γ + MGE Full stretch)

**Round R45 (2026-05-02), Cowork Claude.**

This audit verifies the R45 brief's Grok pre-flight Q1+Q3 claims against
the codebase at branch `track-b-r33cd-gaps` HEAD `8d5b669` (R44-T2.3
build verification + status doc), per behavioural-rule "framing
verification mandatory in T1.1 (lesson from R40 + R44)."

The audit confirms what the R45 brief got structurally right, flags
two concrete misframings, and revises the round's confidence
predictions accordingly.

---

## 1. Codebase ground truth (post-R44)

### Active TAG'd sorry sites (12 total per R44 status)

Verified by `grep -rn "  sorry" Helpers/*.lean Erdos524/*.lean 524.lean`
restricted to TAG'd inventory entries (`AXIOM_INVENTORY.md` lines
174–248):

| # | Site | TAG | R44 closure status |
|---|---|---|---|
| 1 | `TwoDimKMTFromOneDim.lean:609` | R33-C iIndepFun-prod | unchanged |
| 2 | `TwoDimKMTFromOneDim.lean:885` | R33-C uncorrelated-indep | unchanged |
| 3 | `524.lean:3933` | R33-D form-β-to-fullsum bridge | unchanged (line drift from `:3913` to `:3933`) |
| 4 | `PhaseAUpperBound.lean:509` | R41-T2.2 Slepian via Stein | unchanged |
| 5 | `MultivariateGaussianCDF.lean:199` | R35-T2.1 mathlib-gap-density (**Phase 2 target**) | unchanged |
| 6 | `MultivariateGaussianCDF.lean:290` | R41-T2.1 bivariate-density-conditional (MGP) | unchanged |
| 7 | `GLWLowerProof.lean:357` | R39 Yplus IsGLW | unchanged |
| 8 | `GLWLowerProof.lean:381` | R39 Yminus IsGLW | unchanged |
| 9 | `GLWUpperProof.lean:302` | R39 Yplus IsGLW upper | unchanged |
| 10 | `MatrixDetDifferentiable.lean:132` | R40 det.hasFDerivAt | unchanged |
| 11 | `MatrixDetDifferentiable.lean:149` | R40 det.differentiable wrapper | unchanged |
| 12 | `MultivariateGaussianPdf.lean:268` | R43 MGE pushforward (**MGE stretch target**) | unchanged |

R44 retired the MGI variant
`MultivariateGaussianOrthantCDF_eq_lebesgue_integral`
(`MultivariateGaussianPdf.lean:278-344`) Full — verified `grep "sorry"`
on that block returns 0 hits.

### Active user-defined axioms (5 total)

Verified by `grep "^axiom"`:
1. `Cp_T_explicit_pointwise_axiom` (D2)
2. `one_dim_KMT_coupling` (`Helpers/OneDimKMT.lean:101`)
3. `kmt_aided_gaussian_process` (`Helpers/StochasticProcessAxiom.lean:100`)
4. `gao_li_wellner_small_ball_lower` (`524.lean:3643`)
5. `gao_li_wellner_small_ball_upper` (`524.lean:3574`)

Net debt at R45 start: **5 axioms + 12 sorries = 17 items.**

---

## 2. Grok Q1 verification (MGE 3 sub-gaps revisited)

### Q1.a `det_CFC_sqrt_eq_sqrt_det` — Grok claimed: `Matrix.PosSemidef.det_sqrt` already in `Mathlib.Analysis.Matrix.Order`

**Verification.** `grep -rn "det_sqrt\|PosSemidef.*sqrt.*det" .lake/packages/mathlib/Mathlib/`
returns **0 hits**. The claimed lemma `Matrix.PosSemidef.det_sqrt` does
NOT exist in Mathlib at the project pin.

**However**, `Matrix.PosSemidef.sqrt_one` exists in brownian-motion at
`BrownianMotion/Gaussian/MultivariateGaussian.lean:322`. The recipe
ingredient `(CFC.sqrt S) * (CFC.sqrt S) = S` (`CFC.sqrt_mul_sqrt_self`)
is available in CFC infrastructure. Closure of
`(CFC.sqrt S).det = Real.sqrt S.det` requires:
1. `Matrix.det_mul` (Mathlib, packaged) ⟹ `(CFC.sqrt S).det^2 = S.det`.
2. `Real.sqrt_eq_iff_sq_eq` (Mathlib, packaged) + `0 ≤ (CFC.sqrt S).det`
   from `CFC.sqrt` PSD-of-PSD inheritance.

Estimated LOC: ~30-50 (matches R44 audit, NOT Grok Q1.a's "20-40"). The
sub-gap is real but small.

**Verdict: Q1.a MISFRAMED** (claimed Mathlib API doesn't exist), but the
underlying close-route is sound. Net effect on stretch budget: +10-20 LOC.

### Q1.b `stdGaussian_eq_lebesgue_withDensity` — Grok claimed: VitaliFamily.withDensity_limRatioMeas_eq route, 60-100 LOC

**Verification.** `withDensity_limRatioMeas_eq` IS in Mathlib at
`MeasureTheory/Covering/Differentiation.lean:642`:

```lean
theorem withDensity_limRatioMeas_eq : μ.withDensity (v.limRatioMeas hρ) = ρ
```

`gaussianReal_of_var_ne_zero` IS in Mathlib at
`Probability/Distributions/Gaussian/Real.lean:204`:

```lean
gaussianReal μ v = volume.withDensity (gaussianPDF μ v)
```

Both ingredients confirmed available. The route is genuine. The
challenge is the `EuclideanSpace ℝ ι ↔ (ι → ℝ)` identification +
`Measure.pi_withDensity` chain.

**Verdict: Q1.b CORRECT.** Route confirmed feasible. LOC estimate
60-100 plausible if `Measure.pi_withDensity` for product densities
unwraps cleanly; could inflate to 100-150 if custom unwinding needed.

### Q1.c Constant-Jacobian linear pushforward — Grok claimed: `lintegral_abs_det_fderiv_eq_addHaar_image`, 40-80 LOC

**Verification.** `lintegral_abs_det_fderiv_eq_addHaar_image` IS in
Mathlib at `MeasureTheory/Function/Jacobian.lean:1100`. Confirmed.

For a constant-derivative linear map `T = toEuclideanCLM (CFC.sqrt S)`,
applying this lemma with `f' = T.toLinearMap` and using
`HasFDerivAt_const`-style unfolding gives the Jacobian-pushforward
formula. Route is sound.

**Verdict: Q1.c CORRECT.** Route confirmed feasible. LOC estimate
40-80 plausible.

### Combined Q1 verdict

- Q1.a underestimated (no exact Mathlib lemma; ~30-50 LOC bridge).
- Q1.b confirmed (~60-100 LOC).
- Q1.c confirmed (~40-80 LOC).
- Composition (~30-50 LOC).

**Revised MGE Full total**: ~160-280 LOC (Grok said 170-270 — agreement
within tolerance). The R44 audit estimate (180-300 LOC) is also within
tolerance. **No revision to MGE stretch feasibility needed.**

---

## 3. Grok Q3 verification (Phase 2 dependency on MGI vs MGE)

### Q3 claim (verbatim from brief)
> "MGI Full alone is sufficient. Phase 2 body = parametric
> differentiability of orthant integral; integrand derivative is
> `HasFDerivAt` of `multivariateGaussianPdf` w.r.t. Σ — provided by
> MGI Full directly. MGE (pushforward measure equality) only needed
> for Gaussian probability definition, NOT for PDF derivative under
> integral. Treat MGE stub as axiom-equivalent oracle for Phase 2."

### Verification

**Partially MISFRAMED.** Re-reading MGI's signature
(`MultivariateGaussianPdf.lean:278`):

```lean
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) (x : ι → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i} =
      ∫ y in {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i},
        multivariateGaussianPdf S (fun i => y i)
```

MGI gives the **rewrite of the orthantCDF as a Lebesgue integral**.
It does NOT provide `HasFDerivAt` of `multivariateGaussianPdf`
wrt `S`. The latter is a separate fact, derived by chaining:
- `Matrix.det.hasFDerivAt` (R40 stub @ `MatrixDetDifferentiable.lean:124`)
- `Matrix.PosDef.inv_hasFDerivAt` (R41 Full @ `MatrixDetDifferentiable.lean:200`)
- with the closed-form `multivariateGaussianPdf` formula.

**However, Grok's USE of the framing is correct in shape:** Phase 2 closure
proceeds by (i) MGI rewrite, then (ii) diff-under-integral, then (iii)
chain through R40/R41 stubs for the integrand. Grok's "Treat MGE as
axiom-equivalent" advice applies because MGI internally uses MGE as a
black box (R44-T2.2 `rw [multivariateGaussian_eq_lebesgue_withDensity]`),
and the Phase 2 proof chains through MGI without needing MGE again.

**Net verdict on Q3**: claim *attribution* is wrong (MGI doesn't
"provide" pdf-derivative), but *operational guidance* (use MGI rewrite
+ diff-under-integral, treat MGE as axiom-equivalent) is correct.
Phase 2 body proceeds via the chain. **No revision to Path γ
feasibility from Q3 alone.**

---

## 4. Mathlib API check for diff-under-integral

Phase 2 (Path γ) requires `MeasureTheory.hasFDerivAt_integral_of_dominated_loc_of_lip`.
Verified at `Mathlib/Analysis/Calculus/ParametricIntegral.lean:164`:

```lean
theorem hasFDerivAt_integral_of_dominated_loc_of_lip {F' : α → H →L[𝕜] E}
    (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a)
      (F · a) (ball x₀ ε))
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧
      HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀
```

This is the right tool for Path γ. The hypotheses required for our
setting (with `F : Matrix ι ι ℝ → EuclideanSpace ℝ ι → ℝ`,
`x₀ = S₀`, `μ = volume.restrict (orthant x)`):

1. **`ε_pos`**: a positive radius for the PosDef ball around `S₀`. Need
   `S₀.PosDef` is an open condition (det > 0 + Hermitian + eigenvalue
   positivity in `Matrix n n ℝ`). Mathlib has `Matrix.PosDef.det_pos`
   but no packaged `Matrix.PosDef.isOpen`. **Sub-gap A**.
2. **`hF_meas`**: AE-strong-measurability of `F S` for `S` near `S₀`.
   `multivariateGaussianPdf S y` is a continuous function of `y` (already
   proved in R44-T2.2 close), and continuous in `S` once `det` and `inv`
   are continuous (which follows from R40 + R41-Full chain). Should be
   discharge-able with `Continuous.aestronglyMeasurable`.
3. **`hF_int`**: integrability of `multivariateGaussianPdf S₀` on the
   orthant. Standard Gaussian-tail bound. **Sub-gap B**: needs the
   integrability of the Gaussian density, which Mathlib has only via
   `IsGaussian.integrable_id` or similar — would need explicit derivation
   for the closed-form pdf.
4. **`hF'_meas`**: AE-strong-measurability of the derivative `S ↦ F' S`.
   Continuity of the derivative formula gives this; depends on R40 stub
   chain.
5. **`h_lip`**: Lipschitz bound on `S ↦ F S y` on a ball around `S₀`,
   with integrable Lipschitz constant `bound y`. **Sub-gap C, the
   load-bearing step.** Requires:
   - Explicit Fréchet derivative formula for `S ↦
     multivariateGaussianPdf S y` (chains through R40/R41 stubs).
   - Uniform bound on derivative norm by an integrable function of `y`
     (Gaussian-tail-decaying envelope).
6. **`bound_integrable`**: integrability of the Lipschitz envelope.
   Same Gaussian-tail story as sub-gap B.
7. **`h_diff`**: pointwise differentiability at `S₀`. Direct from
   chaining R40/R41 stubs.

**Honest assessment**: hypothesis 5 (`h_lip` with integrable bound) is
the engineering bottleneck. The dominator construction
(Gaussian-tail-bounded uniformly over PosDef neighborhood) is the
load-bearing step and is genuinely ~150-300 LOC by itself, NOT the
"~150-200 LOC" Grok Q4 estimated for the full part 1.

**Revised Path γ cost estimate**: ~400-600 LOC for full body close,
NOT ~300-350 LOC. The dominator construction alone is ~200-300 LOC,
and assembly of the seven hypotheses + final apply is another ~150-300
LOC.

---

## 5. R45 scope revision

### Mandatory floor (T2.1 + T2.2): Phase 2 body Full close via Path γ

**Original brief claim**: ~300-350 LOC, P~0.65 + P~0.65 conditional.

**T1.1 audit revision**: ~400-600 LOC for full close. P~0.30 for full
close in single round, P~0.65 for partial close (skeleton + TAG'd
sub-residuals at the dominator-construction step + LipschitzOnWith
hypothesis).

**Recommended revised plan**: pursue the **partial-close** outcome:
write the Path γ skeleton (MGI rewrite + `hasFDerivAt_integral_of_dominated_loc_of_lip`
application + chain-through-R40-stubs), with TAG'd sub-residuals at
the three engineering hurdles (dominator construction, LipschitzOnWith,
PosDef-neighborhood-open). This keeps the Phase 2 sorry but
substantially advances its diagnostic quality.

**Honest expected outcome**: **the R35 sorry stays at -0** (single
sorry remains), but its diagnostic body is replaced by a real Lean
skeleton with three labelled narrow sub-residuals each pinning a
concrete Mathlib gap. This is **Stub-quality progress, not Full
close**.

This is consistent with the R45 brief's "Honesty over optics"
behavioural rule and the briefing's "Partial accepted as honest
outcome" discipline rule.

### Stretch (T3.1): MGE body Full close

**Original brief claim**: ~170-270 LOC via Grok Q1 recipe (3 sub-gaps).

**T1.1 audit revision**: Q1.a misframed (+10-20 LOC) but Q1.b + Q1.c
confirmed. Revised total: ~180-290 LOC. **Still single-round
feasible but tight.** P~0.40 for full close, P~0.55 for partial close
(advance to second-degree sub-Stub).

### Combined revised R45 outcome distribution

| Outcome | P | Net Δ debt |
|---|---|---|
| Both full (Phase 2 + MGE) | 0.10 | -2 sorries (12 → 10) |
| Phase 2 full, MGE partial | 0.15 | -1 sorry (12 → 11) |
| Phase 2 partial, MGE partial | 0.30 | 0 sorries (skeleton-quality progress) |
| Phase 2 partial, MGE not attempted | 0.25 | 0 sorries |
| Phase 2 not attempted, MGE not attempted | 0.10 | 0 sorries |
| Other | 0.10 | varies |

**Realistic mid-distribution outcome**: -0 sorry, +substantial
diagnostic-quality advance on Phase 2. R59 ceiling gets +1 round of
buffer pressure.

---

## 6. Cross-check: Does this match R44 audit's calibration trajectory?

R44 actual: -1 sorry (MGI Full close, single closure of 2 mandatory
floor tasks).

R45 expected per T1.1 audit: -0 to -1 sorry (skeleton-quality Phase 2
advance + Stub-quality MGE advance).

This pattern matches R44 trajectory. The hard-math V2 axiom-reduction
program is consistently delivering ~1 sorry per round, NOT the
"~1-2 sorries per round" implied by Grok pre-flights. This calibration
data should inform R46+ briefs.

**R59 ceiling re-check**: with -0 to -1 expected at R45, the R59
trajectory shifts:

| Phase | Round | Cumulative Δ sorry |
|---|---|---|
| R45 (this) | 1 | -0 to -1 |
| R46 (Phase 2 full body close + Slepian start) | 1 | -1 to -2 |
| R47 (MGE close + SF) | 1 | -1 |
| R48 (BTIS-merge Q5 compression) | 1 | -2 sorries, -1 axiom |
| ... | ... | ... |

The R59 ceiling **remains at the boundary case** (zero buffer)
post-R45. The Q5 BTIS-merge compression option is still the load-bearing
recovery mechanism if any future round under-delivers.

---

## 7. Conclusion + recommendations

**T1.1 framing-verification finding**: Grok pre-flight is mostly correct
in operational shape but underestimates Phase 2 body Full LOC by
roughly 100-300 LOC. The single most material misframing is the
dominator-construction step in `hasFDerivAt_integral_of_dominated_loc_of_lip`,
which Grok did not surface as a sub-gap.

**Recommendation for R45 mandatory floor**: pursue Path γ skeleton
**deliberately as partial close**, writing the seven hypotheses of
`hasFDerivAt_integral_of_dominated_loc_of_lip` as separate `have`
blocks, with TAG'd sub-residuals at sub-gaps A (PosDef open), B
(integrability), C (Lipschitz envelope). This advances diagnostic
quality without overclaiming closure.

**Recommendation for stretch**: attempt MGE Full close per Grok Q1
recipe + Q1.a revision (det_CFC_sqrt_eq_sqrt_det as ~30-50 LOC bridge,
not ~20-40). Decision gate at T+3:00: if T2.1 + T2.2 not committed by
then, abort stretch and ship mandatory floor.

**Discipline check**: the R45 brief asked for framing verification
**before** starting code work. This audit fulfilled that. The
discipline rule "framing-misframing recurrence = discipline failure"
is tested here: the R45 brief's optimistic Path γ LOC estimate (300-350)
is corrected by this audit to 400-600. **No new misframing
introduced**; existing brief misframings flagged early.

Audit complete. Proceeding to T2.1 with revised expectation: skeleton
+ TAG'd sub-residuals.
