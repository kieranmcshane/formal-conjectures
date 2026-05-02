# R47-T1.1 Grep audit + framing verification

**Round:** R47 Track A (mainline). **Process Q4 ii binding:** Local
Claude grep audit FIRST, before any code edits, against pinned state
`mathlib4 @ 25ce63313608` + `brownian-motion` HEAD.

**Scope this round:** verify the recipes laid out in the R47 pre-flight
prompt for (1) MGE sub-gap (b) `stdGaussian_eq_lebesgue_withDensity`
and (2) Phase 2 body close. Surface any math-reasoning errors at edge
cases or unpackaged Mathlib API claims BEFORE scope commitment.

---

## §1 — R46 helpers verified in repo

Locations confirmed via `git show 58e31ff` + `git show 4e75403`:

| Helper | File | Lines | Status |
|---|---|---|---|
| `det_CFC_sqrt_eq_sqrt_det` | `MultivariateGaussianPdf.lean` | ~158-180 | Full (R46 T2.1) |
| `det_CFC_sqrt_pos_of_posDef` | `MultivariateGaussianPdf.lean` | ~182-189 | Full corollary |
| `posDef_min_eigenvalue_pos` | `PhaseAUpperBound.lean` | (R46 T2.2) | Full |
| `posDef_min_eigenvalue_witness` | `PhaseAUpperBound.lean` | (R46 T2.2) | Full |
| `GaussianParametricAnalysis.lean` | new file | 9.2K | R46 T3.1 stretch |

These four Full helpers are **foundational infrastructure** for R47, but
none of them is the n-ary `Measure.pi.withDensity` factorization, the
`Measure.map.withDensity` chain rule, or the
`(volume : Measure (EuclideanSpace ℝ ι)) = pushforward of pi-volume`
identity that sub-gap (b) actually needs.

---

## §2 — Sub-gap (b) Mathlib state at pin (T2.1 verification)

**Recipe per R45-T1.1 + R46 audit:**
```
stdGaussian (EuclideanSpace ℝ ι)
  =[pi_eq_stdGaussian, brownian-motion MultivariateGaussian.lean:134]
(Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2)
  =[gaussianReal_of_var_ne_zero, mathlib Real.lean:202, on each factor]
(Measure.pi (fun _ ↦ volume.withDensity (gaussianPDF 0 1))).map (toLp 2)
  =[**MISSING BRIDGE A**: n-ary pi-withDensity factorization]
((Measure.pi (fun _ ↦ volume)).withDensity (fun x ↦ ∏ i, gaussianPDF 0 1 (x i))).map (toLp 2)
  =[**MISSING BRIDGE B**: pushforward-of-withDensity through measurable equiv]
((Measure.pi (fun _ ↦ volume)).map (toLp 2)).withDensity (factored pdf ∘ (toLp 2)⁻¹)
  =[**MISSING BRIDGE C**: Lebesgue-on-EuclideanSpace = pushforward of product Lebesgue]
(volume : Measure (EuclideanSpace ℝ ι)).withDensity (stdPdf)
```

**Bridge A — n-ary `Measure.pi.withDensity` factorization.** Search at
pin `mathlib4 @ 25ce63313608`:

* `pi_withDensity` — **0 hits** in
  `Mathlib/MeasureTheory/Constructions/Pi.lean` and
  `Mathlib/MeasureTheory/Measure/WithDensity.lean`.
* `prod_withDensity` — Mathlib has the **binary** version
  (`WithDensity.lean:683`), `prod_withDensity₀` for measurable+aemeasurable.
* Generalisation to `n`-ary `Measure.pi` via induction on `Fintype` or
  via `Measure.pi_eq` characterisation (testing on rectangles) — **NOT
  packaged**. Estimated bridge LOC: ~50-80.

**Bridge B — `Measure.map.withDensity`.** For a measurable equiv
`e : α ≃ᵐ β`:
```
(μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm)
```
Search:
* `map_withDensity` — **0 direct hits** for this exact form.
* The closest is `MeasurableEmbedding.withDensity_map` (somewhere in
  `Mathlib/MeasureTheory/Measure/`), which handles the measurable
  embedding case (one-sided).
* For `MeasurableEquiv` specifically, the lemma is derivable but **not
  packaged as a single equality**. Estimated bridge LOC: ~30-50.

**Bridge C — Lebesgue-EuclideanSpace identification.** The volume
measure on `EuclideanSpace ℝ ι` is defined as the pushforward of the
product Lebesgue measure through `WithLp.equiv 2` /
`PiLp.measurableEquiv`. Search:
* `EuclideanSpace.volume_eq` — possibly packaged but not located in
  this audit window.
* `EuclideanSpace.volume_preserving` family —  exists in
  `Mathlib/MeasureTheory/Measure/Lebesgue/EuclideanSpace.lean` but
  the exact pushforward identity through `toLp 2` needs verification.
* Estimated bridge LOC: ~20-50 if a packaged form exists; ~50-100 if
  custom unwinding needed.

**Total realistic LOC for sub-gap (b) Full close:**
~50+30+20 (low) to ~80+50+100 (high) for bridges + ~50 composition
= **~150-280 LOC**, NOT the 80-120 LOC the R45/R46 audit estimated.

The R45/R46 estimate was based on a partial verification of the
recipe; this round's audit reveals THREE intermediate Mathlib bridges
that each individually require unpackaged work.

---

## §3 — Phase 2 body chain verification (T2.2 verification)

**R46 helpers contribution:** sub-gap (A) "PosDef compact neighbourhood"
is now SUPPLIED via `posDef_min_eigenvalue_pos` (compact PosDef sets
have a uniform spectral lower bound, which combined with an upper bound
on operator norm yields a Lipschitz envelope on inverse + det chain).

**Cross-track library contribution:** `GaussianParametricAnalysis.lean`
(R46 T3.1) provides parametric DCT scaffold — but inspection of
its content (next §) is required to assess whether it directly closes
Phase 2 sub-gap (B) (uniform Gaussian-tail integrability) or only
foundational pieces.

**Remaining Phase 2 body chain blockers (post-R46):**

* (B) Uniform Gaussian tail integrability `Integrable
  (multivariateGaussianPdf S) volume` on `orthant x` — depends on
  MGE main being closed (so the PDF is actually a valid density of
  the multivariateGaussian measure). **Pre-MGE-Full: blocked.**
* (C) Lipschitz envelope on PosDef neighbourhood — requires explicit
  Fréchet-derivative formula chain through `Matrix.det.differentiable`
  (R40 Stub) + `Matrix.PosDef.inv_hasFDerivAt` (R41 Full) +
  `Real.sqrt` differentiability + bilinear form differentiability.
  **R40 Stub status: NOT closed.** Closure depends on
  `Matrix.det.differentiable` which is itself ~30-80 LOC of unpackaged
  Mathlib plumbing.

**Total realistic LOC for Phase 2 body Full close (post-R46 helpers,
honest):**

* Sub-gap (B) bridge: ~50-100 LOC, BUT requires MGE main Full first
  (sub-gap (b) closure).
* Sub-gap (C) Lipschitz envelope: ~150-300 LOC, blocked on
  `Matrix.det.differentiable` (R40 Stub).
* DCT chain composition: ~100-150 LOC.
* **Total:** ~300-550 LOC, BUT most of it depends on MGE main close
  AND on R40 `Matrix.det.differentiable` Stub close.

**Conclusion:** Phase 2 body cannot Full-close in R47 as a single-round
target. Closure depends on the chain MGE main → Phase 2 main, with
Phase 2 main further blocked on the R40 det.differentiable Stub.

---

## §4 — `GaussianParametricAnalysis.lean` (R46 T3.1) audit

Inspection of the cross-track library shows R46-Full helpers for the
parametric Gaussian DCT chain. Specifically (per file content
inspection):

* **What it provides:** parametric Gaussian density bounds + DCT
  scaffold for `S ↦ ∫ pdf(S) dy` differentiability.
* **What it needs:** an explicit `multivariateGaussianPdf` density
  formula on `EuclideanSpace ℝ ι` — i.e., MGE main Full close.
* **Direct consumption of R46 helpers by Phase 2 body:**
  - `posDef_min_eigenvalue_pos` → uniform spectral lower bound on
    compact PosDef neighbourhoods → uniform tail bound. **Direct
    consumer.**
  - `det_CFC_sqrt_eq_sqrt_det` → identifies the Jacobian factor in
    `multivariateGaussianPdf S` as `(det S)^(-1/2)` rather than
    `((CFC.sqrt S).det)^(-1)`. **Foundational** (consumed inside MGE
    main, not directly by Phase 2 body).

**Assessment:** Phase 2 body close is **dependent on MGE main close**
through the `multivariateGaussianPdf` formula chain.

---

## §5 — Math-reasoning edge-case verification

Per the R44/R45/R46 lesson (3 consecutive rounds caught Grok
misframings), this round flagged the following claims for independent
verification:

### Claim 1: "sub-gap (b) is ~80-120 LOC"

**Source:** R44/R45/R46 R47 pre-flight prompts.

**Verification:** **FALSE at pin.** Sub-gap (b) decomposes into THREE
intermediate Mathlib bridges (A, B, C above), each unpackaged. Realistic
LOC: ~150-280. The R44/R45/R46 audits captured the recipe but did NOT
unpack the n-ary pi-withDensity factorization, which is the dominant
unpackaged piece.

**Implication for R47 T2.1:** the 80-120 LOC budget is below realistic
need by 1.5-2.5×. T2.1 mandatory floor downgraded from "Full close" to
"Full close OR honest TAG'd sub-Stub citing the three intermediate
bridges" per brief's abort rules.

### Claim 2: "Phase 2 body Full close ~300-450 LOC with R46 helpers"

**Source:** R47 brief.

**Verification:** **PARTIALLY FALSE.** The 300-450 LOC estimate
underweights:
* The dependency on MGE main Full (which itself depends on sub-gap (b)
  Full).
* The dependency on `Matrix.det.differentiable` (R40 Stub still open).

Realistic LOC for Phase 2 body Full close (without prerequisite
closures) is ~300-550 LOC. With prerequisites blocked, Full close is
**not feasible in R47**.

**Implication for R47 T2.2:** Phase 2 body cannot Full-close this round
as a single-round target. T2.2 mandatory floor downgrades to "honest
TAG'd sub-Stub with concrete diagnostic" per brief's abort rules.

### Claim 3: "MGE sub-gap (b) was R46's Grok Q1 bottleneck"

**Source:** R47 pre-flight + memory file.

**Verification:** **TRUE** per R46 outcome (0 retirements with sub-gap
(b) explicitly deferred). This round's audit confirms the bottleneck is
real and is composed of THREE unpackaged bridges, not a single
80-120 LOC chunk.

### Claim 4: "PosDef.isOpen in `Matrix n n ℝ` is FALSE"

**Source:** R46 T1.1 audit (already in repo).

**Verification:** **TRUE** as previously established. R46 correctly
patched to minimum-eigenvalue formulation. R47 inherits the corrected
framing.

---

## §6 — R47 scope decision (post-audit)

**Recommended R47 scope (honest, brief-aligned):**

1. **T2.1 (priority 1):** Attempt the most accessible of Bridge A
   (n-ary pi-withDensity factorization, ~50-80 LOC) as a standalone
   Full helper in `MultivariateGaussianPdf.lean`. If completed,
   diagnostic-quality enhancement to MGE Stub identifying the
   remaining bridges (B, C) precisely. **Net retirement: 0 sorries**
   (BELOW 2-retirement target), but +1 Full helper landed.

   **Stretch within T2.1:** if Bridge A closes quickly (<1h), attempt
   Bridge C (Lebesgue-EuclideanSpace identification) as a second
   helper. Combined with R46 sub-gap (a) + Mathlib-direct sub-gap (c),
   this would put MGE main one bridge (B) away from Full close.

2. **T2.2 (priority 2):** Land Phase 2 body as honest TAG'd sub-Stub
   with concrete diagnostic citing the three remaining blockers (MGE
   main, `Matrix.det.differentiable` R40 Stub, sub-gap (B)/(C)
   chain). **Net retirement: 0 sorries.** Status: deferred per brief
   abort rules.

**Honest assessment:** R47 lower-distribution outcome (0 retirements)
is the most likely outcome given the audit findings. The aggressive
2-retirement target stated in the brief is incompatible with the
verified Mathlib state. R47 caps at 50% (~235 pts) under brief's
sub-Stub clause if T2.1 lands a Full helper but no retirements.

**R52 gate trajectory implication:** Hybrid (c) gate at items ≤ 8 by
end R52 requires recovery pace 1.875-2.5/round R47-R50 average. R47
contributing 0 retirements → R48-R50 must compensate at 2.5-3.3/round.
Path A (axiomatize BTIS at R54) increasingly likely outcome.

---

## §7 — R47 process discipline notes

* T1.1 audit COMPLETED at T+~0:30 per sub-checkpoint.
* T2.1 attempt commences immediately on Bridge A (n-ary
  pi-withDensity).
* Strict abort rule: if Bridge A not committed by T+2:15, ship as
  TAG'd partial with concrete diagnostic.
* T2.2 lands as deferred-with-diagnostic at T+3:30 per abort rules.
* T2.3 build verification + status doc at T+3:45.

**End R47-T1.1 audit.**
