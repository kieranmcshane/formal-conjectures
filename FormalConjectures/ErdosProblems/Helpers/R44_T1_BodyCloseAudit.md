# R44 — T1.1 Audit: MGE/MGI body close + brief-vs-reality reconciliation

**Branch**: `r33-c-helpers-consolidation` (HEAD `37c671f`,
R43-T2.4 build verification + status doc + AXIOM_INVENTORY).
**Mathlib pin**: `mathlib4 @ 25ce63313608`.
**Round**: R44 (V2 round 6; Phase A upper round 6 of cluster).
**Date**: 2026-05-02.
**Path**: brief Path (b) — MGE body close + MGI body close, no Phase 2.

This audit reconciles the brief's Grok Q1/Q2 pre-flight framing with the
actual file state landed in R43, fixes the realistic R44 scope, and lays
out the body-closure recipes for the two measure-theoretic stubs that R43
upgraded from `True := by trivial` to real signatures.

---

## 1. Brief-vs-reality reconciliation

The R44 brief's Grok Q1 + Q2 pre-flight verdicts describe:

* **Q1 / T2.1 MGE body close** = "Jacobi formula proof" (~80–120 LOC) for
  `HasFDerivAt (fun A : Matrix n n ℝ => A.det) (...) Σ` via
  `Matrix.det_eq_sum_alternatingMap` / cofactor-adjugate expansion.
* **Q2 / T2.2 MGI body close** = "PDF derivative formula" (~100–150 LOC)
  for `HasFDerivAt (fun Σ' => multivariateGaussianPdf μ Σ' x) (...) Σ` via
  chain rule on (i) MGE = `det⁻¹/²`, (ii) R41 PosDef.inv, (iii) quadratic
  form derivative.

This framing **does not match the actual MGE/MGI signatures** that R43
landed in `MultivariateGaussianPdf.lean`. The mismatch is a Grok pre-flight
hallucination: it confused two unrelated stubs that share the "MG…"
prefix. The reality, per the file + memory + R43 status doc:

| Symbol in brief | Q1/Q2 description | Actual file content |
|---|---|---|
| **MGE** = `multivariateGaussian_eq_lebesgue_withDensity` (`MultivariateGaussianPdf.lean:183`) | Jacobi formula `HasFDerivAt det` | Pushforward measure equality `multivariateGaussian 0 S = volume.withDensity (ofReal ∘ pdf)`. Depends on 3 *measure-theoretic* Mathlib gaps (a)–(c) below. |
| **MGI** = `multivariateGaussianOrthantCDF_eq_lebesgue_integral` (`MultivariateGaussianPdf.lean:226`) | PDF derivative chain rule | Orthant probability = Lebesgue integral of PDF over the orthant. Consumer wrapper of MGE via `withDensity_apply`. |
| (Jacobi formula stub, separate) | (matches Q1) | `Matrix.det.hasFDerivAt` (`MatrixDetDifferentiable.lean:124`) — TAG'd `R40-T2.1-det-cofactor-route`. NOT named "MGE" anywhere in the codebase. |
| (Multivariate PDF differentiability stub, separate) | (matches Q2) | `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` (`MultivariateGaussianCDF.lean`) — TAG'd `R35-T2.1`. NOT named "MGI" anywhere. |

The R43 status doc (`PhaseV2R43Status.md:209-210`) unambiguously says:

> R44 trajectory: Phase 2 closes MGE + MGI bodies + CDF differentiability
> Full body (~300-350 LOC).

So "MGE + MGI bodies" in R43's R44 trajectory = the two measure-theoretic
stubs (the file's MGE/MGI), not the Jacobi-formula / PDF-derivative stubs
(`Matrix.det.hasFDerivAt` / R35-T2.1) that Grok hallucinated.

**Decision**: this round follows the file-grounded interpretation. R44
attempts to close the two R43 measure-theoretic stubs (`MultivariateGaussianPdf.lean:183`
+ `:226`). The brief's Grok-LOC and confidence numbers (~180-270 LOC,
P(Full) 0.65-0.75) are based on a misframed scope and do **not** apply
to the realistic body-close work.

---

## 2. Realistic scope — MGE body close

### 2.1 Theorem (signature already landed at R43)

```lean
theorem multivariateGaussian_eq_lebesgue_withDensity
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal (multivariateGaussianPdf S (fun i => y i))) := by
  sorry  -- TAG[R43-T2.1-MGE-pushforward-jacobian-body]
```

### 2.2 Mathlib gaps (carry-over from R40 audit, restated R43)

(a) **Jacobian-of-`CFC.sqrt`**: `(CFC.sqrt S).det = Real.sqrt S.det` for
PosDef `S`. Provable from `CFC.sqrt_mul_sqrt_self` + `Matrix.det_mul`,
but no standalone identity packaged at pin `25ce63313608`.

(b) **`stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace ℝ ι`**:
`stdGaussian` is defined as `(Measure.pi (fun _ ↦ gaussianReal 0 1)).map …`
(`BrownianMotion/Gaussian/MultivariateGaussian.lean:160`). Unwinding the
product structure into the explicit density `(2π)^{-n/2} exp(-‖x‖²/2)`
requires Lebesgue-tensor-product bookkeeping that is not packaged.

(c) **Change-of-variables for constant-Jacobian linear pushforward**:
Mathlib has `MeasureTheory.integral_image_eq_integral_abs_det_jacobian_smul_of_injOn`
(general non-linear C¹), but no specialisation to
`T = toEuclideanCLM (CFC.sqrt S)` linear with constant Jacobian.

### 2.3 Realistic outcome estimate

Each gap is a multi-LOC formalization in its own right; the joint MGE
body close is genuinely ~150–200 LOC if attempted from scratch within
this file (R40 audit estimate, restated in R43 status `PhaseV2R43Status.md:182`).

P(Full close in single round) is realistically **~0.10-0.15** without
new Mathlib API maturing. The brief's claim of "0.75" is based on the
hallucinated Jacobi-formula scope and does not apply.

**Acceptable R44 outcome**: TAG'd partial close with a *strengthened
diagnostic* — explicit sub-goals enumerated, Mathlib API search
documented, fallback recipe sketched. This advances the audit-trail
without artificially claiming closure.

---

## 3. Realistic scope — MGI body close

### 3.1 Theorem (signature already landed at R43)

```lean
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) (x : ι → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i} =
      ∫ y in {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i},
        multivariateGaussianPdf S (fun i => y i) := by
  sorry  -- TAG[R43-T2.1-MGI-orthant-via-MGE-body]
```

### 3.2 Closure recipe (consumer wrapper of MGE)

Given MGE as a black-box assumption, MGI is a consumer wrapper through
`MeasureTheory.withDensity_apply` / `Measure.integral_withDensity_eq_integral_smul`:

1. Apply MGE: `multivariateGaussian 0 S = volume.withDensity (fun y => ENNReal.ofReal (pdf S (fun i => y i)))`.
2. Take `.real` of both sides at the orthant `{z | ∀ i, z i ≤ x i}`:
   `(multivariateGaussian 0 S).real (orthant) = (volume.withDensity ofReal_pdf).real (orthant)`.
3. Compute RHS via `Measure.real_withDensity_apply` (or unfold `Measure.real`
   to `(measure …).toReal`, then apply `withDensity_apply` to convert to
   `∫⁻ y in orthant, ofReal (pdf …) ∂volume`, then convert lintegral of
   `ofReal nn-fn` to `∫ y in orthant, pdf …` via `integral_eq_lintegral_of_nonneg`).

The orthant set `{z | ∀ i, z i ≤ x i}` is measurable (countable
intersection of closed half-spaces), and `pdf S` is non-negative
(`multivariateGaussianPdf_nonneg` already Full at R40 line 109).

### 3.3 Realistic outcome estimate

~30–80 LOC consumer wrapper. Mathlib API used is standard
(`withDensity_apply`, `integral_eq_lintegral_of_nonneg`,
`measurableSet_iInter` for the orthant). The wrapper is mechanical
modulo `Measure.real` ↔ `(...).toReal` unfolding.

P(Full close in single round) ~**0.50** given MGE as black-box. The
biggest risk is API name lookup at the pin (e.g. `Measure.real_withDensity_apply`
may not be the exact lemma name; could need `Measure.withDensity_apply`
+ `Measure.real_def` chain).

---

## 4. Round 44 strategy & priority order

Given the asymmetry in P(Full) — MGE ~0.10 vs MGI ~0.50 — and the
discipline rule "ship honest TAG'd partial if Full not realistic":

1. **T2.2 first** (MGI body close, ~30-80 LOC): high-probability cheap
   close. Routes through MGE as a black-box (the TAG'd Stub gives a
   `sorry`-defined hypothesis, which is enough to derive MGI under the
   interpretation that MGE's *statement* is the assumption). Lands -1
   sorry.

2. **T2.1 second** (MGE body attempt, exploratory): try the body close
   with realistic expectations. If any of (a)/(b)/(c) cannot be
   discharged within 1.5h, leave as TAG'd partial with strengthened
   diagnostic — explicit sub-goals enumerated as named `sorry`s within
   the body, Mathlib API search results documented inline.

3. **T2.3** (build verify + status): unchanged.

This ordering protects the mandatory floor: even if MGE leaves as
TAG'd partial, MGI lands -1 sorry and the round delivers the Path (b)
"close two stubs" intent (one Full, one strengthened).

---

## 5. Net debt forecast (revised vs brief)

| Outcome | Brief forecast | Realistic forecast |
|---|---|---|
| T2.1 MGE body close | -1 sorry (Full) | -1 sorry (Full) at P~0.10 OR TAG'd partial (no net change) at P~0.85 |
| T2.2 MGI body close | -1 sorry (Full) | -1 sorry (Full) at P~0.50 OR TAG'd partial (no net change) at P~0.45 |
| T2.3 build + status | mechanical | mechanical |
| **Net** | -2 sorries (P~0.45) | -1 to -2 sorries (P~0.50 for at least -1; P~0.05 for -2) |

The brief's joint mandatory floor (~0.45 for both Full) is unreachable
given the MGE Mathlib gap depth. Revised honest joint floor for "at
least one Full close" is ~0.50, and "MGI Full + MGE strengthened
diagnostic" is the most likely single-round outcome (P~0.40).

---

## 6. R59 ceiling impact

If MGE leaves as TAG'd partial in R44:

* R44 net: -1 sorry (MGI Full).
* R45 retains Phase 2 (per brief) PLUS MGE body close as a now-named
  sub-task. Re-estimate MGE body at ~150-200 LOC + Phase 2 at ~150-200 LOC
  ⇒ R45 budget exceeds 400 LOC, may need split.
* Q5 BTIS-merge compression option (1 round buffer) absorbs the slip.

If MGE Full + MGI Full at R44 (low-probability happy path):

* R44 net: -2 sorries.
* R45 picks up only Phase 2 (CDF body Full via diff-under-integral) at
  ~150-200 LOC, fits comfortably.

Both paths preserve R59 ceiling within the existing 1-round-buffer
allowance.

---

## 7. Status

**T1.1 audit**: complete. Reconciles brief's misframing with file
reality, fixes realistic R44 scope (close two R43 measure-theoretic
stubs), commits to MGI-first ordering.

R44 mandatory floor proceeds to T2.2 (MGI body close — high-probability),
then T2.1 (MGE body attempt — exploratory, accept TAG'd partial as
honest outcome), then T2.3 (build + status).
