# R49 T1.1 — Path γ' breakage re-verification + Path A axiom signature draft

**Round:** R49 (V2 round 11), Variante 1, mainline-only.
**Branch:** `r46-track-a-mge-posdef` HEAD `434a407` (post-R48-T2.3).
**Date:** 2026-05-02.
**Pin:** `mathlib4 @ 25ce63313608`, brownian-motion `91267abd`, Lean `v4.27.0-rc1`.

This document re-verifies the two Path γ' misframings caught in
R48-T1.1 (`R48_T1_PathGammaPrimeAudit.md`) at the current `r46-track-a-mge-posdef`
HEAD `434a407`, and drafts the Path A axiom signature that will replace the
Phase 2 body Stub at `MultivariateGaussianCDF.lean:160-313` per user-directed
Path A switch.

## §1 — Re-verification at HEAD `434a407`

### Misframing M1: Lean MGI ≠ density differentiability — **STILL HOLDS**

**Brief's Path γ' step (2) claim:** "Density differentiability via MGI Full
(~20-30 LOC): use R44 MGI body to get
`HasFDerivAt (fun Σ => multivariateGaussianPdf 0 Σ x) ... Σ`."

**Verification at HEAD `434a407`:**

The R44 MGI in this codebase is
`Erdos524.Helpers.MultivariateGaussianPdf.multivariateGaussianOrthantCDF_eq_lebesgue_integral`
at `MultivariateGaussianPdf.lean:412`. Re-confirmed signature:

```lean
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) (x : ι → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i} =
      ∫ y in {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i},
        multivariateGaussianPdf S (fun i => y i) := by
```

This is the **measure-vs-Lebesgue-integral REWRITE** identity. The R44 body
(`MultivariateGaussianPdf.lean:427-477`) is:

1. (i) `h_meas` — orthant set is measurable.
2. (ii) `rw [multivariateGaussian_eq_lebesgue_withDensity S _hS]` — applies MGE.
3. (iii) `rw [Measure.real_def, withDensity_apply _ h_meas]` — measure → lintegral.
4. (iv) `rw [integral_eq_lintegral_of_nonneg_ae ...]` — lintegral → integral.

**No `HasFDerivAt`. No `DifferentiableAt`. No derivative formula.** Confirmed
via grep: `grep -n "DifferentiableAt\|HasFDerivAt"
FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean` returns
exactly 1 match (line 331), inside a comment, NOT a theorem statement.

The Lean MGI does not, and cannot, produce
`HasFDerivAt (fun Σ => multivariateGaussianPdf 0 Σ x) ... Σ` directly.
Pdf S-differentiability is a separate chain through the closed-form formula:

* `Matrix.det.differentiable` — R40 Stub at `MatrixDetDifferentiable.lean:149`
  (still open at HEAD `434a407`).
* `Matrix.PosDef.inv_hasFDerivAt` — R41 Full @ `:200`.
* `Real.sqrt` differentiability at positive args.
* `differentiableAt_inv` for `(S.det)⁻¹` at `S₀.det > 0`.
* `Real.exp.differentiable`.
* Bilinear continuity for `y ⬝ᵥ S⁻¹ *ᵥ y`.

**No new theorems on `multivariateGaussianPdf` differentiability have been
added between R48 (`434a407`) and R49 mainline.** Path γ' step (2) remains
chain-blocked on R40 `Matrix.det.differentiable` Stub.

**M1 re-verification: HOLDS.**

### Misframing M2: `GaussianParametricAnalysis.lean` tail bound — **STILL HOLDS**

**Brief's Path γ' step (3) claim:** "Gaussian tail majorant from
`GaussianParametricAnalysis.lean` library (R46 T3.1)."

**Verification at HEAD `434a407`:**

`GaussianParametricAnalysis.lean` re-inspected:

* Lines 1-101: header + R46 deliverables docstring.
* Lines 103-154: Lean theorems — `det_CFC_sqrt_eq_sqrt_det`,
  `det_CFC_sqrt_pos_of_posDef`, `posDef_min_eigenvalue_pos`,
  `posDef_min_eigenvalue_witness`. Re-exports of R46 helpers.
* Lines 156-198: **inside `/-! ... -/` docstring** — R47+ scaffolding
  documentation. Lines 166-192 contain a `markdown ` ``` ` ` code block with
  commented-out theorem signatures:
  - `multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef` (line 168)
  - `hasFDerivAt_integral_multivariateGaussianPdf` (line 177)
  - `posDef_local_stability_under_isHermitian_perturbation` (line 187)
* Lines 200-201: closing namespace.

**Grep confirmation at HEAD `434a407`:**
`grep -rn "uniform_tail_bound" FormalConjectures --include="*.lean"` returns
exactly **1 match**: `GaussianParametricAnalysis.lean:168` — INSIDE the
`/-! ... -/` docstring code block. The line is the start of a markdown-fenced
Lean signature comment, NOT a Lean theorem.

The docstring (lines 162-164) explicitly states:
> **Not added as TAG'd Stubs in R46** to avoid debt inflation. R47+ rounds
> will land them as Full theorems (or honest TAG'd Stubs at that time).

Path γ' step (3) DCT chain consumer "Gaussian tail majorant" does not exist
as a Lean object at HEAD `434a407`. To consume it one would first need to
land the tail bound as a Full helper (~60-100 LOC per the docstring estimate
and `R46_T1_GrepAuditAndFramingVerification.md` §5).

**No new tail-bound theorem has been added between R48 and R49 mainline.**

**M2 re-verification: HOLDS.**

## §2 — Combined Path γ' breakage diagnosis (no change vs. R48-T1.1)

Path γ' Phase 2 body Full close, honest LOC at HEAD `434a407`:

| Sub-step | Brief estimate | Verified estimate | Blockers (re-verified) |
|---|---|---|---|
| (1) Linear path Σ_path | 20-30 | 20-30 | none |
| (2) Pdf S-differentiability | 20-30 | **80-150** | R40 `Matrix.det.differentiable` Stub still open |
| (3) DCT chain step | 20-30 | **50-100 + tail-bound prereq** | tail-bound Full helper still missing |
| Lipschitz envelope (sub-gap C) | not in brief | **150-300** | (2) chain |
| Tail-bound Full helper | not in brief | **60-100** | sub-round target |
| (4) Existence conclusion | 10-20 | 10-20 | none |
| **Total** | ~80-100 | **~380-700** | R40 + tail-bound |

Path γ' is **not executable** as a single round in R49. Neither is Path γ''
(no Path γ'' has been validated since R48-T1.1).

Path B (continue from-scratch closure of Phase 2 body) remains costed at
~400+ LOC across 3-5 rounds with P(Full)/round ~0.30. The R52 milestone gate
target (items ≤ 8) is incompatible with this trajectory under realistic
mainline retirement rates (~0.44 sorry/round R40-R48 cumulative).

## §3 — Path A switch rationale (binding)

Per user-directed Path A switch (R49 brief): axiomatize Phase 2 body in
mainline, +1 axiom / -1 sorry, freeing 3-5 rounds for GLW shortcut (R50-R51)
+ Track C/Track D parallel work.

**Net round outcome (projected):**
* Mainline axioms: 5 → 6 (+1).
* Mainline sorries: 12 → 11 (-1).
* Mainline items (axioms + sorries): 17 → 17 (no item-count change at gate).

But: freed budget is the strategic gain. The 3-5 rounds previously committed
to Path γ' / Path B for Phase 2 body close are redirected to GLW shortcut
+ TC3 + TD4 retirements.

## §4 — Phase 2 body Stub current signature (extracted from `:160-313`)

**File:** `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean`.

**Namespace context (line 91):** `namespace Erdos524.Helpers.MultivariateGaussianCDF`.

**Section variables (line 96):**
```lean
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
```

**Theorem signature (lines 160-163, verbatim):**
```lean
theorem multivariateGaussianOrthantCDF_differentiable_wrt_covariance
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) :
    DifferentiableAt ℝ
      (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀ := by
```

**Body (lines 164-313):** ~150 lines of TAG'd diagnostic comments
(R35/R45/R47 audit history) terminating in `sorry` at line 313.

## §5 — Proposed axiom signature (verbatim Lean)

The Path A axiom **preserves the exact theorem name + type signature** so no
caller breaks. The `theorem ... := by sorry` triple becomes `axiom ...` —
binders identical (including `_h_pd` underscore prefix), conclusion type
identical:

```lean
axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) :
    DifferentiableAt ℝ
      (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀
```

Ambient section variables `{ι : Type*} [Fintype ι] [DecidableEq ι]` will
auto-bind into the axiom's prefix exactly as they do for the existing
`theorem` (Lean 4 auto-binding rule for both `theorem` and `axiom`).

The axiom name is **searchable + specific**: caller-facing identifier is
preserved verbatim, so existing consumers (the R41-T2.1 off-diagonal
directional-derivative scaffold + R35 Phase A scaffold downstream) compile
unchanged.

### Mathematical content (plain-English)

For a positive-definite covariance matrix `Σ : Matrix ι ι ℝ` and threshold
vector `x : ι → ℝ`, the half-space probability

  `F(Σ; x) := ℙ_{Z ∼ 𝒩(0, Σ)} (∀ i, Z i ≤ x i)
            = (multivariateGaussian 0 Σ).real {z | ∀ i, z i ≤ x i}`

is differentiable in `Σ` (in the entry-wise Fréchet sense at `S₀ : Matrix ι ι ℝ`
with `S₀.PosDef`).

This is a **classical fact** in Gaussian probability theory. Standard proofs
go via the Lebesgue density formula
`ρ(z; Σ) = (2π)^(-n/2) (det Σ)^(-1/2) exp(-z^T Σ^(-1) z / 2)`
plus differentiation under the integral sign, with a uniform Gaussian-tail
Lipschitz envelope on a PosDef neighbourhood of `S₀`. The result is the
analytic backbone of Slepian's lemma in covariance-interpolation form
(`d/dα` of `F(Σ_α; x)` along `Σ_α = (1-α)Σ_X + αΣ_Y`).

**Literature reference:** Slepian (1962) "The one-sided barrier problem
for Gaussian noise" Bell System Tech. J. 41:463-501; Tong (1990) "The
Multivariate Normal Distribution" §5.1; or any standard Gaussian-process
reference covering Slepian's lemma. The differentiability claim is a
pre-requisite (often left as a remark) for the comparison-inequality proof.

### Why axiomatize at R49

* Path γ' (R48 brief recipe) is broken per M1 + M2 — re-verified §1 above.
* No Path γ'' has been validated post-R48.
* Path B (from-scratch closure) costed at ~400+ LOC across 3-5 rounds with
  P(Full)/round ~0.30 — incompatible with R52 gate (items ≤ 8) under the
  cumulative ~0.44 sorry/round retirement rate.
* Path A (axiomatize Phase 2 body) frees 3-5 rounds for GLW shortcut +
  Track C round 3 + Track D round 4 work.

### Retirement target: R55-R59 (post-gate)

Sub-plan for retirement of this axiom:

1. **Mathlib pin bump (preferred path):** monitor Mathlib for landings of
   - Pdf-differentiability infrastructure for `multivariateGaussianPdf` /
     `multivariateGaussian` density;
   - Uniform Gaussian-tail bound on `IsCompact ∘ PosDef` neighbourhoods;
   - `Matrix.det.differentiable` (R40 Stub-equivalent).
   If a future Mathlib version (post-`v4.27` toolchain bump) lands these,
   the axiom retires via direct chain composition (~50-100 LOC consumer
   wrapper).

2. **From-scratch closure (fallback):** build the missing pieces in-tree
   per the §2 LOC table — ~150-300 LOC over 2-3 rounds, anchored on:
   - R40 `Matrix.det.differentiable` Stub close (~30-80 LOC);
   - Tail-bound Full helper (~60-100 LOC);
   - Phase 2 body Full close (~150-300 LOC) consuming the above.

   This fallback is the same Path B blocked above, but executed
   post-R52-gate when budget is freed.

**Milestone gating:** retirement of this axiom is **not** required for the
R52 gate (gate measures items count, +1 axiom / -1 sorry is a wash there;
the strategic value is freeing budget for OTHER retirements). Retirement
moves from R55 onwards as part of the post-gate consolidation pass.

## §6 — Scope discipline (R49 binding)

**R49 scope = Phase 2 body axiomatization ONLY.** Other open Stubs on
mainline are explicitly OUT of scope:

* `MatrixDetDifferentiable.lean:149` (`Matrix.det.differentiable`) — separate
  decision, not touched in R49.
* `MultivariateGaussianPdf.lean:402` (MGE main / `multivariateGaussian_eq_lebesgue_withDensity`)
  — separate decision, not touched in R49.

The R49 brief explicitly forbids modifying these in this round. R49 retires
exactly one Stub (the Phase 2 body Stub at `MultivariateGaussianCDF.lean:160-313`)
via axiom replacement; all other technical-debt items remain at their R48
state.

## §7 — Anti-mismatch hygiene checklist (T2.1 binding)

When implementing T2.1 (axiom replacement in
`MultivariateGaussianCDF.lean:160-313`):

1. ✅ Preserve theorem name verbatim: `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`.
2. ✅ Preserve binders verbatim: `(S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ)`.
3. ✅ Preserve conclusion verbatim:
   `DifferentiableAt ℝ (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀`.
4. ✅ Replace `theorem` with `axiom` and remove `:= by ... sorry` body.
5. ✅ Add Lean docstring `/-- ... -/` above axiom: math content +
   why-axiomatized + retirement-target (per R49 brief).
6. ✅ Run `lake build FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianCDF`
   mid-edit to verify axiom signature compiles.
7. ✅ Run full `lake build` to verify no caller breaks (signature drift).
8. ✅ If callers break: revert and diagnose. Do NOT silently rename callers.

## §8 — Confidence

* **M1 + M2 re-verification:** P(both still hold) = **0.99** (mechanical
  grep + file inspection, audit was thorough at R48).
* **Axiom signature compiles:** P = **0.95** (Lean 4 `axiom` accepts
  underscore-prefixed binders per `StochasticProcessAxiom.lean:100-115`).
* **Caller compatibility (no signature drift):** P = **0.95** (name +
  binders preserved verbatim).
* **Joint T1.1 outcome:** **~0.93** — highest-confidence audit deliverable
  in the project so far.

---

**T1.1 conclusion:**

Both Path γ' misframings re-verified at HEAD `434a407`. Path A switch is
the correct decision per R49 brief. Axiom signature drafted with verbatim
preservation of name + binders + conclusion. Math content + retirement plan
(R55-R59 post-gate) documented. T2.1 replacement is mechanical.
