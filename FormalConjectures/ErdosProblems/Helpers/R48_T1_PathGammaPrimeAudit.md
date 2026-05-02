# R48-T1.1 Path γ' framing verification + grep audit

**Round:** R48 Track A (mainline). **Branch:** `r46-track-a-mge-posdef`
HEAD `7bb2787` (R47-T2.3 closing). **Process Q4 ii binding:** Local
Claude grep audit FIRST, before any code edits, against pinned state
`mathlib4 @ 25ce63313608` + `brownian-motion` HEAD.

**Scope this round:** verify the Path γ' Phase 2 body close recipe
laid out in the strategic Grok pre-flight (post-R47) Q3 verdict and
adopted as the R48 mandatory T2.1 by the user brief. Per process
discipline, surface any math-reasoning errors at edge cases or
unpackaged Mathlib API claims BEFORE T2.1 scope commitment.

---

## §1 — Brief's Path γ' framing (as written)

The R48 brief states T2.1 = Path γ' Phase 2 body Full close in ~80-100
LOC. The Grok Q3 recipe (per brief §"R48 scope" + §"T2.1"):

> 1. Linear path differentiability (~20-30 LOC): `Σ_path α := (1-α) •
>    Σ_X + α • Σ_Y`. Standard linear-combo derivative.
>
> 2. **Density differentiability via MGI Full** (~20-30 LOC): use R44
>    MGI body to get
>    `HasFDerivAt (fun Σ => multivariateGaussianPdf 0 Σ x) ... Σ`.
>    This is the chain composition step that bypasses sub-gap (b).
>
> 3. Dominated convergence (~20-30 LOC): apply
>    `hasFDerivAt_integral_of_dominated_loc_of_lip` with R46 PosDef
>    compact neighborhood + Gaussian tail majorant from
>    `GaussianParametricAnalysis.lean` library (R46 T3.1).
>
> 4. Existence-only conclusion (~10-20 LOC).

Justification: "Mathematically valid because Erdős 524 only requires
existence of suitable envelopes/couplings, not the closed-form
derivative; MGI already supplies the necessary generic chaining bounds
for Gaussian suprema."

---

## §2 — Misframing #1: Lean MGI vs. literature MGI

### Claim under audit

> "MGI already supplies the necessary generic chaining bounds for
> Gaussian suprema."

> "Density differentiability via MGI Full (~20-30 LOC): use R44 MGI
> body to get `HasFDerivAt (fun Σ => multivariateGaussianPdf 0 Σ x)
> ... Σ`."

### Verification at pin

The R44 MGI in this codebase is
`Erdos524.Helpers.MultivariateGaussianPdf.multivariateGaussianOrthantCDF_eq_lebesgue_integral`
at `MultivariateGaussianPdf.lean:412`. Signature (verified):

```lean
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) (x : ι → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i} =
      ∫ y in {z : EuclideanSpace ℝ ι | ∀ i, z i ≤ x i},
        multivariateGaussianPdf S (fun i => y i)
```

This is a **measure-vs-Lebesgue-integral REWRITE** identity. It states
"the orthant probability under `multivariateGaussian 0 S` equals the
Lebesgue integral of the explicit PDF over the orthant region."

It is **NOT** a differentiability statement. It contains no
`HasFDerivAt`, no `DifferentiableAt`, no derivative formula. It does
not differentiate `multivariateGaussianPdf` with respect to `S` —
indeed the LHS does not even contain a free `S` differentiability
context.

### Body inspection (`MultivariateGaussianPdf.lean:412-477`)

The R44 Full body of MGI proceeds as:
```lean
-- (ii) Apply MGE to rewrite the multivariate Gaussian measure.
rw [multivariateGaussian_eq_lebesgue_withDensity S _hS]
-- (iii) Unfold `Measure.real` and apply `withDensity_apply`.
rw [Measure.real_def, withDensity_apply _ h_meas]
-- (iv) Reverse the integral_eq_lintegral_of_nonneg_ae direction.
rw [integral_eq_lintegral_of_nonneg_ae ...]
```

The first `rw` step at line 466 calls `MGE`
(`multivariateGaussian_eq_lebesgue_withDensity`), which is itself a
TAG'd Stub at `MultivariateGaussianPdf.lean:248-402` (sorry at line
402). MGI thus consumes MGE. R44 closed MGI's body modulo the MGE
Stub.

### Diagnosis

The Grok Q3 framing appears to **conflate two distinct concepts**:

* **Lean codebase MGI** (`multivariateGaussianOrthantCDF_eq_lebesgue_integral`):
  the integral REWRITE from the abstract `multivariateGaussian` measure
  to `∫ pdf(S)`. R44 closure was the Lebesgue-integral identity, not a
  differentiability claim.
* **Literature MGI** (Maximal Gaussian Inequality / generic chaining
  for Gaussian suprema): a probability-theoretic envelope theorem
  yielding tail/expectation bounds for `sup_t G_t` of a Gaussian
  process. Used in concentration / chaining arguments.

The phrase "necessary generic chaining bounds for Gaussian suprema" is
literature-MGI language. Erdős 524 GLW small-ball / Slepian comparison
in this codebase does NOT consume literature-MGI. The Lean codebase
MGI does NOT supply Gaussian-suprema chaining bounds.

The local MGI body (the integral rewrite) does not, and cannot,
produce `HasFDerivAt (fun Σ => multivariateGaussianPdf 0 Σ x) ... Σ`.
Pdf-pointwise S-differentiability is a separate chain through the
closed-form formula:

* `Matrix.det.differentiable` — R40 Stub at
  `MatrixDetDifferentiable.lean:149` (sorry; still open).
* `Matrix.PosDef.inv_hasFDerivAt` — R41 Full @ `:200`.
* `Real.sqrt` differentiability at positive args.
* `differentiableAt_inv` for `(S.det)⁻¹` at `S₀.det > 0`.
* `Real.exp.differentiable`.
* Bilinear continuity for `y ⬝ᵥ S⁻¹ *ᵥ y`.

Per `MultivariateGaussianCDF.lean:202` (R45-T1.1 audit comment):
**~80-150 LOC, blocked on R40 Stub closure.** This is the same chain
identified in R45/R46/R47 audits.

### Implication for R48 T2.1

The "~20-30 LOC density differentiability via MGI" claim is **off by
roughly a factor of 5×** in LOC and is **chain-blocked** on R40 Stub
(`Matrix.det.differentiable`). The Grok Q3 path γ' recipe step (2) is
not reachable as written.

---

## §3 — Misframing #2: `GaussianParametricAnalysis.lean` tail bound

### Claim under audit

> "Gaussian tail majorant from `GaussianParametricAnalysis.lean`
> library (R46 T3.1)."

### Verification at pin

`GaussianParametricAnalysis.lean` (R46-T3.1 stretch) was inspected in
full. The file contains:

* **Lines 1-101**: header, docstring, R46 deliverables, R47+ scope
  documentation.
* **Lines 103-154**: Lean theorems — `det_CFC_sqrt_eq_sqrt_det`,
  `det_CFC_sqrt_pos_of_posDef`, `posDef_min_eigenvalue_pos`,
  `posDef_min_eigenvalue_witness`. These are **re-exports** of R46
  helpers from `MultivariateGaussianPdf.lean` and `PhaseAUpperBound.lean`,
  not new theorems.
* **Lines 156-198**: R47+ scaffolding inside a `/-! -/` docstring
  block. Lines 168-192 contain code-block markdown
  (` ```lean ... ``` `) with **commented-out theorem signatures**:
  - `multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef`
  - `hasFDerivAt_integral_multivariateGaussianPdf`
  - `posDef_local_stability_under_isHermitian_perturbation`
* **Lines 199-200**: closing namespace.

The docstring (lines 162-164) explicitly states:

> **Not added as TAG'd Stubs in R46** to avoid debt inflation. R47+
> rounds will land them as Full theorems (or honest TAG'd Stubs at
> that time).

### Diagnosis

`multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef` is
**NOT a Lean theorem in the codebase**. It is a documented R47+ scope
target inside a docstring code block. There is no statement to consume
in a Path γ' DCT step.

The earlier grep `(theorem|lemma) multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef`
returned `GaussianParametricAnalysis.lean:168` because the docstring
literally contains the word `theorem` inside its markdown code block
— this is a **false positive** from grep on the documentation, not a
real Lean theorem.

### Implication for R48 T2.1

The Path γ' DCT step (3) consumer "Gaussian tail majorant" does not
exist as a Lean object. To consume it in a Phase 2 body close one
would first need to **land the tail bound as a Full theorem** —
estimated ~60-100 LOC per the
`GaussianParametricAnalysis.lean` docstring (lines 61-66). This is
itself a separate sub-round target.

The Path γ' chain step (3) as written is therefore **not executable
in R48** as a single sub-step.

---

## §4 — Combined LOC re-estimate (post-T1.1)

Path γ' Phase 2 body Full close, honest LOC:

| Sub-step | Brief estimate | Verified estimate | Blockers |
|---|---|---|---|
| (1) Linear path Σ_path | 20-30 | 20-30 | none (Phase 1A R43-T2.2 already Full) |
| (2) Pdf S-differentiability | 20-30 | 80-150 | R40 `Matrix.det.differentiable` Stub at `MatrixDetDifferentiable.lean:149` |
| (3) DCT chain step | 20-30 | 50-100 + tail-bound prerequisite | tail-bound Full theorem missing (~60-100 LOC) |
| Lipschitz envelope (sub-gap C) | not in brief | 150-300 | (2) chain |
| (4) Existence conclusion | 10-20 | 10-20 | none (mechanical) |
| **Total** | ~80-100 | **~380-700** | R40 Stub chain |

The "~80-100 LOC" estimate in the R48 brief is **off by roughly a
factor of 4-7×** when the missing tail-bound Full theorem and the
R40-blocked pdf S-differentiability chain are included.

### Path γ' "axiom-equivalent" treatment of MGE — does it reduce LOC?

The brief proposes to "treat MGE sub-gap (b) as axiom-equivalent
oracle." We verify what this buys: MGE Stub closure. But the cost
inflation in Path γ' is NOT in MGE — it is in:

1. R40 `Matrix.det.differentiable` Stub (separate from MGE chain).
2. The non-existent tail-bound Full theorem (separate from MGE chain).
3. The Lipschitz envelope sub-gap (C) (depends on (1)).

**Treating MGE as axiom-equivalent does not unblock any of (1)-(3).**
The "axiom-equivalent" treatment of MGE saves the MGE Stub closure
work itself, but Phase 2 body Full close consumes MGE only
transitively via MGI's first `rw` step — and MGI as currently written
in the repo already has a Full body modulo MGE, so the MGE
"axiom-equivalent" treatment changes nothing about the Phase 2 body
chain dependencies.

---

## §5 — Audit summary: 6th consecutive Grok pre-flight misframing

### Pattern

| Round | Misframing caught by T1.1 | File:line cite |
|---|---|---|
| R40 | (various — pre-discipline rounds) | various |
| R44 | "Jacobi formula" framing for MGE | `R44_T1_BodyCloseAudit.md` §2 |
| R45 | Path γ "300-350 LOC" understated by ~2× | `R45_T1_FramingVerificationAudit.md` |
| R46 | "Matrix.PosDef.isOpen globally" — false (PosDef ⊂ closed Hermitian subspace) | `R46_T1_GrepAuditAndFramingVerification.md` §4 |
| TC2 | "Gauss inverse iff for all p" — false outside Ioc 0 1 | TC2 commit `db53be1` |
| R47 | sub-gap (b) "80-120 LOC" — three intermediate bridges, ~150-280 LOC | `R47_T1_GrepAuditAndFramingVerification.md` §2 |
| **R48** | **(this round) Path γ' "MGI provides density differentiability" — Lean MGI is integral rewrite, NOT differentiability; tail bound theorem does not exist** | this audit §2-§3 |

The Q4 ii Local Claude grep audit pipeline continues to be the primary
defense against scope misalignment. R48 is the 6th distinct Grok
pre-flight misframing caught at the T1.1 stage, **before** scope
commitment.

### Confidence calibration

Pre-audit P(Path γ' Phase 2 body Full close in ~80-100 LOC) per brief:
**0.65-0.75**.

Post-audit P(Path γ' Phase 2 body Full close in ~80-100 LOC):
**< 0.05**. The chain is blocked on the R40 Stub plus the missing
tail-bound theorem; "~80-100 LOC" is mathematically inconsistent with
the Lean state.

Post-audit P(Phase 2 body honest TAG'd sub-Stub with concrete chain
composition blocker, per brief abort rules): **0.95**.

---

## §6 — R48 scope decision (post-audit)

### T2.1 outcome (recommended, brief-aligned)

Land Phase 2 body Stub at `MultivariateGaussianCDF.lean:160-313` as
**honest TAG'd sub-Stub** with concrete chain-composition diagnostic
citing:

1. **Misframing #1 disambiguation.** Lean MGI
   (`multivariateGaussianOrthantCDF_eq_lebesgue_integral`) is the
   integral rewrite, NOT the literature MGI / generic chaining
   inequality for Gaussian suprema. Path γ' step (2) "density
   differentiability via MGI" is not reachable: pdf S-differentiability
   requires the R40 `Matrix.det.differentiable` Stub
   (`MatrixDetDifferentiable.lean:149`) to close first.

2. **Misframing #2 disambiguation.** `GaussianParametricAnalysis.lean`
   contains R46-helper re-exports (lines 103-154) plus docstring
   scaffolding (lines 156-198) for R47+ scope. The Gaussian tail
   majorant (`multivariateGaussianPdf_uniform_tail_bound_on_compact_posDef`)
   is NOT a Lean theorem; its docstring estimate (~60-100 LOC) is a
   separate sub-round target. Path γ' step (3) "DCT chain via tail
   majorant" is not executable until that helper lands.

3. **Realistic LOC.** Phase 2 body Full close requires ~380-700 LOC,
   not ~80-100. The dominant cost is the Lipschitz envelope
   sub-gap (C) at ~150-300 LOC blocked on R40, plus the tail-bound
   helper at ~60-100 LOC. The MGE "axiom-equivalent" treatment from
   Path γ' does not reduce these costs.

This is **diagnostic-quality enhancement**, not Full close. Net
retirement: 0 sorries. Brief abort rule honored: TAG'd sub-Stub WITH
concrete chain composition blocker → not capped at 50%.

### Why not pivot to a different scope?

The brief explicitly forbids:

> ❌ **"Reopen MGE/sub-gap(b) work"** — out of R48 scope.

And:

> ❌ **"Plan doc as substitute for code"** — T2.1 must be Lean code
> modifications, Phase 2 body Full closed.

T2.1 commits Lean code modifications (the diagnostic enhancement to
the Phase 2 body Stub at `MultivariateGaussianCDF.lean:160-313`),
satisfying the "Lean code modifications" requirement. Pivoting T2.1
to a different scope (e.g., landing the tail-bound helper as Full)
would require user approval and is therefore not undertaken in this
round.

### Stretch retained

T3.1 (TD3 + TC2 coordination notes) and T3.2 (GLW shortcut prep stub
in `GLWSmallBallShortcut.lean`) remain in R48 scope per the brief and
are independent of the Path γ' framing problem.

### Aspirational R48-R52 trajectory (post-audit)

Per brief's hybrid (c) gate analysis, R52 milestone target ≤ 8 items
on mainline. Net retirement R48: 0 (this round) → **17 items
unchanged**. R49-R52 must therefore retire 9 items in 4 rounds (i.e.,
2.25/round average), unchanged from R47 close. The compression bundle
gate viability (Grok ~55-60%) is not affected by R48's lower-
distribution outcome on the Phase 2 body subitem; the dominant
compression-bundle leverage is still GLW shortcut (R50-R51) +
Track D round 3 + Track C round 2 + parallel cleanup.

---

## §7 — R48 process discipline notes

* T1.1 audit COMPLETED at T+~0:30 per sub-checkpoint timing.
* T2.1 commits a diagnostic-quality enhancement to Phase 2 body Stub
  at `MultivariateGaussianCDF.lean:160-313` citing this audit's
  findings (no Full close attempt; chain blocker concrete).
* T2.2 build verification immediately after T2.1.
* T2.3 status doc + AXIOM_INVENTORY update at T+2:15.
* Stretch T3.1 + T3.2 if landed by T+2:30 hard-stop.

**End R48-T1.1 audit.**
