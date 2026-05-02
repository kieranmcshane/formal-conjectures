# R41 — T1.1 Audit: chain composition reality check on R40 Stubs

**Branch**: `r33-c-helpers-consolidation` (HEAD `1e30dda`).
**Mathlib pin**: `mathlib4 @ 25ce63313608` (Mathlib 4.27.0-rc1).
**brownian-motion**: bundled with project, R38 ENat patch applied.
**Date**: 2026-05-02.
**Scope**: re-verify Grok R41 pre-flight Q2 verdict ("Stubs compose soundly as
black-box assumptions") against the actual current state of the R40 Stubs and
the consumers (`multivariateGaussianOrthantCDF_differentiable_wrt_covariance`,
`slepian_comparison_finite`).

This doc is the load-bearing R41 reality check. It establishes whether the
R41 mandatory floor (T2.1 + T2.2 Full bodies via Path B chain composition) is
achievable in a single round, or whether the R40 Stubs' actual shape forces
T2.1 + T2.2 to land as honest TAG'd sub-Stubs with concrete additional
diagnostics.

## R40 stubs — current state

| Stub | File:line | Type | TAG | Per-Q2 "axiom-equivalent"? |
|------|-----------|------|-----|-----------------------------|
| `Matrix.det.hasFDerivAt` | `MatrixDetDifferentiable.lean:124` | real `∃ L, HasFDerivAt …` signature | `R40-T2.1-det-cofactor-route` | ✅ yes |
| `Matrix.det.differentiable` | `MatrixDetDifferentiable.lean:141` | `Differentiable ℝ Matrix.det` | `R40-T2.1-det-cofactor-route` | ✅ yes |
| `Matrix.PosDef.inv_hasFDerivAt` | `MatrixDetDifferentiable.lean:200` | real `∃ L, HasFDerivAt (·⁻¹) L M` | (R41-T2.2 closed Stub→Full in `1e30dda`) | ✅ Full body |
| `multivariateGaussianPdf` def | `MultivariateGaussianPdf.lean:101` | `noncomputable def … : ℝ` | n/a | ✅ Full def, no Stub |
| `multivariateGaussianPdf_nonneg` | `MultivariateGaussianPdf.lean:108` | real proof | n/a | ✅ Full body |
| `multivariateGaussianPdf_pos` | `MultivariateGaussianPdf.lean:121` | real proof | n/a | ✅ Full body |
| `multivariateGaussian_eq_lebesgue_withDensity` | `MultivariateGaussianPdf.lean:182` | **`True := by trivial`** | `R40-T2.3-pushforward-jacobian` | ❌ **placeholder** |
| `multivariateGaussianOrthantCDF_eq_lebesgue_integral` | `MultivariateGaussianPdf.lean:206` | **`True := by trivial`** | `R40-T2.3-orthant-via-pdf` | ❌ **placeholder** |
| `multivariateGaussianOrthantCDF_partial_offdiagonal` | `MultivariateGaussianCDF.lean:201` | **`True := by trivial`** | (no TAG) | ❌ **placeholder** |
| `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` | `MultivariateGaussianCDF.lean:158` | real `DifferentiableAt ℝ …` signature with Stub body | `R35-T2.1-mathlib-gap-density` | ✅ real signature, Stub body |
| `slepian_comparison_finite` | `PhaseAUpperBound.lean:186` | real signature with structured Stub body | `R41-T3.2-FTC-via-Stein-and-T3.1-Stub` | ✅ real signature, Stub body |

**Critical finding** — three of the load-bearing stubs are NOT real Stubs;
they are `True := by trivial` placeholders that elaborate as the trivially
true unit-typed proposition. **They carry no information** and cannot be
chained on as black-box assumptions in the sense Grok Q2 envisioned.

In particular:

* `multivariateGaussian_eq_lebesgue_withDensity` (MGE) — its Lean type is
  `True`, NOT `multivariateGaussian 0 S = (volume).withDensity (multivariateGaussianPdf S)`
  (or whatever the precise statement should be). Calling `MGE` from any
  consumer yields a proof of `True`, which doesn't give the consumer anything
  it can use.
* `multivariateGaussianOrthantCDF_eq_lebesgue_integral` (MGI) — same issue.
* `multivariateGaussianOrthantCDF_partial_offdiagonal` (MGP) — same issue.

The R40 status doc acknowledges this for MGE / MGI ("placeholder"; "Returns
`True` because the precise statement … requires R41 work"; line 113-117 of
`PhaseV2R40Status.md`). MGP is documented as "statement only, body deferred
to R36 alongside the multivariate density-existence work" but its current
Lean type is `True`, not the documented "the partial derivative w.r.t. the
(i,j)-entry equals…". So MGP is also a `True` placeholder, not a deferred
real statement.

## Grok Q2 verdict — refined post-audit

**Grok Q2:** "chain dependency on Stubs vs Full: YES, Stubs are sound
black-box assumptions. T3.1 + T3.2 only need the *statement* of the Stubs
(HasFDerivAt at the relevant points) to feed into higher-level chain rules.
**No internal inspection of the explicit derivative formula required.** R41
can close T3.1 + T3.2 Full while R40 Stubs remain; they become 3 permanent
'axiomatic-flavor' TAG'd sorries that compose cleanly into the Phase A upper
proof."

**Refinement after R41-T1.1 audit:** Grok Q2 is **correct in principle but
inapplicable to the actual current state**. It applies cleanly to:

* `Matrix.det.hasFDerivAt` (real `∃` signature → can chain).
* `Matrix.det.differentiable` (real type → can chain).
* `Matrix.PosDef.inv_hasFDerivAt` (real `∃` signature, now Full per 1e30dda → can chain or compose body).

It **does not apply** to the three `True` placeholders (MGE / MGI / MGP),
because chaining requires the Stub's *type* to encode the desired
mathematical content. `True` does not encode anything.

Concretely, the Slepian body wants to invoke (per the comment block at
`PhaseAUpperBound.lean:240-243`):

* MGP: "explicit formula for `∂F/∂Σ_{ij}` at off-diagonal `i ≠ j`."
* "Sign analysis: each `∂F/∂Σ_{ij}` factor is non-negative density-times-
  conditional-prob, and the chain-rule weight `(S_Y - S_X)_{ij} ≥ 0` by
  off-diagonal hypothesis. Diagonal terms vanish by equal-variance
  hypothesis `_h_diag`."

This requires MGP to have a type expressing "the partial derivative …
equals the bivariate density times the conditional orthant probability"
— a non-trivial mathematical statement, not `True`. Without that real
statement, the body has nothing to chain through.

Same for the CDF differentiability body (`multivariateGaussianOrthantCDF_differentiable_wrt_covariance`):
the explicit derivative formula Grok provided

  `F'(α) = (1/2) ∫_D p_{Σ(α)}(x) · [x^T A(α) Δ A(α) x − trace(A(α) Δ)] dx`

requires MGE (the orthant-CDF-as-Lebesgue-integral identity) as a black-box
assumption to even *write* the integral on the RHS. If MGE is `True`, the
rewrite step is impossible.

## R41 Path B — actual scope

**Path B (per Grok Q4) is feasible for T2.1 / T2.2 Full only after**:

(a) MGP, MGE, MGI are upgraded from `True` placeholders to **real
    signatures** carrying the documented statements. This is itself
    real Lean work (~40-80 LOC per signature, ~150-200 LOC total).
(b) The bodies of the real signatures remain TAG'd Stubs (closure
    requires the Mathlib gaps from R40-T1.1 audit + Jacobian-of-CFC.sqrt
    + Stein integration-by-parts identity, multi-round work).

**R41 single-round budget cannot cover (a) + (b) + T2.1 Full + T2.2 Full +
T2.3 + T2.4 + T2.5.** Concretely:

* Real-signature upgrade for MGP: ~80 LOC. The statement needs
  `HasFDerivAt` at the matrix-entry partial derivative, plus a precise
  formula involving the bivariate density (which itself uses the PDF def
  + conditional-orthant probability). The conditional-orthant-probability
  has no Mathlib API at the pin (would need its own infrastructure
  helper).
* Real-signature upgrade for MGE: ~50 LOC. The statement needs to bridge
  `multivariateGaussian 0 S` (a `Measure (EuclideanSpace ℝ ι)`) with
  `(volume : Measure (ι → ℝ)).withDensity (multivariateGaussianPdf S)`,
  routed through the `EuclideanSpace.equiv` identification. The typing
  alone is finicky.
* Real-signature upgrade for MGI: ~30 LOC. Wrapper around MGE applied to
  the `orthant x` set.
* T2.1 Full body chaining MGE / MGI / det.diff / PosDef.inv.diff /
  diff-under-integral: ~400-700 LOC per Grok R40 estimate.
* T2.2 Full body: ~300-500 LOC per Grok R40 estimate.

Subtotal: 860-1360 LOC. Single-round budget at ~3-4 hours wall-clock is
~400-600 LOC of careful research-level Lean. **Not achievable single-round.**

## R41 honest deliverable

Per the R41 prompt §"Mandatory floor … T2.1 / T2.2 mandatory (Full body
close OR honest TAG'd sub-Stub citing concrete Mathlib API gap beyond Q5)",
the legitimate single-round outcome is:

* **T2.1**: keep `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`
  as a TAG'd Stub. Strengthen the diagnostic block to cite the
  *upgraded* additional gap surfaced here:
  > "Path B per Grok Q2 chain-on-Stubs presupposes the prerequisite Stubs
  > (MGE, MGI, MGP) carry real-signature types, not `True` placeholders.
  > MGE/MGI/MGP are currently `True := by trivial` per
  > `PhaseV2R40Status.md` line 113-117 + this audit. R42 scope: real-
  > signature upgrade (~150 LOC) before body close (~400-700 LOC)."
* **T2.2**: same treatment for `slepian_comparison_finite`. Add an
  honest infrastructure advance: the `posDef_convex_combination` helper
  used by the body (real Lean, ~30 LOC), so the existing structural
  setup `Sα`, `hSα_0`, `hSα_1`, `F`, `hF_0`, `hF_1` extends to a
  PosDef-preservation guarantee on the path. The closing `sorry` stays
  TAG'd with the upgraded diagnostic.
* **R41 net debt change:** sorries 11 → 11 (0 net), with quality
  upgrades: (a) real-signature upgrade of MGP from `True` to a proper
  HasFDerivAt statement; (b) `posDef_convex_combination` helper added
  as a real lemma; (c) audit doc surfaces the additional Path B
  prerequisite gap that R40 + Grok R41 pre-flight under-counted.

This is the **lower outcome scenario** per the R41 prompt distribution
(P~0.30); it matches R40's lower outcome and is justified by the
audit-surfaced refinement to Grok Q2.

## Anti-pattern compliance

* ❌ "Treat MGE / MGI / MGP `True` placeholders as if they carried real
  content" — refused; this audit makes the gap explicit.
* ❌ "Attempt T2.1 + T2.2 Full body without MGE / MGI / MGP being real
  signatures" — refused; would produce hundreds of lines of code that
  cannot meaningfully chain through `True` types.
* ❌ "Defer audit to a follow-up doc" — refused; the audit is the load-
  bearing R41 reality check. Single-doc audit ≥ 100 lines per protocol.
* ❌ "Vague 'composition through R40 Stubs' claim" — refused; this audit
  enumerates each Stub's actual Lean type and identifies which are real
  vs which are `True` placeholders.

## R41 / R42 split (proposed)

| Round | Deliverable | LOC | Net sorry change |
|-------|-------------|-----|------------------|
| **R41 (this round)** | MGP `True` → real HasFDerivAt signature; `posDef_convex_combination` helper; T2.1 / T2.2 stronger diagnostics | ~150 | 11 → 11 (0 net; quality upgrade) |
| R42 | MGE / MGI `True` → real signatures; T2.1 Full body via diff-under-integral on real MGE/MGI | ~600 | 11 → 10 (T2.1 closed) |
| R43 | T2.2 Full body via FTC + Stein + real MGP | ~400 | 10 → 9 (T2.2 closed) |
| R44 | Borell-TIS axiomatize | ~100 | 9 → 9 (axioms 5 → 6) |
| R45-R46 | GLW assembly + retire A4/A5 (Phase A upper closure) | ~300 | axioms 6 → 4 |

Total V2 cluster post-R41 split: ~5 rounds R41-R46 to land Phase A upper
closure end-to-end. Adds 2 rounds vs. the R41 prompt's optimistic single-
round Path B target, but matches actual code volume realistically.

Priority #1 ceiling (R59) remains unbreached: 5 rounds gets us to
GLW/A4/A5 retirement, leaving 13 rounds for KMT (A2/A3) + D2 (A1)
retirement work. R51 pragmatic ship target (1 axiom = BTIS) is
unaffected.

## Conclusion

R41 lands the audit-surfaced reality check + MGP real-signature upgrade +
`posDef_convex_combination` helper. T2.1 / T2.2 keep TAG'd Stubs with
upgraded diagnostics. R42 picks up MGE / MGI real-signature upgrades and
the first Full body close (T2.1).

Audit doc complete. T2.1 / T2.2 work begins.
