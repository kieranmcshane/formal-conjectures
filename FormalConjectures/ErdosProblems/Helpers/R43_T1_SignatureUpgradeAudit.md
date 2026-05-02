# R43 — T1.1 Audit: MGE / MGI signature upgrade + Phase 1A/1B scoping

**Branch**: `r33-c-helpers-consolidation` (HEAD `ee22963`,
tag `r42-v2-slepian-diagnostic-strengthening-lower-outcome`).
**Mathlib pin**: `mathlib4 @ 25ce63313608`.
**Round**: R43 (V2 round 5; Phase A upper round 5 of cluster).
**Date**: 2026-05-02.
**Path**: Grok R43 pre-flight Q4 verdict (b) — signatures + Phase 1A + Phase 1B.

This audit is the load-bearing R43 reality check. It locates the placeholder
sites, identifies the precedent signature pattern (MGP from `f991599`),
fixes the precise post-R43 type for each upgraded theorem, and establishes
where Phase 1A (linear path differentiability) and Phase 1B (chain rule on
R40 stubs) attach.

---

## 1. Placeholder inventory (R42 baseline)

Three R40-T2.3 stubs land at R42 with `True := by trivial` bodies. R41
upgraded one (MGP, in `MultivariateGaussianCDF.lean:274`); R43 upgrades the
remaining two:

| Stub | File:line (R42) | R42 type | R43 target |
|------|------------------|----------|-------------|
| `multivariateGaussian_eq_lebesgue_withDensity` (MGE) | `MultivariateGaussianPdf.lean:182` | `True` | real signature: pushforward measure equality |
| `multivariateGaussianOrthantCDF_eq_lebesgue_integral` (MGI) | `MultivariateGaussianPdf.lean:206` | `True` | real signature: orthant CDF = integral |

Both keep TAG'd Stub bodies (per Grok Q4 path (b) — body closure is R44 Phase 2 scope).

The three R40-T2.1 / T2.2 Stubs that ARE real signatures:

* `Matrix.det.hasFDerivAt` (`MatrixDetDifferentiable.lean:124`) — TAG'd Stub.
* `Matrix.det.differentiable` (`MatrixDetDifferentiable.lean:141`) — TAG'd Stub.
* `Matrix.PosDef.inv_hasFDerivAt` (`MatrixDetDifferentiable.lean:200`) — **Full** at R41 (`1e30dda`).

The R41 MGP signature upgrade in `MultivariateGaussianCDF.lean:274` is the
template R43 mirrors:
```
theorem multivariateGaussianOrthantCDF_partial_offdiagonal
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) (i j : ι)
    (_hij : i ≠ j) :
    ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt
      (fun α : ℝ =>
        multivariateGaussianOrthantCDF
          (S₀ + α • (Matrix.single i j (1 : ℝ) + Matrix.single j i (1 : ℝ))) x)
      d 0 := by
  -- TAG[R41-T2.1-bivariate-density-conditional]
  sorry
```
Pattern: `True` → real Lean type (≠ `True`) carrying an existential or
equality with information, plus a TAG'd `sorry` body with a concrete
Mathlib gap citation.

---

## 2. R43 signature upgrades — precise post-upgrade types

### 2.1 MGE (`multivariateGaussian_eq_lebesgue_withDensity`)

**Pre-R43 type**: `True`.

**Post-R43 type** (Grok Q1):
```
theorem multivariateGaussian_eq_lebesgue_withDensity
    (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun y => ENNReal.ofReal (multivariateGaussianPdf S
          (fun i => y i))) := by
  sorry  -- TAG[R43-T2.1-MGE-pushforward-jacobian-body]
```

**Mathlib gaps documented in body comment** (carry-over from R40-T2.3 audit):
- (a) Jacobian-of-`CFC.sqrt` identity `|det (CFC.sqrt S)| = Real.sqrt S.det`.
- (b) `stdGaussian_eq_lebesgue_withDensity` on `EuclideanSpace ℝ ι`.
- (c) Change-of-variables for constant-Jacobian linear pushforward.

**Key signature consideration**: `volume` here is the canonical Lebesgue
measure on `EuclideanSpace ℝ ι` (which exists via `MeasureSpace`). The
`fun i => y i` coordinate extraction handles the `EuclideanSpace ↔ (ι → ℝ)`
identification at the call site of `multivariateGaussianPdf`. A simpler
typed alternative is to keep `multivariateGaussianPdf` defined on `ι → ℝ`
and use `PiLp.equiv` / `EuclideanSpace.equiv` at call sites.

### 2.2 MGI (`multivariateGaussianOrthantCDF_eq_lebesgue_integral`)

**Pre-R43 type**: `True`.

**Post-R43 type**:
```
theorem multivariateGaussianOrthantCDF_eq_lebesgue_integral
    (S : Matrix ι ι ℝ) (hS : S.PosDef) (x : ι → ℝ) :
    Erdos524.Helpers.MultivariateGaussianCDF.multivariateGaussianOrthantCDF
        S x =
      ∫ y in Erdos524.Helpers.MultivariateGaussianCDF.orthant x,
        multivariateGaussianPdf S (fun i => y i) := by
  sorry  -- TAG[R43-T2.1-MGI-orthant-via-MGE-body]
```

**Mathlib gap**: derives from MGE via `MeasureTheory.withDensity_apply` /
`integral_withDensity_eq_integral_smul`. ~30 LOC consumer wrapper, deferred
to R44 alongside MGE body.

---

## 3. Phase 1A — `Σ_path` linear path differentiability scope

**Goal**: prove `Σ_path α := (1-α) • S_X + α • S_Y` has derivative
`(S_Y - S_X)` at every α ∈ ℝ.

**Statement target**:
```
theorem Σ_path_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S_X S_Y : Matrix ι ι ℝ) (α : ℝ) :
    HasDerivAt (fun α : ℝ => (1 - α) • S_X + α • S_Y)
      (S_Y - S_X) α := by
  ... -- mechanical: linear-combo of two affine paths
```

**Reuse**: `posDef_convex_combination` in `PhaseAUpperBound.lean:186` proves
the PosDef-preservation along the path (already Full at R41); R43 adds the
**differentiability** of the path itself, complementing the PosDef-stays-in-
PosDef-cone fact.

**Mathlib API used**:
- `HasDerivAt.const_smul` for `(1-α) • S_X` (via the linear combo
  `(α ↦ 1 - α)` differentiability)
- `HasDerivAt.add` to combine the two terms
- `HasDerivAt.smul_const` if needed for the scalar multiplication.

No Mathlib gaps. ~80-120 LOC including auxiliary lemmas (constant
differentiability, identity differentiability, smul-of-deriv).

**Attaches to**: this is the entry point for the chain rule in Phase 1B.

---

## 4. Phase 1B — chain rule composition on R40 stubs

**Goal**: prove that the composite
`α ↦ multivariateGaussianOrthantCDF (Σ_path α) x`
has a Fréchet derivative at α ∈ (0, 1) interior, *modulo* the R40
hypotheses being in place (PosDef of `Σ_path α`) and the CDF
differentiability lemma being available as a black-box assumption.

**Statement target** (Phase 1B output):
```
theorem multivariateGaussianOrthantCDF_hasDerivAt_along_Σ_path
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S_X S_Y : Matrix ι ι ℝ) (h_X : S_X.PosDef) (h_Y : S_Y.PosDef)
    (x : ι → ℝ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ
      (fun α : ℝ =>
        Erdos524.Helpers.MultivariateGaussianCDF.multivariateGaussianOrthantCDF
          ((1 - α) • S_X + α • S_Y) x) α := by
  ...
```

(Choosing `DifferentiableAt` rather than `HasDerivAt` with explicit
formula — keeps the explicit derivative formula as R44 Phase 2 scope. This
matches Grok Q2 split and keeps Phase 1B sub-300 LOC.)

**Composition route**:
- (i) `Σ_path_hasDerivAt` from Phase 1A → `Σ_path` is differentiable at α.
- (ii) `posDef_convex_combination` → `Σ_path α` is PosDef at α ∈ [0, 1].
- (iii) `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`
        (R35-T2.1 Stub, **real signature**) → `S ↦ orthantCDF S x` is
        differentiable at every PosDef matrix.
- (iv) `DifferentiableAt.comp` on the composition.

**Mathlib API**: `DifferentiableAt.comp`, `HasDerivAt.differentiableAt`,
identity & const lemmas. The R35-T2.1 lemma is a TAG'd Stub (real
signature) so Phase 1B chains through it as a black-box assumption.

**Sub-Stub deferred to R44 (TAG'd `R43-T2.3-Phase1B-explicit-form-deferred-R44`)**:
the explicit derivative formula
`F'(α) = ⟨fderiv ℝ orthantCDF (Σ_path α), S_Y - S_X⟩`
in coordinate-form `∑_{i,j} (S_Y - S_X)_{ij} · ∂F/∂Σ_{ij}`. Phase 1B
proves the composite is `DifferentiableAt`; the explicit chain-rule formula
that exposes the entry-by-entry decomposition is R44 scope. This is exactly
the Grok Q4 split: Phase 1 ends at "differentiable along the linear path
with R40 stub derivatives plugged in".

---

## 5. R43 LOC budget vs Grok Q2

| Outcome | Grok Q2 LOC | This audit's LOC | Δ |
|---|---|---|---|
| T2.1 MGE+MGI signatures | ~80 | ~70-90 | within band |
| T2.2 Phase 1A | ~80-120 | ~60-120 | within band (lower end if Mathlib already has `HasDerivAt` for affine maps in `Matrix n n ℝ` directly) |
| T2.3 Phase 1B | ~100-150 | ~80-150 | within band |
| **Total** | **~250-300** | **~210-360** | within Grok band |

R43 lands within Grok Q2 budget; bias toward lower end if `posDef_convex_combination`'s already-Full helpers + Mathlib's affine-map differentiability cover most of Phase 1A mechanically.

---

## 6. Net debt forecast

R43 mid-distribution: 11 → 13 sorries (+2 from MGE/MGI signature upgrades; deferred sub-Stub absorbed by Phase 1B). 0 axiom change (5 → 5).

R43 lower-distribution: 11 → 14 sorries (Phase 1B's explicit-form sub-Stub
counted separately, e.g. inside Phase 1B body as a `sorry` with
`R43-T2.3-Phase1B-explicit-form-deferred-R44` tag).

R44 trajectory: Phase 2 closes MGE + MGI bodies + CDF differentiability Full
body (~300-350 LOC). Net debt: 13/14 → 11.

R59 ceiling check (per R42 doc + Q5 compression option): unchanged at 17 rounds (R43 → R59) with 1 round buffer via BTIS-merge if any later round slips.

---

## 7. Status

**T1.1 audit**: complete. Phase 1A and Phase 1B targets are precisely
specified. R43 mandatory floor proceeds to T2.1 (signatures), T2.2 (Phase
1A), T2.3 (Phase 1B), T2.4 (build + status).
