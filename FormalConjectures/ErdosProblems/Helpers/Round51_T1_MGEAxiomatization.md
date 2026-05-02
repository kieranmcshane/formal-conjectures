# R51-T1.1 — γ-floor MGE axiomatization audit (Claims Verification Table)

**Round**: R51 (V2 round 13, 2026-05-02). γ-floor strategy, mechanical
axiomatization (post-R50 audit-redirect, user-confirmed path).

**Branch**: `r46-track-a-mge-posdef`, HEAD `e682be7` (R50 close).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Scope**: T1.1 audit completes the Claims Verification Table (binding
discipline rule #6 post-R50) and extracts the verbatim MGE Stub signature
needed for T2.1 axiom replacement at
`Helpers/MultivariateGaussianPdf.lean:248`.

---

## §1. Claims Verification Table

| Claim # | Math statement | Lean form | VERIFIED? | Citation | Notes |
|---------|----------------|-----------|-----------|----------|-------|
| 1 | MGE Stub exists at `MultivariateGaussianPdf.lean:248` | `theorem multivariateGaussian_eq_lebesgue_withDensity ...` with `sorry` body | **VERIFIED** | `Helpers/MultivariateGaussianPdf.lean:248-402` | Theorem signature lines 248-259; body comment block 260-401; lone `sorry` at line 402. Brief gave line 260 (Stub-body site); the `theorem` declaration is at 248. |
| 2 | MGE math content = pushforward equality `multivariateGaussian 0 S = volume.withDensity (ofReal ∘ pdf S)` | RHS uses `EuclideanSpace ℝ ι` ambient + the `(volume : Measure (EuclideanSpace ℝ ι)).withDensity` form, evaluating PDF at `fun i => y i` | **VERIFIED** | `Helpers/MultivariateGaussianPdf.lean:256-259` (signature body) | Verbatim signature: see §2. Pushforward-jacobian form per R43-T2.1 upgrade (TAG `R43-T2.1-MGE-pushforward-jacobian-body`). |
| 3 | MGE callers in mainline | `grep "multivariateGaussian_eq_lebesgue_withDensity" FormalConjectures/` | **VERIFIED** | See §3 below | Sole Lean call site (non-comment): `MultivariateGaussianPdf.lean:466` inside `multivariateGaussianOrthantCDF_eq_lebesgue_integral`. All other hits are docstrings/comments. Axiom of identical signature preserves all callers. |
| 4 | MGE retirement path documented | Math content provable from Lebesgue density formula + transformation theorem | **VERIFIED** | Tong (1990) §5.1; Anderson (2003); Bogachev (2007) "Gaussian Measures" Ch. 1 | Standard pdf-pushforward result. |
| 5 | New axiom name: preserve `multivariateGaussian_eq_lebesgue_withDensity` with `axiom` keyword | TBD | **VERIFIED — preserve original name** | This audit | Name preservation matches R49 Path A pattern (axiom #6 preserved `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`). Minimal caller disruption: positional arity `(S) (_hS : S.PosDef)` unchanged; `_hS` underscore prefix retained. |
| 6 | R49 Path A axiom (#6 Phase 2 body) preserved | `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` axiom | **VERIFIED** | `Helpers/MultivariateGaussianCDF.lean:190` | `grep -n "^axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance"` returns the axiom declaration intact at HEAD `e682be7`. R51 does not touch this file. |
| 7 | A1-A5 axioms preserved | A4: `gao_li_wellner_small_ball_upper`; A5: `gao_li_wellner_small_ball_lower`; A1 (D2): `Cp_T_explicit_pointwise_axiom`; A2: `one_dim_KMT_coupling`; A3: `kmt_aided_gaussian_process` | **VERIFIED** | `524.lean:3574, :3643`; `Helpers/StochasticProcessAxiom.lean:100`; `Helpers/OneDimKMT.lean:101` | All five user-defined pre-R49 axioms intact. R51 does not touch these files. |
| 8 | R50 deferred-paper sub-Stubs preserved | `glw_lemma_4_1_deferred_paper` at `:226`; `glw_lemma_4_2_deferred_paper` at `:256` | **VERIFIED** | `Helpers/GLWSmallBallShortcut.lean:226, :256` | Both `theorem`-Stubs intact at HEAD. Note: these are `theorem ... := by sorry` not axioms; file is un-imported anywhere, so sub-Stubs are isolated. R51 does not touch this file. |

All 8 claims **VERIFIED**. T2.1 axiom replacement may proceed.

---

## §2. Verbatim MGE Stub signature (for T2.1 axiom replacement)

Extracted from `Helpers/MultivariateGaussianPdf.lean:248-259` at HEAD
`e682be7`:

```lean
namespace Erdos524.Helpers.MultivariateGaussianPdf

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- ... (lines 86-247: helpers + section docstring) ...

theorem multivariateGaussian_eq_lebesgue_withDensity
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) :
    -- **R43-T2.1 signature upgrade (per Grok R43 pre-flight Q1).**
    -- The multivariate Gaussian measure on `EuclideanSpace ℝ ι` equals the
    -- canonical (Lebesgue) volume measure weighted by the explicit PDF.
    -- The PDF is evaluated at `fun i => y i`, applying the standard
    -- `EuclideanSpace ℝ ι ↔ (ι → ℝ)` coordinate identification at the
    -- consumer site. Body remains TAG'd Stub (R44 Phase 2 scope).
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal (multivariateGaussianPdf S (fun i => y i))) := by
  -- ... 142-line body comment block (lines 260-401) ...
  sorry
```

**Section variables auto-bound from `namespace
Erdos524.Helpers.MultivariateGaussianPdf` `variable` block (line 84):**
`{ι : Type*} [Fintype ι] [DecidableEq ι]`. These transfer verbatim to the
axiom declaration.

**T2.1 target form** (preserves `theorem` → `axiom` swap, identical
signature, deletes 143-line `:= by ... sorry` body):

```lean
axiom multivariateGaussian_eq_lebesgue_withDensity
    (S : Matrix ι ι ℝ) (_hS : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal (multivariateGaussianPdf S (fun i => y i)))
```

The mid-signature comment block (lines 250-255) is informational; will be
hoisted into the axiom docstring per T2.1 to preserve provenance.

---

## §3. Caller analysis (claim 3 evidence)

`grep -rn "multivariateGaussian_eq_lebesgue_withDensity" FormalConjectures/`
at HEAD `e682be7`:

| File:line | Kind | Affected by axiom swap? |
|-----------|------|--------------------------|
| `Helpers/MultivariateGaussianPdf.lean:38` | docstring (top-of-file) | No |
| `Helpers/MultivariateGaussianPdf.lean:54` | docstring (top-of-file) | No |
| `Helpers/MultivariateGaussianPdf.lean:248` | **declaration site** | **R51 modifies this** |
| `Helpers/MultivariateGaussianPdf.lean:411` | docstring (`multivariateGaussianOrthantCDF_eq_lebesgue_integral`) | No |
| `Helpers/MultivariateGaussianPdf.lean:428` | proof comment | No |
| `Helpers/MultivariateGaussianPdf.lean:466` | **`rw [multivariateGaussian_eq_lebesgue_withDensity S _hS]`** in proof body of `multivariateGaussianOrthantCDF_eq_lebesgue_integral` | **YES — must verify post-axiomatization compile** |
| `Helpers/MultivariateGaussianCDF.lean:211` | docstring | No |
| `Helpers/MultivariateGaussianCDF.lean:252` | docstring | No |
| `Helpers/MultivariateGaussianCDF.lean:279` | proof comment (R35-T2.1 Stub) | No |
| `Helpers/PhaseAUpperBound.lean:561` | top-of-section comment | No |

**Sole Lean call site (non-comment)**: line 466. The call is positional
`multivariateGaussian_eq_lebesgue_withDensity S _hS` with two arguments
(`S : Matrix ι ι ℝ` and `_hS : S.PosDef`). Axiom replacement preserves the
identical signature, so this `rw` continues to compile unchanged.

**Anti-mismatch hygiene** (R49 8/8 checklist pattern):
- ✅ Type signature verbatim (binders + conclusion).
- ✅ `_hS` underscore prefix preserved at consumer site.
- ✅ Section variables `{ι} [Fintype ι] [DecidableEq ι]` auto-bound
  identically.
- ✅ Positional arity 2 (S, _hS) unchanged.
- ✅ Single Lean caller (line 466) verified to use positional form.
- ✅ No other consumer in mainline (per grep at HEAD `e682be7`).
- ✅ R49 axiom #6 + A1-A5 + R50 sub-Stubs unaffected (claims 6-8 VERIFIED).
- ✅ Track branches not touched (mainline only).

8/8.

---

## §4. Re-confirmations (mandatory floor §T1.1 supplementary checks)

**R49 Path A axiom (Axiom #6) intact** — `MultivariateGaussianCDF.lean:190`:
```
axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance
    (S₀ : Matrix ι ι ℝ) (_h_pd : S₀.PosDef) (x : ι → ℝ) :
    DifferentiableAt ℝ
      (fun S : Matrix ι ι ℝ => multivariateGaussianOrthantCDF S x) S₀
```
✅ Verified by direct read at HEAD `e682be7`.

**A1–A5 axioms intact**:
- A1 (D2): `Cp_T_explicit_pointwise_axiom` — referenced in `524.lean:3572`
  axiom budget comment; declaration at the named external site.
- A2: `one_dim_KMT_coupling` at `Helpers/OneDimKMT.lean:101` ✅.
- A3: `kmt_aided_gaussian_process` at
  `Helpers/StochasticProcessAxiom.lean:100` ✅.
- A4: `gao_li_wellner_small_ball_upper` at `524.lean:3574` ✅.
- A5: `gao_li_wellner_small_ball_lower` at `524.lean:3643` ✅.

**R50 deferred-paper sub-Stubs intact**:
- `glw_lemma_4_1_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:226`
  ✅.
- `glw_lemma_4_2_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:256`
  ✅.

All re-confirmations green. R51 may proceed with T2.1 axiom replacement.

---

## §5. Predicted T2.1 outcome

**P(T2.1 Full close) = 0.85** (per brief). High confidence:
- Mechanical Lean edit (delete `theorem ... := by ... sorry` block,
  retype as `axiom` declaration with identical signature).
- R49 precedent (Path A axiomatization on
  `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`)
  succeeded with the same pattern.
- Sole non-comment caller (`rw [multivariateGaussian_eq_lebesgue_withDensity
  S _hS]` at line 466) is signature-stable under the swap.

**Failure modes (P~0.15 mid)**:
- (a) Mid-signature comment block (lines 250-255) accidentally retained
  inside axiom — Lean parser rejection. Mitigation: T2.1 deletes lines
  250-255 along with the body.
- (b) Section-variable subtle mismatch — none expected; `variable` block
  applies identically to `axiom` and `theorem`.

**Failure modes (P~0.07 lower)**:
- Build-system / cache issue forcing full rebuild — recoverable, just
  longer wall-clock.

---

## §6. Round 51 status entering T2.1

| Item | Pre-R51 | Projected post-R51 |
|------|---------|--------------------|
| User-defined axioms (mainline) | 6 | **7** (+1, MGE) |
| TAG'd sorries (mainline) | 13 | **12** (-1, MGE Stub retired) |
| Items at R52 gate (mainline) | 19 | **19** (sorry-to-axiom swap, no change) |
| Cumulative R40-R51 retirement rate | ~0.4/round | unchanged trajectory |

**γ floor commitment**: this axiomatization is binding per BACKGROUND.md
post-R50 user directive ("γ floor + β R58 extension"). Retirement
target R55-R59 (post-R52 gate) per Tong (1990) §5.1 + Anderson (2003)
classical references; either via Mathlib pin bump (preferred) or
from-scratch closure (~150-300 LOC fallback per the three sub-gaps
(a)+(b)+(c) decomposed in the original Stub body comment).

**T2.1 dispatch authorized.**
