# R53-T1.1 — γ-floor `Matrix.det.differentiable` axiomatization audit (Claims Verification Table)

**Round**: R53 (V2 round 15, 2026-05-02). γ-floor strategy, mechanical
axiomatization (post-R52 user-confirmed dispatch — same R49 + R51
pattern: `theorem ... := by sorry` → `axiom ...` of identical signature
to free mainline budget for downstream retirements).

**Branch**: `r46-track-a-mge-posdef`, HEAD `c38c250` (R52 close).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Scope**: T1.1 audit completes the Claims Verification Table (binding
discipline rule #6) and extracts the verbatim `Matrix.det.differentiable`
Stub signature for T2.1 axiom replacement at
`Helpers/MatrixDetDifferentiable.lean:141-149`.

---

## §1. Claims Verification Table

| Claim # | Math statement | Lean form | VERIFIED? | Citation | Notes |
|---------|----------------|-----------|-----------|----------|-------|
| 1 | `Matrix.det.differentiable` Stub exists at `MatrixDetDifferentiable.lean:141-149` | `theorem Matrix.det.differentiable {n : Type*} [Fintype n] [DecidableEq n] : Differentiable ℝ (fun A : Matrix n n ℝ => A.det) := by ... sorry` | **VERIFIED** | `Helpers/MatrixDetDifferentiable.lean:141-149` | Theorem signature lines 141-143; body comment + `sorry` lines 144-149. TAG `R40-T2.1-det-cofactor-route`. |
| 2 | Math content = global differentiability of determinant function `A ↦ A.det` on `Matrix n n ℝ` | `Differentiable ℝ (fun A : Matrix n n ℝ => A.det)` | **VERIFIED** | Same file, line 142-143 | Standard linear algebra: determinant is a polynomial in the entries (Leibniz expansion `det A = ∑_{σ ∈ Perm n} sign σ · ∏_i A i (σ i)`), hence smooth (in particular differentiable). |
| 3 | Callers in mainline | `grep -rn "Matrix.det.differentiable\|Matrix\.det\.hasFDerivAt"` returns 6 hits, all docstrings/comments | **VERIFIED — sole status: NO LEAN CALL SITES** | `524.lean:3514` (docstring), `MultivariateGaussianPdf.lean:242` (R51 comment), `GLWSmallBallShortcut.lean:220` (un-imported file comment), `MultivariateGaussianCDF.lean:46, :63, :177` (docstrings) | **No actual Lean code consumes `Matrix.det.differentiable` at HEAD `c38c250`**. All references are documentation (Mathlib gap citations + R40-R52 closure-path notes). Axiomatization is consumer-safe with zero call-site adjustment. |
| 4 | Retirement path documented | Standard Leibniz expansion + polynomial differentiability | **VERIFIED** | Top-of-file docstring lines 30-32, 92-101 | Path α: `det A = ∑_{σ ∈ Perm n} sign σ · ∏_i A i (σ i)`; each summand is a polynomial in `A.i.j`; sum and product of differentiable functions; entry-extraction is `Matrix.entryLinearMap` (differentiable). Estimated ~100-200 LOC. |
| 5 | New axiom name: preserve `Matrix.det.differentiable` with `axiom` keyword | TBD | **VERIFIED — preserve original name** | This audit | Name preservation matches R49 (axiom #6 preserved `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`) + R51 (axiom #7 preserved `multivariateGaussian_eq_lebesgue_withDensity`) γ-floor patterns. Minimal caller disruption: zero current Lean callers, but future callers will use `Matrix.det.differentiable` by exactly its original name. |
| 6 | R49 axiom #6 + R51 axiom #7 + A1-A5 preserved | All 7 user-defined axioms intact at HEAD `c38c250` | **VERIFIED** | `MultivariateGaussianCDF.lean:190` (#6), `MultivariateGaussianPdf.lean:282` (#7), `524.lean:3574, :3643` (A4, A5), `OneDimKMT.lean:101` (A2), `StochasticProcessAxiom.lean:100` (A3), `GLWGaussianProjectiveLimit.lean:2013` (A1 D2) | All seven user-defined pre-R53 axioms intact. R53 does not touch these files. |
| 7 | R50 deferred-paper sub-Stubs preserved | `glw_lemma_4_1_deferred_paper`, `glw_lemma_4_2_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:226, :256` | **VERIFIED** | `Helpers/GLWSmallBallShortcut.lean:226, :256` | Both `theorem`-Stubs intact; un-imported file. R53 does not touch this file. |
| 8 | Companion `Matrix.det.hasFDerivAt` Stub at line 124-132 NOT modified | Stub preserved | **VERIFIED — companion Stub deliberately NOT axiomatized in R53** | `Helpers/MatrixDetDifferentiable.lean:124-132` | The brief specifies `Matrix.det.differentiable` axiomatization (singular). The companion `hasFDerivAt` Stub (existential form) shares the same TAG (`R40-T2.1-det-cofactor-route`) and same closure path but remains a Stub for now. Optional R54+ candidate for additional γ-floor axiomatization if needed. |

All 8 claims **VERIFIED**. T2.1 axiom replacement may proceed.

---

## §2. Verbatim `Matrix.det.differentiable` Stub signature (for T2.1 axiom replacement)

Extracted from `Helpers/MatrixDetDifferentiable.lean:141-149` at HEAD
`c38c250`:

```lean
namespace Erdos524.Helpers

open Matrix

-- ... (lines 75-140: helpers + Matrix.det.hasFDerivAt Stub) ...

/-- **Convenience wrapper signature.** `Matrix.det` is differentiable at every matrix.
Follows from `Matrix.det.hasFDerivAt` via `HasFDerivAt.differentiableAt`,
once the appropriate `NormedAddCommGroup (Matrix n n ℝ)` instance is in scope
(via `open Matrix` and `Mathlib.Analysis.Matrix.Normed`).

R40 leaves the body wrapped in the same TAG'd Stub diagnostic as the
`hasFDerivAt` form: closure is gated on Path α body close in R41. -/
theorem Matrix.det.differentiable
    {n : Type*} [Fintype n] [DecidableEq n] :
    Differentiable ℝ (fun A : Matrix n n ℝ => A.det) := by
  -- TAG[R40-T2.1-det-cofactor-route] : derivable from
  -- `Matrix.det.hasFDerivAt` once the `NormedAddCommGroup (Matrix n n ℝ)`
  -- instance synthesis is set up (entry-wise sup norm). For R40 scaffold
  -- purposes the unbundled signature is what consumers (Slepian's
  -- comparison + multivariate-CDF differentiability) need.
  sorry
```

**T2.1 target form** (preserves `theorem` → `axiom` swap, identical
signature, deletes the 5-line `:= by ... sorry` body):

```lean
axiom Matrix.det.differentiable
    {n : Type*} [Fintype n] [DecidableEq n] :
    Differentiable ℝ (fun A : Matrix n n ℝ => A.det)
```

Section variables: `Matrix.det.differentiable` itself binds `{n : Type*}`,
`[Fintype n]`, `[DecidableEq n]` directly (no surrounding `variable`
block in this section). Transfer to axiom is verbatim.

The pre-axiom docstring will be hoisted/expanded to document the γ-floor
strategy + retirement plan.

---

## §3. Caller analysis (claim 3 evidence)

`grep -rn "Matrix.det.differentiable\|Matrix\\.det\\.hasFDerivAt" FormalConjectures/`
at HEAD `c38c250`, excluding self-references in `MatrixDetDifferentiable.lean`:

| File:line | Kind | Affected by axiom swap? |
|-----------|------|--------------------------|
| `524.lean:3514` | docstring (Mathlib gap citation) | No |
| `Helpers/MultivariateGaussianPdf.lean:242` | comment in R51 axiom #7 docstring | No |
| `Helpers/GLWSmallBallShortcut.lean:220` | comment in un-imported file | No |
| `Helpers/MultivariateGaussianCDF.lean:46` | docstring (Mathlib API list) | No |
| `Helpers/MultivariateGaussianCDF.lean:63` | docstring (Mathlib gap citation) | No |
| `Helpers/MultivariateGaussianCDF.lean:177` | docstring (closure prerequisites) | No |

**Sole self-references in `MatrixDetDifferentiable.lean`**: top-of-file
docstring (lines 30-32, 59-66) + theorem docstring (line 134-140). All
documentation; no Lean call sites.

**Conclusion**: zero Lean call sites; axiom swap consumer-safe.

**Anti-mismatch hygiene** (R49 + R51 8/8 checklist pattern):
- ✅ Type signature verbatim (binders + conclusion).
- ✅ No explicit hypotheses to preserve (the theorem has only typeclass
  args).
- ✅ Section variables `{n : Type*} [Fintype n] [DecidableEq n]` bound
  on the theorem itself; preserved verbatim on axiom.
- ✅ No positional consumers in mainline.
- ✅ Companion `Matrix.det.hasFDerivAt` Stub at line 124-132 NOT
  modified.
- ✅ R49 axiom #6 + R51 axiom #7 + A1-A5 + R50 sub-Stubs unaffected.
- ✅ Track branches not touched (mainline only).
- ✅ No new imports needed.

8/8.

---

## §4. Re-confirmations (mandatory floor §T1.1 supplementary checks)

**R49 Path A axiom (Axiom #6) intact** — `MultivariateGaussianCDF.lean:190`:
```
axiom multivariateGaussianOrthantCDF_differentiable_wrt_covariance ...
```
✅ Verified.

**R51 γ-floor axiom (Axiom #7) intact** — `MultivariateGaussianPdf.lean:282`:
```
axiom multivariateGaussian_eq_lebesgue_withDensity ...
```
✅ Verified.

**A1–A5 axioms intact**:
- A1 (D2): `Cp_T_explicit_pointwise_axiom` at
  `Helpers/GLWGaussianProjectiveLimit.lean:2013` ✅.
- A2: `one_dim_KMT_coupling` at `Helpers/OneDimKMT.lean:101` ✅.
- A3: `kmt_aided_gaussian_process` at
  `Helpers/StochasticProcessAxiom.lean:100` ✅.
- A4: `gao_li_wellner_small_ball_upper` at `524.lean:3574` ✅.
- A5: `gao_li_wellner_small_ball_lower` at `524.lean:3643` ✅.

**R50 deferred-paper sub-Stubs intact**:
- `glw_lemma_4_1_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:226` ✅.
- `glw_lemma_4_2_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:256` ✅.

**Companion `Matrix.det.hasFDerivAt` Stub intact** at
`Helpers/MatrixDetDifferentiable.lean:124-132` (line 132 sorry) ✅.

All re-confirmations green. R53 may proceed with T2.1 axiom replacement.

---

## §5. Predicted T2.1 outcome

**P(T2.1 Full close) = 0.95** (per R49 + R51 precedent). High confidence:
- Mechanical Lean edit (delete `theorem ... := by ... sorry` block,
  retype as `axiom` declaration).
- R49 + R51 precedent (Path A axiomatization on
  `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` and
  `multivariateGaussian_eq_lebesgue_withDensity`) succeeded with the
  same pattern.
- Zero Lean call sites — axiom swap cannot break consumers.
- No surrounding `variable` block; theorem binds typeclasses directly.

**Failure modes (P~0.04 mid)**:
- (a) `Matrix.det.differentiable` namespace collision — could the
  namespace `Matrix.det.differentiable` accidentally shadow some
  Mathlib symbol? Mitigation: T2.1 verifies via `lake env lean` clean
  compile.

**Failure modes (P~0.01 lower)**:
- Build-system / cache issue — recoverable.

---

## §6. Round 53 status entering T2.1

| Item | Pre-R53 | Projected post-R53 |
|------|---------|--------------------|
| User-defined axioms (mainline) | 7 | **8** (+1, `Matrix.det.differentiable` axiom #8) |
| TAG'd sorries (mainline) | 12 | **11** (-1, wrapper Stub retired) |
| Items at R52 gate (mainline) | 19 | **19** (sorry-to-axiom swap, no change) |
| Cumulative R40-R53 retirement rate | ~0.35/round | unchanged trajectory |
| Project total items | 38 | 38 (unchanged) |

**γ floor commitment**: this axiomatization is binding per BACKGROUND.md
post-R49/TC3 user directive ("γ floor + β R58 extension"). Retirement
target R55-R59 (post-R52 gate) per Leibniz-expansion + polynomial
differentiability classical references; either via Mathlib pin bump
(preferred, post-`v4.28` toolchain) or from-scratch closure (~100-200
LOC fallback).

**T2.1 dispatch authorized.**
