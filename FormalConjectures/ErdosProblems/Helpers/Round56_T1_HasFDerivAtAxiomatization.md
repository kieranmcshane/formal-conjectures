# R56-T1.1 — γ-floor companion `Matrix.det.hasFDerivAt` axiomatization audit (Claims Verification Table)

**Round**: R56 (V2 round 18, 2026-05-02). γ-floor strategy, mechanical
axiomatization extending R49 / R51 / R53 pattern (`theorem ... := by
sorry` → `axiom ...` of identical signature) to the companion existential
form Stub left in place at R53.

**Branch**: `r46-track-a-mge-posdef`, HEAD `a43ce68` (R55 close).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Scope**: T1.1 audit completes the Claims Verification Table (binding
discipline rule #6) and extracts the verbatim `Matrix.det.hasFDerivAt`
Stub signature for T2.1 axiom replacement at
`Helpers/MatrixDetDifferentiable.lean:126-134`.

---

## §1. Claims Verification Table

| Claim # | Math statement | Lean form | VERIFIED? | Citation | Notes |
|---------|----------------|-----------|-----------|----------|-------|
| 1 | `Matrix.det.hasFDerivAt` Stub exists at `MatrixDetDifferentiable.lean:126-134` | `theorem Matrix.det.hasFDerivAt {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : ∃ L : Matrix n n ℝ →L[ℝ] ℝ, HasFDerivAt (fun A : Matrix n n ℝ => A.det) L M := by ... sorry` | **VERIFIED** | `Helpers/MatrixDetDifferentiable.lean:126-134` | Theorem signature lines 126-129; body comment + `sorry` lines 130-134. TAG `R40-T2.1-det-cofactor-route`. The companion existential form deliberately preserved at R53 per `Round53_T1_MatrixDetDifferentiableAxiomatization.md` §1 row 8 ("companion Stub deliberately NOT axiomatized in R53"). |
| 2 | R53 axiom #8 `Matrix.det.differentiable` preserved | `axiom Matrix.det.differentiable {n : Type*} [Fintype n] [DecidableEq n] : Differentiable ℝ (fun A : Matrix n n ℝ => A.det)` at `MatrixDetDifferentiable.lean:196` | **VERIFIED** | `Helpers/MatrixDetDifferentiable.lean:196-198` | Axiom #8 unchanged from R53 close. R56 does not touch lines 136-198 (R53 docstring + axiom block). |
| 3 | R49 axiom #6 + R51 axiom #7 + A1-A5 preserved | All 7 pre-R53 user-defined axioms intact at HEAD `a43ce68` | **VERIFIED** | A1 (D2) `Cp_T_explicit_pointwise_axiom` `GLWGaussianProjectiveLimit.lean:2013` (private); A2 `one_dim_KMT_coupling` `OneDimKMT.lean:101`; A3 `kmt_aided_gaussian_process` `StochasticProcessAxiom.lean:100`; A4 `gao_li_wellner_small_ball_upper` `524.lean:3574`; A5 `gao_li_wellner_small_ball_lower` `524.lean:3643`; #6 `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` `MultivariateGaussianCDF.lean:190`; #7 `multivariateGaussian_eq_lebesgue_withDensity` `MultivariateGaussianPdf.lean:282` | All 7 pre-R56 user-defined axioms (A1-A5 + #6 + #7) intact. R56 does not touch any of these files. |
| 4 | Math content = local Fréchet differentiability of determinant function `A ↦ A.det` at `M : Matrix n n ℝ` (existential `L` form) | `∃ L : Matrix n n ℝ →L[ℝ] ℝ, HasFDerivAt (fun A : Matrix n n ℝ => A.det) L M` | **VERIFIED** | Same file, line 128-129 | Standard linear algebra: determinant is a polynomial in the entries (Leibniz expansion `det A = ∑_{σ ∈ Perm n} sign σ · ∏_i A i (σ i)`), hence Fréchet-differentiable at every `M`, with derivative `H ↦ tr(adj(M) · H)` (the adjugate / cofactor expansion). The existential form is strictly **stronger than** R53's wrapper `Differentiable ℝ` — it asserts pointwise existence of `L` at the given `M`, from which `Differentiable ℝ` follows by `HasFDerivAt.differentiableAt`. |
| 5 | Callers in mainline | `grep -rn "Matrix\.det\.hasFDerivAt" FormalConjectures/ --include="*.lean"` returns docstring/comment hits only; no Lean call sites | **VERIFIED — sole status: NO LEAN CALL SITES** | Self-references in `MatrixDetDifferentiable.lean` (top-of-file docstring lines 30, 41, 52, 63 + theorem docstring lines 79-125 + R53 axiom docstring line 145, 169, 173) — all documentation. Other files: `R45_T1_FramingVerificationAudit.md`, `R44_T1_BodyCloseAudit.md`, `PhaseV2R{40,41,44,53}Status.md`, `Round53_T1_MatrixDetDifferentiableAxiomatization.md`, `R43_T1_SignatureUpgradeAudit.md`, `R41_T1_ChainCompositionAudit.md`, `R40_T1_DifferentiabilityAudit.md`, `AxiomFoundationAudit.md` — all `.md` audit docs (zero Lean call sites). | **No actual Lean code consumes `Matrix.det.hasFDerivAt` at HEAD `a43ce68`**. All `.lean` references are documentation (Mathlib gap citations + R40-R55 closure-path notes). Axiomatization is consumer-safe with zero call-site adjustment. |
| 6 | Math content = standard Leibniz-expansion + polynomial-differentiability route | Path α: `Matrix.det_apply'` (Leibniz) + `Matrix.entryLinearMap` (entry extraction is differentiable continuous-linear) + `Differentiable.prod_finset` + `Differentiable.sum_finset` + assembly into `HasFDerivAt` form | **VERIFIED** | Top-of-file docstring lines 92-104 + R40-T1.1 audit | Estimated ~100-200 LOC. Mathlib gap diagnostic at lines 106-125 confirms (a) `Matrix.det.hasFDerivAt` not packaged at pin, (b) `MultilinearMap.hasFDerivAt` not packaged at pin (Path β blocked), (c) `Polynomial.eval.hasFDerivAt` exists but too narrow (univariate). Path α is the only available from-scratch route. |
| 7 | New axiom name: preserve `Matrix.det.hasFDerivAt` with `axiom` keyword | TBD | **VERIFIED — preserve original name** | This audit | Name preservation matches R49 (axiom #6 preserved `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`) + R51 (axiom #7 preserved `multivariateGaussian_eq_lebesgue_withDensity`) + R53 (axiom #8 preserved `Matrix.det.differentiable`) γ-floor patterns. Minimal caller disruption: zero current Lean callers, but future callers will use `Matrix.det.hasFDerivAt` by exactly its original name (existential `L` form, more useful for chain-rule composition than the `Differentiable` wrapper). |
| 8 | R50 deferred-paper sub-Stubs preserved | `glw_lemma_4_1_deferred_paper`, `glw_lemma_4_2_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:226, :256` | **VERIFIED** | `Helpers/GLWSmallBallShortcut.lean:226, :256` | Both `theorem`-Stubs intact; un-imported file. R56 does not touch this file. |

All 8 claims **VERIFIED**. T2.1 axiom replacement may proceed.

---

## §2. Verbatim `Matrix.det.hasFDerivAt` Stub signature (for T2.1 axiom replacement)

Extracted from `Helpers/MatrixDetDifferentiable.lean:126-134` at HEAD
`a43ce68`:

```lean
namespace Erdos524.Helpers

open Matrix

-- ... (lines 73-125: top-of-file docstring + theorem docstring) ...

theorem Matrix.det.hasFDerivAt
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    ∃ L : Matrix n n ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun A : Matrix n n ℝ => A.det) L M := by
  -- TAG[R40-T2.1-det-cofactor-route] : ~100-200 LOC, Leibniz expansion
  -- + polynomial differentiability. Mathlib gap: no Matrix.det.hasFDerivAt
  -- in mathlib4 @ 25ce63313608. See R40_T1_DifferentiabilityAudit.md §1.
  -- Closure target: R41 (companion to T2.3 pushforward bridge).
  sorry
```

**T2.1 target form** (preserves `theorem` → `axiom` swap, identical
signature, deletes the 5-line `:= by ... sorry` body; replaces docstring
with R56 γ-floor narrative + retirement plan):

```lean
axiom Matrix.det.hasFDerivAt
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    ∃ L : Matrix n n ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun A : Matrix n n ℝ => A.det) L M
```

Section variables: `Matrix.det.hasFDerivAt` itself binds `{n : Type*}`,
`[Fintype n]`, `[DecidableEq n]`, plus the explicit point `(M : Matrix n
n ℝ)` directly (no surrounding `variable` block in this section).
Transfer to axiom is verbatim.

The pre-axiom docstring (lines 79-125) will be hoisted/expanded to
document the γ-floor strategy + retirement plan, mirroring the R53 axiom
#8 docstring style at lines 136-195.

---

## §3. Caller analysis (claim 5 evidence)

`grep -rn "Matrix\.det\.hasFDerivAt" FormalConjectures/ --include="*.lean"`
at HEAD `a43ce68`:

| File:line | Kind | Affected by axiom swap? |
|-----------|------|--------------------------|
| `Helpers/MatrixDetDifferentiable.lean:30` | top-of-file docstring (overview list) | No |
| `Helpers/MatrixDetDifferentiable.lean:41` | top-of-file docstring (status note) | No |
| `Helpers/MatrixDetDifferentiable.lean:52` | top-of-file docstring (R53 retirement-plan) | No |
| `Helpers/MatrixDetDifferentiable.lean:63` | top-of-file docstring (Mathlib retirement-path note) | No |
| `Helpers/MatrixDetDifferentiable.lean:79–125` | theorem docstring (R40-T2.1 detail) | No (will be edited as part of T2.1) |
| `Helpers/MatrixDetDifferentiable.lean:131` | inline TAG comment in body | No (will be deleted with body) |
| `Helpers/MatrixDetDifferentiable.lean:145` | R53 axiom #8 docstring (companion-Stub note) | No |
| `Helpers/MatrixDetDifferentiable.lean:169` | R53 axiom #8 docstring (Mathlib pin-bump retirement-path note) | No |
| `Helpers/MatrixDetDifferentiable.lean:173` | R53 axiom #8 docstring (2-line consumer-wrapper example) | No |

`grep -rn "Matrix\.det\.hasFDerivAt"` across the whole repo
(`FormalConjectures/`) returns ONLY the above self-references in
`MatrixDetDifferentiable.lean` plus `.md` audit docs. **No `.lean`
call sites in any other file.**

**Conclusion**: zero Lean call sites; axiom swap consumer-safe.

**Anti-mismatch hygiene** (R49 + R51 + R53 8/8 checklist pattern):
- ✅ Type signature verbatim (binders + explicit point + conclusion).
- ✅ Explicit hypothesis `(M : Matrix n n ℝ)` preserved (R53 wrapper had
  no explicit point; this companion form does — a strict signature-shape
  difference, faithful to R40-T2.1 design).
- ✅ Section variables `{n : Type*} [Fintype n] [DecidableEq n]` bound
  on the theorem itself; preserved verbatim on axiom.
- ✅ No positional consumers in mainline.
- ✅ R53 axiom #8 `Matrix.det.differentiable` at line 196 unaffected.
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

**R53 γ-floor axiom (Axiom #8) intact** — `MatrixDetDifferentiable.lean:196`:
```
axiom Matrix.det.differentiable ...
```
✅ Verified.

**A1–A5 axioms intact**:
- A1 (D2): `Cp_T_explicit_pointwise_axiom` at
  `Helpers/GLWGaussianProjectiveLimit.lean:2013` (private) ✅.
- A2: `one_dim_KMT_coupling` at `Helpers/OneDimKMT.lean:101` ✅.
- A3: `kmt_aided_gaussian_process` at
  `Helpers/StochasticProcessAxiom.lean:100` ✅.
- A4: `gao_li_wellner_small_ball_upper` at `524.lean:3574` ✅.
- A5: `gao_li_wellner_small_ball_lower` at `524.lean:3643` ✅.

**R50 deferred-paper sub-Stubs intact**:
- `glw_lemma_4_1_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:226` ✅.
- `glw_lemma_4_2_deferred_paper` at `Helpers/GLWSmallBallShortcut.lean:256` ✅.

**R55 alternate-track build unblocks intact** at
`Wikipedia/DiameterSimpleFiniteGroups.lean` (`eq_top_iff_forall_ne_adj'`
helper at lines 43-51, two call sites lines 86, 124) and
`ErdosProblems/1141.lean` (`Decidable` simp instance with `Nat.lt_succ_iff`
augmentation, line 44) — R56 does not touch either file ✅.

**Q1a/b/c track infrastructure intact** (per BACKGROUND.md post-R50
update §"Q1a/b/c track infrastructure"):
- `Helpers/CauchyDetLowerBound.lean` (Q1a) ✅ (untouched).
- `Helpers/CharFunCrossBlock.lean` (Q1b) ✅ (untouched; R52 patched
  pre-R56, no R56 work).
- `Helpers/MultivariateSmallBallUpper.lean` (Q1c, 3 named sorries at
  lines 73, 238, 616) ✅ (untouched).
- `Helpers/SurgicalDensityAtZero.lean` ✅ (untouched).
- `Helpers/EsseenSmoothing.lean` ✅ (untouched).
- `Helpers/GaussianHierCauchyBox.lean` ✅ (untouched).

All re-confirmations green. R56 may proceed with T2.1 axiom replacement.

---

## §5. Predicted T2.1 outcome

**P(T2.1 Full close) = 0.95** (per R49 + R51 + R53 precedent — 4×
successful mechanical-axiomatization track record). High confidence:
- Mechanical Lean edit (delete `theorem ... := by ... sorry` block,
  retype as `axiom` declaration; expand docstring).
- R49 + R51 + R53 precedent succeeded with the same pattern (3 prior γ-floor
  axiomatizations across mainline, all delivered Full mandatory floor).
- Zero Lean call sites — axiom swap cannot break consumers.
- No surrounding `variable` block; theorem binds typeclasses + explicit
  point directly.

**Failure modes (P~0.04 mid)**:
- (a) `Matrix.det.hasFDerivAt` namespace collision — could the namespace
  `Matrix.det.hasFDerivAt` accidentally shadow some Mathlib symbol?
  Mitigation: T2.1 verifies via `lake env lean` clean compile + grep.

**Failure modes (P~0.01 lower)**:
- Build-system / cache issue — recoverable.

---

## §6. Round 56 status entering T2.1

| Item | Pre-R56 (post-R55) | Projected post-R56 |
|------|---------|--------------------|
| User-defined axioms (mainline) | 8 | **9** (+1, `Matrix.det.hasFDerivAt` axiom #9) |
| TAG'd sorries (mainline) | 11 | **10** (-1, companion Stub retired) |
| Items at R52 gate (mainline) | 19 | **19** (sorry-to-axiom swap, no change) |
| Cumulative R40-R56 retirement rate | ~0.28 sorry/round (R39→R55: 14 → 11 across 16 rounds) | trajectory continues |
| Project total items | 41 (post-R55: 19 mainline + ~22 alternate-track) | 41 (unchanged) |

**γ floor commitment**: this axiomatization is binding per BACKGROUND.md
post-R49/TC3 user directive ("γ floor + β R58 extension"). Retirement
target R57-R59 (post-R52 gate, but pre-R59 ceiling) per Leibniz-expansion
+ polynomial-differentiability classical references; either via Mathlib
pin bump (preferred, post-`v4.28` toolchain may package
`Matrix.det.hasFDerivAt` directly) or from-scratch closure (~50-100 LOC
fallback now that the wrapper-axiom #8 exists — closing the existential
form is strictly easier than the wrapper since the existential form
provides the explicit `L`).

**Note on axiom-pair retirement composition**: once `Matrix.det.hasFDerivAt`
is closed (Mathlib pin bump or from-scratch), Axiom #8
(`Matrix.det.differentiable`) retires automatically as a 2-line consumer:
```
theorem Matrix.det.differentiable :
    Differentiable ℝ (fun A : Matrix n n ℝ => A.det) :=
  fun M => (Matrix.det.hasFDerivAt M).choose_spec.differentiableAt
```
So R56 axiomatization adds technical debt that retires in pairs with
Axiom #8. Net retirement count when both close: **-2 axioms in one Mathlib
pin bump or one from-scratch round**.

**T2.1 dispatch authorized.**
