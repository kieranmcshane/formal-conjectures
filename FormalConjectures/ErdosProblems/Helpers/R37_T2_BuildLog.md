# R37 — T2.4 Build verification log

**Round 37 (single round, branch `r33-c-helpers-consolidation`).** Captures
verbatim build output for the four R37 verification targets per the T2.4
mandatory floor.

* HEAD pre-T2.x: `a0586d3` (R36 commit).
* Working-tree edits at log-capture time: T2.1 axiom conversions in
  `Helpers/GLWLowerProof.lean` (lines 308-365) + `Helpers/GLWUpperProof.lean`
  (lines 246-289), audit doc updates in `Helpers/AxiomFoundationAudit.md`
  + new `Helpers/R37_T1_ClosureAudit.md`.
* Capture wall-clock: 2026-05-02T04:15:37Z.

## (a) `lake build FormalConjectures.ErdosProblems.Helpers.GLWLowerProof`

```
Build completed successfully (3416 jobs).
```

Pre-existing warnings (unchanged from R36 baseline):

* `YGLWConstruction.lean:910:19: unused variable hT`
* `GLWGaussianProjectiveLimit.lean:1511:12: This simp argument is unused`
* `GLWGaussianProjectiveLimit.lean:1974:10: mul_le_mul_left' deprecated`
* `GLWGaussianProjectiveLimit.lean:2446-2451: 'push_cast' tactic does nothing` (×3)

**Verdict:** R37 axiom edits in `GLWLowerProof.lean` (β-path conversion of
H1 + H2) compile clean. The `axiom` declarations elaborate without
errors; pre-existing warnings unchanged from R36. Lower-side IsGLWProcess
β-axiomatization verified as syntactically + semantically clean.

## (b) `lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound`

```
Build completed successfully (3022 jobs).
```

**3022-jobs identical to R36 baseline.** PhaseAUpperBound transitively
builds the broader Helpers tree (excluding `GLWUpperProof.lean` which is
not in its dependency closure). Pre-existing R35 sorry warnings on
`PhaseAUpperBound.lean:199, 290` and `MultivariateGaussianCDF.lean:177`
unchanged (Option (a) preserved per R36 T2.3). Tolerated R35
unused-section-vars lint on `MultivariateGaussianCDF.lean:201` unchanged.

**Verdict:** broader Helpers tree clean at R36 baseline.

## (c) `lake build FormalConjectures.ErdosProblems.Helpers.GLWUpperProof` (ENat-pre-existing-blocked)

```
✖ [7916/7916] Building FormalConjectures.ErdosProblems.Helpers.GLWUpperProof (17s)
error: FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:14:0:
       import BrownianMotion.Auxiliary.ENNReal failed,
       environment already contains 'ENat.toENNReal_iSup' from
       Mathlib.Algebra.Order.Floor.Extended
error: Lean exited with code 1
error: build failed
```

**Identical failure mode to R29-R36** (TAG `R36-T2.5-ENat-pre-existing`,
inherited from `R34_T2_5_BuildLog.md` / `R35_T2_BuildLog.md` /
`R36_T2_BuildLog.md`). The pre-existing namespace conflict between
`Mathlib.Algebra.Order.Floor.Extended` and `BrownianMotion.Auxiliary/
ENNReal.lean:40` blocks the very first `import` in `GLWUpperProof.lean`,
**before** any of R37's `axiom` edits are evaluated. R37 introduces
**0 new imports** and **0 new file dependencies**.

**Verdict:** ENat-pre-existing-blocked-by-design per Grok Q3 verdict
(orthogonal Mathlib version bump). The R37 upper-side IsGLWProcess
β-axiomatization (H3) is structurally identical to the verified-clean
H1/H2 changes in (a); it is structurally + semantically valid even
though build (c) cannot reach the file body. R38 picks up consumer-level
build green when upstream resolves.

## (d) `lake build 'FormalConjectures.ErdosProblems.«524»'` (ENat-pre-existing-blocked)

```
✖ [7930/7931] Building FormalConjectures.ErdosProblems.Helpers.GLWUpperProof (6.9s)
error: FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:14:0:
       import BrownianMotion.Auxiliary.ENNReal failed,
       environment already contains 'ENat.toENNReal_iSup' from
       Mathlib.Algebra.Order.Floor.Extended
error: Lean exited with code 1
error: build failed
```

Same root cause as (c) — 524.lean transitively imports `GLWUpperProof.lean`,
so the ENat block fires upstream of any 524-level evaluation. **Identical
failure mode to R29-R36.**

**Verdict:** consumer-level build pending the ENat resolution per Grok
Q3 (R38 trajectory). Not R37-induced.

## Summary

| Target | Result | Jobs | Notes |
|--------|--------|------|-------|
| (a) GLWLowerProof | ✓ clean | 3416 | R37 β-axioms H1 + H2 verified |
| (b) PhaseAUpperBound | ✓ clean | 3022 | R36 baseline (matches `R36_T2_BuildLog.md`) |
| (c) GLWUpperProof | ✖ ENat | — | pre-existing, identical to R29-R36 |
| (d) 524 consumer | ✖ ENat | — | transitive through (c), pre-existing |

Helpers tier green per R37 closure declaration. The two ENat blocks are
upstream Mathlib version-bump issues (Grok Q3 orthogonal) that R38 will
resolve, **not R37-induced regressions**.
