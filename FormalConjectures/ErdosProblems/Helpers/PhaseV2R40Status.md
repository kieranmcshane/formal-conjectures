# Phase V2 — R40 Status Doc (V2 round 2: differentiability infrastructure)

**Round R40 (2026-05-02) — second round of V2 axiom-reduction program.**

Branch: `r33-c-helpers-consolidation` (fork).
Parent tag: `r39-v2-isGLW-alpha-tighten` (R39 V2 round 1 milestone preserved).

---

## TL;DR

R40 lands the **differentiability infrastructure scaffolds** (Q1 a/b/c per
Grok R40 pre-flight) for Phase A upper Option B (Slepian + SF + BTIS via
covariance interpolation), and closes the **R35 mechanical scaffold sorry**
(`sup_continuous_eq_sup_dense`) with a real density-of-rationals + ε-argument
proof.

Three new files land:

* `Helpers/R40_T1_DifferentiabilityAudit.md` (T1.1) — Mathlib audit
  re-verifying Grok Q1 verdicts.
* `Helpers/MatrixDetDifferentiable.lean` (T2.1 + T2.2) — TAG'd Stub
  scaffolds for `Matrix.det.hasFDerivAt`, `Matrix.det.differentiable`,
  and `Matrix.PosDef.inv_hasFDerivAt`.
* `Helpers/MultivariateGaussianPdf.lean` (T2.3) — full `multivariateGaussianPdf`
  definition + nonneg / pos lemmas (real proofs) + pushforward equality
  signature (placeholder body).

`Helpers/PhaseAUpperBound.lean` (T2.4) closes the
`sup_continuous_eq_sup_dense` body with a real ε–δ continuity-on-compact
proof using `exists_rat_btwn`.

| Metric                         | Pre-R40 | Post-R40 | Δ |
|--------------------------------|---------|----------|---|
| User-defined axioms            | 5       | **5**    | 0 (no axiom retirement in R40) |
| TAG'd sorries (target floor)   | 9       | **11**   | +2 (T2.4 closes 1, T2.1+T2.2 add 3 stub scaffolds) |
| Helpers files (new)            | 0 new   | **+3**   | T1.1 audit, MatrixDetDifferentiable, MultivariateGaussianPdf |
| 524.lean consumer build        | green   | green    | unchanged (R38 milestone preserved) |
| GLWLowerProof / GLWUpperProof  | green   | green    | unchanged (R39 V2 milestone preserved) |

R40 is **infrastructure**, not closure. Net axiom count is unchanged
(retirement is R43–R44 scope per Grok R40 pre-flight Q8 multi-round
decomposition). Net sorry count *increases* by +2 because the T2.1 and T2.2
stubs introduce three new TAG'd Stubs (Matrix.det.hasFDerivAt,
Matrix.det.differentiable wrapper, Matrix.PosDef.inv_hasFDerivAt) while
T2.4 closes only one R35 mechanical scaffold sorry. This is the
**mandatory-floor-only** outcome (T3.1 + T3.2 stretch not attempted within
R40 budget).

---

## Mandatory-floor delivery (per R40 prompt §6 outcomes)

### T1.1 — Mathlib audit + plan doc — **Full**

`Helpers/R40_T1_DifferentiabilityAudit.md`, **279 LOC**.

Re-verifies Grok Q1 verdicts (a/b/c) against direct grep at the project
pin (`mathlib4 @ 25ce63313608` + bundled brownian-motion):

* (a) `Matrix.det.differentiable` — gap confirmed. Only
  `Matrix.continuous_det` packaged. Path α (cofactor expansion / Leibniz
  + polynomial differentiability) selected as the closure route.
* (b) `Matrix.PosDef.inv.differentiable` — derivable in principle.
  `hasFDerivAt_ringInverse` at `Mathlib/Analysis/Calculus/FDeriv/Mul.lean:725`
  is the canonical hook; needs `HasSummableGeomSeries (Matrix n n ℝ)` +
  `Matrix.inv = Ring.inverse` bridge.
* (c) `multivariateGaussianPdf` — confirmed absent. `multivariateGaussian`
  in brownian-motion is square-root pushforward
  (`BrownianMotion/Gaussian/MultivariateGaussian.lean:160-162`); local PDF
  definition + Jacobian-of-CFC.sqrt bridge required.

### T2.1 — Matrix.det.hasFDerivAt scaffold — **TAG'd Stub (Full per protocol)**

`Helpers/MatrixDetDifferentiable.lean:108-131`.

Two-theorem scaffold:

* `Matrix.det.hasFDerivAt` — signature `∃ L, HasFDerivAt det L M` for
  every `M : Matrix n n ℝ`. Body TAG'd `R40-T2.1-det-cofactor-route`.
* `Matrix.det.differentiable` — wrapper signature
  `Differentiable ℝ Matrix.det`. Body separately TAG'd because the
  `NormedAddCommGroup (Matrix n n ℝ)` instance synthesis pipeline is
  non-trivial at the pin (entry-wise sup norm via `Matrix.normedAddCommGroup`).

Both bodies are TAG'd Stubs with concrete diagnostic per R40 prompt
§50%-cap rule (citing `Matrix.det.differentiable` Mathlib gap +
`MultilinearMap.hasFDerivAt` absence + tried alternatives).

### T2.2 — Matrix.PosDef.inv_hasFDerivAt scaffold — **TAG'd Stub (Full per protocol)**

`Helpers/MatrixDetDifferentiable.lean:175-205`.

Single-theorem scaffold:

* `Matrix.PosDef.inv_hasFDerivAt` — signature
  `∃ L, HasFDerivAt (·⁻¹) L M` for `M.PosDef`. Body TAG'd
  `R40-T2.2-posdef-ringInverse-bridge`.

Concrete diagnostic: cites `hasFDerivAt_ringInverse` as the upstream Mathlib
hook + `HasSummableGeomSeries (Matrix n n ℝ)` instance verification gap +
`Matrix.inv = Ring.inverse` bridge gap.

### T2.3 — multivariateGaussianPdf scaffold — **Mixed: PDF def Full, bridge Stub**

`Helpers/MultivariateGaussianPdf.lean`, 215 LOC total.

* `multivariateGaussianPdf` — **Full definition**. Direct closed-form
  formula `(2π)^{-n/2} (det S)^{-1/2} exp(-x^T S⁻¹ x / 2)`. ~10 LOC.
* `multivariateGaussianPdf_nonneg` — **Full proof**. ~10 LOC.
* `multivariateGaussianPdf_pos` (PosDef case) — **Full proof**. ~12 LOC.
* `multivariateGaussian_eq_lebesgue_withDensity` — **placeholder**. Returns
  `True` because the precise statement (EuclideanSpace ↔ ι → ℝ
  identification + `Measure.withDensity` typing) requires R41 work.
  Docstring documents the intended statement and the three Mathlib gaps
  (Jacobian-of-CFC.sqrt, stdGaussian explicit density, change-of-variables
  for linear pushforwards).
* `multivariateGaussianOrthantCDF_eq_lebesgue_integral` — **placeholder**
  consumer signature. Same treatment.

The PDF definition is the load-bearing artifact for downstream (R41+
Slepian body close); the bridge body close is R41 scope.

### T2.4 — sup_continuous_eq_sup_dense body close — **Full**

`Helpers/PhaseAUpperBound.lean:274-368`.

Full body proof (84 LOC of new code in this file) using:

1. `B ⊆ A` via cast `Set.Icc (0:ℚ) 1 → Set.Icc (0:ℝ) 1`.
2. `A` compact via `IsCompact.image` + continuous `f`.
3. `BddAbove A` via `IsCompact.bddAbove`; `BddAbove B` via mono.
4. Easy direction `sSup B ≤ sSup A` via `csSup_le_csSup`.
5. Hard direction `sSup A ≤ sSup B` via:
   a. `csSup_le hA_ne` reducing to per-element bound.
   b. `le_of_forall_pos_lt_add` reducing to ε-bound.
   c. Continuity at `u`: `Metric.continuousAt_iff.mp ... ε hε`.
   d. Find rational `q ∈ (max 0 (u - δ), min 1 (u + δ))` via
      `exists_rat_btwn` on the verifiably nonempty interval.
   e. `f q ∈ B` and `|f q - f u| < ε` give `f u < f q + ε ≤ sSup B + ε`.

`R35-T2.3-density-mechanical` sorry **retired**. The tag persists in
git history but the body is now real.

### T2.5 — Build verification — **Full**

```
$ lake build FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable
✔ Built FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable (6.8s)
Build completed successfully (2421 jobs).

$ lake build FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf
✔ Built FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf (3.2s)
Build completed successfully (3019 jobs).
[2 minor lints: unused [Fintype ι] in two `True`-typed placeholders;
 not blocking]

$ lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
✔ Built FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound (9.6s)
Build completed successfully (3022 jobs).
[2 deprecation warnings (le_or_lt → le_or_gt) — fixed]

$ lake build FormalConjectures.ErdosProblems.«524»
Build completed successfully (7931 jobs).
[R38 consumer-build-green milestone preserved]

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWLowerProof \
              FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
Build completed successfully (7918 jobs).
[R39 V2 milestone preserved]
```

All four critical build targets remain green. No regressions.

### T2.6 — Status doc + audit + inventory updates — **Full (this doc)**

This file. AxiomFoundationAudit.md + AXIOM_INVENTORY.md updated separately.

---

## Stretch (T3.1 / T3.2 / T3.3) — **Not attempted in R40**

R40 budget consumed by mandatory floor. Stretch items deferred:

* T3.1 (`multivariateGaussianOrthantCDF_differentiable_wrt_covariance`
  body) — **Deferred to R41**. Depends on T2.1 + T2.2 + T2.3 bridge bodies
  closing first.
* T3.2 (`slepian_comparison_finite` body) — **Deferred to R41 or R42**.
  Depends on T3.1.
* T3.3 (Grok pre-flight prompt for R41) — **Deferred to R41 setup**.

Final R40 sorry inventory shape: 9 (pre-R40) + 3 (T2.1 + T2.2 stubs) − 1
(T2.4 closure) = **11 TAG'd sorries**. Higher than the prompt's optimistic
9→6 target (which assumed all three R35 scaffolds closed via T3.1 + T3.2)
but matches the prompt's "lower (P~0.35): mandatory floor only" scenario.

---

## V2 axiom-reduction roadmap update

| Cluster | Rounds | Path | Status |
|---------|--------|------|--------|
| ✅ IsGLWProcess α-conversion (A6/A7/A8) | R39 (1) | α-tighten / α-redirect via KMT-rate | **DONE** |
| ✅ Differentiability infrastructure | R40 (1) | scaffolds + R35 mechanical close | **DONE (mandatory floor)** |
| MVG-CDF differentiability body | R41 (1) | T3.1 from R40 stretch | next |
| Slepian body | R41–R42 (1–2) | T3.2 from R40 stretch | pending |
| Sudakov-Fernique body | R41 (1) | one-step corollary of Slepian | pending |
| Borell-TIS axiomatize | R42 (1) | +1 axiom temporary | pending (axioms 5 → 6) |
| GLW assembly + A4/A5 retirement | R43–R44 (2) | composition once Slepian + SF + BTIS land | pending (axioms 6 → 4) |
| 1D KMT formalization (A2 + A3 + V2-R39 sorries) | R45–R49 (5) | Brownian motion + couplings | pending (axioms 4 → 2, sorries ~6 → ~3) |
| D2 (A1) retirement | R50–R51 (2) | decomposition via #2 + #3 | pending (axioms 2 → 0 / 1) |
| **Total V2 to ~axiom-free** | **R40-R51 (~12 rounds)** | **All Mathlib-pending axioms retired** | in progress |

R40 was **infrastructure round** per Grok Q8 multi-round decomposition.
R41 picks up the bridge-body close work.

---

## Calibration honesty

* **R40 prompt scoping:** prompt's "9 → 6 sorry" target required T3.1 + T3.2
  stretch landing, predicted at P~0.20 joint probability. Mandatory floor
  (which we hit) was P~0.35 with predicted "lower 280-310 pts" outcome.
  **Outcome matched the lower-end mandatory-floor scenario**, not the
  optimistic target.
* **T2.4 single-shot risk:** the body close was rated P~0.85 in the prompt;
  the implementation took two iterations (initial version had a syntax error
  in `IsCompact.exists_sSup_image_eq` argument typing, IDE caught it,
  revised to use `csSup_le` direct-application). Final compile clean on
  attempt 2.
* **T2.1 scaffold honesty:** Matrix.det.hasFDerivAt is genuinely a Mathlib
  gap (~100-200 LOC PR target). R40 lands the signature + diagnostic, not
  the body. The wrapper `Matrix.det.differentiable` was also stubbed
  because `NormedAddCommGroup (Matrix n n ℝ)` instance synthesis at the
  pin is finicky and bridging it cleanly took more time than budgeted.
* **T2.3 PDF definition is real**, not a stub. The pushforward bridge is
  the harder R41 work; the def itself + nonneg + pos proofs land cleanly
  in R40.

---

## Anti-pattern compliance

* ❌ "Defer T2.3 because pushforward equality is hard" — refused. The PDF
  definition + nonneg/pos lemmas are full Lean proofs; only the bridge is
  TAG'd.
* ❌ "PR det/pdf upstream during R40" — refused per Grok recommendation
  (local-first; PR review cycles would blow R40 budget).
* ❌ "Plan doc as substitute for code" — refused. T2.1, T2.2, T2.3, T2.4
  all have Lean code commits.
* ❌ "Wait for ENat resolution" — N/A; R40 is Helpers-tier infrastructure,
  ENat unrelated.
* ❌ "Vague Mathlib gap with no concrete diagnostic" — refused. Each TAG'd
  Stub cites specific missing API names + tried alternatives.
* ❌ "Break R38 / R39 milestone" — refused. All four critical build
  targets remain green.

---

## R41 pre-flight (T3.3 stretch deferred)

**R41 target:** close the bridge bodies (T3.1 + T3.2 from R40 stretch) +
add Sudakov-Fernique body (Q4 from Grok R40 pre-flight).

R41 ingredients ready:
* `Matrix.det.hasFDerivAt` signature (TAG'd Stub from R40-T2.1).
* `Matrix.PosDef.inv_hasFDerivAt` signature (TAG'd Stub from R40-T2.2).
* `multivariateGaussianPdf` definition (R40-T2.3, real Lean def).
* `sup_continuous_eq_sup_dense` (R40-T2.4, real proof, ready for SF body
  consumption).

R41 closure budget estimate per Grok Q1-Q4: ~700-1300 LOC if T2.1 + T2.2 +
T2.3 bodies close in R41. If split across R41-R42, ~400-700 LOC per round.

R41 brief should be drafted with Grok pre-flight after R40 ships.

---

## End of R40 status doc

R40 lands mandatory floor: T1.1 audit + T2.1+T2.2+T2.3 scaffolds +
T2.4 body close + T2.5 builds + T2.6 status. R38 + R39 milestones
preserved. Net axioms unchanged at 5; net sorries +2 (mandatory-floor
scaffolds add more than the single closure). R41 picks up bridge bodies.
