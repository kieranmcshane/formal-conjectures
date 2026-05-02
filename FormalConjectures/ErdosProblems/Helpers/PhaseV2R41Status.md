# Phase V2 — R41 Status Doc (V2 round 3: Path B partial — T2.2 Full + T3.2 infra)

**Round R41 (2026-05-02) — third round of V2 axiom-reduction program.**

Branch: `r33-c-helpers-consolidation` (fork).
Parent tag: `r40-v2-differentiability-scaffold-mandatory-floor`.

---

## TL;DR

R41 partially executes Grok Path B (close T3.1 + T3.2 chaining on R40 Stubs).
**Delivered**: T2.2 Full close (Stub → Full, ~30 LOC actual proof, 1/5 of
80-150 LOC estimate), T3.2 infrastructure (linear-path Sα + F endpoints
+ build-clean closure scaffold). T3.2 sign-analysis body and T3.1 CDF body
deferred to R42 per realistic single-conversation budget.

| Metric                         | Pre-R41 | Post-R41 | Δ |
|--------------------------------|---------|----------|---|
| User-defined axioms            | 5       | **5**    | 0 (unchanged) |
| TAG'd sorries                  | 11      | **10**   | -1 (T2.2 closed) |
| T3.2 infrastructure            | nil     | **Full** | path Sα + F endpoints + build-clean scaffold |
| Helpers builds (5 critical)    | green   | green    | unchanged |
| 524.lean consumer build        | green   | green    | R38 milestone preserved |

---

## Q1-Q5 pre-flight delivered

R41 began with Grok Q1-Q5 verdicts on Stub-to-Full feasibility:

* **Q1(a)** `Matrix.det.hasFDerivAt`: 150-300 LOC, medium difficulty, explicit
  derivative formula needed for downstream chain rule.
* **Q1(b)** `Matrix.PosDef.inv_hasFDerivAt`: 80-150 LOC, low-medium difficulty.
  **EMPIRICAL: closed in ~30 LOC** (Grok estimate 3-5× pessimistic).
* **Q1(c)** `multivariateGaussianPdf` pushforward: 250-400 LOC, high difficulty.
* **Q2** Stubs are sound axiom-equivalents — chain rule composes.
* **Q3** Pushforward avoidance feasible via measure-level chain rule.
* **Q4** **Path B** recommended (close T3.1 + T3.2 chaining on R40 Stubs).
* **Q5** Anticipate `HasFDerivAtFilter` vs `HasFDerivAt` gaps for derivative-
  under-integral steps.

---

## T2.2 — Matrix.PosDef.inv_hasFDerivAt Full close (commit `1e30dda`)

`Helpers/MatrixDetDifferentiable.lean:175-207`. **~30 LOC of proof body**.

Strategy:
1. `letI := Matrix.linftyOpNormedRing (n := n) (α := ℝ)` — activate L1-sup
   matrix-norm `NormedRing` instance (Mathlib doesn't make global because
   multiple natural matrix-norm choices exist).
2. `letI := Matrix.linftyOpNormedAlgebra` — `NormedAlgebra ℝ (Matrix n n ℝ)`.
3. `hM.isUnit.unit : (Matrix n n ℝ)ˣ` — unit at the PosDef matrix.
4. `hasFDerivAt_ringInverse u` (Mathlib `FDeriv/Mul.lean:725`) — gives
   `HasFDerivAt Ring.inverse (-mulLeftRight ℝ _ M⁻¹ M⁻¹) M`.
5. **Bridge**: `Matrix.nonsing_inv_eq_ringInverse` (Mathlib
   `LinearAlgebra/Matrix/NonsingularInverse.lean:190`) gives the GLOBAL
   function equality `(·⁻¹ : Matrix n n ℝ → Matrix n n ℝ) = Ring.inverse`
   (works on non-units too via `0 = 0`). No open-set / `eventuallyEq`
   argument needed — `funext` rewriting suffices.

Build: ✔ green in 28s. R40-T2.2 sorry retired.

**Calibration insight**: The R40 audit estimated 80-150 LOC; actual was ~30
LOC. The "open-set restriction" subtlety Grok mentioned (`IsOpen { M | M.PosDef }`
proof) was AVOIDED entirely because `Matrix.nonsing_inv_eq_ringInverse` is
a GLOBAL equality (handles non-units explicitly via `0 = 0`). This pattern
generalizes: Mathlib often has "global equality with junk-on-pathological"
lemmas that bypass the need for open-set restriction.

---

## T3.2 — Slepian comparison Path B infrastructure (`Helpers/PhaseAUpperBound.lean:186-249`)

R41 closes the **infrastructure** scaffold:

1. **Linear interpolation path** `Sα : ℝ → Matrix ι ι ℝ` defined as
   `(1-α) • S_X + α • S_Y` with witness `hSα_def`.
2. **Endpoint identities**: `Sα 0 = S_X`, `Sα 1 = S_Y` (via `simp`).
3. **F definition**: `F α := orthantCDF (Sα α) x`.
4. **F endpoint identities**: `F 0 = orthantCDF S_X x`, `F 1 = orthantCDF S_Y x`
   (via `change` + `rw [hSα_*]`).
5. **Goal rewrite**: `rw [← hF_0, ← hF_1]` reduces the Slepian conclusion
   to `F 0 ≤ F 1`.

Build: ✔ green in 10s.

**Body deferred to R42** as TAG'd Stub `R41-T3.2-FTC-via-Stein-and-T3.1-Stub`
with concrete dependency citation:
* (a) `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` (R35-T2.1
  Stub) — needed for `DifferentiableAt ℝ (orthantCDF · x) (Sα α)`.
* (b) PosSemidef preservation under convex combination (separate small lemma,
  could land in R42 alongside body).
* (c) `multivariateGaussianOrthantCDF_partial_offdiagonal` (currently `True`
  placeholder) — needs upgrade to real signature with explicit
  `∂F/∂Σ_{ij}` formula via Stein identity / bivariate-corner argument.
* (d) Sign analysis: each `(S_Y - S_X)_{ij}` factor non-negative by
  `_h_offdiag`; density factor non-negative by Stein-identity construction.
  Diagonal terms vanish by `_h_diag` (equal-variance hypothesis).
* (e) FTC: `F(0) ≤ F(1)` from `F'(α) ≥ 0` for all `α ∈ [0,1]`.

Estimated R42 body: ~200-300 LOC.

---

## What R41 did NOT deliver (honest accounting)

* **T2.1 Full close** — left as R40 Stub per Path B (chain composes through).
  Not attempted in R41. R42-R44 scope.
* **T2.3 Full close** — left as R40 Stub per Path B. Not attempted in R41.
* **T3.1 CDF differentiability body** — not attempted. ~300-500 LOC required;
  realistic single-conversation budget exceeded by T2.2 + T3.2 infrastructure
  + Q1-Q5 pre-flight + status doc.
* **T3.2 sign-analysis body** — Stub remains, infrastructure laid for R42 close.
* **PosSemidef.convex_combination** standalone lemma — would be ~40 LOC,
  not landed in R41 (R42 prerequisite for T3.2 body).

---

## Build verification

```
$ lake build FormalConjectures.ErdosProblems.Helpers.MatrixDetDifferentiable
✔ green (28s) — sorry count 3 → 2 (T2.2 closed)

$ lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound
✔ green (10s) — sorry count 1 → 1 (slepian_comparison_finite still has
                                    sorry but body is now scaffolded)

$ lake build FormalConjectures.ErdosProblems.«524»
✔ green (7931 jobs) — R38 milestone preserved
```

R39 + R40 milestones preserved.

---

## Net residual sorry inventory after R41 (10 TAG'd sorries)

| # | Sorry / TAG | Status |
|---|---|--------|
| 1 | R33-C T2.4 — `IndepFun(Yplus, Yminus)` | unchanged |
| 2 | R33-C T2.5 — `?ha'.iIndepFun` on Ω × Ω | unchanged |
| 3 | R33-D T2.1 bridge — `two_dim_KMT_coupling_legacy_Ω_form` | unchanged |
| 4 | R35 T2.1 — `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` | unchanged (T3.1 target) |
| 5 | R35 T2.2 — `slepian_comparison_finite` body | infrastructure landed; sign-analysis sorry remains (T3.2 target) |
| 6 | V2-R39 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus` | unchanged |
| 7 | V2-R39 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus` | unchanged |
| 8 | V2-R39 — `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus` | unchanged |
| 9 | V2-R40 — `Matrix.det.hasFDerivAt` | unchanged (T2.1 R42 target) |
| 10 | V2-R40 — `Matrix.det.differentiable` wrapper | unchanged (T2.1 R42 target) |
| ~11~ | V2-R40 — `Matrix.PosDef.inv_hasFDerivAt` | **RETIRED in R41-T2.2** |

Net count: **10 TAG'd sorries** (down from R40's 11 by -1: T2.2 close).

---

## V2 axiom-reduction roadmap update

| Cluster | Round(s) | Status |
|---------|----------|--------|
| ✅ IsGLWProcess α-conversion | R39 (1) | DONE |
| ✅ Differentiability infrastructure scaffolds | R40 (1) | DONE |
| 🔶 Path B partial (T2.2 Full + T3.2 infra) | R41 (1) | **DONE this round** |
| T3.2 sign analysis body (Stein identity) + T3.1 body | R42-R43 (2) | next |
| T2.1 Full close (cofactor route or Differentiable form) | R42-R43 (1) | next |
| T2.3 Full close (pushforward bridge) | R44 (1) | pending |
| Sudakov-Fernique body | R45 (1) | pending |
| Borell-TIS axiomatize (+1 axiom temporary) | R46 (1) | pending |
| GLW assembly + A4/A5 retirement | R47-R48 (2) | pending (axioms 6 → 4) |
| 1D KMT formalization (A2 + A3 + V2-R39 sorries) | R49-R53 (5) | pending (axioms 4 → 2) |
| D2 (A1) retirement | R54-R55 (2) | pending (axioms 2 → 0) |

---

## Calibration honesty

* **Empirical T2.2 calibration**: actual proof body was ~30 LOC vs Grok/R40
  estimate 80-150 LOC. **3-5× overestimate**. The pattern: Mathlib often has
  "global equality with junk-on-pathological" lemmas that bypass the need
  for open-set restrictions, which the audit didn't anticipate.
* **R41 single-conversation budget realistic outcome**: the user pace assumes
  ~30-60 minutes per "round" with sustained compiler iteration. T3.2 body
  alone (~300 LOC) exceeds this without compiler-loop closure budget.
* **Path B selected**: T2.1 + T2.3 stay as Stubs (sound axiom-equivalents per
  Q2). T3.1 + T3.2 close in subsequent rounds chaining on them.
* **What landed concretely**: 1 sorry retired (T2.2), substantive infrastructure
  for T3.2 (linear path + F endpoints), comprehensive Q1-Q5 pre-flight
  delivered with empirical calibration evidence.

---

## Anti-pattern compliance

* ❌ "Land Slepian sign analysis without compiler iteration" — refused as
  unrealistic; T3.2 body deferred to R42 with explicit infrastructure ready.
* ❌ "Claim Path A closure when only T2.2 + T3.2 infra landed" — refused.
  Status doc explicitly distinguishes infrastructure (landed) from body
  (deferred).
* ❌ "Skip Q1-Q5 verdict delivery to maximize body LOC" — refused. The
  pre-flight Q1-Q5 delivery is itself substantive R41 work and informs
  R42+ scope.
* ❌ "Break R38/R39/R40 milestones" — refused. All four critical build
  targets remain green.

---

## R42 pre-flight (recommended scope)

R42 next steps with empirical calibration:
* **Close T3.1 body** via Stein identity (Path C alternative or measure-
  level pushforward). Estimated ~200-300 LOC. Depends on
  `multivariateGaussianOrthantCDF_partial_offdiagonal` upgrade from
  `True` placeholder to real explicit-derivative signature.
* **Close T3.2 sign analysis body** chaining on T3.1. Estimated ~200-300 LOC.
* **Add PosSemidef.convex_combination lemma** (~40 LOC standalone).
* **Optional T2.1 close** (Differentiable form, per Q1(a) Grok). May be
  simpler than expected given T2.2 calibration evidence.

R42 budget: ~500-700 LOC realistic single-conversation outcome.

---

## End of R41 status doc

R41 = Path B partial (T2.2 Full + T3.2 infrastructure). 1 sorry retired
(11 → 10). R38/R39/R40 milestones preserved. T3.2 infrastructure ready
for R42 sign-analysis body. Honest scope: Slepian + CDF bodies are R42
work, not R41.
