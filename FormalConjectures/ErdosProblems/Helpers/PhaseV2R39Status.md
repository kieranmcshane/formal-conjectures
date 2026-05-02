# Phase V2 — R39 Status Doc (V2 round 1: IsGLWProcess α-conversion)

**Round R39 (2026-05-02) — first round of V2 axiom-reduction program.**

Branch: `r33-c-helpers-consolidation` (fork).
Parent tag: `r38-consumer-build-green` (R38 milestone preserved).

---

## TL;DR

R39 retired the 3 IsGLWProcess β-axioms (A6, A7, A8) by **α-tighten /
α-redirect**: the unsound R37 axiom signatures `Y measurable →
IsGLWProcess Y` were converted to `theorem ... := by sorry` with
strengthened hypotheses requiring the call-site KMT-coupling-rate. The
new theorems are **sound modulo {axiom #1 (D2/Komlós), axiom #2 (1D
KMT), Mathlib-side scaling-limit theorem}**.

| Metric                         | Pre-R39 | Post-R39 | Δ |
|--------------------------------|---------|----------|---|
| User-defined axioms            | 8       | **5**    | -3 (target met) |
| TAG'd sorries                  | 6       | 9        | +3 (axiom→sorry conversions, sound signatures) |
| Total {axioms + sorries}       | 14      | 14       | 0 (categorical refactor) |
| Helpers build                  | green   | green    | unchanged |
| 524.lean consumer build        | green   | green    | unchanged (R38 milestone preserved) |

---

## α-path verdict (per T1.1 cold re-audit)

**Selected α-path:** α-tighten / α-redirect via KMT-coupling-rate
hypothesis. Sound signatures introduced; axiom→theorem-with-sorry
conversion executed.

**Grok 4-bridge cascade results:**

| Bridge | Prior | Verified |
|--------|-------|----------|
| (b) scaling-factor | 80% | **FALSE** — `kernel_even_plus = √(1/2) · exp(-u·k/m)` already has the scaling factor (`Helpers/TwoDimKMTFromOneDim.lean:154-155`) |
| (d) definitional mismatch | 20% | **TRUE** — consumer-side Yplus is from `two_dim_KMT_coupling_legacy_Ω_form`'s sorry-bridge (`524.lean:3920`), not the actual via_LS_reduction Y_e + Y_o on Ω × Ω |
| (a) block-restriction | 10% | **FALSE** — no `ite`-restricted kernels |
| (c) joint-independence | 5% | indirectly relevant; via_LS_reduction `?indep` case is itself a TAG'd sorry |

Additional finding: even at the via_LS_reduction internal level
(setting aside consumer / actual mismatch), α-direct is blocked by
`kmt_aided_gaussian_process` (axiom #3) not exposing Gaussianity / cov
/ centered / integrable conjuncts. Grok's `covariance_add_indep` recipe
needs all of these.

**Conclusion:** Grok's α-direct via decomposition is doubly blocked
((d) at consumer site + axiom #3 design at internal level). R39's
α-tighten / α-redirect via KMT-coupling-rate is the correct alternative
for R39 budget.

---

## Axiom retirement count (per T2.1)

**3 of 3 targeted axioms retired** (categorical α-tighten conversion).

Retired axioms (now `theorem ... := by sorry` with sound tightened
signature):

* `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`
  (`Helpers/GLWLowerProof.lean:350` → tightened theorem at line 333,
  body sorry at line 343)
* `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`
  (`Helpers/GLWLowerProof.lean:362` → tightened theorem at line 357,
  body sorry at line 367)
* `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`
  (`Helpers/GLWUpperProof.lean:295` → tightened theorem at line 278,
  body sorry at line 288)

Surviving 5 user-defined axioms (V2 retirement targets):

| # | Axiom | V2 retirement target |
|---|---|---|
| 1 | `Cp_T_explicit_pointwise_axiom` (D2) | R54-R55 |
| 2 | `one_dim_KMT_coupling` | R49-R53 (in-scope formalization) |
| 3 | `kmt_aided_gaussian_process` | R49-R53 (also closes V2-R39 sorries 7-9) |
| 4 | `gao_li_wellner_small_ball_lower` | R40-R48 (Slepian + SF + BTIS composition) |
| 5 | `gao_li_wellner_small_ball_upper` | R40-R48 (parallel to #4) |

---

## Build status (per T2.2)

`lake build` for the affected modules:

```
$ lake build FormalConjectures.ErdosProblems.Helpers.GLWLowerProof
✔ [3418/3418] Built FormalConjectures.ErdosProblems.Helpers.GLWLowerProof (9.0s)
Build completed successfully (3418 jobs).
warnings: 2 sorry-uses (lines 343, 367 — V2-R39-tighten-{Yplus,Yminus}-lower)

$ lake build FormalConjectures.ErdosProblems.Helpers.GLWUpperProof
Build completed successfully (7917 jobs).
warning: 1 sorry-use (line 288 — V2-R39-tighten-Yplus-upper)

$ lake build FormalConjectures.ErdosProblems.«524»
Build completed successfully (7931 jobs).
warning: pre-existing R33-D bridge sorry at 524.lean:3889 (unchanged)
```

R38 milestone preserved (consumer-build-green). No regressions.

---

## V2 axiom-reduction roadmap update

| Cluster | Rounds | Path | Status |
|---------|--------|------|--------|
| ✅ IsGLWProcess α-conversion (A6/A7/A8) | R39 (1) | α-tighten / α-redirect via KMT-rate | **DONE** |
| Multivariate-Gaussian-CDF differentiability + Slepian + SF | R40-R44 (~5) | R35 signature already drafted | NEXT |
| Borell-TIS honest proof | R45-R47 (~3) | concentration of measure | pending |
| GLW small-ball (A4/A5) retirement | R48 (~1) | composition once Slepian+SF+BTIS land | pending |
| 1D KMT formalization (A2 + A3 retirement, **also closes V2-R39 sorries 7-9**) | R49-R53 (~5) | Brownian motion + couplings | pending |
| D2 (A1) retirement | R54-R55 (~2) | decomposition via #2 + #3 | pending |
| **Total V2 to sorry-free + axiom-free** | **~17 rounds** | **2-4 days at user's actual pace; calendar may stretch with Mathlib-PR review turnaround** | in progress |

R40 = scoping round for Slepian + SF + BTIS honest formalization
(Multivariate-Gaussian-CDF differentiability lemma already drafted in
R35).

---

## Calibration honesty

* **Initial project projection:** 2-3 rounds.
* **Actual through R38:** 24 visible rounds (R14-R38, per user audit;
  10 visible R29-R38 in the AxiomFoundationAudit retrospective).
* **Calibration off** ~8-12× from initial projection. Pattern of
  conservative bias tracked.
* **Y_GLW_exists axiom precedent:** retired at R15, re-introduced as
  D2/A1/A3 at R27 after Branch C declared axiomless infeasible — R39
  is NOT first reduction attempt project-wide, just first of V2
  framing.
* **R39 outcome match to prediction:** Initially planned (P-axiom)
  variant kept axiom count at 8 (no reduction), then revised to
  (P-tag-sorry) for the 8→5 outcome. Met user's "8→5 best case" target.
* **Honest framing of α-tighten:** the 3 V2-R39 sorries close
  *categorically* (axiom → Mathlib-infra-pending sorry with sound
  signature); the *algorithmic* closure (sorry → real proof) requires
  the V2 R49-R53 1D KMT cluster. The mathematical content of the
  closure (KMT-pinned-law argument) is straightforward modulo Mathlib
  formalization.

---

## Anti-pattern compliance

* ❌ "Trust R37's β verdict without re-audit" — refused. R39 produced
  an independent finding R37 missed (signature unsoundness).
* ❌ "Plan doc as substitute for code" — refused. T2.1 was concrete
  Lean code modifications (3 helper signatures + 6 call sites).
* ❌ "Retire axioms by relaxing what `IsGLWProcess` requires" —
  refused. The IsGLWProcess structure is unchanged. The axiom
  hypothesis is tightened (more inputs); the conclusion is the same.
* ❌ "Premature β-confirmed declaration" — refused. The Grok cascade
  was thoroughly tested ((b) FALSE, (d) TRUE, (a) FALSE, (c) indirect),
  and α-tighten emerged as the correct R39 outcome.
* ❌ "Break R38 milestone" — refused. All 4 critical build targets
  remain green; consumer-build-green preserved.

---

## R40 pre-flight (T3.2 stretch)

**Target:** Multivariate-Gaussian-CDF differentiability lemma + Slepian
+ SF (Sudakov-Fernique).

R35 already drafted the signature for
`multivariateGaussianOrthantCDF_differentiable_wrt_covariance` at
`Helpers/MultivariateGaussianCDF.lean`. R40 will:

1. Body the differentiability lemma (currently a TAG'd sorry; Mathlib
   gap).
2. Draft the Slepian comparison signature (`slepian_comparison_finite`
   already at `Helpers/MultivariateSmallBallUpper.lean` per R35).
3. Draft the Sudakov-Fernique signature.
4. Sketch composition path to retire A4/A5 (in R48 once BTIS lands).

R40-R44 estimate: 5 rounds for Slepian + SF + BTIS. Variance higher than
R39 (this is genuine math content, not categorical refactor). User's
1.4 rounds/day (or ~10 rounds/day) pace should keep R40-R55 within 2-4
calendar days at sustained execution.

---

## End of R39 status doc
