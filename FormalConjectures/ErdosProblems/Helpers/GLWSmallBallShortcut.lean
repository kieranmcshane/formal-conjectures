/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import FormalConjectures.ErdosProblems.Helpers.GaussianParametricAnalysis

/-!
# R48-T3.2 — GLW small-ball shortcut prep (compression-bundle item iv)

**R48 stretch deliverable** per the strategic post-R47 Grok pre-flight
Q5 BONUS verdict: GLW determinant shortcut for A4/A5 honest closure
~110-150 LOC (vs ~150-300 LOC for the KL+Talagrand chain). Path
B'-style structural shortcut.

This file sets up the R50-R51 GLW shortcut closure target signatures
without inflating mainline debt — following the R46-T3.1 pattern in
`GaussianParametricAnalysis.lean`, the target signatures live in this
docstring as a markdown code block, NOT as TAG'd Stubs. R50-R51 will
land them as Full theorems (or honest TAG'd Stubs at that time).

## Compression bundle context

Per R48-T2.3 status doc, the compression bundle items in play are:

* (i) Path γ' Phase 2 body close — **R48 attempted, T2.1 ABORTED**
  per Q3 framing audit (see `R48_T1_PathGammaPrimeAudit.md`).
* (iii) Track D round 3 cleanup — BTIS-via-Chernoff sub-lemma 3 Full
  closure. ~70% plausibility per R47 process discipline.
* **(iv) GLW shortcut for A4/A5 — this file's R50-R51 scope.**
  ~75% plausibility per Grok Q5 verdict. Net retirement: -2 sorries
  if A4 + A5 both land Full.

R48 stretch lands the imports + scaffolding; R50-R51 ships the bodies.

## Target signatures (R50-R51 scope, NOT yet landed as Stubs)

The following are the consumer-facing target signatures for the GLW
determinant shortcut. They are listed here as named-target theorems so
that R50-R51 rounds can find them by grep without ambiguity.

### Lemma 4.1 (GLW det-route bridge)

```
-- R50 candidate (NOT YET LANDED):
theorem glw_det_route_lower_bound
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) (h_kernel : GLWKernel hierarchy B) :
    ∃ c : ℝ, 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      Real.exp (-c * ε^(-2 / (n : ℝ))) ≤
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε)
```

Recipe (Grok Q5 BONUS): bound the Gaussian small-ball probability
below by a determinant-driven exponential, using the GLW projective
limit + `det_CFC_sqrt_pos_of_posDef` (R46-T2.1) + uniform spectral
lower bound from `posDef_min_eigenvalue_pos` (R46-T2.2). Estimated
~50-70 LOC.

### Lemma 4.2 (GLW det-route upper bridge)

```
-- R50 candidate (NOT YET LANDED):
theorem glw_det_route_upper_bound
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) (h_kernel : GLWKernel hierarchy B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε →
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε) ≤
        C * Real.exp (-c_upper hierarchy * ε^(-2 / (n : ℝ)))
```

Recipe: dual of Lemma 4.1, uses the same R46 helpers + the existing
`GLWUpperProof.gao_li_wellner_small_ball_upper_kernel_bridge`.
Estimated ~50-70 LOC.

### A4 closure (`524.lean` consumer target)

```
-- R51 candidate (NOT YET LANDED):
theorem gao_li_wellner_small_ball_lower_via_det_route
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) :
    ∃ c : ℝ, 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      Real.exp (-c * ε^(-2 / (n : ℝ))) ≤
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε)
```

Closes the A4 axiom via Lemma 4.1 + the GLW kernel construction.
Estimated ~10-15 LOC of composition. **-1 sorry mainline retirement.**

### A5 closure (`524.lean` consumer target)

```
-- R51 candidate (NOT YET LANDED):
theorem gao_li_wellner_small_ball_upper_via_det_route
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hierarchy : GLWHierarchy n) :
    ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε →
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) B).real
          (Metric.ball 0 ε) ≤
        C * Real.exp (-c_upper hierarchy * ε^(-2 / (n : ℝ)))
```

Dual of A4 closure via Lemma 4.2. Estimated ~10-15 LOC. **-1 sorry
mainline retirement.**

## Mathlib API status (R48-T1.1 audit grounding)

All Mathlib citations below verified at `mathlib4 @ 25ce63313608` +
`brownian-motion @ 91267abd71bd`:

* `Matrix.PosDef.eigenvalues_pos` — `Mathlib/Analysis/Matrix/PosDef.lean:85`
* `Matrix.PosSemidef.det_nonneg` — `Mathlib/Analysis/Matrix/PosDef.lean:51`
* `det_CFC_sqrt_eq_sqrt_det` — `Helpers/MultivariateGaussianPdf.lean:171`
  (R46-T2.1 Full)
* `det_CFC_sqrt_pos_of_posDef` — `Helpers/MultivariateGaussianPdf.lean:195`
  (R46-T2.1 corollary Full)
* `posDef_min_eigenvalue_pos` — `Helpers/PhaseAUpperBound.lean:245`
  (R46-T2.2 Full)
* `Metric.ball_pi` — `Mathlib/Topology/MetricSpace/Pi.lean` (verified
  at pin)
* `gao_li_wellner_small_ball_upper_kernel_bridge` —
  `Helpers/GLWUpperProof.lean` (existing R29-R34 work)

## R48 stretch outcome

This file shipped at T+~1:30 as part of T3.2 stretch. **No new TAG'd
Stubs added** — debt-neutral. R50-R51 will land the bodies above as
Full theorems (or honest TAG'd Stubs at that time, per the R46-T3.1
Cowork pattern in `GaussianParametricAnalysis.lean`).

R48 mainline net retirement remains 0; this stretch deliverable is
**preparatory infrastructure** for R50-R51 compression bundle item
(iv) execution. Cumulative R48-R52 mainline retirement target: ~2
(R40 Stub + Phase 2 body) + Track D round 3 contribution (-2 to -3) +
this file's R50-R51 contribution (-2 if both A4/A5 land) = ~6-7
retirements jointly.

See `Helpers/PhaseV2R48Status.md` and
`Helpers/R48_T1_PathGammaPrimeAudit.md` for the round status doc +
framing audit. -/

namespace Erdos524.Helpers.GLWSmallBallShortcut

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Real MatrixOrder

/-! ## R50 deferred-paper sub-Stubs (Lemmas 4.1 + 4.2)

R50 T1.1 audit (`Helpers/Round50_T1_GLWShortcutAudit.md`) found a
chain mismatch: the brief's premise that closing GLW 2010 §4
Lemmas 4.1 + 4.2 retires axioms A4 + A5 is not supported by the
existing axiom signatures or in-tree state. Specifically:

* A4 / A5 (`gao_li_wellner_small_ball_lower` / `_upper` at
  `524.lean:3643` / `:3574`) are **Gaussian-process** small-ball
  asymptotics over `IsGLWProcess Y` on continuous index `u ≥ 0`.
* Lemmas 4.1 + 4.2 are **finite-dim deterministic** matrix
  identities. The bridge requires discretization + Anderson +
  optimization + tail handling + `IsGLWProcess` covariance
  consumption (chain α/β/γ/δ/ε in the audit doc), all 0% in Mathlib
  at pin and not within the brief's 110-150 LOC scope.
* Mainline already contains a 5909+ LOC alternate in-tree closure
  track (Q1a/b/c via Fourier smoothing + Berry-Esseen + hierarchical
  Cauchy: `CauchyDetLowerBound.lean`, `CharFunCrossBlock.lean`,
  `MultivariateSmallBallUpper.lean`, `SurgicalDensityAtZero.lean`,
  `EsseenSmoothing.lean`, `GaussianHierCauchyBox.lean`) which the
  brief's GLW determinant shortcut does not connect to.

Per R50 brief's discipline rule "if any claim cannot be verified,
flag explicitly and propose alternative", T2.1 + T2.2 land as honest
TAG'd sub-Stubs (this section) recording the deferral; T2.3 is
SKIPPED (no axiom-to-theorem swap). Mismatch ledger entry #16 (same
family as #14 — Cowork+Grok shared chain-level scope-mismatch).

Both sub-Stubs below are conservative-shape signatures intended as
forward-compatible deferral records — exact entries / exact
formulation requires Gao-Li-Wellner 2010 §4 paper access (not in R50
audit window). R51+ should refine signatures and either close Full
or replace with the concrete in-tree consumer construction.

This file remains **un-imported** by any other file at R50 close, so
the +2 sorries below are isolated and do not pollute consumer build
state. -/

/-- **GLW 2010 §4 Lemma 4.1 (deferred-paper sub-Stub).**

Conservative-shape forward-compatible deferral record for GLW 2010 §4
Lemma 4.1 (a determinant perturbation identity for the GLW kernel
matrix `K_GLW^(n)`). The exact form of the perturbation identity
requires paper access not in R50 audit window — see
`Round50_T1_GLWShortcutAudit.md` claim #6.

The signature here states a generic Jacobi-style first-order
expansion: along any scalar path `ε ↦ K + ε • E` through a square
real matrix `K`, the determinant is differentiable at `ε = 0` with
some derivative `c`. The actual GLW 2010 §4 Lemma 4.1 is more
specific (it pins `c` to an explicit value involving `K`'s structure);
R51+ should refine.

The body genuinely requires the R40 `Matrix.det.differentiable` Stub
(`MatrixDetDifferentiable.lean:144`) closure plus a chain rule, hence
the sorry is non-trivial and load-bearing.

NOT consumed by any other file at R50 close.
TAG[R50-T2.1-glw-lemma-4-1-deferred-paper] -/
theorem glw_lemma_4_1_deferred_paper :
    ∀ (n : ℕ) (K E : Matrix (Fin n) (Fin n) ℝ),
      ∃ c : ℝ, HasDerivAt (fun ε : ℝ => (K + ε • E).det) c 0 := by
  sorry

/-- **GLW 2010 §4 Lemma 4.2 (deferred-paper sub-Stub).**

Conservative-shape forward-compatible deferral record for GLW 2010 §4
Lemma 4.2 (`per(A) = 1` and `det(A) = 32·m·(240·e⁻³)^m` for a specific
structured matrix `A` of dimension `m × m` indexed by the
hierarchical grid). The exact matrix entries and the precise
formulation require paper access not in R50 audit window — see
`Round50_T1_GLWShortcutAudit.md` claim #7.

The signature here states the existence of a structured matrix `A`
of dimension `m² × m²` (suggested by the hierarchical-grid index
structure used in the in-tree Q1a/b/c track:
`hierGrid m : Fin m × Fin m`) such that both the permanent and the
determinant take the values stated in the brief. The dimension `m²`
is a guess based on the in-tree Q1a/b/c hierarchical-grid pattern;
the GLW 2010 §4 paper may use a different convention (e.g. `m × m`
or `(m+1) × (m+1)`), in which case R51+ refines.

The brief's stated formula `32m · (240 e^{-3})^m` is interpreted as
`32 · m · (240 · e⁻³)^m`. The alternative interpretation
`32^m · (240 · e⁻³)^m` is also plausible; without paper access,
neither can be verified. R51+ refines if needed.

NOT consumed by any other file at R50 close.
TAG[R50-T2.2-glw-lemma-4-2-deferred-paper] -/
theorem glw_lemma_4_2_deferred_paper :
    ∀ m : ℕ, 1 ≤ m → ∃ A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ,
      A.permanent = 1 ∧
      A.det = (32 : ℝ) * (m : ℝ) * ((240 : ℝ) * Real.exp (-3)) ^ m := by
  sorry

end Erdos524.Helpers.GLWSmallBallShortcut

/-! ## R59 → R60 — GLW infrastructure (paper-faithful sigs, R61 bodies)

R59 was an infrastructure round drafted from a Cowork-derived recall
of arXiv:1001.0200v1 §4 (paper-recheck not independently verified at
draft time, see `TrackA_R59_T1_GrepAudit.md` lines 94–108 hedge
clause). R60 attempt 1 surfaced empirical disproofs of both R59
closure claims at m=1 (`per(A) = 4 ≠ 1`; Lemma 4.1 RHS form fails on
`a = [[2]], b = [[0]]`) — see `TrackA_R60_T1_PerLemma41Audit.md` §T1.2
/ §T1.3. R60 attempt 2 (this revision) fetches the paper verbatim
and replaces the R59 sigs with their paper-exact forms.

**Verbatim corrections vs R59** (audit doc §T1.6):

* Grid: `δ_{m·p+q} = 4^{p+m} · (m+q)` for `0 ≤ p < m`, `1 ≤ q ≤ m`
  (the exponent on 4 is `p+m`, each block scales ×4 — R59 had `4·m`
  flat, missing the geometric block factor).
* Matrix `A`: Cauchy form `a_{ij} = 1 / (δ_i + δ_j)` (R59 had
  `δ²` / exp split, paper-incorrect).
* Auxiliary matrix `B`: `b_{ij} = exp(−δ_i − δ_j) · a_{ij}` (absent
  in R59; used in Lemma 4.1 application).
* Lemma 4.2: both halves are **inequalities** —
  `per(A) ≤ 1` and `det(A) ≥ (240·e)^{−2m³}` (R59 had equalities
  with paper-incorrect constants `32^m·(240·e^{-3})^m`).
* Lemma 4.1: ratio-based perturbation —
  `det(a − b) ≥ det(a) − (∑_k max_l (b_{kl}/a_{kl})) · per(a)` (R59
  had absolute `∑_l B` without ratio against `A`, and used `B` rather
  than `(a − b)` on the LHS index).

The R59 helper `Matrix.rowSup` is removed — it was infra for the old
Lemma 4.1 sig, which the paper-exact ratio form does not consume.
The R50 historical sub-Stubs above (`glw_lemma_4_1_deferred_paper`,
`glw_lemma_4_2_deferred_paper`) are unchanged and remain as
conservative-shape deferral records.

R60 lands the sig revisions; bodies stage to R61. Net debt change
R59 → R60: **0 sorries / 0 axioms / 0 Stub retirements** (the two
R59 sorries persist with TAGs migrated from `R60-*` / `R61-*` to
`R61-*`).

See `Helpers/TrackA_R60_T1_PerLemma41Audit.md` (especially §T1.2,
§T1.3, §T1.6) for the audit trail. -/

namespace Erdos524.Helpers.GLWSmallBallShortcut

/-- Discretization grid from Gao–Li–Wellner 2010 §4
(arXiv:1001.0200v1), paper-exact form: `δ_{m·p + q} = 4^{p+m} · (m+q)`
for `0 ≤ p < m`, `1 ≤ q ≤ m`. Encoded flat on `Fin (m * m)` via
`p = i.val / m`, `q = (i.val % m) + 1`. The exponent `p + m` on 4
is critical — each `p`-block scales ×4 (R59 had `4·m` flat, missing
this geometric factor). -/
noncomputable def hierarchicalGrid (m : ℕ) (_hm : 0 < m) :
    Fin (m * m) → ℝ :=
  fun i =>
    (4 : ℝ) ^ (i.val / m + m) * ((m : ℝ) + ((i.val % m + 1 : ℕ) : ℝ))

/-- Test lemma — every grid value is positive when `m ≥ 1`. -/
theorem hierarchicalGrid_pos (m : ℕ) (hm : 0 < m) (i : Fin (m * m)) :
    0 < hierarchicalGrid m hm i := by
  unfold hierarchicalGrid
  have h4 : (0 : ℝ) < (4 : ℝ) ^ (i.val / m + m) := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
  have hq1 : (1 : ℝ) ≤ ((i.val % m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hsum : (0 : ℝ) < (m : ℝ) + ((i.val % m + 1 : ℕ) : ℝ) := by linarith
  exact mul_pos h4 hsum

/-- Cauchy-form matrix `A` from Gao–Li–Wellner 2010 §4 (paper-exact):
`a_{ij} = 1 / (δ_i + δ_j)`. The Cauchy structure is exploited in
Lemma 4.2 via the classical Cauchy determinant identity (R61 body;
identity NOT in Mathlib at the project pin, must be derived from
scratch or axiomatised at R61). -/
noncomputable def glwMatrixA (m : ℕ) (hm : 0 < m) :
    Matrix (Fin (m * m)) (Fin (m * m)) ℝ :=
  fun i j => 1 / (hierarchicalGrid m hm i + hierarchicalGrid m hm j)

/-- Auxiliary matrix `B` from Gao–Li–Wellner 2010 §4 (paper-exact):
`b_{ij} = exp(−δ_i − δ_j) · a_{ij}`. Used in Lemma 4.1 application
to bound `det(A − B)`. -/
noncomputable def glwMatrixB (m : ℕ) (hm : 0 < m) :
    Matrix (Fin (m * m)) (Fin (m * m)) ℝ :=
  fun i j =>
    Real.exp (-(hierarchicalGrid m hm i) - hierarchicalGrid m hm j)
      * glwMatrixA m hm i j

/-- **GLW 2010 §4 Lemma 4.2 (paper-exact, both halves are inequalities).**

States `permanent (glwMatrixA m hm) ≤ 1` and
`det (glwMatrixA m hm) ≥ (240 · e)^(−2·m³)`. Body is staged for R61
(per side: Cauchy permanent bound + grid constants, ~150–250 LOC; det
side: Cauchy determinant identity + telescoping + grid constants,
~500–700 LOC; the Cauchy det identity is NOT in Mathlib at this pin
and must be derived from scratch ~30–60 LOC or axiomatised — choice
deferred to R61).

Refines (does NOT retire) the conservative-shape R50 sub-Stub
`glw_lemma_4_2_deferred_paper` above. R60 corrects two paper-fidelity
errors in the R59 sig: (a) both halves are inequalities, not
equalities; (b) the constants are `(240·e)^{−2m³}`, not
`32^m · (240·e^{−3})^m`.

NOT consumed by any other file at R60 close.
TAG[R61-glw-lemma-4-2-paper-specs] -/
theorem glw_lemma_4_2_paper_specs (m : ℕ) (hm : 0 < m) :
    Matrix.permanent (glwMatrixA m hm) ≤ 1 ∧
    (glwMatrixA m hm).det ≥
      (240 * Real.exp 1) ^ (-2 * (m : ℤ) ^ 3) := by
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

/-- **GLW 2010 §4 Lemma 4.1 (paper-exact perturbation).**

For square real matrices with `0 < a_{ij}` everywhere and
`0 < b_{ij} < a_{ij}` everywhere,
`det(a − b) ≥ det(a) − (∑_k max_l (b_{kl} / a_{kl})) · per(a)`.

Body is staged for R61 (multilinearity of `det` + bookkeeping of the
ratio sup, ~80–120 LOC).

Refines (does NOT retire) the conservative-shape R50 sub-Stub
`glw_lemma_4_1_deferred_paper` above. R60 corrects the R59 sig: the
perturbation term is `max_l (b/a)` ratio (not `∑_l B` absolute), and
the matrix index on the LHS is `(a − b)` (not `b`).

NOT consumed by any other file at R60 close.
TAG[R61-glw-lemma-4-1-perturbation] -/
theorem glw_lemma_4_1_perturbation
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : Matrix ι ι ℝ)
    (h_pos_a : ∀ i j, 0 < a i j)
    (h_strict : ∀ i j, 0 < b i j ∧ b i j < a i j) :
    Matrix.det (fun i j => a i j - b i j) ≥
      Matrix.det a -
        (∑ k : ι, Finset.univ.sup' Finset.univ_nonempty
          (fun l : ι => b k l / a k l)) * Matrix.permanent a := by
  sorry

end Erdos524.Helpers.GLWSmallBallShortcut
