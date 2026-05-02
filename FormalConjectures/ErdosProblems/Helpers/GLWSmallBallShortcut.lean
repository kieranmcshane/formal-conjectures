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

/-! ## R59 — GLW infrastructure (paper-faithful sigs, R60-R61 bodies)

R59 is an **infrastructure** round, not a closure round. The
post-TC9 Grok strategy probe surfaced three candidate signatures
for the GLW 2010 §4 shortcut; cross-checking against the project
pin (`mathlib4 @ 25ce63313608`) revealed:

* The Cauchy determinant identity is **not** in Mathlib at this
  pin (0 hits for `cauchyMatrix / det_cauchy / cauchy_det`).
* Lemma 4.1 needs a `rowSup` helper since `Matrix.row A k |>.max'`
  does not compile at this pin.
* The hierarchical-grid dimension is `m * m` (not `m * (m+1)`)
  per arXiv:1001.0200v1 §4.
* The realistic `det(A)` body budget is 600–900+ LOC, not 300–450,
  once Cauchy + the A/B/C partition step are zoom-checked.

R59 lands the paper-faithful refinement of the R50 deferred-paper
sub-Stubs above: corrected `hierarchicalGrid` (`Fin (m*m)`,
δ-formula `4m/(m+q)`), `glwMatrixA` with the diagonal /
off-diagonal split, and three signatures (Lemma 4.2 paper specs,
Lemma 4.1 perturbation, plus the auxiliary `Matrix.rowSup`). All
theorem bodies are sorried with TAG comments naming the staged
round (R60 or R61).

The two R50 sub-Stubs above (`glw_lemma_4_1_deferred_paper`,
`glw_lemma_4_2_deferred_paper`) are **not retired** by R59 — they
remain as historical conservative-shape deferral records, to be
retired by a future round once R60–R61 close the paper-faithful
bodies and the consumer call sites
(`gao_li_wellner_small_ball_lower / _upper`) are bridged in R62+.

Net debt change R58 → R59: **+2 sorries (TAG'd for R60–R61),
0 axioms, 0 Stub retirements**. Reported as `infra +2 sorries`,
NOT as net debt change toward the R52 gate (per Erdős 524 framing:
infrastructure rounds are milestones, not closures).

See `Helpers/TrackA_R59_T1_GrepAudit.md` for the audit grounding
(Mathlib API surface, paper recheck of the δ formula and the
`det(A)` constant `32^m · (240 · exp(−3))^m`, and placeholder
location confirmation). -/

namespace Matrix

/-- Row supremum of a square real matrix at row `k`. Wraps
`Finset.univ.sup'` so downstream proofs (R60+) can rewrite without
re-deriving the construction. Used in
`glw_lemma_4_1_perturbation` below. -/
noncomputable def rowSup {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (k : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (A k)

end Matrix

namespace Erdos524.Helpers.GLWSmallBallShortcut

/-- Discretization grid from Gao–Li–Wellner 2010 §4
(arXiv:1001.0200v1), paper-exact form: `δ_{m·p + q} = 4·m / (m + q)`
for `p ∈ {0, …, m-1}` and `q ∈ {1, …, m}`, encoded flat on
`Fin (m * m)` via `q = (i.val % m) + 1`, `p = i.val / m`. The
formula depends only on `q`; the `p` index is the row-block
selector and is preserved in the docstring for paper-faithfulness. -/
noncomputable def hierarchicalGrid (m : ℕ) (_hm : 0 < m) :
    Fin (m * m) → ℝ :=
  fun i => (4 * (m : ℝ)) / ((m : ℝ) + (((i.val % m : ℕ) : ℝ) + 1))

/-- Test lemma — every grid value is positive when `m ≥ 1`. -/
theorem hierarchicalGrid_pos (m : ℕ) (hm : 0 < m) (i : Fin (m * m)) :
    0 < hierarchicalGrid m hm i := by
  unfold hierarchicalGrid
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hi : (0 : ℝ) ≤ ((i.val % m : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hnum : (0 : ℝ) < 4 * (m : ℝ) := by linarith
  have hden : (0 : ℝ) < (m : ℝ) + (((i.val % m : ℕ) : ℝ) + 1) := by
    linarith
  exact div_pos hnum hden

/-- Test lemma — every grid value is bounded above by `4·m`.

Follows from `4·m / (m + q) ≤ 4·m` when `m + q ≥ 1`, which holds
since `q ≥ 1`. -/
theorem hierarchicalGrid_le_4m (m : ℕ) (hm : 0 < m) (i : Fin (m * m)) :
    hierarchicalGrid m hm i ≤ 4 * (m : ℝ) := by
  unfold hierarchicalGrid
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hi : (0 : ℝ) ≤ ((i.val % m : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hnum : (0 : ℝ) ≤ 4 * (m : ℝ) := by linarith
  have hden : (1 : ℝ) ≤ (m : ℝ) + (((i.val % m : ℕ) : ℝ) + 1) := by
    linarith
  exact div_le_self hnum hden

/-- Structured matrix `A` from Gao–Li–Wellner 2010 §4 (paper-exact
form): on the diagonal, `A i i = δ_i · δ_i`; off the diagonal,
`A i j = exp(−(δ_i · δ_j))`. The `δ_i` are values of
`hierarchicalGrid m hm`. Lemma 4.2
(`glw_lemma_4_2_paper_specs` below) computes
`permanent A = 1` and `det A = 32^m · (240 · exp(−3))^m`. -/
noncomputable def glwMatrixA (m : ℕ) (hm : 0 < m) :
    Matrix (Fin (m * m)) (Fin (m * m)) ℝ :=
  fun i j =>
    let δi := hierarchicalGrid m hm i
    let δj := hierarchicalGrid m hm j
    if i = j then δi * δj else Real.exp (-(δi * δj))

/-- **GLW 2010 §4 Lemma 4.2 (paper-faithful sig).**

States `permanent (glwMatrixA m hm) = 1` and
`det (glwMatrixA m hm) = 32^m · (240 · exp(−3))^m`. Body is staged
across R60 (`per(A) = 1`, ~100–150 LOC, 5-step crude bound) and
R61 (`det(A)`, ~600–900 LOC with the Cauchy identity + A/B/C
partition; if R60 gate binds the explicit constant may be
axiomatized hybrid (c)).

Refines (does NOT retire) the conservative-shape R50 sub-Stub
`glw_lemma_4_2_deferred_paper` above. The R50 form had an
ambiguous `32 · m` vs `32^m` self-flag; the R59 brief's paper
recheck (see `TrackA_R59_T1_GrepAudit.md` T1.2) records `32^m`
as the correct form per arXiv:1001.0200v1 §4.

NOT consumed by any other file at R59 close.
TAG[R59-T3-glw-lemma-4-2-paper-specs] -/
theorem glw_lemma_4_2_paper_specs (m : ℕ) (hm : 0 < m) :
    Matrix.permanent (glwMatrixA m hm) = 1 ∧
    (glwMatrixA m hm).det =
      (32 : ℝ) ^ m * ((240 : ℝ) * Real.exp (-3)) ^ m := by
  sorry

/-- **GLW 2010 §4 Lemma 4.1 (paper-faithful perturbation sig).**

States the determinant comparison: for `B ≤ A` entrywise and
`0 ≤ B` entrywise on a square real matrix,
`det B ≥ det A − (∑ k, (∑ l, B k l) · rowSup A k) · permanent A`.
Body is staged for R60 (Strategy A: `det` multilinearity +
permanent expansion via `Matrix.det_apply`, ~60–100 LOC).

Refines (does NOT retire) the conservative-shape R50 sub-Stub
`glw_lemma_4_1_deferred_paper` above. The R50 form was a generic
Jacobi-style first-order expansion `∃ c, HasDerivAt …`; R59
upgrades to the paper-faithful comparison form.

Uses `Matrix.rowSup` (defined above this section).

NOT consumed by any other file at R59 close.
TAG[R59-T3-glw-lemma-4-1-perturbation] -/
theorem glw_lemma_4_1_perturbation {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℝ)
    (h_le : ∀ i j, B i j ≤ A i j) (h_nonneg : ∀ i j, 0 ≤ B i j) :
    B.det ≥ A.det
      - (∑ k : ι, (∑ l : ι, B k l) * Matrix.rowSup A k)
        * Matrix.permanent A := by
  sorry

end Erdos524.Helpers.GLWSmallBallShortcut
