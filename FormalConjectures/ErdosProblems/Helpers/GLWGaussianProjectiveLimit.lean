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

import FormalConjectures.ErdosProblems.Helpers.YGLWFromBrownianMotion
import FormalConjectures.ErdosProblems.Helpers.SubGaussianGaussianReal
import BrownianMotion.Gaussian.MultivariateGaussian
import BrownianMotion.Gaussian.ProjectiveLimit
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.KolmogorovChentsov
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.PSeries

/-!
# Phase 2 / Round 15 — GLW Gaussian projective limit

Kernel-generic projective-limit construction for the GLW kernel
`K_GLW(s, t) = (1 - exp(-(s + t))) / (s + t)`.

`brownian-motion`'s `gaussianProjectiveFamily` is hardcoded to the
Brownian covariance `brownianCovMatrix(I) = min(s, t)`. To realize the
`Y_GLW` process we cannot **substitute** — we must **construct in
parallel**, using `glwCovMatrixNN(I) = K_GLW(s, t)` from the bridge
file `Helpers/YGLWFromBrownianMotion.lean` (R13/R14 §4.49).

This file is structured to mirror
`brownian-motion/BrownianMotion/Gaussian/ProjectiveLimit.lean`
1-to-1: every public lemma in the brownian template has a `glw`-prefixed
counterpart here.

## Outcome map (R15)

| ID | Public name | Status |
|----|-------------|--------|
| O1 | `glwGaussianProjectiveFamily`             | definition + simp lemma |
| O2 | `isProjectiveMeasureFamily_glwGaussianProjectiveFamily` | full proof |
| O3 | `glwGaussianLimit`, `isProjectiveLimit_glwGaussianLimit` | definition + cylinder lemma |
| O4 | `glwGaussianLimit_isKolmogorovProcess`    | partial / structured-sorry |
| O5 | `isGLWProcess_of_glwGaussianLimit_witness`  | partial / structured-sorry |

## Design

* The map `(MeasurableEquiv.toLp 2 (I → ℝ)).symm` is the brownian-motion
  convention for converting between `EuclideanSpace ℝ I`-valued and
  `(I → ℝ)`-valued measures. We re-use it verbatim so that consumers
  expecting the brownian-motion shape can plug in `glwGaussianLimit`
  with no boilerplate adapter.
* `Finset.restrict₂` is the canonical projection between
  `Π i : J, X i` and `Π i : I, X i` for `I ⊆ J`. Composed with the
  `EuclideanSpace.restrict₂` of `MultivariateGaussian.lean` this gives
  the projective-consistency datum.
* PSD on every grid is `glwCovMatrixNN_PosSemidef` (R13 §4.49). Sub-grid
  identity is `glwCovMatrixNN_submatrix` (`rfl`). These are the two
  "B1+B2 preconditions" already factored out by R13.
-/

namespace Erdos524.Helpers

open MeasureTheory NormedSpace Set ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

/-!
## O1 — `glwGaussianProjectiveFamily`

The pushforward of `multivariateGaussian 0 (glwCovMatrixNN I)` under
the `EuclideanSpace ℝ I ≃ (I → ℝ)` measurable equivalence. Mirrors
`ProbabilityTheory.gaussianProjectiveFamily` from
`brownian-motion/BrownianMotion/Gaussian/ProjectiveLimit.lean`.
-/

/-- The Gaussian projective family on the NNReal grid for the GLW
kernel. For each finset `I : Finset NNReal`, this is the multivariate
Gaussian on `(I → ℝ)` with covariance `K_GLW`. -/
noncomputable
def glwGaussianProjectiveFamily (I : Finset NNReal) : Measure (I → ℝ) :=
  multivariateGaussian 0 (glwCovMatrixNN I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

/-- **O1 simp lemma**: applying `glwGaussianProjectiveFamily` is the
pushforward of `multivariateGaussian 0 (glwCovMatrixNN I)`. Direct
unfold; useful for rewriting in projective-consistency proofs. -/
@[simp]
lemma glwGaussianProjectiveFamily_apply (I : Finset NNReal) :
    glwGaussianProjectiveFamily I =
      (multivariateGaussian 0 (glwCovMatrixNN I)).map
        (MeasurableEquiv.toLp 2 (I → ℝ)).symm := rfl

/-- The pushforward direction of the equivalence is measure-preserving,
in the multivariate-Gaussian-to-projective-family direction. Mirrors
`measurePreserving_equiv_multivariateGaussian` from brownian-motion's
`ProjectiveLimit.lean`. -/
lemma glwMeasurePreserving_equiv_multivariateGaussian (I : Finset NNReal) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm
      (multivariateGaussian 0 (glwCovMatrixNN I)) (glwGaussianProjectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

/-- `glwGaussianProjectiveFamily I` is Gaussian, hence in particular
finite. Needed to bring the `IsFiniteMeasure (glwGaussianProjectiveFamily i)`
instance into scope for `projectiveLimit` / `IsProbabilityMeasure`. -/
instance isGaussian_glwGaussianProjectiveFamily (I : Finset NNReal) :
    IsGaussian (glwGaussianProjectiveFamily I) := by
  unfold glwGaussianProjectiveFamily
  rw [MeasurableEquiv.coe_toLp_symm_eq]
  infer_instance

/-!
## O2 — Projective consistency

Mirror of `isProjectiveMeasureFamily_gaussianProjectiveFamily` from the
brownian template. The proof structure: rewrite via `Measure.map_map`,
exhibit the conjugating equivalence, then close with the Lebesgue
substitution from `measurePreserving_restrict_multivariateGaussian`,
using `glwCovMatrixNN_PosSemidef` for the PSD precondition.
-/

/-- **O2 (Full).** `glwGaussianProjectiveFamily` is consistent under
`Finset.restrict₂` for every inclusion `J ⊆ I`. Mirrors
`isProjectiveMeasureFamily_gaussianProjectiveFamily`. -/
lemma isProjectiveMeasureFamily_glwGaussianProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ : NNReal ↦ ℝ) glwGaussianProjectiveFamily := by
  intro I J hJI
  nth_rw 2 [glwGaussianProjectiveFamily]
  rw [Measure.map_map]
  · have h_eq :
        (Finset.restrict₂ (π := fun _ : NNReal ↦ ℝ) hJI ∘
            (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
          (MeasurableEquiv.toLp 2 (J → ℝ)).symm ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [h_eq, ((glwMeasurePreserving_equiv_multivariateGaussian J).comp
      (measurePreserving_restrict_multivariateGaussian
        (glwCovMatrixNN_PosSemidef I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _
  · fun_prop

/-!
## O3 — `glwGaussianLimit`

Apply Kolmogorov extension to the projective family. Mirrors
`gaussianLimit` and `isProjectiveLimit_gaussianLimit`.
-/

/-- **O3 (Full).** The GLW Gaussian process measure on `NNReal → ℝ`,
obtained by Kolmogorov extension from `glwGaussianProjectiveFamily`. -/
noncomputable
def glwGaussianLimit : Measure (NNReal → ℝ) :=
  projectiveLimit glwGaussianProjectiveFamily
    isProjectiveMeasureFamily_glwGaussianProjectiveFamily

/-- **O3 cylindrical-projection lemma.** `glwGaussianLimit` is the
projective limit of `glwGaussianProjectiveFamily`. -/
lemma isProjectiveLimit_glwGaussianLimit :
    IsProjectiveLimit glwGaussianLimit glwGaussianProjectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_glwGaussianProjectiveFamily

/-- The projective-limit measure is a probability measure, since the
finite-dimensional projections are. -/
instance IsProbabilityMeasure_glwGaussianLimit :
    IsProbabilityMeasure glwGaussianLimit :=
  isProbabilityMeasure_projectiveLimit isProjectiveMeasureFamily_glwGaussianProjectiveFamily

/-- The cylindrical-restriction `Finset.restrict I` is measure-preserving
between `glwGaussianLimit` and `glwGaussianProjectiveFamily I`. -/
lemma hasLaw_restrict_glwGaussianLimit {I : Finset NNReal} :
    HasLaw I.restrict (glwGaussianProjectiveFamily I) glwGaussianLimit :=
  isProjectiveLimit_glwGaussianLimit.hasLaw_restrict

/-!
## O3.5 — Single-coordinate evaluation lemmas (R17)

Direct ports of the brownian-motion analogs from
`brownian-motion/Gaussian/ProjectiveLimit.lean` lines 78–202.
For the GLW kernel, the variance of `ω s` is `K_GLW(s, s)` (rather
than `min s s = s` in the Brownian case), and the bivariate-difference
variance is `K_GLW(s,s) + K_GLW(t,t) - 2 K_GLW(s,t)` (rather than the
brownian-motion's `max (s-t) (t-s)`).
-/

/-- Pushforward identity for integrals on `glwGaussianProjectiveFamily I`:
the integral against the projective family is the integral against
the multivariate Gaussian, after composing with the
Euclidean-vs-Pi equivalence. Direct port of
`integral_gaussianProjectiveFamily`. -/
lemma integral_glwGaussianProjectiveFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset NNReal) (f : (I → ℝ) → E) :
    ∫ x, f x ∂glwGaussianProjectiveFamily I =
      ∫ x, f (EuclideanSpace.equiv I ℝ x)
        ∂multivariateGaussian 0 (glwCovMatrixNN I) := by
  simp only [glwGaussianProjectiveFamily, integral_map_equiv, MeasurableEquiv.toLp_symm_apply]
  rfl

/-- Centeredness of the projective family: the identity has integral
`0`. Direct port of `integral_id_gaussianProjectiveFamily`. -/
@[simp]
lemma integral_id_glwGaussianProjectiveFamily (I : Finset NNReal) :
    ∫ x, x ∂(glwGaussianProjectiveFamily I) = 0 := by
  rw [integral_glwGaussianProjectiveFamily, ← ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian, map_zero]

/-- The covariance of two coordinate evaluations under the projective
family equals the kernel value `K_GLW(s, t)`. Direct port of
`covariance_eval_gaussianProjectiveFamily`, with `min s.1 t.1`
replaced by `K_GLW (s.1) (t.1)`. -/
lemma covariance_eval_glwGaussianProjectiveFamily (I : Finset NNReal) (s t : I) :
    cov[fun x ↦ x s, fun x ↦ x t; glwGaussianProjectiveFamily I] =
      K_GLW (s.1 : ℝ) (t.1 : ℝ) := by
  rw [glwGaussianProjectiveFamily, covariance_map_equiv]
  change cov[fun x : EuclideanSpace ℝ I ↦ x s, fun x ↦ x t; _] = _
  have (u : I) : (fun x : EuclideanSpace ℝ I ↦ x u) =
      fun x ↦ ⟪EuclideanSpace.basisFun I ℝ u, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covarianceBilin_apply_eq_cov,
    covarianceBilin_multivariateGaussian (glwCovMatrixNN_PosSemidef I),
    ContinuousBilinForm.ofMatrix_orthonormalBasis, glwCovMatrixNN_apply]
  exact IsGaussian.memLp_two_id

/-- Variance specialization of the covariance lemma: the variance of
a single coordinate is the diagonal of `K_GLW`. -/
lemma variance_eval_glwGaussianProjectiveFamily {I : Finset NNReal} (s : I) :
    Var[fun x ↦ x s; glwGaussianProjectiveFamily I] = K_GLW (s.1 : ℝ) (s.1 : ℝ) := by
  rw [← covariance_self, covariance_eval_glwGaussianProjectiveFamily]
  exact Measurable.aemeasurable <| by fun_prop

/-- The marginal law of a coordinate evaluation under the projective
family is a centered real Gaussian with variance `K_GLW(s, s)`.
Direct port of `hasLaw_eval_gaussianProjectiveFamily`. -/
lemma hasLaw_eval_glwGaussianProjectiveFamily {I : Finset NNReal} (s : I) :
    HasLaw (fun x ↦ x s) (gaussianReal 0 (K_GLW (s.1 : ℝ) (s.1 : ℝ)).toNNReal)
      (glwGaussianProjectiveFamily I) where
  aemeasurable := Measurable.aemeasurable <| by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_eval_glwGaussianProjectiveFamily]
    conv => enter [1, 1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) s x
    rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_glwGaussianProjectiveFamily,
      map_zero]
    exact IsGaussian.integrable_id

/-- The marginal law of a coordinate-difference under the projective
family is a centered real Gaussian with variance the K_GLW
quadratic-difference. Direct port of
`hasLaw_eval_sub_eval_gaussianProjectiveFamily`, but with
`max (s - t) (t - s)` replaced by `K_GLW(s,s) + K_GLW(t,t) - 2 K_GLW(s,t)`. -/
lemma hasLaw_eval_sub_eval_glwGaussianProjectiveFamily (I : Finset NNReal) (s t : I) :
    HasLaw ((fun x ↦ x s - x t))
      (gaussianReal 0 (K_GLW (s.1 : ℝ) (s.1 : ℝ) + K_GLW (t.1 : ℝ) (t.1 : ℝ)
        - 2 * K_GLW (s.1 : ℝ) (t.1 : ℝ)).toNNReal)
      (glwGaussianProjectiveFamily I) where
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_fun_sub,
      variance_eval_glwGaussianProjectiveFamily, variance_eval_glwGaussianProjectiveFamily,
      covariance_eval_glwGaussianProjectiveFamily]
    · conv =>
        enter [1, 1, 2];
        change fun x ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun i : I ↦ ℝ) s -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun i : I ↦ ℝ) t) x
      rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_glwGaussianProjectiveFamily,
        map_zero]
      · rw [show K_GLW (s.1 : ℝ) (s.1 : ℝ) - 2 * K_GLW (s.1 : ℝ) (t.1 : ℝ)
                + K_GLW (t.1 : ℝ) (t.1 : ℝ)
              = K_GLW (s.1 : ℝ) (s.1 : ℝ) + K_GLW (t.1 : ℝ) (t.1 : ℝ)
                - 2 * K_GLW (s.1 : ℝ) (t.1 : ℝ) from by ring]
      · exact IsGaussian.integrable_id
    any_goals exact HasGaussianLaw.memLp_two

/-- The marginal law of a coordinate evaluation under the projective
limit is a centered real Gaussian with variance `K_GLW(t, t)`. -/
lemma hasLaw_eval_glwGaussianLimit {t : NNReal} :
    HasLaw (fun ω : NNReal → ℝ ↦ ω t) (gaussianReal 0 (K_GLW (t : ℝ) (t : ℝ)).toNNReal)
      glwGaussianLimit := by
  have h_eq : (fun ω : NNReal → ℝ ↦ ω t) =
      (fun x : ({t} : Finset NNReal) → ℝ ↦ x ⟨t, by simp⟩) ∘
        (({t} : Finset NNReal).restrict) := by
    funext ω; rfl
  rw [h_eq]
  exact (hasLaw_eval_glwGaussianProjectiveFamily ⟨t, by simp⟩).comp
    hasLaw_restrict_glwGaussianLimit

/-- The marginal law of a coordinate-difference under the projective
limit is a centered real Gaussian with variance the K_GLW
quadratic-difference. -/
lemma hasLaw_eval_sub_eval_glwGaussianLimit (s t : NNReal) :
    HasLaw (fun ω : NNReal → ℝ ↦ ω s - ω t)
      (gaussianReal 0 (K_GLW (s : ℝ) (s : ℝ) + K_GLW (t : ℝ) (t : ℝ)
        - 2 * K_GLW (s : ℝ) (t : ℝ)).toNNReal)
      glwGaussianLimit := by
  have hs : s ∈ ({s, t} : Finset NNReal) := by simp
  have ht : t ∈ ({s, t} : Finset NNReal) := by simp
  have h_eq : (fun ω : NNReal → ℝ ↦ ω s - ω t) =
      (fun x : ({s, t} : Finset NNReal) → ℝ ↦ x ⟨s, hs⟩ - x ⟨t, ht⟩) ∘
        (({s, t} : Finset NNReal).restrict) := by
    funext ω; rfl
  rw [h_eq]
  exact (hasLaw_eval_sub_eval_glwGaussianProjectiveFamily ({s, t} : Finset NNReal)
    ⟨s, hs⟩ ⟨t, ht⟩).comp hasLaw_restrict_glwGaussianLimit

/-- The covariance of two coordinate evaluations under the projective
limit equals `K_GLW(s, t)`. Direct port of
`covariance_eval_gaussianLimit`. -/
lemma covariance_eval_glwGaussianLimit {s t : NNReal} :
    cov[fun ω : NNReal → ℝ ↦ ω s, fun ω ↦ ω t; glwGaussianLimit] =
      K_GLW (s : ℝ) (t : ℝ) := by
  convert (hasLaw_restrict_glwGaussianLimit (I := {s, t})).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := Function.eval ⟨t, by simp⟩) ?_ ?_
  · rw [covariance_eval_glwGaussianProjectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)

/-!
## O4 — `IsKolmogorovProcess` instance

The projection process `fun (t : NNReal) (ω : NNReal → ℝ) ↦ ω t`,
under the projective-limit measure `glwGaussianLimit`, satisfies the
Kolmogorov-Chentsov condition with constants `(p, q, M) = (2, 2, 1)`
via the bridge-file Hölder bound
`glwCovMatrixNN_pairwise_diff_quadratic_le_sq`.

**Note on K-C threshold (R15 calibration finding).** The K-C theorem
for continuous modification on a 1-D index requires `q > p`. With
`p = q = 2` this is a critical case, which is why the standard recipe
uses higher even moments (`p = 4, q = 2 + ε`) for Gaussian processes.
The R15 partial-credit form below records `(2, 2, 1)` as the
arithmetically-correct moment bound, and flags the `q > p` lift as a
separate downstream step (it's a one-line bookkeeping adjustment using
the Gaussian higher-moment formula).
-/

/-- **O4 (Partial).** `IsKolmogorovProcess` for the coordinate
projection process `fun t ω ↦ ω t` under `glwGaussianLimit`, with
exponents `(p, q, M) = (2, 2, 1)` (the L²-Hölder-1 bound from the
bridge file).

Two of the four structure fields (`p_pos`, `q_pos`) are filled
inline. The remaining two (`measurablePair`, `kolmogorovCondition`)
are structured sorries:

* **`measurablePair`**: needs a projection-measurability lift —
  `fun ω ↦ (ω s, ω t)` is jointly measurable on the cylindrical
  σ-algebra. Standard one-liner via `Measurable.prodMk` once the
  projection-measurability instance for `glwGaussianLimit` is in scope
  (analog to `gaussianLimit`'s eval-measurability — also currently a
  Hölder-fit gap on the BM side).

* **`kolmogorovCondition`**: needs the Hölder-constant fit. The
  arithmetic content is
  `E[(ω s - ω t)²] = K_GLW(s,s) + K_GLW(t,t) - 2 K_GLW(s,t)
                  ≤ ((s : ℝ) - (t : ℝ))²`, supplied by
  `glwCovMatrixNN_pairwise_diff_quadratic_le_sq` and convertible to
  `M * edist s t ^ q` with `(q, M) = (2, 1)` modulo a `2`/`edist`
  bookkeeping step. The reduction `∫⁻ edist² = E[(diff)²]` uses
  `covariance_eval_multivariateGaussian` + `hasLaw_restrict_glwGaussianLimit`.

Note (K-C threshold gap): the Mathlib K-C continuous-modification
theorem requires `q > p` on a 1-D index, so the `(2, 2)` form in O4
suffices for the **structure** but a future R16 lift to `(4, 2, 3)`
via the centered-Gaussian 4-th moment formula `E[X⁴] = 3 E[X²]²`
will be needed before O5's continuous modification can be obtained
from `IsAEKolmogorovProcess.mk`. -/
theorem glwGaussianLimit_isKolmogorovProcess :
    IsKolmogorovProcess (T := NNReal) (Ω := NNReal → ℝ) (E := ℝ)
      (fun t ω => ω t) glwGaussianLimit 2 2 1 where
  measurablePair := by
    intro s t
    rw [← BorelSpace.measurable_eq]
    fun_prop
  kolmogorovCondition := by
    intro s t
    -- Convert real-pow exponent `(2 : ℝ)` to nat-pow `(2 : ℕ)` so subsequent
    -- ENNReal manipulations are in `Monoid.npow` form.
    have h2cast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    simp_rw [h2cast, ENNReal.rpow_natCast]
    set σ := K_GLW (s : ℝ) (s : ℝ) + K_GLW (t : ℝ) (t : ℝ) - 2 * K_GLW (s : ℝ) (t : ℝ) with hσ_def
    have hσ_nn : 0 ≤ σ := by
      have := K_GLW_diff_quadratic_nonneg (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)
      simp only [hσ_def]; linarith
    have hσ_le : σ ≤ ((s : ℝ) - (t : ℝ)) ^ 2 := by
      have := K_GLW_diff_quadratic_le_sq (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)
      simp only [hσ_def]; linarith
    have h_integrable : Integrable (fun x : ℝ ↦ x ^ 2)
        (gaussianReal (0 : ℝ) σ.toNNReal) := by
      have hmem := IsGaussian.memLp_id (μ := gaussianReal (0 : ℝ) σ.toNNReal)
        2 (by exact ENNReal.natCast_ne_top 2)
      have := hmem.integrable_norm_pow' (p := 2)
      refine this.congr ?_
      filter_upwards with x using by simp [Real.norm_eq_abs, sq_abs]
    have h_var : ∫ x, x ^ 2 ∂(gaussianReal (0 : ℝ) σ.toNNReal) = σ := by
      have hint_zero : ∫ ω, id ω ∂(gaussianReal (0 : ℝ) σ.toNNReal) = 0 := by
        show ∫ ω, ω ∂(gaussianReal (0 : ℝ) σ.toNNReal) = 0
        exact integral_id_gaussianReal
      have h := variance_of_integral_eq_zero (μ := gaussianReal (0 : ℝ) σ.toNNReal)
        (X := (id : ℝ → ℝ)) measurable_id'.aemeasurable hint_zero
      rw [variance_id_gaussianReal] at h
      simp only [id_eq] at h
      rw [← h, Real.coe_toNNReal _ hσ_nn]
    have h_lhs : ∫⁻ ω, edist (ω s) (ω t) ^ 2 ∂glwGaussianLimit = ENNReal.ofReal σ := by
      have h_pt : ∀ ω : NNReal → ℝ,
          edist (ω s) (ω t) ^ 2 = ENNReal.ofReal ((ω s - ω t) ^ 2) := fun ω => by
        rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      simp_rw [h_pt]
      rw [(hasLaw_eval_sub_eval_glwGaussianLimit s t).lintegral_comp
        (f := fun x : ℝ ↦ ENNReal.ofReal (x ^ 2)) (by fun_prop)]
      rw [← ofReal_integral_eq_lintegral_ofReal h_integrable
        (ae_of_all _ fun _ ↦ sq_nonneg _), h_var]
    calc ∫⁻ ω, edist (ω s) (ω t) ^ 2 ∂glwGaussianLimit
        = ENNReal.ofReal σ := h_lhs
      _ ≤ ENNReal.ofReal (((s : ℝ) - (t : ℝ)) ^ 2) := ENNReal.ofReal_le_ofReal hσ_le
      _ = (1 : ℝ≥0) * edist s t ^ 2 := by
          rw [ENNReal.coe_one, one_mul, edist_dist, NNReal.dist_eq,
            ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  p_pos := by norm_num
  q_pos := by norm_num

/-!
## O4-local — Local Kolmogorov–Chentsov on `[T, T+1]` (R20)

The **R20 sharpening** of `glwGaussianLimit_isKolmogorovProcess`: on
the unit block `Set.Ico (T : NNReal) (T + 1)` for `T : ℕ` with `T ≥ 1`,
the projection process satisfies the K-C condition with the **local
constant** `M_T = 1/(2T³)`, derived from `K_GLW_increment_var_le_T_cube`.

This sharper bound is what makes the chaining moment bound
`E[glwHolderConstantENN T] ≤ Cp · M_T` summable in `T` — a global
constant `M = 1` (as in `glwGaussianLimit_isKolmogorovProcess`) gives
non-summable per-block tails.
-/

/-- **R20 / T2.1 — local Kolmogorov–Chentsov on the unit block `[T, T+1]`.**
The projection process on the subtype `↥(Set.Ico T (T+1)) : Set NNReal`
satisfies the K-C condition with `(p, q, M_T) = (2, 2, 1/(2T³))`. -/
theorem glwGaussianLimit_isKolmogorovProcess_local (T : ℕ) (hT : 1 ≤ T) :
    IsKolmogorovProcess
      (T := ↥(Set.Ico ((T : NNReal)) ((T : NNReal) + 1)))
      (Ω := NNReal → ℝ) (E := ℝ)
      (fun u ω => ω u.1) glwGaussianLimit
      2 2 (Real.toNNReal (1 / (2 * (T : ℝ) ^ 3))) where
  measurablePair := by
    intro s t
    rw [← BorelSpace.measurable_eq]
    fun_prop
  kolmogorovCondition := by
    intro s t
    set σ := K_GLW (s.1 : ℝ) (s.1 : ℝ) + K_GLW (t.1 : ℝ) (t.1 : ℝ)
        - 2 * K_GLW (s.1 : ℝ) (t.1 : ℝ) with hσ_def
    have hT_real : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hT_pos : (0 : ℝ) < (T : ℝ) := by linarith
    have hT3_pos : (0 : ℝ) < 2 * (T : ℝ) ^ 3 := by positivity
    have hM_T_nn : (0 : ℝ) ≤ 1 / (2 * (T : ℝ) ^ 3) := by positivity
    -- The subtype lower bound `T ≤ s.1` (as NNReal, hence as ℝ).
    have hs_T : (T : ℝ) ≤ (s.1 : ℝ) := by
      have h : ((T : NNReal) : ℝ) ≤ ((s.1 : NNReal) : ℝ) := by
        exact_mod_cast s.2.1
      simpa using h
    have ht_T : (T : ℝ) ≤ (t.1 : ℝ) := by
      have h : ((T : NNReal) : ℝ) ≤ ((t.1 : NNReal) : ℝ) := by
        exact_mod_cast t.2.1
      simpa using h
    have hσ_nn : 0 ≤ σ := by
      have := K_GLW_diff_quadratic_nonneg
        (NNReal.coe_nonneg s.1) (NNReal.coe_nonneg t.1)
      simp only [hσ_def]; linarith
    have hσ_le : σ ≤ ((s.1 : ℝ) - (t.1 : ℝ)) ^ 2 / (2 * (T : ℝ) ^ 3) := by
      have := K_GLW_increment_var_le_T_cube hT_real hs_T ht_T
      simp only [hσ_def]; linarith
    -- Variance computation (mirror of the global proof).
    have h_integrable : Integrable (fun x : ℝ ↦ x ^ 2)
        (gaussianReal (0 : ℝ) σ.toNNReal) := by
      have hmem := IsGaussian.memLp_id (μ := gaussianReal (0 : ℝ) σ.toNNReal)
        2 (by exact ENNReal.natCast_ne_top 2)
      have := hmem.integrable_norm_pow' (p := 2)
      refine this.congr ?_
      filter_upwards with x using by simp [Real.norm_eq_abs, sq_abs]
    have h_var : ∫ x, x ^ 2 ∂(gaussianReal (0 : ℝ) σ.toNNReal) = σ := by
      have hint_zero : ∫ ω, id ω ∂(gaussianReal (0 : ℝ) σ.toNNReal) = 0 := by
        show ∫ ω, ω ∂(gaussianReal (0 : ℝ) σ.toNNReal) = 0
        exact integral_id_gaussianReal
      have h := variance_of_integral_eq_zero (μ := gaussianReal (0 : ℝ) σ.toNNReal)
        (X := (id : ℝ → ℝ)) measurable_id'.aemeasurable hint_zero
      rw [variance_id_gaussianReal] at h
      simp only [id_eq] at h
      rw [← h, Real.coe_toNNReal _ hσ_nn]
    -- Pointwise rpow → real square reduction (no simp_rw on `2 : ℝ`!).
    have h_pt : ∀ ω : NNReal → ℝ,
        edist (ω s.1) (ω t.1) ^ (2 : ℝ) = ENNReal.ofReal ((ω s.1 - ω t.1) ^ 2) := fun ω => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
        edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have h_lhs : ∫⁻ ω, edist (ω s.1) (ω t.1) ^ (2 : ℝ) ∂glwGaussianLimit
        = ENNReal.ofReal σ := by
      simp_rw [h_pt]
      rw [(hasLaw_eval_sub_eval_glwGaussianLimit s.1 t.1).lintegral_comp
        (f := fun x : ℝ ↦ ENNReal.ofReal (x ^ 2)) (by fun_prop)]
      rw [← ofReal_integral_eq_lintegral_ofReal h_integrable
        (ae_of_all _ fun _ ↦ sq_nonneg _), h_var]
    -- The edist on the subtype reduces to edist on NNReal.
    have h_edist_sq : edist s t ^ (2 : ℝ)
        = ENNReal.ofReal (((s.1 : ℝ) - (t.1 : ℝ)) ^ 2) := by
      rw [show (edist s t : ℝ≥0∞) = edist s.1 t.1 from rfl,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
        edist_dist, NNReal.dist_eq,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    -- Final calc.
    -- `(Real.toNNReal x : ℝ≥0∞) = ENNReal.ofReal x` is rfl
    -- (ENNReal.ofReal is defined as `↑(Real.toNNReal ·)`).
    calc ∫⁻ ω, edist (ω s.1) (ω t.1) ^ (2 : ℝ) ∂glwGaussianLimit
        = ENNReal.ofReal σ := h_lhs
      _ ≤ ENNReal.ofReal (((s.1 : ℝ) - (t.1 : ℝ)) ^ 2 / (2 * (T : ℝ) ^ 3)) :=
          ENNReal.ofReal_le_ofReal hσ_le
      _ = ENNReal.ofReal (1 / (2 * (T : ℝ) ^ 3))
            * ENNReal.ofReal (((s.1 : ℝ) - (t.1 : ℝ)) ^ 2) := by
          rw [← ENNReal.ofReal_mul hM_T_nn]
          congr 1
          field_simp
      _ = ((Real.toNNReal (1 / (2 * (T : ℝ) ^ 3))) : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
          rw [h_edist_sq]
          rfl
  p_pos := by norm_num
  q_pos := by norm_num

/-!
## O4½ — Continuous-path modification (R18)

The Kolmogorov-Chentsov continuous-modification theorem applied to
`glwGaussianLimit_isKolmogorovProcess` produces a process
`Y' : NNReal → (NNReal → ℝ) → ℝ` such that:

* each `Y' t` is measurable;
* `Y' t =ᵐ[glwGaussianLimit] (· t)` for every `t`;
* every sample path `t ↦ Y' t ω` is continuous on `NNReal`.

This is the missing ingredient for conjunct 8 of O5. The covering-
number datum is `isCoverWithBoundedCoveringNumber_Ico_nnreal` (the
canonical `Ico (0 : NNReal) (n+1)` exhaustion of `NNReal`); the
strict K-C process is `glwGaussianLimit_isKolmogorovProcess` at
`(p, q, M) = (2, 2, 1)`, which gives Hölder regularity
`β < (q - d)/p = 1/2` after we use `d = 1` from the Ico cover.
-/

/-- **R18 — continuous-path modification of the projection process.**

The output `Y'` is a measurable, continuous-path modification of
`fun t ω ↦ ω t` under `glwGaussianLimit`. -/
theorem exists_glwBrownianModification :
    ∃ Y : NNReal → (NNReal → ℝ) → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[glwGaussianLimit] (fun ω => ω t)) ∧
      (∀ ω, Continuous (fun t => Y t ω)) := by
  obtain ⟨Y, hY_meas, hY_ae_eq, hY_holder, _⟩ :=
    exists_modification_holder''' (T := NNReal) (Ω := NNReal → ℝ) (E := ℝ)
      (P := glwGaussianLimit) (X := fun t ω => ω t) (p := 2) (q := 2) (M := 1)
      isCoverWithBoundedCoveringNumber_Ico_nnreal
      glwGaussianLimit_isKolmogorovProcess
      (fun n => by finiteness)
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2)
  refine ⟨Y, hY_meas, hY_ae_eq, fun ω => ?_⟩
  -- Local Hölder => continuity at every point => continuity.
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨U, hU_mem, hU⟩ := hY_holder ω t
  -- Pick β = 1/4 ∈ (0, 1/2) = (0, (q - d)/p).
  obtain ⟨C, hC⟩ := hU ((1 : ℝ≥0) / 4) (by norm_num) (by norm_num)
  exact (hC.continuousOn (by norm_num : (0 : ℝ≥0) < 1 / 4)).continuousAt hU_mem

/-!
## R19 / T2.1 — Sub-Gaussian + measurable-Hölder prerequisites

R19 T1.1's API scoping (`Helpers/R19APIScoping.md`) corrected the
R18 diagnostic on Claim 2: the Hölder constant in
`KolmogorovChentsov.holderOnWith_holderModification` is *explicitly
defined* (lines 650-651) as a countable iSup of measurable functions,
hence measurable by construction.

This block exposes the two T2.1 prerequisites for the conjunct-9
proof:

* **T2.1.a:** marginal sub-Gaussianness of `(· t)` under
  `glwGaussianLimit` (via the gaussianReal adapter from
  `Helpers/SubGaussianGaussianReal.lean`).
* **T2.1.b:** the measurable Hölder constant `glwHolderConstant`,
  defined directly from the iSup formula
  `⨆ s, t : (denseCountable NNReal ∩ U), edist^p / edist^(β·p)`.
-/

/-- **R19 / T2.1.a (Path B step 1).** The coordinate evaluation
`(· t)` is sub-Gaussian under `glwGaussianLimit` with parameter
`K_GLW(t, t).toNNReal`. -/
lemma hasSubgaussianMGF_eval_glwGaussianLimit (t : NNReal) :
    HasSubgaussianMGF (fun ω : NNReal → ℝ ↦ ω t)
      (K_GLW (t : ℝ) (t : ℝ)).toNNReal glwGaussianLimit := by
  have hL := hasLaw_eval_glwGaussianLimit (t := t)
  have h_meas : AEMeasurable (fun ω : NNReal → ℝ ↦ ω t) glwGaussianLimit :=
    hL.aemeasurable
  have h_id : HasSubgaussianMGF id (K_GLW (t : ℝ) (t : ℝ)).toNNReal
      ((glwGaussianLimit).map (fun ω : NNReal → ℝ ↦ ω t)) := by
    rw [hL.map_eq]
    exact hasSubgaussianMGF_id_gaussianReal _
  exact (HasSubgaussianMGF.id_map_iff h_meas).mp h_id

/-- **R19 / T2.1.a (Path B step 2).** Two-sided Chernoff tail for the
marginal `(· t)` under `glwGaussianLimit`. -/
lemma eval_glwGaussianLimit_real_abs_ge_le (t : NNReal) {ε : ℝ} (hε : 0 ≤ ε) :
    glwGaussianLimit.real {ω : NNReal → ℝ | ε ≤ |ω t|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (K_GLW (t : ℝ) (t : ℝ)).toNNReal)) := by
  have hL := hasLaw_eval_glwGaussianLimit (t := t)
  have h_set : {ω : NNReal → ℝ | ε ≤ |ω t|} =
      (fun ω : NNReal → ℝ ↦ ω t) ⁻¹' {x : ℝ | ε ≤ |x|} := rfl
  rw [h_set]
  have h_map : (gaussianReal 0 (K_GLW (t : ℝ) (t : ℝ)).toNNReal).real
      {x : ℝ | ε ≤ |x|} ≤ 2 * Real.exp (-ε ^ 2 /
        (2 * (K_GLW (t : ℝ) (t : ℝ)).toNNReal)) :=
    gaussianReal_real_abs_ge_le _ hε
  have h_meas_set : MeasurableSet {x : ℝ | ε ≤ |x|} :=
    measurableSet_le measurable_const measurable_id.norm
  have h_map_real :
      (Measure.map (fun ω : NNReal → ℝ ↦ ω t) glwGaussianLimit).real
        {x : ℝ | ε ≤ |x|} =
      glwGaussianLimit.real
        ((fun ω : NNReal → ℝ ↦ ω t) ⁻¹' {x : ℝ | ε ≤ |x|}) := by
    rw [Measure.real, Measure.map_apply_of_aemeasurable hL.aemeasurable h_meas_set]
    rfl
  rw [hL.map_eq] at h_map_real
  rw [← h_map_real]
  exact h_map

/-- **R19 / T2.1.b (measurable Hölder constant).**

Per R19 / T1.1 Claim 2 correction, the Hölder constant in
`KolmogorovChentsov.holderOnWith_holderModification` is given
explicitly at lines 650-651 by

  `C ω := ⨆ (s, t : denseCountable T ∩ U), edist (X s ω) (X t ω) ^ p
                                              / edist s t ^ (β · p)`,

a countable iSup of measurable functions of `ω`. This is the
specialisation to the GLW projection process
`X t ω = ω t` with our K-C parameters `(p, q, M) = (2, 2, 1)` and a
fixed Hölder exponent `β = 1/4 < (q - d) / p = 1/2`, on the cover
element `U = Set.Ico n (n + 1) ⊆ NNReal`.

Output type is `ℝ≥0` to match the v2-manifest signature; the
underlying iSup lives in `ℝ≥0∞` to absorb potentially-infinite values
on the null set where the K-C modulus diverges. -/
noncomputable def glwHolderConstant (n : NNReal) (ω : NNReal → ℝ) : ℝ≥0 :=
  ((⨆ (s : ↥(denseCountable NNReal ∩ Set.Ico n (n + 1)))
      (t : ↥(denseCountable NNReal ∩ Set.Ico n (n + 1))),
        (edist (ω s.1) (ω t.1)) ^ (2 : ℝ) /
          (edist (s.1 : NNReal) (t.1 : NNReal)) ^ ((1 / 2 : ℝ))) ^
    (1 / 2 : ℝ)).toNNReal

/-- The countable-iSup-base of `glwHolderConstant`, exposed for the
measurability proof. -/
noncomputable def glwHolderConstantENN (n : NNReal) (ω : NNReal → ℝ) : ℝ≥0∞ :=
  ⨆ (s : ↥(denseCountable NNReal ∩ Set.Ico n (n + 1)))
    (t : ↥(denseCountable NNReal ∩ Set.Ico n (n + 1))),
      (edist (ω s.1) (ω t.1)) ^ (2 : ℝ) /
        (edist (s.1 : NNReal) (t.1 : NNReal)) ^ ((1 / 2 : ℝ))

lemma glwHolderConstant_eq (n : NNReal) (ω : NNReal → ℝ) :
    glwHolderConstant n ω =
      ((glwHolderConstantENN n ω) ^ (1 / 2 : ℝ)).toNNReal := rfl

/-- **R19 / T2.1.b: measurability of `glwHolderConstantENN`.**

The iSup is over the countable subtype `↥(denseCountable NNReal ∩
Set.Ico n (n + 1))`. Each summand is measurable in `ω` because
`ω ↦ ω s.1` and `ω ↦ ω t.1` are measurable (function-evaluation
projections), `edist` is measurable (continuous), `· ^ (2 : ℝ)` and
`· / c` (for `c` constant) are measurable. The countable iSup of
measurable functions is measurable. -/
lemma measurable_glwHolderConstantENN (n : NNReal) :
    Measurable (glwHolderConstantENN n) := by
  unfold glwHolderConstantENN
  -- The intersection set is countable, hence the subtype is.
  have h_count : (denseCountable NNReal ∩ Set.Ico n (n + 1)).Countable :=
    countable_denseCountable.mono Set.inter_subset_left
  haveI : Countable ↥(denseCountable NNReal ∩ Set.Ico n (n + 1)) :=
    h_count.to_subtype
  refine Measurable.iSup fun s => Measurable.iSup fun t => ?_
  -- The denominator `edist s.1 t.1 ^ (1/2)` is constant in ω.
  refine Measurable.div ?_ measurable_const
  -- Numerator: edist (ω s.1) (ω t.1) ^ (2 : ℝ).
  have h_edist : Measurable (fun ω : NNReal → ℝ => edist (ω s.1) (ω t.1)) :=
    (measurable_pi_apply s.1).edist (measurable_pi_apply t.1)
  exact ENNReal.continuous_rpow_const.measurable.comp h_edist

lemma measurable_glwHolderConstant (n : NNReal) :
    Measurable (fun ω : NNReal → ℝ => glwHolderConstant n ω) := by
  unfold glwHolderConstant
  exact ENNReal.measurable_toNNReal.comp
    (ENNReal.continuous_rpow_const.measurable.comp
      (measurable_glwHolderConstantENN n))

/-! ## R19 / T2.1.a sequel — variance bound at integer points -/

/-- **R19 / T2.1.a (Path B step 3).** For `T ≥ 1`, the variance bound
`K_GLW(T, T) ≤ 1/(2T)` (`K_GLW_var_le_recip`) collapses the marginal
tail to `≤ 2 · exp(-ε² T)`. The hypothesis `T ≥ 1` keeps both `K_GLW`
and `1/(2T)` strictly positive. -/
lemma eval_glwGaussianLimit_real_abs_ge_le_of_pos {T : ℝ} (hT : 1 ≤ T)
    {ε : ℝ} (hε : 0 ≤ ε) :
    glwGaussianLimit.real {ω : NNReal → ℝ | ε ≤ |ω T.toNNReal|} ≤
      2 * Real.exp (-ε ^ 2 * T) := by
  have hT_pos : 0 < T := by linarith
  have h_T_toNNReal : ((T.toNNReal : NNReal) : ℝ) = T := Real.coe_toNNReal _ hT_pos.le
  have h_var_le : K_GLW T T ≤ 1 / (2 * T) := K_GLW_var_le_recip hT_pos
  have h_var_pos : 0 < K_GLW T T := K_GLW_pos T T hT_pos.le hT_pos.le
  have h_marg :=
    eval_glwGaussianLimit_real_abs_ge_le (t := T.toNNReal) (ε := ε) hε
  rw [h_T_toNNReal] at h_marg
  have h_coe : ((K_GLW T T).toNNReal : ℝ) = K_GLW T T :=
    Real.coe_toNNReal _ h_var_pos.le
  rw [h_coe] at h_marg
  have h_two_kvar_pos : 0 < 2 * K_GLW T T := by linarith
  have h_kvar2T_le : K_GLW T T * (2 * T) ≤ 1 :=
    (le_div_iff₀ (by linarith : (0:ℝ) < 2 * T)).mp h_var_le
  have h_eps_sq_nn : 0 ≤ ε ^ 2 := sq_nonneg _
  have h_recip_le : ε ^ 2 * T ≤ ε ^ 2 / (2 * K_GLW T T) := by
    rw [le_div_iff₀ h_two_kvar_pos]
    nlinarith [h_kvar2T_le, h_eps_sq_nn, hT_pos.le, h_var_pos.le]
  have h_neg_le : -(ε ^ 2 / (2 * K_GLW T T)) ≤ -(ε ^ 2 * T) := neg_le_neg h_recip_le
  have h_div_eq : -ε ^ 2 / (2 * K_GLW T T) = -(ε ^ 2 / (2 * K_GLW T T)) := by
    rw [neg_div]
  rw [h_div_eq] at h_marg
  have h_exp_mono : Real.exp (-(ε ^ 2 / (2 * K_GLW T T))) ≤ Real.exp (-(ε ^ 2 * T)) :=
    Real.exp_le_exp.mpr h_neg_le
  have h_neg_exp_eq : Real.exp (-(ε ^ 2 * T)) = Real.exp (-ε ^ 2 * T) := by ring_nf
  calc glwGaussianLimit.real {ω : NNReal → ℝ | ε ≤ |ω T.toNNReal|}
      ≤ 2 * Real.exp (-(ε ^ 2 / (2 * K_GLW T T))) := h_marg
    _ ≤ 2 * Real.exp (-(ε ^ 2 * T)) := by gcongr
    _ = 2 * Real.exp (-ε ^ 2 * T) := by rw [h_neg_exp_eq]

/-! ## R19 / T2.1.a sequel — summability over integer points -/

/-- **R19 / T2.1.a (Path B step 4).** For `ε > 0`, the geometric series
`∑_{T : ℕ}, 2 · exp(-ε² T)` converges. -/
lemma summable_marginal_tail {ε : ℝ} (hε : 0 < ε) :
    Summable (fun T : ℕ => 2 * Real.exp (-ε ^ 2 * (T : ℝ))) := by
  have h_eps_sq_pos : 0 < ε ^ 2 := by positivity
  have h_exp_lt : Real.exp (-ε ^ 2) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h_exp_nn : 0 ≤ Real.exp (-ε ^ 2) := (Real.exp_pos _).le
  have h_eq : (fun T : ℕ => 2 * Real.exp (-ε ^ 2 * (T : ℝ))) =
              (fun T : ℕ => 2 * (Real.exp (-ε ^ 2)) ^ T) := by
    funext T
    rw [← Real.exp_nat_mul, mul_comm (-ε ^ 2) (T : ℝ)]
  rw [h_eq]
  exact (summable_geometric_of_lt_one h_exp_nn h_exp_lt).mul_left _

/-! ## R20 / T2.2 — chaining moment bound on `glwHolderConstantENN T` (Stub)

With `glwGaussianLimit_isKolmogorovProcess_local T hT` (R20 / T2.1
Full) supplying the local K-C with `(p, q, M_T) = (2, 2, 1/(2T³))`,
the chaining moment bound from the brownian-motion library

```
countable_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber U c d)
  (hX : IsAEKolmogorovProcess X P p q M)
  ...
  (T' : Set T) [hT' : Countable T'] (hT'U : T' ⊆ U) :
  ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
    ≤ M * constL T c d p q β U
```

(in `BrownianMotion/Continuity/KolmogorovChentsovInequality.lean:326`)
applied with `T = ↥(Set.Ico T_n (T_n + 1))`, the local IsKolmogorovProcess,
`U = univ`, `T' = the countable subtype matching `glwHolderConstantENN`,
gives

```
E[glwHolderConstantENN T_n] ≤ M_T_n · constL = O(1/T_n³)
```

— **the load-bearing summability bound**.

**R20 status (T2.2 Stub).** The chaining lemma `countable_kolmogorov_chentsov`
needs three companion facts to apply on the unit block:

* `HasBoundedInternalCoveringNumber Set.univ` for the subtype
  `↥(Set.Ico T (T+1))`. The cumulative cover
  `isCoverWithBoundedCoveringNumber_Ico_nnreal` (R19 used) gives
  bounded covering numbers for `[0, n+1)` blocks of NNReal but not
  directly for the standalone subtype block. Constructing the block-
  local version via `HasBoundedInternalCoveringNumber.subset` is
  ~30 LOC.
* The countable index `T' = denseCountable NNReal ∩ Set.Ico T (T+1)`
  matching the inner iSup of `glwHolderConstantENN`.
* The `constL` constant evaluation (the explicit chaining constant
  `Cp(d, p, q)` from the K-C inequality; `Cp(1, 2, 2)` instantiation).

These are well-defined Mathlib API hooks; the assembly is mechanical
but each step has potential for sub-lemma name mismatches and is
estimated at ~80-120 LOC total.
-/

/-- **R21 helper.** Lift `HasBoundedInternalCoveringNumber S c d` on
the ambient space to the subtype `↥S` with `Set.univ`. The map
`Subtype.val : ↥S → α` is an isometry (`isometry_subtype_coe`), so the
internal covering number transports verbatim. -/
lemma _root_.HasBoundedInternalCoveringNumber.subtype_univ
    {α : Type*} [PseudoEMetricSpace α] {S : Set α} {c : ℝ≥0∞} {d : ℝ}
    (h : HasBoundedInternalCoveringNumber S c d) :
    HasBoundedInternalCoveringNumber (Set.univ : Set ↥S) c d := by
  intro ε hε_le
  have h_iso : Isometry ((↑) : S → α) := isometry_subtype_coe
  have h_image : ((↑) : S → α) '' (Set.univ : Set ↥S) = S := by
    ext x; simp
  have h_diam : EMetric.diam (Set.univ : Set ↥S) = EMetric.diam S := by
    rw [← h_iso.ediam_image, h_image]
  have h_cn : internalCoveringNumber ε (Set.univ : Set ↥S) =
      internalCoveringNumber ε S := by
    conv_rhs => rw [← h_image]
    rw [h_iso.internalCoveringNumber_image' Subtype.val_injective.injOn]
  rw [h_cn]
  rw [h_diam] at hε_le
  exact h _ hε_le

/-- **R21 / T2.2 (Full).** Chaining moment bound:
`E[glwHolderConstantENN T] ≤ M_T · constL = O(1/T³)`. Apply
`countable_kolmogorov_chentsov` from the brownian-motion library to
`glwGaussianLimit_isKolmogorovProcess_local T hT` with the countable
subtype `denseCountable NNReal ∩ Set.Ico T (T+1)`. -/
lemma glwHolderConstantENN_lintegral_le_R20 (T : ℕ) (hT : 1 ≤ T) :
    ∃ Cp_T : ℝ≥0∞,
      Cp_T < ∞ ∧
      ∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit ≤ Cp_T := by
  -- Setup: short names for the local-K-C parameters.
  set S : Set NNReal := Set.Ico ((T : NNReal)) ((T : NNReal) + 1) with hS_def
  set M_T : ℝ≥0 := Real.toNNReal (1 / (2 * (T : ℝ) ^ 3)) with hM_T_def
  set c_T : ℝ≥0∞ := 6 * ((T : ℝ≥0∞) + 1) with hc_T_def
  -- HBICN of the unit block `Set.Ico T (T+1)` in NNReal at `(c, d) = (6*(T+1), 1)`.
  have h_hbicn_block : HasBoundedInternalCoveringNumber S c_T 1 := by
    have h_full :=
      isCoverWithBoundedCoveringNumber_Ico_nnreal.hasBoundedCoveringNumber T
    -- `h_full : HasBoundedInternalCoveringNumber (Set.Ico (0 : ℝ≥0) (T+1)) (3*(T+1)) 1`.
    have h_sub : S ⊆ Set.Ico (0 : NNReal) ((T : ℕ) + 1) := by
      intro x hx
      refine ⟨zero_le _, ?_⟩
      have : (x : NNReal) < (T : NNReal) + 1 := hx.2
      simpa using this
    have := h_full.subset h_sub (by norm_num : (0 : ℝ) ≤ 1)
    -- this : HasBoundedInternalCoveringNumber S (2 ^ (1 : ℝ) * (3 * (T + 1))) 1
    have h_simp : (2 : ℝ≥0∞) ^ (1 : ℝ) * (3 * ((T : ℝ≥0∞) + 1)) = c_T := by
      rw [ENNReal.rpow_one, hc_T_def]; ring
    rw [h_simp] at this
    exact this
  -- HBICN on the subtype universe.
  have h_hbicn_sub : HasBoundedInternalCoveringNumber
      (Set.univ : Set ↥S) c_T 1 := h_hbicn_block.subtype_univ
  -- The countable index set `T'` inside the subtype `↥S`.
  set T' : Set ↥S := {u : ↥S | u.1 ∈ denseCountable NNReal} with hT'_def
  have hT'_sub : T' ⊆ (Set.univ : Set ↥S) := fun _ _ => Set.mem_univ _
  -- Countability: `T' = Subtype.val ⁻¹' denseCountable NNReal`, with
  -- `Subtype.val` injective; so `T'` is countable.
  have h_count : (denseCountable NNReal).Countable := countable_denseCountable
  have hT'_count : T'.Countable :=
    h_count.preimage (f := (Subtype.val : ↥S → NNReal)) Subtype.val_injective
  haveI : Countable ↥T' := hT'_count.to_subtype
  -- IsAEKolmogorovProcess from the local IsKolmogorovProcess.
  have h_K := (glwGaussianLimit_isKolmogorovProcess_local T hT).IsAEKolmogorovProcess
  -- K-C parameters: `0 < d = 1`, `d < q = 2`, `0 < β = 1/4`.
  have hd_pos : (0 : ℝ) < 1 := by norm_num
  have hdq_lt : (1 : ℝ) < 2 := by norm_num
  have hβ_pos : (0 : ℝ≥0) < (1 / 4 : ℝ≥0) := by norm_num
  -- Apply countable_kolmogorov_chentsov.
  have h_kc := countable_kolmogorov_chentsov
    (T := ↥S) (Ω := NNReal → ℝ) (E := ℝ)
    (X := fun (u : ↥S) ω => ω u.1)
    (P := glwGaussianLimit) (p := 2) (q := 2) (M := M_T)
    (c := c_T) (d := 1) (β := (1 / 4 : ℝ≥0))
    (U := Set.univ) h_hbicn_sub h_K hd_pos hdq_lt hβ_pos T' hT'_sub
  -- Define the candidate Cp_T.
  refine ⟨(M_T : ℝ≥0∞) * constL ↥S c_T 1 2 2 (1 / 4 : ℝ≥0) Set.univ, ?_, ?_⟩
  · -- Finiteness via `constL_lt_top`.
    have h_diam_sub : EMetric.diam (Set.univ : Set ↥S) < ∞ :=
      h_hbicn_sub.diam_lt_top hd_pos
    have hc_T_ne : c_T ≠ ∞ := by
      simp [hc_T_def, ENNReal.mul_ne_top]
    have hβ_lt : ((1 / 4 : ℝ≥0) : ℝ) < (2 - 1) / 2 := by
      simp; norm_num
    have h_constL_lt :=
      constL_lt_top (T := ↥S) (c := c_T) (d := 1) (p := 2) (q := 2)
        (β := (1 / 4 : ℝ≥0)) (U := (Set.univ : Set ↥S))
        h_diam_sub hc_T_ne hd_pos (by norm_num : (0 : ℝ) < 2) hdq_lt hβ_lt
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h_constL_lt
  · -- Bridge the iSup form: `glwHolderConstantENN T ω` equals the
    -- K-C iSup over `T'` with `(β·p) = 1/2`.
    -- Use the equivalence `e : ↥(denseCountable NNReal ∩ S) ≃ ↥T'`.
    have h_eq_pt : ∀ ω : NNReal → ℝ,
        glwHolderConstantENN T ω =
          ⨆ (s : ↥T') (t : ↥T'),
            edist (ω s.1.1) (ω t.1.1) ^ (2 : ℝ) /
              edist (s.1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ) := by
      intro ω
      -- Build the equivalence between the two index types.
      let e : ↥(denseCountable NNReal ∩ S) ≃ ↥T' :=
        { toFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
          invFun := fun y => ⟨y.1.1, y.2, y.1.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      unfold glwHolderConstantENN
      -- Show the two iSup forms agree under `e`.
      rw [show ((1 / 2 : ℝ)) = ((1 / 4 : ℝ≥0) * 2 : ℝ) by push_cast; ring]
      -- Reindex the outer iSup via `e`.
      rw [← e.iSup_comp (g := fun s => ⨆ (t : ↥T'),
            edist (ω s.1.1) (ω t.1.1) ^ (2 : ℝ) /
              edist (s.1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ))]
      refine iSup_congr fun s => ?_
      rw [← e.iSup_comp (g := fun t =>
            edist (ω (e s).1.1) (ω t.1.1) ^ (2 : ℝ) /
              edist ((e s).1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ))]
      refine iSup_congr fun t => ?_
      -- Both numerators and denominators reduce by `Subtype.edist_eq` (rfl).
      -- `(e s).1.1 = s.1` and `(e t).1.1 = t.1` by definition of `e`.
      rfl
    -- Now apply h_kc on the rewritten integrand.
    have h_lintegral_eq :
        ∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit =
          ∫⁻ ω, ⨆ (s : ↥T') (t : ↥T'),
            edist (ω s.1.1) (ω t.1.1) ^ (2 : ℝ) /
              edist (s.1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ)
            ∂glwGaussianLimit := by
      apply lintegral_congr
      intro ω; exact h_eq_pt ω
    rw [h_lintegral_eq]
    exact h_kc

/-! ## R22 / T2.1 — explicit chaining-moment constant `Cp_T_explicit`

The R21 lemma `glwHolderConstantENN_lintegral_le_R20` returns the
chaining-moment bound through `∃ Cp_T < ∞, ...`, which suffices for
isolated Markov applications but obstructs term-wise summability
checks `∑_T Cp_T < ∞`. R22 hoists the same candidate constant
`(M_T : ℝ≥0∞) * constL ↥S c_T 1 2 2 (1/4) Set.univ` (`M_T = 1/(2T³)`,
`c_T = 6(T+1)`) to a top-level definition `Cp_T_explicit`, and
re-derives the moment bound and finiteness directly. The R21
existential lemma is preserved verbatim as a fallback / consumer of
the same K-C application internals; nothing downstream of R21 needs
to change. -/

/-- **R22 / T2.1.** Explicit chaining-moment constant for the unit
block `Set.Ico T (T+1)` at K-C parameters `(p, q, M_T, β, d) = (2, 2,
1/(2T³), 1/4, 1)` with covering number `c_T = 6(T+1)`. Pointwise
identical to the candidate produced inside the R21 lemma
`glwHolderConstantENN_lintegral_le_R20` (line 878). -/
noncomputable def Cp_T_explicit (T : ℕ) : ℝ≥0∞ :=
  (Real.toNNReal (1 / (2 * (T : ℝ) ^ 3)) : ℝ≥0∞) *
    constL ↥(Set.Ico ((T : NNReal)) ((T : NNReal) + 1))
      (6 * ((T : ℝ≥0∞) + 1)) 1 2 2 (1 / 4 : ℝ≥0) Set.univ

/-- **R22 / T2.1.** `Cp_T_explicit T` is finite for `T ≥ 1`. The
finiteness uses `constL_lt_top` plus the HBICN of the unit-block
subtype, exactly as in R21. -/
lemma Cp_T_explicit_lt_top (T : ℕ) (_hT : 1 ≤ T) : Cp_T_explicit T < ∞ := by
  unfold Cp_T_explicit
  set S : Set NNReal := Set.Ico ((T : NNReal)) ((T : NNReal) + 1) with hS_def
  set c_T : ℝ≥0∞ := 6 * ((T : ℝ≥0∞) + 1) with hc_T_def
  -- HBICN of `Set.Ico T (T+1)` in NNReal at `(c, d) = (6*(T+1), 1)`,
  -- via `.subset` from the cumulative `Ico 0 (T+1)` cover (R19).
  have h_hbicn_block : HasBoundedInternalCoveringNumber S c_T 1 := by
    have h_full :=
      isCoverWithBoundedCoveringNumber_Ico_nnreal.hasBoundedCoveringNumber T
    have h_sub : S ⊆ Set.Ico (0 : NNReal) ((T : ℕ) + 1) := by
      intro x hx
      refine ⟨zero_le _, ?_⟩
      have : (x : NNReal) < (T : NNReal) + 1 := hx.2
      simpa using this
    have := h_full.subset h_sub (by norm_num : (0 : ℝ) ≤ 1)
    have h_simp : (2 : ℝ≥0∞) ^ (1 : ℝ) * (3 * ((T : ℝ≥0∞) + 1)) = c_T := by
      rw [ENNReal.rpow_one, hc_T_def]; ring
    rw [h_simp] at this
    exact this
  have h_hbicn_sub : HasBoundedInternalCoveringNumber
      (Set.univ : Set ↥S) c_T 1 := h_hbicn_block.subtype_univ
  have h_diam_sub : EMetric.diam (Set.univ : Set ↥S) < ∞ :=
    h_hbicn_sub.diam_lt_top (by norm_num : (0 : ℝ) < 1)
  have hc_T_ne : c_T ≠ ∞ := by
    simp [hc_T_def, ENNReal.mul_ne_top]
  have hβ_lt : ((1 / 4 : ℝ≥0) : ℝ) < (2 - 1) / 2 := by simp; norm_num
  have h_constL_lt :=
    constL_lt_top (T := ↥S) (c := c_T) (d := 1) (p := 2) (q := 2)
      (β := (1 / 4 : ℝ≥0)) (U := (Set.univ : Set ↥S))
      h_diam_sub hc_T_ne (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (1 : ℝ) < 2) hβ_lt
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h_constL_lt

/-- **R22 / T2.1.** Explicit chaining moment bound:
`∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit ≤ Cp_T_explicit T`.
This is the constructive form of the R21 existential
`glwHolderConstantENN_lintegral_le_R20`, with the constant hoisted out
so summability `∑_T Cp_T_explicit T < ∞` can be checked term-wise. -/
lemma glwHolderConstantENN_lintegral_le_R22_explicit (T : ℕ) (hT : 1 ≤ T) :
    ∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit ≤ Cp_T_explicit T := by
  -- Mirror the R21 proof body, but unfold the explicit constant in the
  -- conclusion rather than packaging it under `∃`.
  unfold Cp_T_explicit
  set S : Set NNReal := Set.Ico ((T : NNReal)) ((T : NNReal) + 1) with hS_def
  set M_T : ℝ≥0 := Real.toNNReal (1 / (2 * (T : ℝ) ^ 3)) with hM_T_def
  set c_T : ℝ≥0∞ := 6 * ((T : ℝ≥0∞) + 1) with hc_T_def
  have h_hbicn_block : HasBoundedInternalCoveringNumber S c_T 1 := by
    have h_full :=
      isCoverWithBoundedCoveringNumber_Ico_nnreal.hasBoundedCoveringNumber T
    have h_sub : S ⊆ Set.Ico (0 : NNReal) ((T : ℕ) + 1) := by
      intro x hx
      refine ⟨zero_le _, ?_⟩
      have : (x : NNReal) < (T : NNReal) + 1 := hx.2
      simpa using this
    have := h_full.subset h_sub (by norm_num : (0 : ℝ) ≤ 1)
    have h_simp : (2 : ℝ≥0∞) ^ (1 : ℝ) * (3 * ((T : ℝ≥0∞) + 1)) = c_T := by
      rw [ENNReal.rpow_one, hc_T_def]; ring
    rw [h_simp] at this
    exact this
  have h_hbicn_sub : HasBoundedInternalCoveringNumber
      (Set.univ : Set ↥S) c_T 1 := h_hbicn_block.subtype_univ
  set T' : Set ↥S := {u : ↥S | u.1 ∈ denseCountable NNReal} with hT'_def
  have hT'_sub : T' ⊆ (Set.univ : Set ↥S) := fun _ _ => Set.mem_univ _
  have h_count : (denseCountable NNReal).Countable := countable_denseCountable
  have hT'_count : T'.Countable :=
    h_count.preimage (f := (Subtype.val : ↥S → NNReal)) Subtype.val_injective
  haveI : Countable ↥T' := hT'_count.to_subtype
  have h_K := (glwGaussianLimit_isKolmogorovProcess_local T hT).IsAEKolmogorovProcess
  have hd_pos : (0 : ℝ) < 1 := by norm_num
  have hdq_lt : (1 : ℝ) < 2 := by norm_num
  have hβ_pos : (0 : ℝ≥0) < (1 / 4 : ℝ≥0) := by norm_num
  have h_kc := countable_kolmogorov_chentsov
    (T := ↥S) (Ω := NNReal → ℝ) (E := ℝ)
    (X := fun (u : ↥S) ω => ω u.1)
    (P := glwGaussianLimit) (p := 2) (q := 2) (M := M_T)
    (c := c_T) (d := 1) (β := (1 / 4 : ℝ≥0))
    (U := Set.univ) h_hbicn_sub h_K hd_pos hdq_lt hβ_pos T' hT'_sub
  have h_eq_pt : ∀ ω : NNReal → ℝ,
      glwHolderConstantENN T ω =
        ⨆ (s : ↥T') (t : ↥T'),
          edist (ω s.1.1) (ω t.1.1) ^ (2 : ℝ) /
            edist (s.1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ) := by
    intro ω
    let e : ↥(denseCountable NNReal ∩ S) ≃ ↥T' :=
      { toFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
        invFun := fun y => ⟨y.1.1, y.2, y.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    unfold glwHolderConstantENN
    rw [show ((1 / 2 : ℝ)) = ((1 / 4 : ℝ≥0) * 2 : ℝ) by push_cast; ring]
    rw [← e.iSup_comp (g := fun s => ⨆ (t : ↥T'),
          edist (ω s.1.1) (ω t.1.1) ^ (2 : ℝ) /
            edist (s.1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ))]
    refine iSup_congr fun s => ?_
    rw [← e.iSup_comp (g := fun t =>
          edist (ω (e s).1.1) (ω t.1.1) ^ (2 : ℝ) /
            edist ((e s).1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ))]
    refine iSup_congr fun t => ?_
    rfl
  have h_lintegral_eq :
      ∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit =
        ∫⁻ ω, ⨆ (s : ↥T') (t : ↥T'),
          edist (ω s.1.1) (ω t.1.1) ^ (2 : ℝ) /
            edist (s.1 : ↥S) (t.1 : ↥S) ^ ((1 / 4 : ℝ≥0) * 2 : ℝ)
          ∂glwGaussianLimit := by
    apply lintegral_congr
    intro ω; exact h_eq_pt ω
  rw [h_lintegral_eq]
  -- h_kc : ∫⁻ ... ≤ M_T * constL ↥S c_T 1 2 2 (1/4) Set.univ
  -- Goal: ≤ (Real.toNNReal _ : ℝ≥0∞) * constL ↥S c_T 1 2 2 (1/4) Set.univ
  -- where the `Real.toNNReal _` is exactly `M_T` by `hM_T_def`. Defeq.
  exact h_kc

/-! ## R20 / T3.1 — marginal sup-tail bound on `[T, T+1]` (Stub)

Combining T2.2 (chaining moment bound) with the R19 marginal Chernoff
tail (`eval_glwGaussianLimit_real_abs_ge_le_of_pos`):

For each integer `T ≥ 1` and `ε > 0`,

```
P(sup_{u ∈ [T, T+1]} |Y u ω| ≥ ε) ≤
  2 · exp(-ε² T / 4) + 4 · Cp_T / ε²
```

where `Cp_T = O(1/T³)` from T2.2. Both terms are summable in `T`.

**Sup decomposition.** For `ω` in the a.s. set where the
`exists_glwBrownianModification`-witness `Y'` is sample-path continuous
and Hölder on each block (R18 conjunct 8 Full),

```
sup_{[T, T+1]} |Y u ω| ≤ |Y T ω| + glwHolderConstant T ω
```

(diameter of `[T, T+1]` is 1; Hölder exponent `β = 1/4` so
`|s-t|^β ≤ 1` on the unit block).

**R20 status (T3.1 Stub).** Gated on T2.2 Full + the explicit Hölder
relation from `holderOnWith_holderModification`. The connection
between `Y' = exists_glwBrownianModification`'s witness and the
explicit iSup-formula `glwHolderConstantENN T` requires re-establishing
the `holderOnWith` bound after the R18 routing through
`exists_modification_holder'''`. ~60-80 LOC.
-/

/-- **R21 / T3.1 (Markov form).** Markov bound on the Hölder-constant
event. For each integer `T ≥ 1` and `δ > 0`, the probability of the
event `{ω | δ ≤ glwHolderConstantENN T ω}` is bounded by `Cp_T / δ`,
where `Cp_T` is the moment bound from T2.2.

Reformulated from the R20 spec: instead of bounding the sup over
`Set.Ico T (T+1)` (uncountable, projection iSup not Borel-measurable),
we bound the measurable Hölder-constant event. The conjunct-9 proof
combines this with the marginal Chernoff bound at integer points and
the modification's Hölder regularity. -/
lemma marginal_sup_tail_le_R20 (T : ℕ) (hT : 1 ≤ T) {δ : ℝ≥0∞} (hδ_pos : δ ≠ 0)
    (hδ_top : δ ≠ ∞) :
    glwGaussianLimit {ω : NNReal → ℝ | δ ≤ glwHolderConstantENN T ω}
      ≤ (Classical.choose (glwHolderConstantENN_lintegral_le_R20 T hT)) / δ := by
  -- Markov inequality applied to the measurable function
  -- `glwHolderConstantENN T : (NNReal → ℝ) → ℝ≥0∞`.
  have hCp := Classical.choose_spec (glwHolderConstantENN_lintegral_le_R20 T hT)
  refine le_trans (meas_ge_le_lintegral_div
    (measurable_glwHolderConstantENN T).aemeasurable hδ_pos hδ_top) ?_
  exact ENNReal.div_le_div_right hCp.2 _

/-! ## R20 / T3.2 — Borel–Cantelli on the integer ladder (Stub)

Once T3.1 lands the summable sup-tail `f(T, ε)` with `∑_T f(T, ε) < ∞`,
`MeasureTheory.measure_limsup_atTop_eq_zero` (or
`MeasureTheory.ae_eventually_notMem` / `Filter.eventually_atTop`)
applied to the events `E_T(ε) := {ω | sup_{[T, T+1]} |Y u ω| ≥ ε}`
gives `P(limsup_T E_T(ε)) = 0`. Equivalently, a.s. for every `ε > 0`,
∃ `T₀ : ℕ`, ∀ `T ≥ T₀`, `sup_{[T, T+1]} |Y u| < ε`.

The quantifier interleaving over a countable rational `ε`-net then
delivers the conjunct-9 statement (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀,
|Y u ω| ≤ ε).

**R20 status (T3.2 Stub).** Gated on T3.1 Full. The Borel–Cantelli
step is a direct API call to Mathlib's `measure_limsup_atTop_eq_zero`
followed by the `Filter.eventually_atTop` unfolding; ~30-40 LOC.
-/

/-- **R21 / T3.2 (BC on integer marginals).** Borel–Cantelli on the
integer ladder applied to the marginal events `{ω | ε ≤ |ω T|}`.
For every `ε > 0`, almost-surely the marginal `|ω (T : NNReal)|` is
eventually less than `ε` as `T → ∞`. -/
lemma BC_integer_ladder_R20 {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂glwGaussianLimit,
      ∀ᶠ T : ℕ in Filter.atTop, ¬(ε ≤ |ω (T : NNReal)|) := by
  -- Goal: apply `ae_eventually_notMem` to the events
  --   `s T := {ω | ε ≤ |ω (T : NNReal)|}`.
  -- We need `∑' T, glwGaussianLimit (s T) ≠ ∞`.
  -- For T ≥ 1, R19's `eval_glwGaussianLimit_real_abs_ge_le_of_pos`
  -- gives `(s T : ℝ).measure ≤ 2 · exp(-ε² T)`, summable in T.
  set s : ℕ → Set (NNReal → ℝ) := fun T =>
    {ω : NNReal → ℝ | ε ≤ |ω (T : NNReal)|} with hs_def
  -- It suffices to show `∑' T, glwGaussianLimit (s T) ≠ ∞`.
  -- Strategy: bound each measure by `ENNReal.ofReal (2 * exp(-ε² * max 1 T))`,
  -- which is summable.
  suffices h_sum : (∑' T : ℕ, glwGaussianLimit (s T)) ≠ ∞ by
    have h_bc := ae_eventually_notMem (μ := glwGaussianLimit) h_sum
    filter_upwards [h_bc] with ω hω
    exact hω
  -- Bound each term using R19's marginal Chernoff (for T ≥ 1).
  -- For T = 0 (a single term), use `glwGaussianLimit (s 0) ≤ 1`
  -- (probability measure).
  have h_bound : ∀ T : ℕ, 1 ≤ T →
      glwGaussianLimit (s T) ≤ ENNReal.ofReal (2 * Real.exp (-ε ^ 2 * (T : ℝ))) := by
    intro T hT
    have hT_real : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have h_marg :=
      eval_glwGaussianLimit_real_abs_ge_le_of_pos hT_real hε.le
    -- h_marg : glwGaussianLimit.real {ω | ε ≤ |ω T.toNNReal|} ≤ 2 · exp(-ε²·T)
    -- We need: glwGaussianLimit {ω | ε ≤ |ω (T : NNReal)|} ≤ ENNReal.ofReal (...)
    -- First, identify (T : NNReal) with (T : ℝ).toNNReal.
    have hT_nn : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    have h_eq : ((T : ℝ).toNNReal : NNReal) = (T : NNReal) := by
      ext
      push_cast
      exact Real.coe_toNNReal _ hT_nn
    have h_set_eq : s T = {ω : NNReal → ℝ | ε ≤ |ω (T : ℝ).toNNReal|} := by
      simp only [hs_def]
      congr 1
      ext ω
      rw [h_eq]
    rw [h_set_eq]
    -- Now use h_marg via the relation between Measure.real and the original measure.
    have h_meas_set : MeasurableSet {ω : NNReal → ℝ | ε ≤ |ω (T : ℝ).toNNReal|} := by
      refine measurableSet_le measurable_const ?_
      exact (measurable_pi_apply _).abs
    have h_finite : glwGaussianLimit {ω : NNReal → ℝ | ε ≤ |ω (T : ℝ).toNNReal|} ≠ ∞ :=
      measure_ne_top _ _
    have h_real_eq : glwGaussianLimit.real {ω : NNReal → ℝ | ε ≤ |ω (T : ℝ).toNNReal|}
        = (glwGaussianLimit {ω : NNReal → ℝ | ε ≤ |ω (T : ℝ).toNNReal|}).toReal :=
      rfl
    rw [h_real_eq] at h_marg
    have h_nn : 0 ≤ 2 * Real.exp (-ε ^ 2 * (T : ℝ)) := by
      positivity
    -- Convert: a ≤ b.toReal where a is ENNReal: equivalent to a ≤ ENNReal.ofReal b when
    -- b ≥ 0 (and a ≠ ∞).
    rw [show (glwGaussianLimit {ω : NNReal → ℝ | ε ≤ |ω (T : ℝ).toNNReal|}) =
          ENNReal.ofReal (glwGaussianLimit {ω : NNReal → ℝ | ε ≤ |ω (T : ℝ).toNNReal|}).toReal
        from (ENNReal.ofReal_toReal h_finite).symm]
    exact ENNReal.ofReal_le_ofReal h_marg
  -- Summability: bound each term by an indicator-summable sequence.
  -- For T = 0: glwGaussianLimit (s 0) ≤ 1 (it's a probability measure).
  -- For T ≥ 1: glwGaussianLimit (s T) ≤ ENNReal.ofReal (2·exp(-ε²·T)).
  -- Define `b T := if T = 0 then 1 else ENNReal.ofReal (2·exp(-ε²·T))`.
  -- Then `glwGaussianLimit (s T) ≤ b T` and `∑ b T < ∞`.
  set b : ℕ → ℝ≥0∞ := fun T =>
    if T = 0 then 1 else ENNReal.ofReal (2 * Real.exp (-ε ^ 2 * (T : ℝ))) with hb_def
  have h_le_b : ∀ T : ℕ, glwGaussianLimit (s T) ≤ b T := by
    intro T
    simp only [hb_def]
    by_cases hT0 : T = 0
    · simp [hT0]; exact prob_le_one
    · simp [hT0]
      have h_bnd := h_bound T (Nat.one_le_iff_ne_zero.mpr hT0)
      -- h_bnd : ... ≤ ENNReal.ofReal (2 * Real.exp (-ε ^ 2 * ↑T))
      -- Goal:  ... ≤ 2 * ENNReal.ofReal (Real.exp (-(ε ^ 2 * ↑T)))
      -- Convert: ofReal (2 * x) = 2 * ofReal x for x ≥ 0; -ε^2 * T = -(ε^2 * T).
      have h_pos : 0 ≤ Real.exp (-ε ^ 2 * (T : ℝ)) := (Real.exp_pos _).le
      rw [show (-ε ^ 2 * (T : ℝ)) = -(ε ^ 2 * (T : ℝ)) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at h_bnd
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
      exact h_bnd
  refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum h_le_b) ?_)
  -- Use tsum_eq_zero_add' : ∑' n : ℕ, f n = f 0 + ∑' n, f (n+1).
  rw [tsum_eq_zero_add' (f := b) ENNReal.summable]
  refine ENNReal.add_lt_top.mpr ⟨by simp [hb_def], ?_⟩
  -- ∑' T, b (T+1) = ∑' T, ENNReal.ofReal (2·exp(-ε²·(T+1))) < ∞.
  have h_eq : ∀ T : ℕ, b (T + 1) = ENNReal.ofReal (2 * Real.exp (-ε ^ 2 * ((T + 1 : ℕ) : ℝ))) := by
    intro T
    simp [hb_def]
  simp_rw [h_eq]
  rw [show (∑' T : ℕ, ENNReal.ofReal (2 * Real.exp (-ε ^ 2 * ((T + 1 : ℕ) : ℝ)))) =
        ENNReal.ofReal (∑' T : ℕ, 2 * Real.exp (-ε ^ 2 * ((T + 1 : ℕ) : ℝ))) from ?_]
  · exact ENNReal.ofReal_lt_top
  · have h_sum : Summable (fun T : ℕ => 2 * Real.exp (-ε ^ 2 * ((T + 1 : ℕ) : ℝ))) := by
      have := (summable_marginal_tail hε).comp_injective Nat.succ_injective
      convert this using 1
    rw [ENNReal.ofReal_tsum_of_nonneg (fun T => by positivity) h_sum]

/-! ## R22 / T3.1 — dense grid-point existence

For Blocker A, the modification sup-tail bound needs an anchor grid
point `u_T ∈ denseCountable NNReal ∩ Set.Ico T (T+1)` so that the
marginal Chernoff at `u_T` and the K-C chaining bound on the unit
block can be combined via the triangle decomposition `|ω u| ≤
|ω u_T| + |ω u - ω u_T|`. -/

/-- **R22 / T3.1.** Existence of a grid point inside the half-open
unit block `Set.Ico (T : NNReal) (T+1)`. By density of
`denseCountable NNReal` in NNReal and openness of
`Set.Ioo (T : NNReal) (T+1) ⊆ Set.Ico (T : NNReal) (T+1)`. -/
lemma dense_grid_point_in_block (T : ℕ) :
    (denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)).Nonempty := by
  have h_lt : (T : NNReal) < (T : NNReal) + 1 := lt_add_one _
  have h_Ioo_open : IsOpen (Set.Ioo ((T : NNReal)) ((T : NNReal) + 1)) := isOpen_Ioo
  have h_Ioo_nonempty : (Set.Ioo ((T : NNReal)) ((T : NNReal) + 1)).Nonempty :=
    Set.nonempty_Ioo.mpr h_lt
  obtain ⟨x, hx_Ioo, hx_dense⟩ :=
    dense_iff_inter_open.mp dense_denseCountable _ h_Ioo_open h_Ioo_nonempty
  exact ⟨x, hx_dense, Set.Ioo_subset_Ico_self hx_Ioo⟩

/-! ## R22 / T3.2 — Blocker A: composed sup-tail bound on the unit block

The load-bearing R22 result. For each integer `T ≥ 1` and `ε > 0`,
combines:
* R19 marginal Chernoff at the grid anchor `u_T` (T3.1):
  `P(|ω u_T| ≥ ε/2) ≤ 2 · exp(-ε² T / 4)` (since `u_T ≥ T`).
* R22 / T2.1 explicit chaining bound (Markov on the K-C iSup):
  `P((ε/2)² ≤ glwHolderConstantENN T ω) ≤ Cp_T_explicit T / (ε/2)²`.

The decomposition `|ω u| ≤ |ω u_T| + |ω u - ω u_T|` plus the diameter
bound `(edist u u_T)^(1/2) ≤ 1` on the unit block reduces the bad
event to the union of these two pieces. -/

set_option maxHeartbeats 800000 in
/-- **R22 / T3.2 (Blocker A composed).** For each integer `T ≥ 1` and
`ε > 0`, a quantitative bound on the probability that the projection's
countable iSup over `denseCountable ∩ Set.Ico T (T+1)` exceeds `ε`.

Both terms on the RHS are summable in `T` (Chernoff: geometric;
Markov: bounded by a constant times `1/T²` since `Cp_T_explicit =
O(1/T²)`). This is the load-bearing input to the R22 conjunct-9 proof.
-/
lemma block_sup_tail_le_R22 (T : ℕ) (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    glwGaussianLimit
      {ω : NNReal → ℝ | ε ≤ ⨆ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
                              |ω u.1|}
      ≤ ENNReal.ofReal (2 * Real.exp (-ε^2 * T / 4))
        + 4 * Cp_T_explicit T / ENNReal.ofReal (ε^2) := by
  -- Setup: anchor point + names + basic positivity facts.
  set G : Set NNReal := denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)
    with hG_def
  obtain ⟨u_T, hu_T_mem⟩ := dense_grid_point_in_block T
  obtain ⟨hu_T_dense, hu_T_block⟩ := hu_T_mem
  have hT_real : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hu_T_ge_T : (T : NNReal) ≤ u_T := hu_T_block.1
  have hu_T_real_ge_T : (T : ℝ) ≤ (u_T : ℝ) := by exact_mod_cast hu_T_ge_T
  have hu_T_real_ge_one : (1 : ℝ) ≤ (u_T : ℝ) := le_trans hT_real hu_T_real_ge_T
  have hε_half_pos : (0 : ℝ) < ε / 2 := by linarith
  have hε_half_sq_pos : (0 : ℝ) < (ε / 2) ^ 2 := by positivity
  have hε_sq_pos : (0 : ℝ) < ε ^ 2 := by positivity
  -- The two events.
  set A : Set (NNReal → ℝ) := {ω | ε / 2 ≤ |ω u_T|} with hA_def
  set B : Set (NNReal → ℝ) :=
    {ω | ENNReal.ofReal ((ε / 2) ^ 2) ≤ glwHolderConstantENN T ω} with hB_def
  -- ## Lemma A: diameter bound on the unit block.
  have h_diam_le_one : ∀ s t : ↥G,
      edist (s.1 : NNReal) (t.1 : NNReal) ≤ 1 := by
    intro s t
    have hs := s.2.2
    have ht := t.2.2
    -- Real-valued |s.1 - t.1| ≤ 1; transport to edist via Real.
    have h_real_le : |((s.1 : NNReal) : ℝ) - ((t.1 : NNReal) : ℝ)| ≤ 1 := by
      have hsR_lo : (T : ℝ) ≤ ((s.1 : NNReal) : ℝ) := by exact_mod_cast hs.1
      have hsR_hi : ((s.1 : NNReal) : ℝ) < (T : ℝ) + 1 := by exact_mod_cast hs.2
      have htR_lo : (T : ℝ) ≤ ((t.1 : NNReal) : ℝ) := by exact_mod_cast ht.1
      have htR_hi : ((t.1 : NNReal) : ℝ) < (T : ℝ) + 1 := by exact_mod_cast ht.2
      rw [abs_le]
      refine ⟨by linarith, by linarith⟩
    have h_dist_eq : dist (s.1 : NNReal) (t.1 : NNReal)
        = |((s.1 : NNReal) : ℝ) - ((t.1 : NNReal) : ℝ)| := NNReal.dist_eq _ _
    have h_dist_le : dist (s.1 : NNReal) (t.1 : NNReal) ≤ 1 := h_dist_eq ▸ h_real_le
    rw [edist_dist]
    exact_mod_cast (ENNReal.ofReal_le_one.mpr h_dist_le)
  have h_diam_pow_le_one : ∀ s t : ↥G,
      edist (s.1 : NNReal) (t.1 : NNReal) ^ ((1 / 2 : ℝ)) ≤ 1 := by
    intro s t
    calc edist (s.1 : NNReal) (t.1 : NNReal) ^ ((1 / 2 : ℝ))
        ≤ (1 : ℝ≥0∞) ^ ((1 / 2 : ℝ)) :=
          ENNReal.rpow_le_rpow (h_diam_le_one s t) (by norm_num : (0 : ℝ) ≤ 1/2)
      _ = 1 := ENNReal.one_rpow _
  -- ## Lemma B: K-C iSup pointwise bound.
  have h_kc_pair : ∀ (ω : NNReal → ℝ) (s t : ↥G),
      edist (ω s.1) (ω t.1) ^ (2 : ℝ) /
        edist (s.1 : NNReal) (t.1 : NNReal) ^ ((1 / 2 : ℝ))
        ≤ glwHolderConstantENN T ω := by
    intro ω s t
    -- Convert subtype indices `↥G` ↔ `↥(denseCountable ∩ Ico T (T+1))`.
    let s' : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)) :=
      ⟨s.1, s.2⟩
    let t' : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)) :=
      ⟨t.1, t.2⟩
    show edist (ω s'.1) (ω t'.1) ^ (2 : ℝ) /
        edist (s'.1 : NNReal) (t'.1 : NNReal) ^ ((1 / 2 : ℝ))
        ≤ glwHolderConstantENN T ω
    unfold glwHolderConstantENN
    exact le_iSup_of_le s' (le_iSup_of_le t' le_rfl)
  -- ## Lemma C: edist on ℝ is ENNReal.ofReal of abs.
  have h_edist_real : ∀ (a b : ℝ), edist a b = ENNReal.ofReal |a - b| := by
    intro a b
    rw [edist_dist, Real.dist_eq]
  -- Nonempty G (for ciSup_le).
  haveI hG_nonempty : Nonempty ↥G := ⟨⟨u_T, hu_T_dense, hu_T_block⟩⟩
  -- ## Step 1: Set inclusion `bad ⊆ A ∪ B`.
  have h_inclusion :
      {ω : NNReal → ℝ | ε ≤ ⨆ u : ↥G, |ω u.1|} ⊆ A ∪ B := by
    intro ω h_bad
    by_contra h_neither
    rw [Set.mem_union] at h_neither
    push_neg at h_neither
    obtain ⟨h_notA, h_notB⟩ := h_neither
    rw [hA_def, Set.mem_setOf_eq, not_le] at h_notA
    rw [hB_def, Set.mem_setOf_eq, not_le] at h_notB
    -- Strategy: produce uniform bound `|ω u.1| ≤ |ω u_T| + c < ε` for u in G,
    -- where c := ((glwHolderConstantENN T ω)^(1/2)).toReal < ε/2.
    have h_holder_lt_top : glwHolderConstantENN T ω < ∞ :=
      lt_of_lt_of_le h_notB ENNReal.ofReal_lt_top.le
    set c_ENN : ℝ≥0∞ := (glwHolderConstantENN T ω) ^ ((1 / 2 : ℝ)) with hc_ENN_def
    have h_cENN_lt_top : c_ENN < ∞ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) h_holder_lt_top.ne
    set c : ℝ := c_ENN.toReal with hc_def
    have h_c_nn : 0 ≤ c := ENNReal.toReal_nonneg
    have h_cENN_ofReal_eq : c_ENN = ENNReal.ofReal c :=
      (ENNReal.ofReal_toReal h_cENN_lt_top.ne).symm
    -- c² ≤ glwHolderConstantENN T ω < (ε/2)² (in ENNReal), so c < ε/2.
    have h_c_lt : c < ε / 2 := by
      -- c_ENN ^ 2 = glwHolderConstantENN T ω.
      have h_cENN_sq : c_ENN ^ (2 : ℝ) = glwHolderConstantENN T ω := by
        rw [hc_ENN_def, ← ENNReal.rpow_mul]
        norm_num
      -- c_ENN ^ 2 = ENNReal.ofReal (c^2).
      have h_cENN_sq_eq : c_ENN ^ (2 : ℝ) = ENNReal.ofReal (c^2) := by
        rw [h_cENN_ofReal_eq, ENNReal.ofReal_rpow_of_nonneg h_c_nn (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.rpow_two]
      -- Combine: ENNReal.ofReal (c^2) < ENNReal.ofReal ((ε/2)^2).
      have h_lt_ofReal : ENNReal.ofReal (c^2) < ENNReal.ofReal ((ε/2)^2) := by
        rw [← h_cENN_sq_eq, h_cENN_sq]; exact h_notB
      have h_real_lt : c^2 < (ε/2)^2 :=
        (ENNReal.ofReal_lt_ofReal_iff hε_half_sq_pos).mp h_lt_ofReal
      exact lt_of_pow_lt_pow_left₀ 2 hε_half_pos.le h_real_lt
    -- Uniform bound: ∀ u ∈ ↥G, |ω u.1 - ω u_T| ≤ c.
    have h_diff_le : ∀ u : ↥G, |ω u.1 - ω u_T| ≤ c := by
      intro u
      let uT_sub : ↥G := ⟨u_T, hu_T_dense, hu_T_block⟩
      have h_pair := h_kc_pair ω u uT_sub
      -- (edist (ω u.1) (ω u_T))^2 ≤ glwHolderConstantENN T ω.
      have h_pair_clean :
          edist (ω u.1) (ω u_T) ^ (2 : ℝ) ≤ glwHolderConstantENN T ω := by
        by_cases h_eq : edist (u.1 : NNReal) (u_T : NNReal) ^ ((1 / 2 : ℝ)) = 0
        · -- s.1 = u_T case ⟹ edist (ω s.1) (ω u_T) = 0.
          have h_e_eq_zero : edist (u.1 : NNReal) (u_T : NNReal) = 0 := by
            by_contra h_ne
            have h_e_pos : (0 : ℝ≥0∞) < edist (u.1 : NNReal) (u_T : NNReal) :=
              pos_iff_ne_zero.mpr h_ne
            have h_pow_pos : (0 : ℝ≥0∞) <
                edist (u.1 : NNReal) (u_T : NNReal) ^ ((1 / 2 : ℝ)) :=
              ENNReal.rpow_pos h_e_pos (by finiteness)
            exact (ne_of_gt h_pow_pos) h_eq
          have h_uT_eq : (u.1 : NNReal) = u_T := edist_eq_zero.mp h_e_eq_zero
          rw [h_uT_eq, edist_self, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact zero_le _
        · -- Generic: convert div-form to mul-form, then use diameter.
          have h_pow_top : edist (u.1 : NNReal) (u_T : NNReal) ^ ((1 / 2 : ℝ)) ≠ ∞ := by
            apply ne_of_lt
            have h_e_top : edist (u.1 : NNReal) (u_T : NNReal) ≠ ∞ := by
              rw [edist_dist]; exact ENNReal.ofReal_ne_top
            exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h_e_top
          have h_mul := (ENNReal.div_le_iff h_eq h_pow_top).mp h_pair
          -- h_mul : edist (ω u.1) (ω u_T) ^ 2 ≤ glwHolderConstantENN T ω * edist u.1 u_T ^ (1/2)
          have h_uT_subtype_diam :
              edist ((u : ↥G) : NNReal).1 ((uT_sub : ↥G) : NNReal).1 ^ ((1 / 2 : ℝ)) ≤ 1 := by
            exact_mod_cast h_diam_pow_le_one u uT_sub
          calc edist (ω u.1) (ω u_T) ^ (2 : ℝ)
              ≤ glwHolderConstantENN T ω *
                  edist (u.1 : NNReal) (u_T : NNReal) ^ ((1 / 2 : ℝ)) := h_mul
            _ ≤ glwHolderConstantENN T ω * 1 := by
                gcongr
                exact h_uT_subtype_diam
            _ = glwHolderConstantENN T ω := mul_one _
      -- Take square root: edist (ω u.1) (ω u_T) ≤ c_ENN.
      have h_e_ω_le : edist (ω u.1) (ω u_T) ≤ c_ENN := by
        have h_take_sqrt :
            (edist (ω u.1) (ω u_T) ^ (2 : ℝ)) ^ ((1/2 : ℝ)) ≤ c_ENN := by
          rw [hc_ENN_def]
          exact ENNReal.rpow_le_rpow h_pair_clean (by norm_num : (0 : ℝ) ≤ 1/2)
        rwa [← ENNReal.rpow_mul, show (2 : ℝ) * (1/2) = 1 from by norm_num,
             ENNReal.rpow_one] at h_take_sqrt
      -- Convert: |ω u.1 - ω u_T| ≤ c.
      rw [h_edist_real, h_cENN_ofReal_eq] at h_e_ω_le
      exact (ENNReal.ofReal_le_ofReal_iff h_c_nn).mp h_e_ω_le
    -- Use h_diff_le + h_notA: ⨆_u |ω u.1| ≤ |ω u_T| + c < ε.
    have h_uniform_bound : ∀ u : ↥G, |ω u.1| ≤ |ω u_T| + c := by
      intro u
      have h_tri : |ω u.1| - |ω u_T| ≤ |ω u.1 - ω u_T| := abs_sub_abs_le_abs_sub _ _
      linarith [h_diff_le u]
    have h_sup_le : ⨆ u : ↥G, |ω u.1| ≤ |ω u_T| + c := ciSup_le h_uniform_bound
    linarith [le_trans h_bad h_sup_le]
  -- ## Step 2: Bound P(A) by Chernoff.
  have h_PA : glwGaussianLimit A ≤ ENNReal.ofReal (2 * Real.exp (-ε^2 * T / 4)) := by
    have h_chernoff :=
      eval_glwGaussianLimit_real_abs_ge_le_of_pos hu_T_real_ge_one hε_half_pos.le
    have h_uT_eq : ((u_T : ℝ).toNNReal : NNReal) = u_T := Real.toNNReal_coe
    have h_set_eq : {ω : NNReal → ℝ | ε / 2 ≤ |ω (u_T : ℝ).toNNReal|}
                   = {ω : NNReal → ℝ | ε / 2 ≤ |ω u_T|} := by
      ext ω; rw [h_uT_eq]
    rw [h_set_eq] at h_chernoff
    have h_pA_finite : glwGaussianLimit A ≠ ∞ := measure_ne_top _ _
    have h_pA_real_eq : glwGaussianLimit.real A = (glwGaussianLimit A).toReal := rfl
    have h_PA_step1 : glwGaussianLimit A ≤
        ENNReal.ofReal (2 * Real.exp (-(ε / 2) ^ 2 * (u_T : ℝ))) := by
      rw [show (glwGaussianLimit A) = ENNReal.ofReal ((glwGaussianLimit A).toReal)
          from (ENNReal.ofReal_toReal h_pA_finite).symm]
      apply ENNReal.ofReal_le_ofReal
      rw [← h_pA_real_eq]
      exact h_chernoff
    have h_exp_bound : Real.exp (-(ε / 2) ^ 2 * (u_T : ℝ)) ≤ Real.exp (-ε^2 * T / 4) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(ε / 2) ^ 2 * (u_T : ℝ) = -(ε^2 / 4) * (u_T : ℝ) := by ring
      rw [h1]
      have h_neg : -(ε^2 / 4) ≤ 0 := by nlinarith [sq_nonneg ε]
      have h_le : -(ε^2 / 4) * (u_T : ℝ) ≤ -(ε^2 / 4) * (T : ℝ) :=
        mul_le_mul_of_nonpos_left hu_T_real_ge_T h_neg
      linarith
    have h_step2 : ENNReal.ofReal (2 * Real.exp (-(ε / 2) ^ 2 * (u_T : ℝ)))
                  ≤ ENNReal.ofReal (2 * Real.exp (-ε^2 * T / 4)) := by
      apply ENNReal.ofReal_le_ofReal
      linarith [Real.exp_pos (-(ε / 2) ^ 2 * (u_T : ℝ)),
                Real.exp_pos (-ε^2 * T / 4)]
    exact le_trans h_PA_step1 h_step2
  -- ## Step 3: Bound P(B) by Markov on `glwHolderConstantENN`.
  have h_PB : glwGaussianLimit B ≤ 4 * Cp_T_explicit T / ENNReal.ofReal (ε^2) := by
    have h_δ_pos : ENNReal.ofReal ((ε / 2) ^ 2) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hε_half_sq_pos
    have h_δ_top : ENNReal.ofReal ((ε / 2) ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
    have h_markov : glwGaussianLimit
          {ω | ENNReal.ofReal ((ε / 2) ^ 2) ≤ glwHolderConstantENN T ω}
          ≤ (∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit) /
              ENNReal.ofReal ((ε / 2) ^ 2) :=
      meas_ge_le_lintegral_div (measurable_glwHolderConstantENN T).aemeasurable
        h_δ_pos h_δ_top
    have h_chaining := glwHolderConstantENN_lintegral_le_R22_explicit T hT
    have h_PB_step1 : glwGaussianLimit B ≤ Cp_T_explicit T / ENNReal.ofReal ((ε / 2) ^ 2) := by
      calc glwGaussianLimit B
          ≤ (∫⁻ ω, glwHolderConstantENN T ω ∂glwGaussianLimit) /
              ENNReal.ofReal ((ε / 2) ^ 2) := h_markov
        _ ≤ Cp_T_explicit T / ENNReal.ofReal ((ε / 2) ^ 2) :=
            ENNReal.div_le_div_right h_chaining _
    -- Algebra: ofReal ((ε/2)^2) = ofReal (ε^2) / 4, so RHS = 4 * Cp / ofReal(ε²).
    have h_eq_div : ENNReal.ofReal ((ε / 2) ^ 2) = ENNReal.ofReal (ε ^ 2) / 4 := by
      rw [show ((ε / 2) ^ 2) = ε ^ 2 / 4 from by ring]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num]
      simp [ENNReal.ofReal_natCast]
    rw [h_eq_div] at h_PB_step1
    -- Cp / (E / 4) = 4 * Cp / E. Algebraic chain via mul_div_assoc'.
    have h_alg : Cp_T_explicit T / (ENNReal.ofReal (ε^2) / 4)
                = 4 * Cp_T_explicit T / ENNReal.ofReal (ε^2) := by
      have h_inv : (ENNReal.ofReal (ε^2) / 4)⁻¹ = 4 / ENNReal.ofReal (ε^2) :=
        ENNReal.inv_div (Or.inl (by finiteness : (4 : ℝ≥0∞) ≠ ∞))
          (Or.inl (by norm_num : (4 : ℝ≥0∞) ≠ 0))
      calc Cp_T_explicit T / (ENNReal.ofReal (ε^2) / 4)
          = Cp_T_explicit T * (ENNReal.ofReal (ε^2) / 4)⁻¹ := div_eq_mul_inv _ _
        _ = Cp_T_explicit T * (4 / ENNReal.ofReal (ε^2)) := by rw [h_inv]
        _ = (Cp_T_explicit T * 4) / ENNReal.ofReal (ε^2) := mul_div_assoc' _ _ _
        _ = (4 * Cp_T_explicit T) / ENNReal.ofReal (ε^2) := by
            rw [mul_comm (Cp_T_explicit T) 4]
    rw [h_alg] at h_PB_step1
    exact h_PB_step1
  -- ## Step 4: combine via union bound.
  calc glwGaussianLimit {ω | ε ≤ ⨆ u : ↥G, |ω u.1|}
      ≤ glwGaussianLimit (A ∪ B) := measure_mono h_inclusion
    _ ≤ glwGaussianLimit A + glwGaussianLimit B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-ε^2 * T / 4)) + 4 * Cp_T_explicit T / ENNReal.ofReal (ε^2) :=
        add_le_add h_PA h_PB

/-! ## R22 / T4.1 — modification ↔ projection a.s.-bridge

For any modification `Y'` of the projection process satisfying
`Y' t =ᵐ (· t)` pointwise in `t`, the iSup of `|Y' u.1 ω|` over the
countable index `denseCountable ∩ Set.Ico T (T+1)` equals the iSup of
`|ω u.1|` over the same index, almost-surely. The R21 modification's
ae-equality is pointwise in `t`; the countable iSup combined with
`ae_all_iff` yields the equality on a common a.s.-set. -/

/-- **R22 / T4.1.** A.s.-equality of the dense-iSup form for the
modification and the projection. -/
lemma modification_sup_eq_projection_iSup_ae (T : ℕ)
    {Y' : NNReal → (NNReal → ℝ) → ℝ}
    (hY'_ae_eq : ∀ t, Y' t =ᵐ[glwGaussianLimit] (fun ω => ω t)) :
    ∀ᵐ ω ∂glwGaussianLimit,
      (⨆ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
          |Y' u.1 ω|)
        =
      (⨆ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
          |ω u.1|) := by
  have h_count : (denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)).Countable :=
    countable_denseCountable.mono Set.inter_subset_left
  haveI : Countable ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)) :=
    h_count.to_subtype
  have h_pt : ∀ᵐ ω ∂glwGaussianLimit,
      ∀ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
        Y' u.1 ω = ω u.1 := by
    rw [ae_all_iff]; exact fun u => hY'_ae_eq u.1
  filter_upwards [h_pt] with ω hω
  refine iSup_congr fun u => ?_
  rw [hω u]

/-! ## R22 / T4.2 — continuous block-pointwise ≤ countable-dense bound

For `f : NNReal → ℝ` continuous, if `|f v| ≤ ε` for every `v` in the
dense countable subset `denseCountable ∩ Set.Ico T (T+1)`, then
`|f u| ≤ ε` for every `u` in `Set.Ico T (T+1)`. The idea: the set
`{v | |f v| ≤ ε}` is closed; the dense countable subset is dense in
`Set.Ioo T (T+1)`, whose closure is `Set.Icc T (T+1) ⊇ Set.Ico T (T+1)`.
The closed set contains the dense subset, hence its closure, hence
the entire `Set.Ico T (T+1)`. -/

/-- **R22 / T4.2.** For continuous `f`, a uniform bound on `|f|` over
the dense-countable subset of the unit block lifts to a uniform bound
over the full block. -/
lemma continuous_block_pt_le (T : ℕ)
    {f : NNReal → ℝ} (hf : Continuous f) {ε : ℝ}
    (h_dense : ∀ v : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
                 |f v.1| ≤ ε)
    {u : NNReal} (hu : u ∈ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)) :
    |f u| ≤ ε := by
  -- The set `S := {v | |f v| ≤ ε}` is closed.
  have h_closed : IsClosed {v : NNReal | |f v| ≤ ε} :=
    isClosed_le hf.abs continuous_const
  -- The dense countable subset is contained in S (by hypothesis).
  have h_subset : (denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1))
                 ⊆ {v : NNReal | |f v| ≤ ε} := fun v hv => h_dense ⟨v, hv⟩
  -- u ∈ closure (denseCountable ∩ Ico T (T+1)).
  have h_T_lt : (T : NNReal) < (T : NNReal) + 1 := lt_add_one _
  have h_closure_Ioo : closure (Set.Ioo ((T : NNReal)) ((T : NNReal) + 1)) =
                       Set.Icc ((T : NNReal)) ((T : NNReal) + 1) :=
    closure_Ioo h_T_lt.ne
  -- denseCountable ∩ Ioo T (T+1) is dense in Ioo T (T+1):
  -- for x ∈ Ioo T (T+1) and any V ∈ 𝓝 x, V ∩ Ioo is open nbhd of x;
  -- by density of denseCountable, denseCountable hits V ∩ Ioo.
  have h_Ioo_subset_closure :
      Set.Ioo ((T : NNReal)) ((T : NNReal) + 1) ⊆
      closure (denseCountable NNReal ∩ Set.Ioo ((T : NNReal)) ((T : NNReal) + 1)) := by
    intro x hx
    rw [mem_closure_iff_nhds]
    intro V hV
    have h_Ioo_nhd : Set.Ioo ((T : NNReal)) ((T : NNReal) + 1) ∈ 𝓝 x :=
      isOpen_Ioo.mem_nhds hx
    have h_inter_nhd : V ∩ Set.Ioo ((T : NNReal)) ((T : NNReal) + 1) ∈ 𝓝 x :=
      Filter.inter_mem hV h_Ioo_nhd
    rcases mem_nhds_iff.mp h_inter_nhd with ⟨W, hW_subset, hW_open, hW_x⟩
    obtain ⟨y, hy_W, hy_dense⟩ :=
      dense_iff_inter_open.mp dense_denseCountable W hW_open ⟨x, hW_x⟩
    refine ⟨y, ?_, hy_dense, (hW_subset hy_W).2⟩
    exact (hW_subset hy_W).1
  -- closure (Ioo) = Icc ⊇ Ico, so u ∈ closure (denseCountable ∩ Ioo).
  have h_u_in_Icc : u ∈ Set.Icc ((T : NNReal)) ((T : NNReal) + 1) := ⟨hu.1, le_of_lt hu.2⟩
  have h_closure_Ioo_subset :
      Set.Icc ((T : NNReal)) ((T : NNReal) + 1) ⊆
      closure (denseCountable NNReal ∩ Set.Ioo ((T : NNReal)) ((T : NNReal) + 1)) := by
    rw [← h_closure_Ioo]
    exact (closure_mono h_Ioo_subset_closure).trans closure_closure.le
  have h_dense_subset :
      closure (denseCountable NNReal ∩ Set.Ioo ((T : NNReal)) ((T : NNReal) + 1)) ⊆
      closure (denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)) :=
    closure_mono (Set.inter_subset_inter_right _ Set.Ioo_subset_Ico_self)
  have h_u_closure : u ∈ closure (denseCountable NNReal ∩
                                  Set.Ico ((T : NNReal)) ((T : NNReal) + 1)) :=
    h_dense_subset (h_closure_Ioo_subset h_u_in_Icc)
  -- Closed set containing a subset contains its closure.
  exact (h_closed.closure_subset_iff.mpr h_subset) h_u_closure

/-! ## R22 / T4.3 — summability of the explicit chaining-moment constants

The sum-tail bound from `block_sup_tail_le_R22` has two parts: a
Chernoff-type geometric `2 · exp(-ε² T / 4)` (summable by
`summable_marginal_tail`) and a chaining/Markov term `4 · Cp_T_explicit T / ε²`,
whose summability requires `∑_T Cp_T_explicit T < ∞`.

Per `R22APIScoping.md` Commitment C (Grok-validated), `Cp_T_explicit T = O(1/T²)`
since `constL = Θ(T (log T)²)` (linear in `c_T = 6(T+1)` with a
bounded-by-dyadic-series log² factor) and `M_T = 1/(2T³)`. Hence the
tsum is bounded by a `1/T²`-style p-series. The Lean proof requires
unfolding `constL`'s tsum and bounding the log-factor times the
dyadic-series sum — ~150 LOC of `ENNReal.tsum_le` arithmetic that
deserves its own engineering pass. R22 isolates this as a single
named `sorry` and routes the conjunct-9 closure through it; R23
discharges it. -/

/-! ## R23 / T2.1 — discharge of `tsum_Cp_T_explicit_lt_top_R22`

Strategy (Grok-validated, α = 1/2 / p = 3/2 route): bound
`Cp_T_explicit T ≤ ENNReal.ofReal (boundReal T)` for a real-valued
summable function `boundReal`, then apply `ENNReal.tsum_le_tsum` and
`ENNReal.ofReal_tsum_of_nonneg`.

The asymptotic is `Cp_T_explicit T = Θ((log T)²/T²) = O(1/T^(3/2))`,
proved uniformly via `Real.log_le_rpow_div` at α = 1/4 (squaring gives
`(log x)² ≤ 16 √x`, hence `(log T)² / T² ≤ 16/T^(3/2)`).

The unfolding of `constL` is mechanical: separate the inner dyadic
tsum from the `T`-dependence using the Cauchy-Schwarz split
`(L + (k+2))² ≤ 2L² + 2(k+2)²`. -/

/-- **R23 / T2.1 (auxiliary).** Logarithmic asymptotic: for `x ≥ 1`,
`(Real.log x)^2 ≤ 16 * x^(1/2)` (uniform via `Real.log_le_rpow_div`
at α = 1/4). -/
private lemma log_sq_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 16 * x ^ (1 / 2 : ℝ) := by
  have hx_nn : 0 ≤ x := by linarith
  have h_log_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have h_log_le : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hx_nn (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have h_pow_eq : (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    rw [sq, ← Real.rpow_add hx_pos]
    norm_num
  calc (Real.log x) ^ 2
      ≤ (4 * x ^ (1 / 4 : ℝ)) ^ 2 := by
        have h_sq := sq_le_sq' (by linarith : -(4 * x ^ (1 / 4 : ℝ)) ≤ Real.log x) h_log_le
        linarith
    _ = 16 * (x ^ (1 / 4 : ℝ)) ^ 2 := by ring
    _ = 16 * x ^ (1 / 2 : ℝ) := by rw [h_pow_eq]

/-- **R23 / T2.1 (auxiliary, summable bound).** Summability of
`K / (T+1)^(3/2)` for any positive constant K. Used as the
asymptotic upper bound for `Cp_T_explicit T`. -/
private lemma summable_K_div_succ_rpow_three_halves (K : ℝ) :
    Summable (fun T : ℕ => K / ((T : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
  -- Reduce to `Real.summable_one_div_nat_rpow` at p = 3/2 > 1.
  have h_base : Summable (fun T : ℕ => 1 / ((T : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    have h_p : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)
    have h_shift := (summable_nat_add_iff (G := ℝ) 1).mpr h_p
    exact h_shift.congr (fun n => by push_cast; rfl)
  exact h_base.mul_left K |>.congr (fun n => by ring)

/-- **R23 / T2.1 (auxiliary).** A.s. nonnegativity of the bound, for
the `ENNReal.ofReal_tsum_of_nonneg` step. -/
private lemma K_div_succ_rpow_nonneg (K : ℝ) (hK : 0 ≤ K) :
    ∀ T : ℕ, 0 ≤ K / ((T : ℝ) + 1) ^ (3 / 2 : ℝ) := by
  intro T
  have h_pos : (0 : ℝ) < ((T : ℝ) + 1) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  positivity

/-! ## R23 / T2.1 (PARTIAL)

The asymptotic bound `Cp_T_explicit T = O((log T)²/T²) = O(1/T^(3/2))`
is supplied through `log_sq_le_sqrt` (uniform `(log x)² ≤ 16√x` for
`x ≥ 1`) and the chain of `constL` unfoldings + Cauchy-Schwarz on
`(L+(k+2))² ≤ 2L² + 2(k+2)²`. Per Grok validation the math is
flawless; the obstacle is the substantial ENNReal arithmetic plumbing
needed to expose `constL` and propagate the bound through the inner
dyadic tsum (`~150-300 LOC` per the R22 manifest's projection).

R23 lands the **summability of the bound itself** as Full
(`summable_K_div_succ_rpow_three_halves`) and the **uniform
logarithmic asymptotic** as Full (`log_sq_le_sqrt`); the *pointwise*
bound `Cp_T_explicit T ≤ ENNReal.ofReal (K / (T+1)^(3/2))` remains
the residual sorry, gated on the constL-unfolding plumbing. -/

/-- **R23 / T2.1 (Partial).** Summability of the chaining moment
constants `Cp_T_explicit T`. Per Commitment C (Grok-validated),
`Cp_T_explicit T = O((log T)²/T²) = O(1/T^(3/2))`. The summability of
the bound side is Full (via `Real.summable_one_div_nat_rpow` at
p = 3/2). The residual sorry is the **per-T pointwise bound**, which
needs the `constL` unfolding + Cauchy-Schwarz inner-dyadic split. -/
private theorem tsum_Cp_T_explicit_lt_top_R22 :
    (∑' T : ℕ, Cp_T_explicit T) < ∞ := by
  -- Plan: Cp_T_explicit T ≤ ENNReal.ofReal (K_total / (T+1)^(3/2)) for an absolute K_total.
  -- Then ∑' T, ofReal(K_total / (T+1)^(3/2)) = ofReal(K_total · ∑' 1/(T+1)^(3/2)) < ∞.
  -- The asymptotic (log T)² ≤ 16√T (`log_sq_le_sqrt`) reduces (log T)²/T² to 16/T^(3/2).
  -- Set K_total to a sufficiently large absolute constant.
  set K_total : ℝ := 2 ^ 30 with hK_total_def  -- generous absolute upper bound
  have hK_nn : (0 : ℝ) ≤ K_total := by positivity
  -- Pointwise bound. For T = 0: Cp_T_explicit 0 = 0 (since M_0 = 0); trivial.
  -- For T ≥ 1: requires the constL unfolding (residual sorry, R23-Partial).
  have h_bound : ∀ T : ℕ,
      Cp_T_explicit T ≤ ENNReal.ofReal (K_total / ((T : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    intro T
    by_cases hT0 : T = 0
    · -- Cp_T_explicit 0 = ofReal(0) * constL = 0.
      subst hT0
      have h_M0 : Real.toNNReal (1 / (2 * ((0 : ℕ) : ℝ) ^ 3)) = 0 := by
        simp
      simp only [Cp_T_explicit, h_M0, ENNReal.coe_zero, zero_mul]
      exact zero_le _
    · -- T ≥ 1: residual sorry on the asymptotic bound.
      sorry  -- TAG[R23-bound-pointwise]: needs constL unfolding + Cauchy-Schwarz inner-dyadic split.
  have h_summable := summable_K_div_succ_rpow_three_halves K_total
  have h_nonneg := K_div_succ_rpow_nonneg K_total hK_nn
  calc (∑' T : ℕ, Cp_T_explicit T)
      ≤ ∑' T : ℕ, ENNReal.ofReal (K_total / ((T : ℝ) + 1) ^ (3 / 2 : ℝ)) :=
        ENNReal.tsum_le_tsum h_bound
    _ = ENNReal.ofReal (∑' T : ℕ, K_total / ((T : ℝ) + 1) ^ (3 / 2 : ℝ)) :=
        (ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-! ## R22 / T4.3 — block-event summability and Borel-Cantelli

For each `ε > 0`, the per-T probability bound from
`block_sup_tail_le_R22` is summable, so Borel-Cantelli closes the
"a.s. eventually no block has dense-iSup ≥ ε" statement. -/

/-- **R22 / T4.3.** Borel-Cantelli closure of the block-sup events.
For each `ε > 0`, almost-surely the dense-countable iSup of `|ω u.1|`
over `denseCountable ∩ Set.Ico T (T+1)` is eventually `< ε` as
`T → ∞`. -/
private lemma BC_block_sup_R22 {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂glwGaussianLimit,
      ∀ᶠ T : ℕ in Filter.atTop,
        ¬(ε ≤ ⨆ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
                 |ω u.1|) := by
  set s : ℕ → Set (NNReal → ℝ) := fun T =>
    {ω | ε ≤ ⨆ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
           |ω u.1|} with hs_def
  suffices h_sum : (∑' T : ℕ, glwGaussianLimit (s T)) ≠ ∞ by
    have h_bc := ae_eventually_notMem (μ := glwGaussianLimit) h_sum
    filter_upwards [h_bc] with ω hω
    exact hω
  -- Strategy: split T = 0 + T ≥ 1, use block_sup_tail_le_R22 on T ≥ 1.
  have h_eps_sq_pos : (0 : ℝ) < ε^2 := by positivity
  have h_eps_ne_zero : ENNReal.ofReal (ε^2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact h_eps_sq_pos
  -- Bound for T ≥ 1.
  have h_le_block : ∀ T : ℕ, 1 ≤ T → glwGaussianLimit (s T) ≤
        ENNReal.ofReal (2 * Real.exp (-ε^2 * T / 4))
          + 4 * Cp_T_explicit T / ENNReal.ofReal (ε^2) := by
    intro T hT
    exact block_sup_tail_le_R22 T hT hε
  -- ∑' T, glwGaussianLimit (s T) = glwGaussianLimit (s 0) + ∑' T, glwGaussianLimit (s (T+1)).
  rw [tsum_eq_zero_add' (f := fun T => glwGaussianLimit (s T)) ENNReal.summable]
  apply (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩).ne
  · exact measure_lt_top _ _
  -- ∑' T, glwGaussianLimit (s (T+1)) ≤ ∑' T, [chernoff + markov] (T+1).
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun T =>
    h_le_block (T+1) (Nat.succ_le_succ (Nat.zero_le T))))
  rw [ENNReal.tsum_add]
  apply ENNReal.add_lt_top.mpr
  refine ⟨?_, ?_⟩
  · -- Chernoff: ∑' T, ENNReal.ofReal (2 * exp(-ε² (T+1)/4)) < ∞.
    have h_summable :
        Summable (fun T : ℕ => 2 * Real.exp (-ε^2 * ((T+1 : ℕ) : ℝ) / 4)) := by
      have h := summable_marginal_tail (ε := ε/2) (by linarith)
      have h_shift := h.comp_injective Nat.succ_injective
      refine h_shift.congr ?_
      intro T
      simp only [Function.comp_apply]
      congr 1
      push_cast
      ring
    rw [show (∑' T : ℕ, ENNReal.ofReal (2 * Real.exp (-ε^2 * ((T+1 : ℕ) : ℝ) / 4)))
          = ENNReal.ofReal (∑' T : ℕ, 2 * Real.exp (-ε^2 * ((T+1 : ℕ) : ℝ) / 4)) from
        (ENNReal.ofReal_tsum_of_nonneg (fun T => by positivity) h_summable).symm]
    exact ENNReal.ofReal_lt_top
  · -- Markov: ∑' T, 4 * Cp_T_explicit (T+1) / ENNReal.ofReal (ε²) < ∞.
    have h_factored : (fun T : ℕ => 4 * Cp_T_explicit (T+1) / ENNReal.ofReal (ε^2))
                    = (fun T : ℕ => (4 / ENNReal.ofReal (ε^2)) * Cp_T_explicit (T+1)) := by
      funext T; exact ENNReal.mul_div_right_comm
    rw [h_factored]
    rw [ENNReal.tsum_mul_left]
    apply ENNReal.mul_lt_top
    · exact ENNReal.div_lt_top (by finiteness) h_eps_ne_zero
    · -- ∑' T, Cp_T_explicit (T+1) ≤ ∑' T, Cp_T_explicit T < ∞.
      have h_split : ∑' T : ℕ, Cp_T_explicit T
                    = Cp_T_explicit 0 + ∑' T : ℕ, Cp_T_explicit (T+1) :=
        tsum_eq_zero_add' (f := Cp_T_explicit) ENNReal.summable
      have h_le : ∑' T : ℕ, Cp_T_explicit (T+1) ≤ ∑' T : ℕ, Cp_T_explicit T := by
        rw [h_split]; exact le_add_self
      exact lt_of_le_of_lt h_le tsum_Cp_T_explicit_lt_top_R22

/-!
## O5 — Process-existence witness in the 9-conjunct form

The continuous modification of the projection process from O4
satisfies the same 9-conjunct existence statement that
`Helpers/GLWProcess.lean`'s `Y_GLW_exists` axiom asserts:
measurability, integrability, integrable-prod, centeredness, K_GLW
covariance, joint Gaussianity, continuous paths, tail decay.

The signature below is **stated in the 9-conjunct form (not via
`IsGLWProcess`)** to break the dependency cycle that would otherwise
arise: `GLWProcessPredicate` imports `GLWProcess`, so importing
`GLWProcessPredicate` here would forbid `GLWProcess.lean` from
importing this file (which is what the O6 axiom-retirement requires).
The 9-conjunct shape is the canonical Y_GLW existence statement;
projecting back to `IsGLWProcess` is a downstream `intro/exact`-style
1-line move that consumers do at use-site.
-/

/-- **O2 (Partial — R16).** Existence of a probability space carrying a
process satisfying the **9-conjunct shape** that matches
`Y_GLW_exists` (`Helpers/GLWProcess.lean:130`).

R16 progress vs R15:

* Conjuncts 1, 2 (`IsProbabilityMeasure`, `Measurable (Y u)`) — Full.
* Conjuncts 3-7 — structured sorries, each pointing at the precise
  brownian-motion-shaped helper needed (`hasLaw_eval_glwGaussianLimit`
  / `covariance_eval_glwGaussianLimit`-style ports of the existing
  `gaussianLimit` API).
* Conjunct 8 (continuous paths) — depends on O1 Full: once
  `glwGaussianLimit_isKolmogorovProcess` is sorry-free, the continuous
  modification follows from `IsAEKolmogorovProcess.mk`.
* Conjunct 9 (tail decay) — independent dependency on Borell + BC. -/
theorem glwGaussianLimit_Y_GLW_existence :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (Y : ℝ → Ω → ℝ),
      IsProbabilityMeasure μ ∧
      (∀ u, Measurable (Y u)) ∧
      (∀ u, Integrable (Y u) μ) ∧
      (∀ u v : ℝ, Integrable (fun ω => Y u ω * Y v ω) μ) ∧
      (∀ u, ∫ ω, Y u ω ∂μ = 0) ∧
      (∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
        ∫ ω, Y u ω * Y v ω ∂μ = K_GLW u v) ∧
      (∀ (n : ℕ) (us : Fin n → ℝ) (cs : Fin n → ℝ),
        IsGaussian (Measure.map (fun ω => ∑ i, cs i * Y (us i) ω) μ)) ∧
      (∀ᵐ ω ∂μ, Continuous (fun u => Y u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω ∂μ, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε) := by
  -- **R18** witness: probability space `(NNReal → ℝ, glwGaussianLimit)`,
  -- process `Y u ω := Y' u.toNNReal ω` where `Y'` is the continuous-
  -- path modification produced by `exists_glwBrownianModification`.
  -- All conjuncts 3-7 are re-derived from the original projection-
  -- based proofs by ae-transfer along `Y' t =ᵐ (· t)`.
  obtain ⟨Y', hY'_meas, hY'_ae_eq, hY'_cont⟩ := exists_glwBrownianModification
  refine ⟨NNReal → ℝ, inferInstance, glwGaussianLimit,
    fun u ω => Y' u.toNNReal ω, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Conjunct 2 (measurable): inherited from `hY'_meas`.
    intro u; exact hY'_meas u.toNNReal
  · -- Conjunct 3 (Integrable (Y u) glwGaussianLimit). The marginal at
    -- `u.toNNReal` is centred Gaussian with variance `K_GLW(u, u)`
    -- (cf. `hasLaw_eval_glwGaussianLimit`); integrability of the
    -- identity then transfers along the law. **R18:** ae-transfer to
    -- the modification.
    intro u
    have hL := hasLaw_eval_glwGaussianLimit (t := u.toNNReal)
    have h_int_id : Integrable (id : ℝ → ℝ)
        (Measure.map (fun ω : NNReal → ℝ ↦ ω u.toNNReal) glwGaussianLimit) := by
      rw [hL.map_eq]; exact IsGaussian.integrable_id
    have h_orig : Integrable (fun ω : NNReal → ℝ => ω u.toNNReal) glwGaussianLimit :=
      h_int_id.comp_aemeasurable hL.aemeasurable
    exact h_orig.congr (hY'_ae_eq u.toNNReal).symm
  · -- Conjunct 4 (bivariate integrability of `Y u * Y v`). Both
    -- marginals are `MemLp 2`, so `Y u * Y v` is integrable
    -- (Cauchy-Schwarz: `MemLp.integrable_mul`). **R18:** ae-transfer.
    intro u v
    have hLu := hasLaw_eval_glwGaussianLimit (t := u.toNNReal)
    have hLv := hasLaw_eval_glwGaussianLimit (t := v.toNNReal)
    have hMu : MemLp (fun ω : NNReal → ℝ ↦ ω u.toNNReal) 2 glwGaussianLimit := by
      have h_id : MemLp (id : ℝ → ℝ) 2
          (Measure.map (fun ω : NNReal → ℝ ↦ ω u.toNNReal) glwGaussianLimit) := by
        rw [hLu.map_eq]; exact IsGaussian.memLp_two_id
      exact h_id.comp_of_map hLu.aemeasurable
    have hMv : MemLp (fun ω : NNReal → ℝ ↦ ω v.toNNReal) 2 glwGaussianLimit := by
      have h_id : MemLp (id : ℝ → ℝ) 2
          (Measure.map (fun ω : NNReal → ℝ ↦ ω v.toNNReal) glwGaussianLimit) := by
        rw [hLv.map_eq]; exact IsGaussian.memLp_two_id
      exact h_id.comp_of_map hLv.aemeasurable
    have h_orig : Integrable (fun ω : NNReal → ℝ => ω u.toNNReal * ω v.toNNReal)
        glwGaussianLimit := hMu.integrable_mul hMv
    refine h_orig.congr ?_
    filter_upwards [(hY'_ae_eq u.toNNReal).symm, (hY'_ae_eq v.toNNReal).symm] with ω hu hv
    rw [hu, hv]
  · -- Conjunct 5 (centered): the marginal at `u.toNNReal` has centred
    -- Gaussian law, so its integral is `0` (via `integral_id_gaussianReal`).
    -- **R18:** transfer via `integral_congr_ae`.
    intro u
    have h_orig : ∫ ω : NNReal → ℝ, ω u.toNNReal ∂glwGaussianLimit = 0 :=
      (hasLaw_eval_glwGaussianLimit (t := u.toNNReal)).integral_eq.trans
        integral_id_gaussianReal
    rw [integral_congr_ae (hY'_ae_eq u.toNNReal)]
    exact h_orig
  · -- Conjunct 6 (covariance fit). Combine `covariance_eval_glwGaussianLimit`
    -- (giving `cov[ω u.toNNReal, ω v.toNNReal] = K_GLW (↑u.toNNReal) (↑v.toNNReal)`)
    -- with `covariance_eq_sub` and centeredness to obtain `∫ XY = K_GLW u v`.
    -- **R18:** transfer via `integral_congr_ae` on the product.
    intro u v hu hv
    have hu_eq : (u.toNNReal : ℝ) = u := Real.coe_toNNReal _ hu
    have hv_eq : (v.toNNReal : ℝ) = v := Real.coe_toNNReal _ hv
    -- MemLp 2 for both coordinates, transferred from `gaussianReal`'s
    -- second-moment finiteness via the marginal law.
    have hLu := hasLaw_eval_glwGaussianLimit (t := u.toNNReal)
    have hLv := hasLaw_eval_glwGaussianLimit (t := v.toNNReal)
    have hMu : MemLp (fun ω : NNReal → ℝ ↦ ω u.toNNReal) 2 glwGaussianLimit := by
      have h_id : MemLp (id : ℝ → ℝ) 2
          (Measure.map (fun ω : NNReal → ℝ ↦ ω u.toNNReal) glwGaussianLimit) := by
        rw [hLu.map_eq]; exact IsGaussian.memLp_two_id
      exact h_id.comp_of_map hLu.aemeasurable
    have hMv : MemLp (fun ω : NNReal → ℝ ↦ ω v.toNNReal) 2 glwGaussianLimit := by
      have h_id : MemLp (id : ℝ → ℝ) 2
          (Measure.map (fun ω : NNReal → ℝ ↦ ω v.toNNReal) glwGaussianLimit) := by
        rw [hLv.map_eq]; exact IsGaussian.memLp_two_id
      exact h_id.comp_of_map hLv.aemeasurable
    -- Centered moments
    have hEu : ∫ ω, ω u.toNNReal ∂glwGaussianLimit = 0 :=
      hLu.integral_eq.trans integral_id_gaussianReal
    have hEv : ∫ ω, ω v.toNNReal ∂glwGaussianLimit = 0 :=
      hLv.integral_eq.trans integral_id_gaussianReal
    -- Covariance evaluation, with `↑u.toNNReal = u` etc.
    have hcov := covariance_eval_glwGaussianLimit (s := u.toNNReal) (t := v.toNNReal)
    rw [hu_eq, hv_eq] at hcov
    -- Combine via `covariance_eq_sub`:
    have h_eq := covariance_eq_sub hMu hMv
    -- h_eq : cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y]
    rw [hcov, hEu, hEv] at h_eq
    -- h_eq : K_GLW u v = μ[X * Y] - 0 * 0 = μ[X * Y]
    simp only [zero_mul, sub_zero] at h_eq
    -- h_eq : K_GLW u v = ∫ ω, X ω * Y ω ∂μ
    have h_orig : ∫ ω : NNReal → ℝ, ω u.toNNReal * ω v.toNNReal ∂glwGaussianLimit
        = K_GLW u v := h_eq.symm
    -- R18: transfer to the Y'-witness via integral_congr_ae.
    have h_ae : (fun ω : NNReal → ℝ => Y' u.toNNReal ω * Y' v.toNNReal ω) =ᵐ[glwGaussianLimit]
                (fun ω => ω u.toNNReal * ω v.toNNReal) := by
      filter_upwards [hY'_ae_eq u.toNNReal, hY'_ae_eq v.toNNReal] with ω hu' hv'
      rw [hu', hv']
    rw [integral_congr_ae h_ae]
    exact h_orig
  · -- Conjunct 7 (joint Gaussianity). The linear functional
    -- `f ω = ∑ i, cs i * ω (us i).toNNReal` factors as `φ ∘ I.restrict`
    -- where `I` is the finset of distinct `(us i).toNNReal` values and
    -- `φ : (↥I → ℝ) →L[ℝ] ℝ` is a CLM. Then
    -- `Measure.map f μ = Measure.map φ (glwGaussianProjectiveFamily I)`,
    -- and the latter is Gaussian by `isGaussian_map`.
    -- **R18:** the same factoring works after replacing the integrand
    -- by the ae-equivalent `Y'`-version, via `Measure.map_congr`.
    intro n us cs
    -- R18: ae-equivalence of the two integrands.
    have h_ae : (fun ω : NNReal → ℝ => ∑ i, cs i * Y' (us i).toNNReal ω) =ᵐ[glwGaussianLimit]
                (fun ω => ∑ i, cs i * ω (us i).toNNReal) := by
      have h_pt : ∀ᵐ ω ∂glwGaussianLimit,
          ∀ i : Fin n, Y' (us i).toNNReal ω = ω (us i).toNNReal := by
        rw [ae_all_iff]
        intro i; exact hY'_ae_eq (us i).toNNReal
      filter_upwards [h_pt] with ω hω
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hω i]
    rw [Measure.map_congr h_ae]
    -- Original projection-functional argument.
    let I : Finset NNReal := Finset.image (fun i : Fin n => (us i).toNNReal) Finset.univ
    have h_mem : ∀ i : Fin n, (us i).toNNReal ∈ I :=
      fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    let φ : (↥I → ℝ) →L[ℝ] ℝ :=
      ∑ i : Fin n, cs i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥I => ℝ)
        ⟨(us i).toNNReal, h_mem i⟩
    have h_factor : (fun ω : NNReal → ℝ => ∑ i, cs i * ω (us i).toNNReal) =
        φ ∘ (Finset.restrict I (π := fun _ : NNReal => ℝ)) := by
      funext ω
      show ∑ i, cs i * ω (us i).toNNReal = φ (I.restrict ω)
      simp only [φ, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
        ContinuousLinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [h_factor]
    have hmf : Measurable (Finset.restrict I (π := fun _ : NNReal => ℝ)) :=
      Finset.measurable_restrict _
    have hmφ : Measurable (⇑φ) := φ.continuous.measurable
    rw [show Measure.map (⇑φ ∘ I.restrict) glwGaussianLimit
          = Measure.map φ (Measure.map I.restrict glwGaussianLimit) from
        (Measure.map_map hmφ hmf).symm]
    rw [hasLaw_restrict_glwGaussianLimit.map_eq]
    exact isGaussian_map _
  · -- Conjunct 8 (continuous paths). **R18: Full.**
    -- The witness is `fun u ω => Y' u.toNNReal ω` where every sample
    -- path `t : NNReal ↦ Y' t ω` is continuous (from
    -- `exists_glwBrownianModification`). Composition with
    -- `Real.toNNReal : ℝ → NNReal` (continuous) gives continuity in `u`.
    -- Continuity holds for **every** ω (not just a.s.), so we lift via
    -- `ae_of_all`.
    refine ae_of_all _ fun ω => ?_
    exact (hY'_cont ω).comp continuous_real_toNNReal
  · -- Conjunct 9 (tail decay). For every `ε > 0`, `Y u ω → 0` as
    -- `u → ∞`, almost-surely under `glwGaussianLimit`.
    --
    -- **R18 status: structured sorry. The sole remaining sorry in
    -- `glwGaussianLimit_Y_GLW_existence` after R18.**
    --
    -- R18 closed conjunct 8 by routing through the continuous-path
    -- modification `Y'` from `exists_glwBrownianModification`. Conjunct
    -- 9 is the only conjunct still gated on Mathlib infrastructure that
    -- has not yet landed.
    --
    -- Proof outline (Borell-TIS + Borel-Cantelli):
    --
    -- 1. **Pointwise variance decay.** From `K_GLW_var_le_recip` in
    --    `Helpers/YGLWConstruction.lean`: `K_GLW(u, u) ≤ 1/(2u)` for
    --    `u > 0`. So `Var[Y u]` decays like `1/u`.
    --
    -- 2. **Block-supremum tail bound.** For each integer `T ∈ ℕ`,
    --    consider `M_T := sup_{u ∈ [T, T+1]} |Y u|` (a.s. finite by
    --    sample-path continuity, conjunct 8 — now Full).
    --    By Borell-TIS for centred Gaussian processes:
    --      `P(M_T ≥ ε) ≤ 2 * exp(-ε²/(2σ_T²))`
    --    where `σ_T² = sup_{u ∈ [T, T+1]} Var[Y u] ≤ 1/(2T)`.
    --    Hence:
    --      `P(M_T ≥ ε) ≤ 2 * exp(-ε² T)`.
    --
    -- 3. **Borel-Cantelli on the integer ladder.**
    --      `∑_T P(M_T ≥ ε) ≤ 2 * ∑_T exp(-ε² T) < ∞` (geometric series).
    --    By BC (`MeasureTheory.ae_eventually_notMem`): `P(limsup_T
    --    {M_T ≥ ε}) = 0`. Hence almost-surely, only finitely many `T`
    --    have `M_T ≥ ε`, i.e., for all sufficiently large `u`,
    --    `|Y u| < ε`.
    --
    -- 4. **Convert to ε-existence form.** Almost-surely, for every
    --    `ε > 0`, ∃ T₀, ∀ u ≥ T₀, |Y u| ≤ ε. Quantifier interleaving
    --    via a countable rational `ε`-net.
    --
    -- **Mathlib gap (R19 readiness Blocker A):** the Borell-TIS
    -- inequality is not in Mathlib at HEAD; the brownian-motion
    -- library has not yet landed it either. The diagnostic's
    -- "elementary route" via finite ε-net + marginal Gaussian tail
    -- requires (a) a Mathlib-native Gaussian tail bound (currently
    -- only the MGF/charFun infrastructure exists) and (b) a uniform-
    -- in-ω Hölder constant control for the modification (the
    -- `exists_modification_holder'''` API gives only per-ω constants).
    -- Neither is a one-wave fix. See `Helpers/R19ReadinessDiagnostic.md`.
    --
    -- **R19 progress (Helpers/R19APIScoping.md):** sub-prerequisites
    -- T2.1.a + T2.1.b are now Full:
    --   * `eval_glwGaussianLimit_real_abs_ge_le_of_pos`: marginal sub-
    --     Gaussian tail at integer points giving `≤ 2·exp(-ε²T)`
    --     (closes Mathlib gap (a)).
    --   * `glwHolderConstant` + `measurable_glwHolderConstant`:
    --     measurable Hölder constant from the explicit iSup formula
    --     at `KolmogorovChentsov.lean:650-651` (closes Mathlib gap (b);
    --     R18's reading of the API was wrong here).
    -- The remaining R19-blocker is T2.2 (the analytical bound
    -- `Var(Y_s - Y_t) = O(|s-t|² / T³)` for `s, t ∈ [T, T+1]`, which
    -- supplies the local K-C constant `M_T` needed for a *summable*
    -- modulus-of-continuity tail). Documented in
    -- `marginal_sup_tail_blocker_R19` above. R20 readiness diagnostic
    -- will track the K_GLW Taylor-expansion bound separately.
    -- **R21 status (T4.1 partial):** T3.1 (Markov on glwHolderConstantENN T)
    -- and T3.2 (BC on integer marginals via summable_marginal_tail) are
    -- now sorry-free.
    --
    -- The remaining gap is the **modification's local oscillation**: BC
    -- on integer marginals gives a.s. eventually `|ω T| < ε` (for
    -- T : ℕ), but the conjunct asserts `|Y u ω| = |Y' u.toNNReal ω| ≤ ε`
    -- for all real `u ≥ T₀`. For non-integer `u` with `u.toNNReal ∈
    -- (T, T+1)`, the bound on `|Y' u.toNNReal ω|` requires either
    --
    --   (i) a sup-over-block bound on the modification, which would
    --       follow from BC on `{(ε/2)² ≤ glwHolderConstantENN T}` events
    --       — but proving summability of the Markov bound `Cp_T / (ε/2)²`
    --       requires extracting the explicit form `Cp_T = M_T · constL`
    --       and showing `∑ Cp_T < ∞` (where `M_T = 1/(2T³)` from R20
    --       T2.1 and `constL` is polynomial in `c_T = 6(T+1)`); or
    --
    --   (ii) a per-ω modulus-of-continuity argument from
    --       `exists_modification_holder'''`'s local Hölder data, which
    --       is per-(ω, t) and not directly summable in T.
    --
    -- Both routes are several hundred LOC of additional brownian-motion
    -- API alignment. The R21 bound `glwHolderConstantENN_lintegral_le_R20`
    -- (T2.2 Full) is the load-bearing prerequisite; route (i)'s
    -- summability is the next major sub-task.
    intro ε hε
    -- **R22 closure.** BC on dense-iSup block events + T4.1 a.s.-bridge +
    -- T4.2 continuity transfer + floor argument.
    have h_BC := BC_block_sup_R22 hε
    have h_eq_T : ∀ᵐ ω ∂glwGaussianLimit, ∀ T : ℕ,
        (⨆ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
            |Y' u.1 ω|) =
        (⨆ u : ↥(denseCountable NNReal ∩ Set.Ico ((T : NNReal)) ((T : NNReal) + 1)),
            |ω u.1|) := by
      rw [ae_all_iff]
      intro T
      exact modification_sup_eq_projection_iSup_ae T hY'_ae_eq
    filter_upwards [h_BC, h_eq_T] with ω h_evt h_eq
    rw [Filter.eventually_atTop] at h_evt
    obtain ⟨T₀_nat, hT₀⟩ := h_evt
    refine ⟨(T₀_nat : ℝ), ?_⟩
    intro u_real hu_real
    -- Setup: u_real ≥ T₀_nat ≥ 0; T := ⌊u_real⌋₊; T ≥ T₀_nat; u.toNNReal ∈ Ico T (T+1).
    have h_u_nn : (0 : ℝ) ≤ u_real :=
      le_trans (Nat.cast_nonneg T₀_nat) hu_real
    set T : ℕ := ⌊u_real⌋₊ with hT_def
    have hT_ge : T₀_nat ≤ T := by
      rw [hT_def]
      have h_floor_T₀ : ⌊(T₀_nat : ℝ)⌋₊ = T₀_nat := Nat.floor_natCast _
      rw [← h_floor_T₀]
      exact Nat.floor_le_floor hu_real
    have h_T_le_u : (T : ℝ) ≤ u_real := Nat.floor_le h_u_nn
    have h_u_lt_T1 : u_real < (T : ℝ) + 1 := Nat.lt_floor_add_one u_real
    have h_uN_ge_T : (T : NNReal) ≤ u_real.toNNReal := by
      rw [← Real.toNNReal_coe_nat T]
      exact Real.toNNReal_mono h_T_le_u
    have h_uN_lt_T1 : u_real.toNNReal < (T : NNReal) + 1 := by
      have h_real : u_real < ((T : ℕ) + 1 : ℝ) := by push_cast; exact h_u_lt_T1
      have h_pos : (0 : ℝ) < ((T : ℕ) + 1 : ℝ) := by push_cast; positivity
      have h_lt_NNReal : u_real.toNNReal < ((T : ℕ) + 1 : ℝ).toNNReal :=
        (Real.toNNReal_lt_toNNReal_iff h_pos).mpr h_real
      have h_eq_NNReal : ((T : ℕ) + 1 : ℝ).toNNReal = (T : NNReal) + 1 := by
        push_cast
        rw [Real.toNNReal_add (by exact_mod_cast Nat.zero_le T) (by norm_num : (0 : ℝ) ≤ 1),
            Real.toNNReal_coe_nat, Real.toNNReal_one]
      rw [← h_eq_NNReal]; exact h_lt_NNReal
    have h_uN_block : u_real.toNNReal ∈
        Set.Ico ((T : NNReal)) ((T : NNReal) + 1) := ⟨h_uN_ge_T, h_uN_lt_T1⟩
    -- BC at T: dense_iSup_T |ω u.1| < ε.
    have h_T_bound : ¬ (ε ≤ ⨆ u : ↥(denseCountable NNReal ∩
                          Set.Ico ((T : NNReal)) ((T : NNReal) + 1)), |ω u.1|) := hT₀ T hT_ge
    push_neg at h_T_bound
    -- T4.1 transfer: dense_iSup_T |Y' u.1 ω| = dense_iSup_T |ω u.1| < ε.
    have h_T_bound_Y : ⨆ u : ↥(denseCountable NNReal ∩
                       Set.Ico ((T : NNReal)) ((T : NNReal) + 1)), |Y' u.1 ω| < ε := by
      rw [h_eq T]; exact h_T_bound
    -- BddAbove of the dense family for |Y' · ω| (via continuity on compact Icc).
    have h_cont_abs : Continuous (fun u : NNReal => |Y' u ω|) := (hY'_cont ω).abs
    have h_icc_compact : IsCompact (Set.Icc ((T : NNReal)) ((T : NNReal) + 1)) := isCompact_Icc
    have h_bdd : BddAbove (Set.range (fun v : ↥(denseCountable NNReal ∩
                  Set.Ico ((T : NNReal)) ((T : NNReal) + 1)) => |Y' v.1 ω|)) := by
      have h_image_bdd : BddAbove ((fun u : NNReal => |Y' u ω|) ''
                Set.Icc ((T : NNReal)) ((T : NNReal) + 1)) :=
        (h_icc_compact.image h_cont_abs).bddAbove
      apply BddAbove.mono ?_ h_image_bdd
      rintro x ⟨v, rfl⟩
      exact ⟨v.1, ⟨v.2.2.1, le_of_lt v.2.2.2⟩, rfl⟩
    -- Pointwise |Y' v.1 ω| ≤ dense_iSup < ε for all v in the dense subset.
    have h_dense_bound : ∀ v : ↥(denseCountable NNReal ∩
                      Set.Ico ((T : NNReal)) ((T : NNReal) + 1)), |Y' v.1 ω| ≤ ε := by
      intro v
      have h_le_iSup : |Y' v.1 ω| ≤ ⨆ u : ↥(denseCountable NNReal ∩
                       Set.Ico ((T : NNReal)) ((T : NNReal) + 1)), |Y' u.1 ω| :=
        le_ciSup h_bdd v
      linarith
    -- T4.2: continuous Y' · ω on block, dense bound transfers to all u in Ico.
    exact continuous_block_pt_le T (hY'_cont ω) h_dense_bound h_uN_block

end Erdos524.Helpers
