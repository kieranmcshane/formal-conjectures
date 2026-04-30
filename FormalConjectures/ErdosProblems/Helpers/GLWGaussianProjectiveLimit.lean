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

open MeasureTheory NormedSpace Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

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
    intro ε hε
    sorry  -- TAG[R18-blocker]: tail decay -- Borell-TIS / Mathlib gap

end Erdos524.Helpers
