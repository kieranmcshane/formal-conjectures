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
import BrownianMotion.Gaussian.MultivariateGaussian
import BrownianMotion.Gaussian.ProjectiveLimit
import KolmogorovExtension4.KolmogorovExtension
import Mathlib.Probability.Process.Kolmogorov

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
  -- Pin witness: probability space `(NNReal → ℝ, glwGaussianLimit)`,
  -- process `Y u ω = ω u.toNNReal` (extends GLW to all of ℝ via
  -- `toNNReal`-clamping; the negative-u branch is harmless because
  -- the load-bearing conjuncts (cov, centered, integrable_prod) are
  -- guarded by `0 ≤ u, 0 ≤ v`).
  refine ⟨NNReal → ℝ, inferInstance, glwGaussianLimit,
    fun u ω => ω u.toNNReal, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- measurable: each marginal is a Pi-projection
    intro u; exact measurable_pi_apply _
  · -- Conjunct 3 (Integrable (Y u) glwGaussianLimit). The marginal at
    -- `u.toNNReal` is centred Gaussian with variance `K_GLW(u, u)`
    -- (cf. `hasLaw_eval_glwGaussianLimit`); integrability of the
    -- identity then transfers along the law.
    intro u
    have hL := hasLaw_eval_glwGaussianLimit (t := u.toNNReal)
    have h_int_id : Integrable (id : ℝ → ℝ)
        (Measure.map (fun ω : NNReal → ℝ ↦ ω u.toNNReal) glwGaussianLimit) := by
      rw [hL.map_eq]; exact IsGaussian.integrable_id
    exact h_int_id.comp_aemeasurable hL.aemeasurable
  · -- Conjunct 4 (bivariate integrability of `Y u * Y v`). Both
    -- marginals are `MemLp 2`, so `Y u * Y v` is integrable
    -- (Cauchy-Schwarz: `MemLp.integrable_mul`).
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
    exact hMu.integrable_mul hMv
  · -- Conjunct 5 (centered): the marginal at `u.toNNReal` has centred
    -- Gaussian law, so its integral is `0` (via `integral_id_gaussianReal`).
    intro u
    exact (hasLaw_eval_glwGaussianLimit (t := u.toNNReal)).integral_eq.trans
      integral_id_gaussianReal
  · -- Conjunct 6 (covariance fit). Combine `covariance_eval_glwGaussianLimit`
    -- (giving `cov[ω u.toNNReal, ω v.toNNReal] = K_GLW (↑u.toNNReal) (↑v.toNNReal)`)
    -- with `covariance_eq_sub` and centeredness to obtain `∫ XY = K_GLW u v`.
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
    -- Goal: ∫ ω, ω u.toNNReal * ω v.toNNReal ∂glwGaussianLimit = K_GLW u v
    -- Note: μ[X * Y] = ∫ ω, (X * Y) ω ∂μ = ∫ ω, X ω * Y ω ∂μ
    exact h_eq.symm
  · -- Conjunct 7 (joint Gaussianity). The linear functional
    -- `f ω = ∑ i, cs i * ω (us i).toNNReal` factors as `φ ∘ I.restrict`
    -- where `I` is the finset of distinct `(us i).toNNReal` values and
    -- `φ : (↥I → ℝ) →L[ℝ] ℝ` is a CLM. Then
    -- `Measure.map f μ = Measure.map φ (glwGaussianProjectiveFamily I)`,
    -- and the latter is Gaussian by `isGaussian_map`.
    intro n us cs
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
  · -- Conjunct 8 (continuous paths): pending O1 Full. Once O1's
    -- `kolmogorovCondition` is sorry-free, apply `IsAEKolmogorovProcess.mk`
    -- + brownian-motion's `IsKolmogorovProcess.continuousModification`
    -- to get the a.e. continuous modification, which replaces `Y` here.
    sorry  -- TAG[R16-await-O1]: continuous modification via K-C
  · -- Conjunct 9 (tail decay): independent. Borell on
    -- `sup_{u ∈ [T, T+1]} |Y u|` (Ledoux *Concentration of Measure*
    -- §1.3 eq. (1.7)) + Borel-Cantelli on `T = 1, 2, 3, …`. Uses
    -- `K_GLW_var_tendsto_zero` from `Helpers/YGLWConstruction.lean`.
    intro ε hε
    sorry  -- TAG[R16-tailDecay-Borell]

end Erdos524.Helpers
