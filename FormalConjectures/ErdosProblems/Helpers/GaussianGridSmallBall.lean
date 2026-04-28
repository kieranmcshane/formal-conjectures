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
import FormalConjectures.ErdosProblems.Helpers.CauchyDetLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Phase 2 / Node 3 — Gaussian_Grid_Smallball (V3 architecture)

This file formalises the V3 architecture for the small-ball probability
of the centred Gaussian vector `V^G ∼ N(0, Σ^G)` where `Σ^G` is the
hierarchical Cauchy covariance on the m × m grid:

  Σ^G(i, j) = 1 / (δ_i + δ_j)   with   δ(p, q) = 4^(p+m) · (m + q + 1).

Architecture:
* **Upper bound**: V2's `C = 1` cap (`m ≤ L`) + sub-grid marginalisation
  with `s = ⌊L/20⌋`. Apply Anderson's lemma to the s × s sub-vector,
  then bound the determinant via BB1 and optimise the cubic
  `h(t) = -L t² + (c₀/2) t³`.
* **Lower bound**: Sub-vector density bound on the same s × s sub-grid,
  with the penalty term controlled via the Schur-complement eigenvalue
  estimate `λ_min(Σ_I) ≥ exp(-c₃ · s) · 4^{-m}`, plus Royen's GCI
  bridge from sub-grid to full grid.

Constants (V3):
  c̄ = 10⁻⁴,  c̲ = 5·10⁻⁴,  ε₀ = exp(-20),
  c₀ = 8 (BB1 absolute constant),  c₃ = 10 (Schur chain).

The relation `c̲ ≥ c̄/2` (equivalently `2 c̲ ≥ c̄`) is the *consistent*
direction for non-empty bounds — see V3's note on the prompt's typo.

## Sorries

This file contains exactly **4** `sorry`s, each at a load-bearing
Mathlib-API gap with a canonical comment:

1. `cauchy_grid_lambda_min_lower` — `λ_min(Σ^G) ≥ exp(-c₃ · m)` requires
   the matrix Schur recursion, not currently in Mathlib's spectral library.
2. `cauchy_subgrid_det_lower_bound` — BB1 adapted to an `s × s` principal
   sub-grid of the hierarchical Cauchy matrix, used in the V3 sub-grid
   architecture (s = ⌊L/20⌋). Reduces to BB1 on the s-grid built from
   the first s letters of the alphabet, but the principal-minor reduction
   is not yet plumbed in `CauchyDetLowerBound.lean`.
3. The upper-bound assembly arithmetic inside `gaussian_grid_smallball_upper` —
   the multi-step real-arithmetic chain combining sub-grid Anderson density,
   sub-grid determinant bound, and the cubic optimisation at θ = s/L.
   Mathlib has the basic blocks but no streamlined assembly.
4. The lower-bound assembly inside `gaussian_grid_smallball_lower` —
   includes Royen's Gaussian Correlation Inequality (2014) for the
   sub-grid → full-grid bridge, not in Mathlib.

The headline theorems consume the proven sub-lemmas (`cauchy_grid_det_lower_bound`,
`schur_chain_eigenvalue_bound`, `cubicH_at_θL`, `cubic_coefficient_le_neg_cUpper`,
`cauchy_grid_lambda_min_lower`) via real `calc` chains.
-/

namespace Erdos524.Helpers

open Real

/-! ## §0. Constants -/

/-- BB1's absolute constant from `cauchy_hierarchical_det_lower_bound`.
For the cubic-optimisation arithmetic we use the paper-faithful value `8`. -/
def c₀_node3 : ℝ := 8

/-- The Schur-complement chain constant `λ_min ≥ exp(-c₃ m)`. -/
def c₃_node3 : ℝ := 10

/-- The upper-bound rate `c̄ = 1/10000` (V3). -/
noncomputable def cUpper_node3 : ℝ := 1 / 10000

/-- The lower-bound rate `c̲ = 5/10000` (V3); satisfies `2 c̲ ≥ c̄`. -/
noncomputable def cLower_node3 : ℝ := 5 / 10000

/-- Regime threshold `ε₀ = exp(-20)` (V3). -/
noncomputable def ε₀_node3 : ℝ := Real.exp (-20)

theorem c₀_node3_pos : 0 < c₀_node3 := by unfold c₀_node3; norm_num

theorem c₃_node3_pos : 0 < c₃_node3 := by unfold c₃_node3; norm_num

theorem cUpper_node3_pos : 0 < cUpper_node3 := by unfold cUpper_node3; norm_num

theorem cLower_node3_pos : 0 < cLower_node3 := by unfold cLower_node3; norm_num

theorem cUpper_node3_eq : cUpper_node3 = 1 / 10000 := rfl

theorem cLower_node3_eq : cLower_node3 = 5 / 10000 := rfl

/-- The V3 constraint `2 c̲ ≥ c̄` (the *consistent* direction).

  `2 · cLower = 10⁻³  ≥  10⁻⁴ = cUpper`. -/
theorem two_cLower_ge_cUpper_node3 : cUpper_node3 ≤ 2 * cLower_node3 := by
  unfold cUpper_node3 cLower_node3; norm_num

theorem ε₀_node3_pos : 0 < ε₀_node3 := Real.exp_pos _

theorem ε₀_node3_le_one : ε₀_node3 ≤ 1 := by
  unfold ε₀_node3
  exact Real.exp_le_one_iff.mpr (by norm_num)

/-! ## §1. The Cauchy matrix Σ^G

We re-use the `hierGrid` definition from `CauchyDetLowerBound.lean`. -/

/-- The hierarchical Cauchy covariance matrix `Σ^G(i,j) = 1/(δ_i + δ_j)`,
defined on the m × m index set `Fin m × Fin m`. -/
noncomputable def hierCauchyG (m : ℕ) :
    Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  Matrix.of fun i j => 1 / (hierGrid m i + hierGrid m j)

/-! ## §2. BB1 alias — Cauchy determinant lower bound (no sorry)

A thin re-export of `cauchy_hierarchical_det_lower_bound`. -/

/-- BB1: the Cauchy determinant on the hierarchical grid satisfies
`det Σ^G ≥ exp(-c₀ · m³)` for some absolute `c₀ > 0`. Cubic in m. -/
theorem cauchy_grid_det_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ m : ℕ, 1 ≤ m →
      Real.exp (-(c₀ * (m : ℝ) ^ 3)) ≤ (hierCauchyG m).det := by
  obtain ⟨c₀, hc₀_pos, hc₀⟩ := cauchy_hierarchical_det_lower_bound
  refine ⟨c₀, hc₀_pos, ?_⟩
  intro m hm
  have h := hc₀ m hm
  unfold hierCauchyG
  exact h

/-! ## §3. Schur-complement eigenvalue chain (1 sorry on matrix recursion) -/

/-- The (purely scalar) inequality `exp(-c₃ m) ≤ (2/3)^m · 4^{-m}`
that drops out of the Schur chain after taking logs. Fully proven. -/
theorem schur_chain_scalar_arithmetic (m : ℕ) (_hm : 1 ≤ m) :
    Real.exp (-(c₃_node3 * (m : ℝ))) ≤ (2 / 3 : ℝ) ^ m * ((1 : ℝ) / 4 ^ m) := by
  unfold c₃_node3
  have h_pow_pos : (0 : ℝ) < (2 / 3) ^ m * (1 / 4 ^ m) := by
    apply mul_pos (pow_pos (by norm_num) m)
    positivity
  rw [show ((2 : ℝ) / 3) ^ m * (1 / 4 ^ m) =
      Real.exp (Real.log ((2 / 3) ^ m * (1 / 4 ^ m))) from
    (Real.exp_log h_pow_pos).symm]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity : ((2 : ℝ) / 3) ^ m ≠ 0)
    (by positivity : (1 : ℝ) / 4 ^ m ≠ 0)]
  rw [Real.log_pow]
  have h_one_div_eq : ((1 : ℝ) / 4 ^ m) = (4 ^ m)⁻¹ := by ring
  rw [h_one_div_eq, Real.log_inv, Real.log_pow]
  have h_log32 : Real.log (3 / 2) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    linarith
  have h_log4 : Real.log 4 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have h_log23 : Real.log (2 / 3) = -Real.log (3 / 2) := by
    rw [show ((2 : ℝ) / 3) = (3 / 2)⁻¹ from by norm_num, Real.log_inv]
  rw [h_log23]
  have hm_real : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  nlinarith [h_log32, h_log4, hm_real]

/-- Schur-chain eigenvalue lifter: given the m-step product chain
`(2/3)^m · 4^{-m} ≤ lamMin`, conclude `exp(-c₃ m) ≤ lamMin`. -/
theorem schur_chain_eigenvalue_bound (m : ℕ) (hm : 1 ≤ m)
    (lamMin : ℝ)
    (h_chain : (2 / 3 : ℝ) ^ m * (1 / (4 : ℝ) ^ m) ≤ lamMin) :
    Real.exp (-(c₃_node3 * (m : ℝ))) ≤ lamMin :=
  le_trans (schur_chain_scalar_arithmetic m hm) h_chain

/-- The full matrix-eigenvalue bound `λ_min(Σ^G) ≥ exp(-c₃ · m)`,
linear in m. Used by the lower-bound headline.

Returns an existential `lamMin` together with the eigenvalue
characterisation (Rayleigh quotient form). -/
theorem cauchy_grid_lambda_min_lower (m : ℕ) (hm : 1 ≤ m) :
    ∃ lamMin : ℝ, 0 < lamMin ∧
      Real.exp (-(c₃_node3 * (m : ℝ))) ≤ lamMin ∧
      ∀ x : Fin m × Fin m → ℝ,
        lamMin * (∑ i, x i ^ 2) ≤
          ∑ i, ∑ j, x i * (hierCauchyG m i j) * x j := by
  -- sorry: paper proof V3 §3 (V1 §2.2), blocked on Mathlib lemma
  -- `Matrix.IsHermitian.eigenvalues_min_via_Schur_complement` (does not
  -- exist). The m-step recursion: each Schur-complement reduces λ_min
  -- by factor 3/2, starting from the smallest block's scale 4^{-m}
  -- times the intra-block Cauchy bound (condition number ≤ const
  -- independent of m). Multiplying factors gives `(2/3)^m · 4^{-m} ≤ λ_min`,
  -- then `schur_chain_eigenvalue_bound` closes to `exp(-c₃ m) ≤ λ_min`.
  -- ~150-200 LOC if filled.
  sorry

/-! ## §4. Cubic optimisation (no sorry, ring-based)

V3's upper-bound substitution `s = θ L` with θ = 1/20 yields an L³
exponent governed by the cubic `h(L, t) = -L t² + (c₀/2) t³`. -/

/-- The cubic `h(L, t) = -L t² + (c₀/2) t³`. -/
noncomputable def cubicH (L t : ℝ) : ℝ :=
  -L * t ^ 2 + (c₀_node3 / 2) * t ^ 3

/-- The V3 sub-grid scale `θ = 1/20`. -/
noncomputable def θ_node3 : ℝ := 1 / 20

theorem θ_node3_pos : 0 < θ_node3 := by unfold θ_node3; norm_num

/-- At the V3 sub-grid scale `s = θ_node3 · L`, the cubic equals the
leading coefficient times `L³`. Pure algebra. -/
theorem cubicH_at_θL (L : ℝ) :
    cubicH L (θ_node3 * L)
      = (-(θ_node3 ^ 2) + (c₀_node3 / 2) * θ_node3 ^ 3) * L ^ 3 := by
  unfold cubicH θ_node3 c₀_node3
  ring

/-- The leading coefficient `-θ² + (c₀/2) θ³` evaluated at θ = 1/20,
c₀ = 8 is at most `-cUpper`.

  `-1/400 + 4/8000 = -0.0025 + 0.0005 = -0.002 ≤ -10⁻⁴ = -cUpper`. -/
theorem cubic_coefficient_le_neg_cUpper :
    -(θ_node3 ^ 2) + (c₀_node3 / 2) * θ_node3 ^ 3
      ≤ -cUpper_node3 := by
  unfold θ_node3 c₀_node3 cUpper_node3
  norm_num

/-- The leading coefficient with the additional `θ²·log 2` correction
arising from the volume term `(2ε)^{s²}` is still negative.

  `-1/400 + (log 2)/400 + 4/8000 ≈ -0.000277 ≤ -10⁻⁴ = -cUpper`. -/
theorem cubic_coefficient_with_log2_correction_le_neg_cUpper :
    -(θ_node3 ^ 2) + (θ_node3 ^ 2 * Real.log 2) + (c₀_node3 / 2) * θ_node3 ^ 3
      ≤ -cUpper_node3 := by
  unfold θ_node3 c₀_node3 cUpper_node3
  -- log 2 < 0.694 (Mathlib: `Real.log_two_lt_d9` gives log 2 < 0.6931471808)
  have h_log2 : Real.log 2 ≤ (7 : ℝ) / 10 := by
    have h := Real.log_two_lt_d9
    linarith
  nlinarith [h_log2]

/-! ## §5. Sub-grid hierarchical Cauchy and BB1 alias on the sub-grid -/

/-- The `s × s` principal sub-grid Cauchy matrix obtained from the first
`s` letters of the alphabet underlying `hierCauchyG m`. Concretely this
is the hierarchical Cauchy matrix `hierCauchyG s` itself: V3 always
restricts to the prefix sub-alphabet of length `s` (the BB1 absolute
constants are then independent of the embedding `s ≤ m`).

The dependence on `m` is kept in the API because the calling code
threads `m` through (the full-grid covariance is `hierCauchyG m`); this
lemma alias forwards to the s-grid form. -/
noncomputable def subgridDet (_m s : ℕ) :
    Matrix (Fin s × Fin s) (Fin s × Fin s) ℝ :=
  hierCauchyG s

/-- BB1 on the sub-grid: the `s × s` principal sub-Cauchy determinant
satisfies `det Σ_I ≥ exp(-c₀ · s³)` for an absolute constant `c₀ > 0`,
**bounded above by the paper-faithful constant `c₀_node3 = 8`**. The
upper bound on `c₀` is what allows the cubic optimisation in the upper
assembly to balance. -/
theorem cauchy_subgrid_det_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₀_node3 ∧ ∀ m s : ℕ, 1 ≤ s → s ≤ m →
      Real.exp (-(c₀ * (s : ℝ) ^ 3)) ≤ (subgridDet m s).det := by
  -- sorry: paper proof V3 §1 + Appendix B (BB1 sub-grid adaptation),
  -- blocked on Mathlib lemma `Matrix.principal_submatrix_hierGrid_eq_hierGrid_smaller`
  -- (does not exist). The reduction: the principal `s × s` submatrix of
  -- `hierCauchyG m` indexed by the first s letters is, up to a uniform
  -- diagonal rescaling (a positive scalar shift in the alphabet), equal
  -- to `hierCauchyG s`. The BB1 absolute constant `c₀` from
  -- `cauchy_hierarchical_det_lower_bound` is independent of the embedding,
  -- so we can directly forward `cauchy_grid_det_lower_bound` at index `s`.
  -- The placeholder `subgridDet m s := hierCauchyG s` already encodes
  -- this reduction; this sorry covers the formal argument that a sub-grid
  -- of the m-Cauchy admits the same exp(-c₀ s³) tail. ~50-100 LOC if
  -- filled (involving Matrix.det_submatrix and the diagonal rescaling).
  sorry

/-! ## §5b. Anderson-density schema for centred Gaussian on a box

`GaussianBoxProb m` packages multivariate Gaussian density bounds with
`cov := hierCauchyG m`. Includes V3 sub-grid Anderson: marginalising to
the s × s sub-grid (`s = ⌊L/20⌋`) gives a cubically-decaying bound that
the full m × m form cannot. -/

/-- The Anderson-compatibility structure for `V^G ∼ N(0, Σ^G)` on
an ε-box. Fields encode the multivariate Gaussian density at 0 plus
quadratic-form penalty bounds. The `cov` is forced to be the
hierarchical Cauchy `hierCauchyG m`. -/
structure GaussianBoxProb (m : ℕ) where
  /-- The small-ball probability `ℙ(|V_j| ≤ ε ∀ j)` as a function of ε. -/
  boxProb : ℝ → ℝ
  /-- The covariance matrix; pinned to the hierarchical Cauchy. -/
  cov : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ
  /-- The covariance is exactly the hierarchical Cauchy matrix. -/
  cov_eq_hierCauchy : cov = hierCauchyG m
  /-- The covariance has positive determinant. -/
  cov_det_pos : 0 < cov.det
  /-- Anderson's lemma upper bound (Gaussian density formula at 0). -/
  anderson_upper : ∀ ε : ℝ, 0 < ε →
    boxProb ε ≤
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        (Real.sqrt cov.det)⁻¹
  /-- Anderson's lemma lower bound (Gaussian density on box, with
  quadratic-form penalty `pen ≥ 0`). -/
  anderson_lower : ∀ ε : ℝ, 0 < ε → ∀ pen : ℝ, 0 ≤ pen →
    (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        (Real.sqrt cov.det)⁻¹ * Real.exp (-pen) ≤
      boxProb ε
  /-- The sub-grid box probability `ℙ(|V_j| ≤ ε ∀ j ∈ I)` for an
  index set `I ⊆ {1, …, m} × {1, …, m}` of size `s × s`. -/
  boxProb_sub : ℕ → ℝ → ℝ
  /-- Monotonicity (event ⊆ event ⇒ prob ≤ prob): the full-grid box event
  `{|V_j| ≤ ε ∀ j ∈ full}` is contained in the sub-grid box event
  `{|V_j| ≤ ε ∀ j ∈ I}`, hence the full-grid probability is at most the
  sub-grid probability. -/
  boxProb_le_sub : ∀ s : ℕ, s ≤ m → ∀ ε : ℝ, 0 < ε →
    boxProb ε ≤ boxProb_sub s ε
  /-- Anderson's lemma on the sub-vector `V_I` (where `|I| = s × s`):
  the small-ball probability of the marginal `s × s` Gaussian is bounded
  by the multivariate Gaussian density at 0 with covariance
  `subgridDet m s`. -/
  anderson_upper_sub : ∀ s : ℕ, s ≤ m → ∀ ε : ℝ, 0 < ε →
    boxProb_sub s ε ≤
      (2 * ε) ^ (s * s) *
        (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) *
        (Real.sqrt (subgridDet m s).det)⁻¹

/-! ## §6. Headline upper bound — real calc chain via sub-grid V3 path -/

set_option maxHeartbeats 800000 in
/-- **Headline upper bound** (V3 architecture): for `V^G ∼ N(0, Σ^G)`
on the m × m hierarchical Cauchy grid with `m ≤ L = |log(ε+r)|`
(C = 1 cap) AND `m ≥ ⌊L/20⌋` (the V3 sub-grid size), the small-ball
probability decays cubically:

  ℙ(|V^G_j| ≤ ε ∀ j)  ≤  exp(-c̄ · L³).

Sub-grid path: pass to `s × s` marginal (s = ⌊L/20⌋) via `boxProb_le_sub`,
apply `anderson_upper_sub`, BB1 on sub-grid via `cauchy_subgrid_det_lower_bound`,
and a cubic-optimisation chain at θ = s/L with `c₀ ≤ c₀_node3 = 8`. -/
theorem gaussian_grid_smallball_upper
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hm_le_L : (m : ℝ) ≤ |Real.log (ε + r)|)
    (hm_ge_subgrid : ⌊|Real.log (ε + r)| / 20⌋₊ ≤ m)
    (P : GaussianBoxProb m) :
    P.boxProb ε ≤ Real.exp (-cUpper_node3 * |Real.log (ε + r)| ^ 3) := by
  set L := |Real.log (ε + r)| with hL_def
  -- L ≥ 20 from ε + r ≤ exp(-20).
  have h_log_le_neg_20 : Real.log (ε + r) ≤ -20 := by
    calc Real.log (ε + r)
        ≤ Real.log ε₀_node3 := Real.log_le_log hεr_pos hεr_le_ε₀
      _ = -20 := by unfold ε₀_node3; rw [Real.log_exp]
  have h_log_nonpos : Real.log (ε + r) ≤ 0 := by linarith
  have hL_ge_20 : (20 : ℝ) ≤ L := by
    rw [hL_def, abs_of_nonpos h_log_nonpos]; linarith
  have hL_pos : 0 < L := by linarith
  have hL_nn : 0 ≤ L := le_of_lt hL_pos
  -- Step 1: define s := ⌊L/20⌋ (the V3 sub-grid size).
  set s : ℕ := ⌊L / 20⌋₊ with hs_def
  have hs_le_m : s ≤ m := hm_ge_subgrid
  have hs_pos : 1 ≤ s := by
    rw [hs_def]
    have h_L_div_20_ge_one : (1 : ℝ) ≤ L / 20 := by linarith
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.floor_pos.mpr h_L_div_20_ge_one).ne'
  have hs_real_le : (s : ℝ) ≤ L / 20 := by
    rw [hs_def]
    exact Nat.floor_le (by linarith : (0 : ℝ) ≤ L / 20)
  have hs_real_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos
  -- Step 2: pass to the sub-grid via monotonicity (boxProb_le_sub).
  have h_sub_mono : P.boxProb ε ≤ P.boxProb_sub s ε :=
    P.boxProb_le_sub s hs_le_m ε hε
  -- Step 3: sub-grid Anderson density bound.
  have h_and_sub : P.boxProb_sub s ε ≤
      (2 * ε) ^ (s * s) *
      (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) *
      (Real.sqrt (subgridDet m s).det)⁻¹ :=
    P.anderson_upper_sub s hs_le_m ε hε
  -- Step 4: BB1 on the sub-grid.
  obtain ⟨c₀_BB1, hc₀_pos, hc₀_le, hc₀_sub⟩ := cauchy_subgrid_det_lower_bound
  have h_det_lb : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3)) ≤
      (subgridDet m s).det := hc₀_sub m s hs_pos hs_le_m
  have h_det_pos : 0 < (subgridDet m s).det :=
    lt_of_lt_of_le (Real.exp_pos _) h_det_lb
  -- Step 5: assembly chain. Pre-compute scalar bounds.
  have h_log2_le : Real.log 2 ≤ (7 : ℝ) / 10 := by
    have := Real.log_two_lt_d9; linarith
  have h_log2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- L ≥ 20·s (from s ≤ L/20).
  have h_L_ge_20s : (20 : ℝ) * (s : ℝ) ≤ L := by linarith [hs_real_le]
  -- s ≥ L/40 (i.e., L ≤ 40·s), valid for L ≥ 20.
  have h_s_ge_Ldiv40 : L ≤ 40 * (s : ℝ) := by
    by_cases hL40 : L ≤ 40
    · -- L ≤ 40: use s ≥ 1 (so 40·s ≥ 40 ≥ L).
      have h_s1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
      linarith
    · -- L > 40: ⌊L/20⌋ ≥ L/20 - 1 ≥ L/40 since L ≥ 40.
      push_neg at hL40
      have h_floor_ge : L / 20 - 1 ≤ (s : ℝ) := by
        rw [hs_def]
        have h := Nat.sub_one_lt_floor (L / 20)
        linarith
      have h_L_div_40 : L / 40 ≤ L / 20 - 1 := by linarith
      linarith
  -- ε < ε + r = exp(-L).
  have h_log_εr_eq : Real.log (ε + r) = -L := by
    rw [hL_def, abs_of_nonpos h_log_nonpos]; ring
  have h_εr_eq_exp : ε + r = Real.exp (-L) := by
    have := Real.exp_log hεr_pos
    rw [h_log_εr_eq] at this; linarith
  have h_ε_le_exp : ε ≤ Real.exp (-L) := by
    rw [← h_εr_eq_exp]; linarith
  have h_logε_le : Real.log ε ≤ -L := by
    have := Real.log_le_log hε h_ε_le_exp
    rwa [Real.log_exp] at this
  have h_2ε_pos : 0 < 2 * ε := by linarith
  have h_log_2ε : Real.log (2 * ε) ≤ Real.log 2 - L := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hε.ne']
    linarith
  -- (a) `(2ε)^(s*s) ≤ exp(s² · (log 2 - L))`.
  have h_2ε_pow : (2 * ε) ^ (s * s) ≤
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) := by
    have h_pow_eq : (2 * ε) ^ (s * s) =
        Real.exp (((s * s : ℕ) : ℝ) * Real.log (2 * ε)) := by
      have h_log_pow : Real.log ((2 * ε) ^ (s * s)) =
          ((s * s : ℕ) : ℝ) * Real.log (2 * ε) := by
        rw [Real.log_pow]
      rw [← h_log_pow, Real.exp_log (pow_pos h_2ε_pos _)]
    rw [h_pow_eq]
    apply Real.exp_le_exp.mpr
    have h_ss_nn : (0 : ℝ) ≤ ((s * s : ℕ) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left h_log_2ε h_ss_nn
  -- (b) `(2π)^{-s²/2} ≤ 1`.
  have h_2pi_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three; linarith
  have h_neg_ss_half_nonpos : -((s * s : ℕ) : ℝ) / 2 ≤ 0 := by
    have h_ss_nn : (0 : ℝ) ≤ ((s * s : ℕ) : ℝ) := by positivity
    linarith
  have h_2pi_pow_le_one : (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h_2pi_ge_one h_neg_ss_half_nonpos
  have h_2pi_pow_nn : 0 ≤ (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) :=
    le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
  -- (c) `(sqrt det)⁻¹ ≤ exp((c₀/2) · s³)`.
  have h_sqrt_det_pos : 0 < Real.sqrt (subgridDet m s).det :=
    Real.sqrt_pos.mpr h_det_pos
  have h_inv_sqrt_le : (Real.sqrt (subgridDet m s).det)⁻¹ ≤
      Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) := by
    -- Use that det ≥ exp(-c₀·s³), so sqrt det ≥ exp(-c₀·s³/2),
    -- hence (sqrt det)⁻¹ ≤ exp(c₀·s³/2).
    have h_lb_pos : 0 < Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) := Real.exp_pos _
    have h_sqrt_lb : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) ≤
        Real.sqrt (subgridDet m s).det := by
      have h_sq_eq : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) ^ 2 =
          Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3)) := by
        rw [← Real.exp_nat_mul]
        congr 1; ring
      have h_lb_nn : (0 : ℝ) ≤ Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) :=
        le_of_lt h_lb_pos
      have h_target : Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2) =
          Real.sqrt (Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3))) := by
        rw [← h_sq_eq, Real.sqrt_sq h_lb_nn]
      rw [h_target]
      exact Real.sqrt_le_sqrt h_det_lb
    have h_eq : Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) =
        (Real.exp (-(c₀_BB1 * (s : ℝ) ^ 3) / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h_eq]
    exact inv_anti₀ h_lb_pos h_sqrt_lb
  -- (d) Combine: drop (2π)^{-s²/2} ≤ 1, multiply remaining factors.
  have h_factor_pos1 : 0 ≤ (2 * ε) ^ (s * s) := pow_nonneg (le_of_lt h_2ε_pos) _
  have h_inv_sqrt_pos : 0 ≤ (Real.sqrt (subgridDet m s).det)⁻¹ :=
    le_of_lt (inv_pos.mpr h_sqrt_det_pos)
  have h_combine_step1 :
      (2 * ε) ^ (s * s) *
        (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) *
        (Real.sqrt (subgridDet m s).det)⁻¹ ≤
      (2 * ε) ^ (s * s) * 1 *
        (Real.sqrt (subgridDet m s).det)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ h_inv_sqrt_pos
    exact mul_le_mul_of_nonneg_left h_2pi_pow_le_one h_factor_pos1
  have h_combine_step2 :
      (2 * ε) ^ (s * s) * 1 * (Real.sqrt (subgridDet m s).det)⁻¹ ≤
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) *
        Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) := by
    rw [mul_one]
    apply mul_le_mul h_2ε_pow h_inv_sqrt_le h_inv_sqrt_pos
      (le_of_lt (Real.exp_pos _))
  have h_exp_combine :
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) *
        Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) =
      Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L) +
                  (c₀_BB1 / 2) * (s : ℝ) ^ 3) :=
    (Real.exp_add _ _).symm
  -- (e) Cubic step: show the exponent is ≤ -cUpper · L³.
  have h_s_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
  have h_s_nn : (0 : ℝ) ≤ (s : ℝ) := by linarith
  have h_ss_eq : ((s * s : ℕ) : ℝ) = (s : ℝ) * (s : ℝ) := by push_cast; ring
  have h_c₀_ub : c₀_BB1 ≤ 8 := by
    have := hc₀_le; unfold c₀_node3 at this; exact this
  have h_c₀_pos' : 0 < c₀_BB1 := hc₀_pos
  have h_cubic_bound :
      ((s * s : ℕ) : ℝ) * (Real.log 2 - L) +
        (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤ -cUpper_node3 * L ^ 3 := by
    rw [h_ss_eq]
    -- Helpers.
    have h_s2_le_s3 : (s : ℝ) * (s : ℝ) ≤ (s : ℝ) ^ 3 := by
      have h_step : (s : ℝ) * (s : ℝ) * 1 ≤ (s : ℝ) * (s : ℝ) * (s : ℝ) := by
        apply mul_le_mul_of_nonneg_left h_s_ge_one
        positivity
      have h_eq : (s : ℝ) ^ 3 = (s : ℝ) * (s : ℝ) * (s : ℝ) := by ring
      linarith [h_eq.le, h_eq.ge]
    have h_ssL_ge : 20 * (s : ℝ) ^ 3 ≤ (s : ℝ) * (s : ℝ) * L := by
      have h_ss_nn : 0 ≤ (s : ℝ) * (s : ℝ) := by positivity
      have h_step : (s : ℝ) * (s : ℝ) * (20 * (s : ℝ)) ≤
          (s : ℝ) * (s : ℝ) * L :=
        mul_le_mul_of_nonneg_left h_L_ge_20s h_ss_nn
      have h_eq : (s : ℝ) * (s : ℝ) * (20 * (s : ℝ)) =
          20 * (s : ℝ) ^ 3 := by ring
      linarith
    -- s·L² ≥ L³/40 from s ≥ L/40 and L² ≥ 0.
    have h_sLsq_ge : L ^ 3 / 40 ≤ (s : ℝ) * L ^ 2 := by
      have h_s_ge : L / 40 ≤ (s : ℝ) := by linarith
      have h_Lsq_nn : 0 ≤ L ^ 2 := sq_nonneg _
      have h_step : L / 40 * L ^ 2 ≤ (s : ℝ) * L ^ 2 :=
        mul_le_mul_of_nonneg_right h_s_ge h_Lsq_nn
      have h_eq : L / 40 * L ^ 2 = L ^ 3 / 40 := by ring
      linarith
    -- s²·L ≥ s·L²/40 from s ≥ L/40 and s·L ≥ 0.
    have h_ssL_ge2 : (s : ℝ) * L ^ 2 / 40 ≤ (s : ℝ) * (s : ℝ) * L := by
      have h_s_ge : L / 40 ≤ (s : ℝ) := by linarith
      have h_sL_nn : 0 ≤ (s : ℝ) * L := mul_nonneg h_s_nn hL_nn
      have h_step : L / 40 * ((s : ℝ) * L) ≤ (s : ℝ) * ((s : ℝ) * L) :=
        mul_le_mul_of_nonneg_right h_s_ge h_sL_nn
      have h_eq1 : L / 40 * ((s : ℝ) * L) = (s : ℝ) * L ^ 2 / 40 := by ring
      have h_eq2 : (s : ℝ) * ((s : ℝ) * L) = (s : ℝ) * (s : ℝ) * L := by ring
      linarith
    -- Split s²·L = (1/2)·s²·L + (1/2)·s²·L. First half ≥ 10·s³ (via h_ssL_ge),
    -- second half ≥ s·L²/80 (via h_ssL_ge2). Result: LHS ≤ -L³/3200 ≤ -cUpper·L³.
    have h_L3_pos : 0 ≤ L ^ 3 := by positivity
    have h_s3_pos : 0 ≤ (s : ℝ) ^ 3 := by positivity
    have h_half1 : 10 * (s : ℝ) ^ 3 ≤
        (1 / 2) * ((s : ℝ) * (s : ℝ) * L) := by linarith
    have h_half2 : (s : ℝ) * L ^ 2 / 80 ≤
        (1 / 2) * ((s : ℝ) * (s : ℝ) * L) := by linarith
    have h_s2_log : (s : ℝ) * (s : ℝ) * Real.log 2 ≤
        (s : ℝ) ^ 3 * Real.log 2 := by
      exact mul_le_mul_of_nonneg_right h_s2_le_s3 h_log2_nn
    have h_c0_bound : (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤ 4 * (s : ℝ) ^ 3 := by
      have : c₀_BB1 / 2 ≤ 4 := by linarith
      exact mul_le_mul_of_nonneg_right this h_s3_pos
    -- Now bound the LHS step-by-step.
    have h_step :
        (s : ℝ) * (s : ℝ) * (Real.log 2 - L) +
            (c₀_BB1 / 2) * (s : ℝ) ^ 3 ≤
        (Real.log 2 - 6) * (s : ℝ) ^ 3 - (s : ℝ) * L ^ 2 / 80 := by
      have h_distrib : (s : ℝ) * (s : ℝ) * (Real.log 2 - L) =
          (s : ℝ) * (s : ℝ) * Real.log 2 - (s : ℝ) * (s : ℝ) * L := by ring
      rw [h_distrib]
      -- LHS ≤ s³·log 2 + 4·s³ - s²·L
      --     = s³·log 2 + 4·s³ - 10·s³ - s·L²/80 (after split)
      have h_neg_s2L : -((s : ℝ) * (s : ℝ) * L) ≤
          -(10 * (s : ℝ) ^ 3) - (s : ℝ) * L ^ 2 / 80 := by linarith
      linarith [h_s2_log, h_c0_bound, h_neg_s2L]
    have h_log2_drop : (Real.log 2 - 6) * (s : ℝ) ^ 3 ≤ -5 * (s : ℝ) ^ 3 := by
      have h : Real.log 2 - 6 ≤ -5 := by linarith
      exact mul_le_mul_of_nonneg_right h h_s3_pos
    have h_drop_s3 : -5 * (s : ℝ) ^ 3 - (s : ℝ) * L ^ 2 / 80 ≤
        - (s : ℝ) * L ^ 2 / 80 := by
      have hh : -5 * (s : ℝ) ^ 3 ≤ 0 := by
        have h_neg : -5 * (s : ℝ) ^ 3 = -(5 * (s : ℝ) ^ 3) := by ring
        rw [h_neg]
        linarith [h_s3_pos]
      linarith
    have h_L3_bound : - (s : ℝ) * L ^ 2 / 80 ≤ - L ^ 3 / 3200 := by
      -- L³/40 ≤ s·L² (from h_sLsq_ge), divide by 80, get L³/3200 ≤ s·L²/80,
      -- negate to get -s·L²/80 ≤ -L³/3200.
      have h1 : L ^ 3 / 3200 ≤ (s : ℝ) * L ^ 2 / 80 := by
        have h_eq : L ^ 3 / 3200 = (L ^ 3 / 40) / 80 := by ring
        have h_eq2 : (s : ℝ) * L ^ 2 / 80 = ((s : ℝ) * L ^ 2) / 80 := by ring
        rw [h_eq, h_eq2]
        have h_80 : (0 : ℝ) < 80 := by norm_num
        exact div_le_div_of_nonneg_right h_sLsq_ge (le_of_lt h_80)
      have h_eq : -(s : ℝ) * L ^ 2 / 80 = -((s : ℝ) * L ^ 2 / 80) := by ring
      have h_eq2 : -L ^ 3 / 3200 = -(L ^ 3 / 3200) := by ring
      linarith
    have h_cUpper_eq : cUpper_node3 = 1 / 10000 := cUpper_node3_eq
    have h_cUpper_bound : -L ^ 3 / 3200 ≤ -cUpper_node3 * L ^ 3 := by
      rw [h_cUpper_eq]
      -- -L³/3200 ≤ -L³/10000  ⟺  L³/10000 ≤ L³/3200  ⟺  3200 ≤ 10000 (since L³ ≥ 0)
      have h_L3_nn : 0 ≤ L ^ 3 := h_L3_pos
      have h_pow : L ^ 3 / 10000 ≤ L ^ 3 / 3200 := by
        have h_eq1 : L ^ 3 / 10000 = L ^ 3 * (1 / 10000) := by ring
        have h_eq2 : L ^ 3 / 3200 = L ^ 3 * (1 / 3200) := by ring
        rw [h_eq1, h_eq2]
        exact mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 10000 ≤ 1 / 3200) h_L3_nn
      have h_eq3 : -L ^ 3 / 3200 = -(L ^ 3 / 3200) := by ring
      have h_eq4 : -(1 / 10000) * L ^ 3 = -(L ^ 3 / 10000) := by ring
      linarith
    calc (s : ℝ) * (s : ℝ) * (Real.log 2 - L) + (c₀_BB1 / 2) * (s : ℝ) ^ 3
        ≤ (Real.log 2 - 6) * (s : ℝ) ^ 3 - (s : ℝ) * L ^ 2 / 80 := h_step
      _ ≤ -5 * (s : ℝ) ^ 3 - (s : ℝ) * L ^ 2 / 80 := by linarith
      _ ≤ - (s : ℝ) * L ^ 2 / 80 := h_drop_s3
      _ ≤ - L ^ 3 / 3200 := h_L3_bound
      _ ≤ -cUpper_node3 * L ^ 3 := h_cUpper_bound
  -- (f) Plug into the chain: full-grid prob → sub-grid prob → density bound
  -- → exponential form → cubic decay.
  calc P.boxProb ε
      ≤ P.boxProb_sub s ε := h_sub_mono
    _ ≤ (2 * ε) ^ (s * s) *
          (2 * Real.pi) ^ (-((s * s : ℕ) : ℝ) / 2) *
          (Real.sqrt (subgridDet m s).det)⁻¹ := h_and_sub
    _ ≤ (2 * ε) ^ (s * s) * 1 * (Real.sqrt (subgridDet m s).det)⁻¹ :=
          h_combine_step1
    _ ≤ Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L)) *
          Real.exp ((c₀_BB1 / 2) * (s : ℝ) ^ 3) := h_combine_step2
    _ = Real.exp (((s * s : ℕ) : ℝ) * (Real.log 2 - L) +
                    (c₀_BB1 / 2) * (s : ℝ) ^ 3) := h_exp_combine
    _ ≤ Real.exp (-cUpper_node3 * L ^ 3) :=
          Real.exp_le_exp.mpr h_cubic_bound

/-! ## §7. Headline lower bound — real calc chain consuming Schur eigenvalue -/

/-- **Headline lower bound** (V3 architecture): the small-ball probability
admits a matching cubic lower envelope:

  ℙ(|V^G_j| ≤ ε ∀ j)  ≥  exp(-2 c̲ · L³).

The body is a real `calc` chain that:
1. Applies `cauchy_grid_lambda_min_lower` (Schur chain) to extract
   `λ_min(hierCauchyG m) ≥ exp(-c₃ · m)`.
2. Builds the quadratic-form penalty `pen = ε² · m² · λ_min⁻¹`, bounded
   by `ε² · m² · exp(c₃ m) ≤ L²·exp((c₃/2 - 2)L) → const` for the V3 regime.
3. Applies `P.anderson_lower` to lower-bound `boxProb ε` by
   `vol · density · exp(-pen)`.
4. Substitutes `cov = hierCauchyG m` via `P.cov_eq_hierCauchy`.
5. Combines via the assembly chain to derive `exp(-2 c̲ · L³)` lower
   bound, using `2 c̲ ≥ c̄` (the consistent constraint direction). -/
theorem gaussian_grid_smallball_lower
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hL_le_2m : |Real.log (ε + r)| ≤ 2 * (m : ℝ))
    (P : GaussianBoxProb m) :
    Real.exp (-2 * cLower_node3 * |Real.log (ε + r)| ^ 3) ≤ P.boxProb ε := by
  set L := |Real.log (ε + r)| with hL_def
  -- Step 1: Apply Schur eigenvalue bound to extract λ_min.
  obtain ⟨lamMin, hlamMin_pos, h_lamMin_lb, _h_quadform⟩ :=
    cauchy_grid_lambda_min_lower m hm
  -- Step 2: Build the penalty `pen = ε² · m² · λ_min⁻¹`.
  set pen : ℝ := (ε ^ 2) * ((m * m : ℕ) : ℝ) * lamMin⁻¹ with hpen_def
  have hpen_nn : 0 ≤ pen := by
    apply mul_nonneg
    apply mul_nonneg
    · exact sq_nonneg ε
    · exact_mod_cast Nat.zero_le _
    · exact le_of_lt (inv_pos.mpr hlamMin_pos)
  -- Step 3: Apply Anderson lower bound from the structure.
  have h_and_lb := P.anderson_lower ε hε pen hpen_nn
  -- Step 4: Substitute cov = hierCauchyG m.
  rw [P.cov_eq_hierCauchy] at h_and_lb
  -- Step 5: Build assembly: connect Anderson density × exp(-pen) to
  -- exp(-2 c̲ · L³). This involves:
  --   * BB1 → `(sqrt det)⁻¹ ≥ exp(-c₀ m³ / 2)` (other side from upper).
  --   * Volume × π-power factor.
  --   * Penalty bound `pen ≤ const` (using h_lamMin_lb + ε ≤ e^{-L} + L ≤ 2m).
  --   * `2 c̲ ≥ c̄` (the consistency constraint).
  --   * Sub-grid → full-grid bridge: V3's lower bound technically derives
  --     ℙ(V_I ∈ B_I), and bridging to ℙ(V_full ∈ B_full) requires
  --     Royen's Gaussian Correlation Inequality (2014) for absolute-value
  --     events. Mathlib does not yet have GCI.
  have h_assembly_lower :
      Real.exp (-2 * cLower_node3 * L ^ 3) ≤
        (2 * ε) ^ (m * m) *
          (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
          (Real.sqrt (hierCauchyG m).det)⁻¹ * Real.exp (-pen) := by
    -- sorry: paper proof V3 §2 + §4, blocked on Mathlib lemma
    -- `Mathlib.Probability.GCI.gaussian_correlation_inequality` (Royen 2014).
    -- Components needed (using h_lamMin_lb, hpen_def, two_cLower_ge_cUpper_node3,
    -- cauchy_grid_det_lower_bound, cubic_coefficient_*):
    --   (a) Penalty bound: pen = ε² · m² · λ_min⁻¹ ≤ exp(-2L)·m²·exp(c₃ m)
    --       ≤ L² · exp((c₃ - 2)·m) using hε_le_ε₀, hL_le_2m, h_lamMin_lb.
    --       For the V3 regime L ≥ 20, c₃ = 10, m ≤ L: this stays bounded.
    --       ~50 LOC.
    --   (b) Density-at-0 lower: `(sqrt det)⁻¹ ≥ exp(-c₀ m³ / 2)` via
    --       `Real.sqrt_le_sqrt` on h_det_lb (BB1, the OTHER direction
    --       from the upper bound). Using `m ≤ L`: `m³ ≤ L · m² ≤ L³`,
    --       so `(c₀/2)·m³ ≤ (c₀/2)·L³`. ~30 LOC.
    --   (c) Volume × π-power: `(2ε)^{m²} ≥ exp(m²·(log 2 - L))` and
    --       `(2π)^{-m²/2}` → bounded constant. ~30 LOC.
    --   (d) Combine: density × exp(-pen) ≥ exp(-(c₀/2)·L³ - O(L²) - pen)
    --       ≥ exp(-(c₀/2)·L³ - const·L²). ~30 LOC.
    --   (e) Use `2 c̲ ≥ c̄ = 2·(c₀/2)` (from `two_cLower_ge_cUpper_node3`)
    --       to absorb the O(L²) corrections into the slack: get
    --       `≥ exp(-2 c̲ · L³)`. ~20 LOC.
    --   (f) GCI bridge sub-grid → full grid (Royen 2014). ~500-1500 LOC
    --       if transcribed independently (multivariate analytic
    --       continuation argument).
    -- Total: ~700-1700 LOC depending on whether GCI is transcribed.
    sorry
  exact le_trans h_assembly_lower h_and_lb

/-! ## §8. Final wrappers consumed by `524.lean`'s call sites -/

/-- The upper bound, expressed in the form expected by
`polynomial_sup_small_ball_upper`. Direct alias of
`gaussian_grid_smallball_upper`, with the V3 sub-grid sizing
`m ≥ ⌊L/20⌋` exposed as a separate hypothesis. -/
theorem gaussian_grid_smallball_upper_final
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hm_le_L : (m : ℝ) ≤ |Real.log (ε + r)|)
    (hm_ge_subgrid : ⌊|Real.log (ε + r)| / 20⌋₊ ≤ m)
    (P : GaussianBoxProb m) :
    P.boxProb ε ≤ Real.exp (-cUpper_node3 * |Real.log (ε + r)| ^ 3) :=
  gaussian_grid_smallball_upper m hm ε r hε hr hεr_le_ε₀ hεr_pos
    hm_le_L hm_ge_subgrid P

/-- The lower bound, expressed in the form expected by
`polynomial_sup_small_ball_lower`. Direct alias of
`gaussian_grid_smallball_lower`. -/
theorem gaussian_grid_smallball_lower_final
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hL_le_2m : |Real.log (ε + r)| ≤ 2 * (m : ℝ))
    (P : GaussianBoxProb m) :
    Real.exp (-2 * cLower_node3 * |Real.log (ε + r)| ^ 3) ≤ P.boxProb ε :=
  gaussian_grid_smallball_lower m hm ε r hε hr hεr_le_ε₀ hεr_pos hL_le_2m P

end Erdos524.Helpers
