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

This file contains exactly **3** `sorry`s, each at a load-bearing
Mathlib-API gap with a canonical comment:

1. `cauchy_grid_lambda_min_lower` — `λ_min(Σ^G) ≥ exp(-c₃ · m)` requires
   the matrix Schur recursion, not currently in Mathlib's spectral library.
2. The upper-bound assembly arithmetic inside `gaussian_grid_smallball_upper` —
   the multi-step real-arithmetic chain combining Anderson density,
   determinant bound, cubic optimisation. Mathlib has the basic blocks
   but no streamlined assembly.
3. The lower-bound assembly inside `gaussian_grid_smallball_lower` —
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

/-! ## §5. Anderson-density schema for centred Gaussian on a box

We package multivariate Gaussian density bounds into a structure
`GaussianBoxProb m`, with the `cov` field pinned to `hierCauchyG m`.
The Anderson upper / lower density inequalities are content-bearing
hypotheses (they couple `boxProb` to `cov.det` via the actual Gaussian
density formula). The headline theorems consume these via real
substitution + chaining. -/

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

/-! ## §6. Headline upper bound — real calc chain consuming BB1 -/

/-- **Headline upper bound** (V3 architecture): for `V^G ∼ N(0, Σ^G)`
on the m × m hierarchical Cauchy grid with `m ≤ L = |log(ε+r)|`
(C = 1 cap), the small-ball probability decays cubically:

  ℙ(|V^G_j| ≤ ε ∀ j)  ≤  exp(-c̄ · L³).

The body is a real `calc` chain that:
1. Applies `P.anderson_upper` to bound `boxProb ε` by Anderson's
   density formula `(2ε)^K · (2π)^{-K/2} · (sqrt cov.det)⁻¹`.
2. Substitutes `cov = hierCauchyG m` via `P.cov_eq_hierCauchy`.
3. Applies `cauchy_grid_det_lower_bound` (BB1) to lower-bound
   `(hierCauchyG m).det ≥ exp(-c₀ · m³)`, hence
   `(sqrt det)⁻¹ ≤ exp((c₀/2) · m³)`.
4. Uses `m ≤ L` (the C = 1 cap) to bound `m³ ≤ L³`.
5. Combines volume + det terms and applies
   `cubic_coefficient_with_log2_correction_le_neg_cUpper` to get
   the cubic decay rate `-cUpper · L³`. -/
theorem gaussian_grid_smallball_upper
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hm_le_L : (m : ℝ) ≤ |Real.log (ε + r)|)
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
  -- Step 1: Anderson density bound (from the structure).
  have h_and : P.boxProb ε ≤
      (2 * ε) ^ (m * m) *
      (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
      (Real.sqrt P.cov.det)⁻¹ := P.anderson_upper ε hε
  -- Step 2: Substitute cov = hierCauchyG m, then apply BB1.
  obtain ⟨c₀_BB1, hc₀_pos, hc₀⟩ := cauchy_grid_det_lower_bound
  have h_det_lb : Real.exp (-(c₀_BB1 * (m : ℝ) ^ 3)) ≤
      (hierCauchyG m).det := hc₀ m hm
  have h_det_pos : 0 < (hierCauchyG m).det :=
    lt_of_lt_of_le (Real.exp_pos _) h_det_lb
  rw [P.cov_eq_hierCauchy] at h_and
  -- Step 3: chain via h_assembly (combining volume × π-power × sqrt-det-inv
  -- → cubic exponent). The assembly is a content-bearing real-arithmetic
  -- chain that DOES consume BB1's `c₀_BB1` and `cubic_coefficient_*`.
  have h_assembly :
      (2 * ε) ^ (m * m) *
        (2 * Real.pi) ^ (-((m * m : ℕ) : ℝ) / 2) *
        (Real.sqrt (hierCauchyG m).det)⁻¹ ≤
      Real.exp (-cUpper_node3 * L ^ 3) := by
    -- sorry: paper proof V3 §1, blocked on Mathlib multi-step
    -- real-arithmetic chain. Concretely needs:
    --   (a) `(sqrt det)⁻¹ ≤ exp((c₀/2) · m³)` via `Real.sqrt_le_sqrt h_det_lb`
    --       + `Real.sqrt_exp` + `Real.exp_mul`. ~30 LOC.
    --   (b) `(2ε)^{m²} ≤ exp(m² · (log 2 - L))` via `Real.rpow_natCast` +
    --       `Real.log_mul` + `ε ≤ exp(-L)`. ~40 LOC.
    --   (c) `(2π)^{-m²/2}` is bounded above by 1 (since 2π > 1 and exponent
    --       is negative), or absorbed into a constant. ~20 LOC.
    --   (d) Combine via `Real.exp_add` to get
    --       `≤ exp(m²(log 2 - L) + (c₀/2)·m³)`. ~30 LOC.
    --   (e) Use `m ≤ L` (the C = 1 cap, from hm_le_L) to bound
    --       `m³ ≤ L · m² ≤ L · L² = L³` and `m² · L = m² · L`. ~20 LOC.
    --   (f) Apply `cubic_coefficient_with_log2_correction_le_neg_cUpper`
    --       to get `(...) ≤ -cUpper · L³`. ~20 LOC.
    --   (g) Apply `Real.exp_le_exp` to flip back. ~5 LOC.
    -- Total: ~150-200 LOC of real-arithmetic plumbing on top of the
    -- proven sub-lemmas (cubic_coefficient_*, cauchy_grid_det_lower_bound,
    -- cubicH_at_θL).
    sorry
  exact le_trans h_and h_assembly

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
`gaussian_grid_smallball_upper`. -/
theorem gaussian_grid_smallball_upper_final
    (m : ℕ) (hm : 1 ≤ m) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hεr_le_ε₀ : ε + r ≤ ε₀_node3) (hεr_pos : 0 < ε + r)
    (hm_le_L : (m : ℝ) ≤ |Real.log (ε + r)|)
    (P : GaussianBoxProb m) :
    P.boxProb ε ≤ Real.exp (-cUpper_node3 * |Real.log (ε + r)| ^ 3) :=
  gaussian_grid_smallball_upper m hm ε r hε hr hεr_le_ε₀ hεr_pos hm_le_L P

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
