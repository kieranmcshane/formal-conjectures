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

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-!
# Binomial-tail Beta-integral representation (Carter–Pollard 2004 §3 Step 1)

Mathlib pin status (verified TC9 T1.1):
  * `intervalIntegral.integral_hasDerivAt_right` ✅ (FTC right-endpoint)
  * `eq_of_has_deriv_right_eq` ✅ (derivative-matching)
  * `Nat.add_one_mul_choose_eq`, `Nat.choose_mul_succ_eq` ✅ (Pascal-adjacent identities)

Provides the local **incomplete-Beta-as-binomial-tail** identity in
real-polynomial form:

  `Σ_{j=k}^{m} C(m, j) · p^j · (1-p)^(m-j) = m · C(m-1, k-1) · ∫_0^p x^(k-1) (1-x)^(m-k) dx`

for `1 ≤ k ≤ m` and `0 ≤ p ≤ 1`. The `m · C(m-1, k-1)` factor equals
`m! / ((k-1)! · (m-k)!) = 1 / B(k, m - k + 1)`.

**Step 1 of Carter–Pollard polynomial bound assembly**; the `PMF.binomial`
bridge is deferred to TC10.

## Proof: derivative matching

Both sides are functions of `p ∈ [0, 1]` with right-derivative
`m · C(m-1, k-1) · p^(k-1) · (1-p)^(m-k)` and equal at `p = 0`. Apply
`eq_of_has_deriv_right_eq`. -/

namespace Erdos524.Helpers

open MeasureTheory intervalIntegral
open scoped Topology NNReal ENNReal Nat

/-- The binomial tail polynomial as a function of `p`:
`Σ_{j=k}^{m} C(m, j) · p^j · (1-p)^(m-j)`. -/
noncomputable def binomialPolyTail (m k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico k (m + 1), (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

/-- The partial Beta integral: `∫_0^p x^(k-1) (1-x)^(m-k) dx`. -/
noncomputable def betaPartialIntegral (m k : ℕ) (p : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..p, x ^ (k - 1) * (1 - x) ^ (m - k)

/-! ### Auxiliary algebraic identities -/

/-- `j · C(m, j) = m · C(m-1, j-1)` for `1 ≤ j ≤ m`, in ℝ. -/
lemma natCast_j_mul_choose_eq (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (j : ℝ) * (m.choose j : ℝ) = (m : ℝ) * ((m - 1).choose (j - 1) : ℝ) := by
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hj)
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.one_le_iff_ne_zero.mp (le_trans hj hjm))
  have h := Nat.add_one_mul_choose_eq m' j'
  -- h : (m' + 1) * choose m' j' = choose (m' + 1) (j' + 1) * (j' + 1)
  have h_R : ((m' + 1 : ℕ) : ℝ) * (m'.choose j' : ℝ) =
      (((m' + 1).choose (j' + 1) : ℕ) : ℝ) * ((j' + 1 : ℕ) : ℝ) := by exact_mod_cast h
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  push_cast
  push_cast at h_R
  linarith

/-- `(m - j) · C(m, j) = m · C(m-1, j)` for `j ≤ m` and `1 ≤ m`, in ℝ. -/
lemma natCast_sub_mul_choose_eq (m j : ℕ) (hjm : j ≤ m) (hm : 1 ≤ m) :
    ((m - j : ℕ) : ℝ) * (m.choose j : ℝ) = (m : ℝ) * ((m - 1).choose j : ℝ) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  have h := Nat.choose_mul_succ_eq m' j
  -- h : m'.choose j * (m' + 1) = (m' + 1).choose j * (m' + 1 - j)
  have hjm' : j ≤ m' + 1 := hjm
  have h_R : (m'.choose j : ℝ) * ((m' + 1 : ℕ) : ℝ) =
      (((m' + 1).choose j : ℕ) : ℝ) * (((m' + 1 - j : ℕ) : ℕ) : ℝ) := by exact_mod_cast h
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  push_cast
  push_cast at h_R
  linarith

/-! ### Termwise derivative -/

/-- Derivative of `(1 - p)^n` at `p`. -/
lemma hasDerivAt_oneSub_pow (n : ℕ) (p : ℝ) :
    HasDerivAt (fun q : ℝ => (1 - q) ^ n) (-(n : ℝ) * (1 - p) ^ (n - 1)) p := by
  have h_id : HasDerivAt (fun q : ℝ => 1 - q) (-1 : ℝ) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have hp := h_id.pow n
  -- hp : HasDerivAt (fun q => (1-q)^n) (n * (1-p)^(n-1) * (-1)) p
  convert hp using 1
  ring

/-- Derivative of `p^j · (1-p)^(m-j)` at `p`. -/
lemma hasDerivAt_term (m j : ℕ) (p : ℝ) :
    HasDerivAt (fun q : ℝ => q ^ j * (1 - q) ^ (m - j))
      ((j : ℝ) * p ^ (j - 1) * (1 - p) ^ (m - j) -
        ((m - j : ℕ) : ℝ) * p ^ j * (1 - p) ^ (m - j - 1)) p := by
  have h_pow : HasDerivAt (fun q : ℝ => q ^ j) ((j : ℝ) * p ^ (j - 1) * 1) p := by
    have := (hasDerivAt_id p).pow j
    simpa using this
  have h_one_sub : HasDerivAt (fun q : ℝ => (1 - q) ^ (m - j))
      (-((m - j : ℕ) : ℝ) * (1 - p) ^ (m - j - 1)) p :=
    hasDerivAt_oneSub_pow (m - j) p
  have hmul := h_pow.mul h_one_sub
  -- hmul: HasDerivAt (fun q => q^j * (1-q)^(m-j)) ((j*p^(j-1)*1) * (1-p)^(m-j) +
  --   p^j * (-(m-j)*(1-p)^(m-j-1))) p
  convert hmul using 1
  ring

/-! ### Telescoping identity -/

/-- Standard telescoping sum identity. -/
lemma sum_Ico_sub_telescope (f : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (f j - f (j + 1)) = f a - f b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    ring

/-! ### LHS derivative: termwise derivatives + telescoping collapse -/

/-- The "telescoping summand" `S_j(p) := m · C(m-1, j-1) · p^(j-1) · (1-p)^(m-j)`. -/
noncomputable def telescopeS (m j : ℕ) (p : ℝ) : ℝ :=
  (m : ℝ) * ((m - 1).choose (j - 1) : ℝ) * p ^ (j - 1) * (1 - p) ^ (m - j)

/-- For `1 ≤ j ≤ m` and `1 ≤ m`: termwise derivative of
`C(m,j) · p^j · (1-p)^(m-j)` equals `S_j(p) - S_{j+1}(p)`. -/
lemma hasDerivAt_choose_term_eq_telescope (m j : ℕ)
    (hj : 1 ≤ j) (hjm : j ≤ m) (hm : 1 ≤ m) (p : ℝ) :
    HasDerivAt (fun q : ℝ => (m.choose j : ℝ) * (q ^ j * (1 - q) ^ (m - j)))
      (telescopeS m j p - telescopeS m (j + 1) p) p := by
  have h_term := (hasDerivAt_term m j p).const_mul (m.choose j : ℝ)
  -- h_term : HasDerivAt (fun q => C(m,j) * (q^j * (1-q)^(m-j)))
  --   (C(m,j) * ((j : ℝ) * p^(j-1) * (1-p)^(m-j) -
  --     ((m-j : ℕ) : ℝ) * p^j * (1-p)^(m-j-1))) p
  have h1 : (j : ℝ) * (m.choose j : ℝ) =
      (m : ℝ) * ((m - 1).choose (j - 1) : ℝ) :=
    natCast_j_mul_choose_eq m j hj hjm
  have h2 : ((m - j : ℕ) : ℝ) * (m.choose j : ℝ) =
      (m : ℝ) * ((m - 1).choose j : ℝ) :=
    natCast_sub_mul_choose_eq m j hjm hm
  have hj1 : j + 1 - 1 = j := by omega
  have hmj : m - (j + 1) = m - j - 1 := by omega
  -- Reduce the goal value `telescopeS m j p - telescopeS m (j+1) p` symbolically.
  have h_value :
      telescopeS m j p - telescopeS m (j + 1) p =
        (m.choose j : ℝ) * ((j : ℝ) * p ^ (j - 1) * (1 - p) ^ (m - j) -
          ((m - j : ℕ) : ℝ) * p ^ j * (1 - p) ^ (m - j - 1)) := by
    unfold telescopeS
    rw [hj1, hmj]
    -- (m * C(m-1, j-1) * p^(j-1) * (1-p)^(m-j))
    --   - (m * C(m-1, j) * p^j * (1-p)^(m-j-1))
    -- = C(m,j) * (j * p^(j-1) * (1-p)^(m-j) - (m-j) * p^j * (1-p)^(m-j-1))
    rw [show (m : ℝ) * ((m - 1).choose (j - 1) : ℝ) =
          (j : ℝ) * (m.choose j : ℝ) from h1.symm,
        show (m : ℝ) * ((m - 1).choose j : ℝ) =
          ((m - j : ℕ) : ℝ) * (m.choose j : ℝ) from h2.symm]
    ring
  rw [h_value]
  exact h_term

/-- The LHS derivative: termwise sum telescopes to `S_k(p) - S_{m+1}(p) = S_k(p)`. -/
lemma hasDerivAt_binomialPolyTail (m k : ℕ)
    (hk : 1 ≤ k) (hkm : k ≤ m) (p : ℝ) :
    HasDerivAt (binomialPolyTail m k)
      ((m : ℝ) * ((m - 1).choose (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (m - k)) p := by
  have hm : 1 ≤ m := le_trans hk hkm
  -- Step 1: rewrite `binomialPolyTail m k` as Σ over Ico of `C(m,j) * (q^j * (1-q)^(m-j))`.
  have h_eq : binomialPolyTail m k = fun q : ℝ =>
      ∑ j ∈ Finset.Ico k (m + 1), (m.choose j : ℝ) * (q ^ j * (1 - q) ^ (m - j)) := by
    funext q
    unfold binomialPolyTail
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_eq]
  -- Step 2: termwise derivative.
  have h_each : ∀ j ∈ Finset.Ico k (m + 1),
      HasDerivAt (fun q : ℝ => (m.choose j : ℝ) * (q ^ j * (1 - q) ^ (m - j)))
        (telescopeS m j p - telescopeS m (j + 1) p) p := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨hkj, hjm⟩ := hj
    have hj_pos : 1 ≤ j := le_trans hk hkj
    have hjm' : j ≤ m := Nat.lt_succ_iff.mp hjm
    exact hasDerivAt_choose_term_eq_telescope m j hj_pos hjm' hm p
  have h_sum := HasDerivAt.fun_sum h_each
  -- Step 3: telescope the derivative value.
  have hkm1 : k ≤ m + 1 := le_trans hkm (Nat.le_succ m)
  have h_telescope :
      (∑ j ∈ Finset.Ico k (m + 1), (telescopeS m j p - telescopeS m (j + 1) p)) =
        telescopeS m k p - telescopeS m (m + 1) p :=
    sum_Ico_sub_telescope (fun j => telescopeS m j p) hkm1
  rw [h_telescope] at h_sum
  -- Step 4: telescopeS m (m+1) p = 0 since C(m-1, m) = 0.
  have h_boundary : telescopeS m (m + 1) p = 0 := by
    unfold telescopeS
    have hidx : (m + 1 : ℕ) - 1 = m := by omega
    rw [hidx]
    have h_zero : (m - 1).choose m = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h_zero]
    push_cast
    ring
  rw [h_boundary, sub_zero] at h_sum
  -- Step 5: telescopeS m k p = m * C(m-1, k-1) * p^(k-1) * (1-p)^(m-k).
  unfold telescopeS at h_sum
  exact h_sum

/-! ### Integral side derivative (FTC right) -/

/-- Continuity of the integrand `x^(k-1) · (1-x)^(m-k)`. -/
lemma continuous_betaIntegrand (m k : ℕ) :
    Continuous (fun x : ℝ => x ^ (k - 1) * (1 - x) ^ (m - k)) := by
  exact (continuous_id.pow _).mul ((continuous_const.sub continuous_id).pow _)

/-- Integrability of the integrand on any interval. -/
lemma intervalIntegrable_betaIntegrand (m k : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ (k - 1) * (1 - x) ^ (m - k)) volume a b :=
  (continuous_betaIntegrand m k).intervalIntegrable a b

/-- FTC right: derivative of `betaPartialIntegral m k` at `p` is the integrand at `p`. -/
lemma hasDerivAt_betaPartialIntegral (m k : ℕ) (p : ℝ) :
    HasDerivAt (betaPartialIntegral m k) (p ^ (k - 1) * (1 - p) ^ (m - k)) p :=
  intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_betaIntegrand m k 0 p)
    (continuous_betaIntegrand m k).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_betaIntegrand m k).continuousAt

/-! ### Initial conditions at `p = 0` -/

lemma binomialPolyTail_zero (m k : ℕ) (hk : 1 ≤ k) :
    binomialPolyTail m k 0 = 0 := by
  unfold binomialPolyTail
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  have hj_pos : 1 ≤ j := le_trans hk hj.1
  have : (0 : ℝ) ^ j = 0 := zero_pow (Nat.one_le_iff_ne_zero.mp hj_pos)
  rw [this]
  ring

lemma betaPartialIntegral_zero (m k : ℕ) :
    betaPartialIntegral m k 0 = 0 := by
  unfold betaPartialIntegral
  exact intervalIntegral.integral_same

/-! ### Main theorem: Beta-integral representation of binomial tail -/

/-- **Carter–Pollard 2004 §3 Step 1**: incomplete-Beta-as-binomial-tail identity.

For `1 ≤ k ≤ m` and `0 ≤ p ≤ 1`:

  `Σ_{j=k}^{m} C(m, j) · p^j · (1-p)^(m-j) =
     m · C(m-1, k-1) · ∫_0^p x^(k-1) (1-x)^(m-k) dx`

The factor `m · C(m-1, k-1) = m! / ((k-1)! · (m-k)!) = 1 / B(k, m-k+1)`. -/
theorem binomial_tail_beta_integral
    (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialPolyTail m k p =
      ((m : ℝ) * ((m - 1).choose (k - 1) : ℝ)) * betaPartialIntegral m k p := by
  -- Define `g(p) := constant · betaPartialIntegral m k p` and show
  -- `binomialPolyTail m k p = g p` via derivative matching.
  set C : ℝ := (m : ℝ) * ((m - 1).choose (k - 1) : ℝ) with hC_def
  -- Both functions are differentiable everywhere with matching derivative.
  have h_deriv_lhs : ∀ x : ℝ, HasDerivAt (binomialPolyTail m k)
      (C * x ^ (k - 1) * (1 - x) ^ (m - k)) x := by
    intro x
    have := hasDerivAt_binomialPolyTail m k hk hkm x
    simpa [hC_def, mul_assoc] using this
  have h_deriv_rhs : ∀ x : ℝ, HasDerivAt (fun q => C * betaPartialIntegral m k q)
      (C * x ^ (k - 1) * (1 - x) ^ (m - k)) x := by
    intro x
    have h_int := hasDerivAt_betaPartialIntegral m k x
    have := h_int.const_mul C
    simpa [mul_assoc] using this
  -- Apply `eq_of_has_deriv_right_eq` on `[0, 1]`.
  have h_diff_lhs : ∀ x ∈ Set.Ico (0:ℝ) 1,
      HasDerivWithinAt (binomialPolyTail m k)
        (C * x ^ (k - 1) * (1 - x) ^ (m - k)) (Set.Ici x) x :=
    fun x _ => (h_deriv_lhs x).hasDerivWithinAt
  have h_diff_rhs : ∀ x ∈ Set.Ico (0:ℝ) 1,
      HasDerivWithinAt (fun q => C * betaPartialIntegral m k q)
        (C * x ^ (k - 1) * (1 - x) ^ (m - k)) (Set.Ici x) x :=
    fun x _ => (h_deriv_rhs x).hasDerivWithinAt
  have h_cont_lhs : ContinuousOn (binomialPolyTail m k) (Set.Icc (0:ℝ) 1) :=
    (continuous_iff_continuousAt.mpr
      (fun x => (h_deriv_lhs x).continuousAt)).continuousOn
  have h_cont_rhs : ContinuousOn (fun q => C * betaPartialIntegral m k q)
      (Set.Icc (0:ℝ) 1) :=
    (continuous_iff_continuousAt.mpr
      (fun x => (h_deriv_rhs x).continuousAt)).continuousOn
  have h_init : binomialPolyTail m k 0 = C * betaPartialIntegral m k 0 := by
    rw [binomialPolyTail_zero m k hk, betaPartialIntegral_zero m k]
    ring
  have h_eq := eq_of_has_deriv_right_eq h_diff_lhs h_diff_rhs h_cont_lhs h_cont_rhs h_init
  exact h_eq p ⟨hp0, hp1⟩

/-! ### Stirling prefactor and PMF.binomial bridge (Carter–Pollard 2004 §3 Step 2)

The prefactor `m · C(m-1, k-1)` from Step 1 admits the explicit upper bound
`m^k / (k-1)!` (asymptotically sharp, but proved here without invoking
Stirling's asymptotic). The binomial-tail polynomial then bridges to the
PMF.binomial tail probability for use by downstream KMT-style couplings. -/

/-- ℕ-level identity: `m · (C(m-1, k-1) · (k-1)!) = m.descFactorial k` for
`1 ≤ k ≤ m`.

Combines `Nat.choose_mul_factorial_mul_factorial` with
`Nat.factorial_mul_descFactorial` to express the binomial-tail prefactor as a
falling factorial. -/
lemma m_mul_choose_mul_factorial_eq_descFactorial
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    m * ((m - 1).choose (k - 1) * (k - 1)!) = m.descFactorial k := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m - k))
  have h_split : (m - 1) - (k - 1) = m - k := by omega
  have hkm1 : k - 1 ≤ m - 1 := by omega
  have h1 : (m - 1).choose (k - 1) * (k - 1)! * (m - k)! = (m - 1)! := by
    have := Nat.choose_mul_factorial_mul_factorial hkm1
    rwa [h_split] at this
  have h2 : (m - k)! * m.descFactorial k = m ! := Nat.factorial_mul_descFactorial hkm
  calc m * ((m - 1).choose (k - 1) * (k - 1)!) * (m - k)!
      = m * ((m - 1).choose (k - 1) * (k - 1)! * (m - k)!) := by ring
    _ = m * (m - 1)! := by rw [h1]
    _ = m ! := Nat.mul_factorial_pred (by omega)
    _ = (m - k)! * m.descFactorial k := h2.symm
    _ = m.descFactorial k * (m - k)! := Nat.mul_comm _ _

/-- **Stirling prefactor explicit bound** (Carter–Pollard 2004 §3 Step 2):
`m · C(m-1, k-1) ≤ m^k / (k-1)!` for `1 ≤ k ≤ m`, in ℝ.

Elementary explicit bound via `Nat.descFactorial_le_pow`; does not invoke
Stirling's asymptotic. Asymptotic sharpness
(`m · C(m-1, k-1) = (1+o(1)) · m^k / (k-1)!` as `m → ∞`) is not proved here. -/
theorem stirling_prefactor_bound {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (m : ℝ) * ((m - 1).choose (k - 1) : ℝ) ≤ (m : ℝ) ^ k / ((k - 1).factorial : ℝ) := by
  have hfact_pos : (0 : ℝ) < ((k - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  rw [le_div_iff₀ hfact_pos]
  have h_eq : m * ((m - 1).choose (k - 1) * (k - 1)!) = m.descFactorial k :=
    m_mul_choose_mul_factorial_eq_descFactorial hk hkm
  have h_le : m.descFactorial k ≤ m ^ k := Nat.descFactorial_le_pow m k
  have key : m * ((m - 1).choose (k - 1) * (k - 1)!) ≤ m ^ k := h_eq ▸ h_le
  have key_R : ((m * ((m - 1).choose (k - 1) * (k - 1)!) : ℕ) : ℝ)
      ≤ ((m ^ k : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at key_R
  linarith

/-! ### PMF.binomial bridge corollary -/

/-- **PMF.binomial bridge corollary** (Carter–Pollard 2004 §3 Step 2):
the analytic binomial-tail polynomial `binomialPolyTail m k p` equals the
PMF.binomial tail probability `P(X ≥ k)` for `X ~ Binomial(m, p)`.

For `1 ≤ k ≤ m` and `p : ℝ≥0` with `p ≤ 1`:

  `binomialPolyTail m k (p:ℝ) =
     ((PMF.binomial p h m).toOuterMeasure {i | k ≤ (i : ℕ)}).toReal`

Connects the analytic Step-1 identity (`binomial_tail_beta_integral`) to the
probabilistic interface used downstream by KMT-style couplings. -/
theorem binomialPolyTail_eq_pmf_tail
    {m k : ℕ} (_hk : 1 ≤ k) (_hkm : k ≤ m)
    (p : ℝ≥0) (h : p ≤ 1) :
    binomialPolyTail m k (p : ℝ) =
      (((PMF.binomial p h m).toOuterMeasure
        {i : Fin (m + 1) | k ≤ (i : ℕ)})).toReal := by
  -- Convert the Set to a Finset for sum extraction.
  set S : Finset (Fin (m + 1)) :=
    Finset.filter (fun i : Fin (m + 1) => k ≤ (i : ℕ)) Finset.univ with hS_def
  have hSet_eq : ((↑S : Set (Fin (m + 1)))) =
      {i : Fin (m + 1) | k ≤ (i : ℕ)} := by
    ext i; simp [hS_def]
  rw [← hSet_eq, PMF.toOuterMeasure_apply_finset]
  -- Distribute toReal over the finite ENNReal sum.
  rw [ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top _ _)]
  -- Re-index from S (Fin (m+1)) to Finset.Ico k (m+1) (ℕ) via i ↦ i.val.
  unfold binomialPolyTail
  symm
  refine Finset.sum_bij (fun (i : Fin (m + 1)) (_ : i ∈ S) => i.val) ?_ ?_ ?_ ?_
  · -- i ∈ S → i.val ∈ Finset.Ico k (m+1)
    intro i hi
    have hi' : k ≤ (i : ℕ) := by simpa [hS_def] using hi
    exact Finset.mem_Ico.mpr ⟨hi', i.isLt⟩
  · -- injectivity on S
    intro a _ b _ hab
    exact Fin.ext hab
  · -- surjectivity onto Finset.Ico k (m+1)
    intro j hj
    rcases Finset.mem_Ico.mp hj with ⟨hjk, hjm⟩
    refine ⟨⟨j, hjm⟩, ?_, rfl⟩
    simp [hS_def, hjk]
  · -- function values match: (binomial p h m i).toReal as a real summand
    intro i hi
    have hi_le : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    have hp1 : (↑p : ℝ≥0∞) ≤ 1 := by exact_mod_cast h
    rw [PMF.binomial_apply]
    -- The exponent `(Fin.last m - i : ℕ)` elaborates to `↑(Fin.last m) - ↑i` in ℕ.
    simp only [Fin.val_last]
    -- Distribute `.toReal` over the ENNReal product, then collapse coercions.
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
        ENNReal.toReal_sub_of_le hp1 ENNReal.one_ne_top, ENNReal.toReal_one,
        ENNReal.coe_toReal, ENNReal.toReal_natCast]
    ring

end Erdos524.Helpers
