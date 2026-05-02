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

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Real-valued Beta function (helper for Erdős problem 524)

Mathlib pin status (`mathlib4 @ 25ce633136`, verified TC6 T1.1):
  * `Complex.betaIntegral (u v : ℂ) : ℂ` ✅
    (`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60`),
  * `Real.Beta` ❌ (not packaged anywhere in `.lake/packages/mathlib/Mathlib/`).

This file provides a *local* `realBeta` definition via the standard real interval integral
form, together with the Beta-Gamma ratio identity in TAG'd-Stub form, to be filled in TC7+
when the polynomial-bound assembly for `tusnady_base_polynomial` requires Beta-function
moments of the binomial distribution. This avoids the cyclic blocker that the Tusnády
polynomial bound depends on real Beta-function identities while only the complex Beta
integral is packaged in pinned Mathlib.

## Lemmas (TC7+ closure targets)

* `realBeta_eq_Gamma_ratio`: `B(a, b) = Γ(a) · Γ(b) / Γ(a + b)` for `a, b > 0`.

The Beta-Gamma identity is a workhorse of Carter-Pollard 2004 §4 in computing the
binomial-Gaussian-pairing tail through moments of the form `∑ k (n choose k) p^k (1-p)^(n-k)`.
-/

namespace Erdos524.Helpers

open MeasureTheory
open scoped Real

/-- **Real-valued Beta function (local definition).**

For `a b : ℝ`, the Beta function is defined as
`B(a, b) = ∫_0^1 x^(a-1) · (1-x)^(b-1) dx`.

The integral converges for `a, b > 0`; outside this regime the value of the integral
may be undefined or infinite, but the `realBeta` definition is total (returning `0`
or whatever the underlying `intervalIntegral` returns when divergent). Use only with
positivity hypotheses on `a, b`.

This local definition matches the `Complex.betaIntegral` packaging in Mathlib up to
the real-vs-complex distinction; defining a real wrapper here avoids the cyclic blocker
that Tusnády polynomial bounds need real-Beta identities while pinned Mathlib only
provides the complex form. -/
noncomputable def realBeta (a b : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1)

/-- **Beta-Gamma ratio identity.**

For `a, b > 0`, `B(a, b) = Γ(a) · Γ(b) / Γ(a + b)`.

This is the workhorse of Carter-Pollard 2004 §4 in computing binomial-Gaussian-pairing
moments. Standard proof: derive from the substitution `x = u / (u + v)` in the double
integral `Γ(a) · Γ(b) = ∫∫ u^(a-1) v^(b-1) e^{-u-v} du dv`, then split via change of
variables to express as `Γ(a+b) · B(a,b)`. -/
theorem realBeta_eq_Gamma_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h_a_re : 0 < ((a : ℂ)).re := by simpa using ha
  have h_b_re : 0 < ((b : ℂ)).re := by simpa using hb
  -- Step 1: integrand identity on [0, 1].
  have h_integrand : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) =
        (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have h_one_sub : (0:ℝ) ≤ 1 - x := by linarith
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0 (a - 1),
        Complex.ofReal_cpow h_one_sub (b - 1)]
    push_cast
    ring
  -- Step 2: real-Beta-as-complex via integral_ofReal + integrand congruence.
  have h_realBeta : ((realBeta a b) : ℂ) = Complex.betaIntegral (a:ℂ) (b:ℂ) := by
    unfold realBeta Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr h_integrand
  -- Step 3: Beta-Gamma identity in ℂ + bridge to ℝ.
  have h_gamma : Complex.betaIntegral (a:ℂ) (b:ℂ) =
      ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div (a:ℂ) (b:ℂ) h_a_re h_b_re,
        Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        ← Complex.ofReal_add, Complex.Gamma_ofReal]
  -- Step 4: combine and use ℝ → ℂ injectivity.
  have : ((realBeta a b) : ℂ) =
      ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) : ℂ) :=
    h_realBeta.trans h_gamma
  exact_mod_cast this

end Erdos524.Helpers
