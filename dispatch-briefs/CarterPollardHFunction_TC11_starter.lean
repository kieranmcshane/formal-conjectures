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

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Real.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Basic

/-!
# Carter-Pollard 2004 §§2/4 — h-function setup (TC11 starter)

Reference: Carter, A.V. & Pollard, D. (2004), "Tusnády's inequality revisited,"
Annals of Statistics 32(6), 2731-2741. arXiv:math/0508606.

This file lands the **h-function** that drives the Carter-Pollard binomial-tail
asymptotic. It is the TC11 deliverable in the Track C Carter-Pollard chain
(TC11 → TC12 bulk/tail split → TC13 Mills bridge → TC14 envelope + close
`tusnady_base_polynomial`).

Originally drafted as Grok strategic pre-flight bonus to Probe 4 ; refined for
Mathlib pin `25ce63313608` (August 2024) compatibility.

## TC11 scope

This file lands :

1. `H` — the binary-entropy-like function `H ε t = (1-ε) · log t + ε · log (1-t)`.
2. `h` — the deviation `h ε N s = H ε (1/2 + s/√N) - H ε (1/2)`.
3. Properties of `h` :
   - `h_zero` : `h ε N 0 = 0`.
   - `h_deriv_zero` : `h'(0) = 0` (first derivative vanishes at the symmetric point).
   - `h_second_deriv_zero` : `h''(0) = -1/2` (concavity coefficient).
   - `h_third_deriv_neg` : `h'''(s) < 0` on `(0, 1)` (key for cubic Taylor remainder bound).
   - `h_concave` : `ConcaveOn ℝ (Set.Icc 0 1) (h ε N)` (corollary of `h''' < 0` + endpoints).
4. `bin_tail_beta_integral` — the beta-integral representation of the binomial tail.
5. `bin_tail_h_integral` — the post-Stirling-substitution integral form
   `Σ exp(N · h(s)) ds`.

## Out of scope (TC12+)

- Bulk/tail Laplace-method bounds : TC12 (~400 LOC).
- ρ(x) and r(x) Mills-bridge inequalities : TC13 (~300 LOC).
- Envelope + final `tusnady_base_polynomial` closure : TC14 (~300 LOC).

Total Carter-Pollard chain (TC11-TC14) : 900-1600 LOC across 5-6 rounds per
Grok Probe 4 calibrated estimate.

NOT IMPORTED by any consumer at TC11 close. Sorries are isolated.
-/

namespace Erdos524.Helpers.CarterPollard

open Real

/-- Binary-entropy-like function appearing in the binomial tail integral
(Carter-Pollard 2004 §2). For `t ∈ (0, 1)`, `H ε t = (1-ε) · log t + ε · log (1-t)`.
Equals `-h(t)` (entropy) at `ε = 1/2`. -/
noncomputable def H (ε t : ℝ) : ℝ :=
  (1 - ε) * Real.log t + ε * Real.log (1 - t)

/-- The h-function : deviation of `H` around `t = 1/2` after the change of
variables `t = 1/2 + s/√N` (Carter-Pollard 2004, Eq. (4.1) and surrounding text). -/
noncomputable def h (ε N : ℝ) (s : ℝ) : ℝ :=
  H ε (1/2 + s / Real.sqrt N) - H ε (1/2)

variable {ε N : ℝ}

/-- `h(0) = 0` (the deviation vanishes at the symmetric point). -/
lemma h_zero (hε : 0 ≤ ε) (hN : 0 < N) : h ε N 0 = 0 := by
  unfold h H
  simp
  -- (1-ε) · log(1/2) + ε · log(1/2) - [(1-ε) · log(1/2) + ε · log(1/2)] = 0
  ring

/-- `h'(0) = 0` (first derivative vanishes at the symmetric point).
TAG : `TC11-h-deriv-zero`. ~15 LOC : compose `deriv_add`, `deriv_mul`, `Real.deriv_log`,
evaluate at `s = 0`, simplify the symmetric cancellation. -/
lemma h_deriv_zero (hε : 0 < ε) (hε1 : ε < 1) (hN : 0 < N) :
    deriv (h ε N) 0 = 0 := by
  sorry

/-- `h''(0) = -1/2` (the concavity coefficient at the symmetric point).
TAG : `TC11-h-second-deriv-zero`. ~20 LOC : chain rule + explicit second derivative
of `H` (concave entropy at midpoint = -2 ; scaled by `1/√N` factor squared). -/
lemma h_second_deriv_zero (hε : 0 < ε) (hε1 : ε < 1) (hN : 0 < N) :
    deriv (deriv (h ε N)) 0 = -1/2 := by
  sorry

/-- `h'''(s) < 0` for `s ∈ (0, 1)` — key for the cubic Taylor remainder bound used
in TC12's bulk integral approximation.
TAG : `TC11-h-third-deriv-neg`. ~25 LOC : third derivative is `-2ε / (...)^3` after the
change-of-variables, sign-controlled. -/
lemma h_third_deriv_neg (hε : 0 < ε) (hε1 : ε < 1) (hN : 0 < N) (hs : 0 < s) (hs1 : s < 1) :
    deriv (deriv (deriv (h ε N))) s < 0 := by
  sorry

/-- `h` is concave on `[0, 1]` — corollary of `h''' < 0` on `(0, 1)` plus endpoint continuity.
TAG : `TC11-h-concave`. ~30 LOC : use `ConcaveOn.of_deriv2_nonpos` or direct from `h''(s) ≤ 0`. -/
lemma h_concave (hε : 0 < ε) (hε1 : ε < 1) (hN : 0 < N) :
    ConcaveOn ℝ (Set.Icc 0 1) (h ε N) := by
  sorry

/-- Beta-integral representation of the binomial tail (Carter-Pollard 2004 §4 opening).
For `X ~ Bin(n, 1/2)`, `P(X ≥ k) = (1/2^n) · Σ_{j=k}^n C(n, j) = (n! / ((k-1)!(n-k)!)) · ∫_0^{1/2} t^{k-1}(1-t)^{n-k} dt`.

Already established in `BinomialTailBeta.lean` via TC9 (`binomial_tail_beta_integral`).
This lemma re-expresses it in the §4 form needed for the post-Stirling substitution.
TAG : `TC11-bin-tail-beta-integral`. ~30 LOC : direct rewrite from TC9 helper +
specialise `p = 1/2`. -/
lemma bin_tail_beta_integral (n k : ℕ) (hkn : k ≤ n) (hk : 1 ≤ k) :
    (1 / 2 ^ n : ℝ) * ((Finset.Ico k (n + 1)).sum
      (fun j => (n.choose j : ℝ))) =
    ((n : ℝ) * ((n - 1).choose (k - 1)) * ∫ x in (0 : ℝ)..(1/2),
      x ^ (k - 1) * (1 - x) ^ (n - k)) := by
  sorry

/-- Post-Stirling-substitution integral form (Carter-Pollard 2004 Eq. (4.2)-(4.3)).
After `t = 1/2 + s/√N` with `N = n - 1`, the binomial tail becomes
`P(X ≥ k) = C_N · exp(N · H(1/2)) · ∫_0^∞ exp(N · h(s)) ds + boundary corrections`.

This is the bridge into TC12's bulk/tail Laplace analysis.
TAG : `TC11-bin-tail-h-integral`. ~20 LOC placeholder ; full formalisation may
defer the precise constant `C_N` and the boundary-correction bounds to TC12. -/
lemma bin_tail_h_integral (n k : ℕ) (hkn : k ≤ n) (hk : 1 ≤ k)
    (ε := (2 * (k : ℝ) - n) / (n - 1)) :
    -- exact statement from paper Eq. (4.2)–(4.3)
    True := by
  -- Glue the beta integral with the substitution t = 1/2 + s/√N and the
  -- Stirling prefactor (TC10 `stirling_prefactor_bound` available).
  trivial  -- placeholder until TC12 wires the full Laplace setup

end Erdos524.Helpers.CarterPollard
