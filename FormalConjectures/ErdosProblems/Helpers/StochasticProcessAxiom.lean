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

import FormalConjectures.ErdosProblems.Helpers.RademacherSequence
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Stepping-stone Itô-isometry axiom for KMT-aided Gaussian processes

This axiom encapsulates the upstream gap currently blocking the discharge
of `two_dim_KMT_coupling`'s sub-sorries (T3.1 Yplus / T3.2 Yminus /
T3.3-C4 coupling-error in `Helpers/TwoDimKMTFromOneDim.lean`):

* Mathlib + brownian-motion package do not yet expose stochastic-integral
  existence + L²-isometry for deterministic kernels parameterized by
  `(u : ℝ, k : ℕ, n : ℕ) ↦ ℝ`.
* Once that API lands upstream, `kmt_aided_gaussian_process` is provable
  in Lean as a theorem (combining Itô-integral construction +
  Kolmogorov–Chentsov sample-path regularity + KMT coupling on partial
  sums).
* Until then, axiomatized at the minimum level needed for our use case.

**Validation.**  Grok-validated R30 design (kernel-parametrized form,
atomicity sweet spot).  Net axiom count flat after `two_dim_KMT_coupling`
is replaced by theorem (R30 T-replace).

**Hypothesis-shape note (R30 → R33-A → R33-B → R33-C tightening).**
The R30 form used only the pointwise bound `|kernel u k n| ≤ 1`, which
is satisfied by the constant-`1` kernel — and that kernel produces a
partial sum that is asymptotically `N(0, 1)` and does NOT decay as
`u → ∞`, contradicting the conclusion's tail-decay conjunct.  R32's
audit (`Helpers/AxiomFoundationAudit.md`, A3-α) flagged this as the
"single-call hypothesis-too-weak" issue; R33-A's Grok pre-flight added
a second hypothesis `kernel_decay` that the constant-`1` kernel
violates.

R33-A used the literal Grok-supplied form
`∀ ε > 0, ∃ U, ∀ n ≥ 1, ∀ u ≥ U, ∀ k ≤ n, |kernel u k n| ≤ ε`, which is
unsatisfiable at `k = 0` for the R31 reparametrized kernels
(`kernel_even_plus u 0 m = √(1/2) · exp 0 = √(1/2)`).  R33-B retightened
to `1 ≤ k ≤ n`.  R33-B-debrief showed this pointwise form remains
unsatisfiable for `kernel_even_plus` at `(k = 1, n` large`)`.

**R33-C / Path A (Grok-validated).**  Replace the pointwise eventual
smallness with **normalized L²-energy decay** of the kernel:

```
kernel_decay : ∀ ε > 0, ∃ U > 0, ∀ n ≥ 1, ∀ u ≥ U,
    (1/n) · ∑_{k=1..n} (kernel u k n)² ≤ ε.
```

This form is satisfiable for `kernel_even_plus` with explicit witness
`U = 1/(4ε)`, via `a/(e^a − 1) ≤ 1` applied to `a = 2u/n` (geometric
sum bound on `(1/2)·∑exp(−2uk/n) ≤ 1/(4u)`). Sub-Gaussian tail control
on `Y` then follows from the Rademacher structure + Borel-Cantelli on
the integer grid + sample-path continuity.

See `Helpers/R33C_T1_KernelDecayAudit.md` for the audit verifying that
no other decay hypothesis (`kernel_geometric_decay`) exists in the
codebase, and `Helpers/AxiomFoundationAudit.md` for the broader
foundational reasoning.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory

/-- **R30 stepping-stone axiom: KMT-aided Gaussian process for bounded
deterministic kernels.**

Given a deterministic kernel `(u, k, n) ↦ ℝ` pointwise bounded by `1` on
`u ≥ 0`, there exists a measurable, continuous-sample-path Gaussian
process `Y : ℝ → Ω → ℝ` with a.s. tail decay, coupled to the partial
sum `(1/√n) ∑_k a_k · kernel(u, k, n)` with KMT-rate error
`log(n + 1) / √n` uniformly in `(n, ω, u)`.

This is the minimal axiom needed to close the 3 upstream-gated sorries
in `TwoDimKMTFromOneDim.lean` (T3.1, T3.2, T3.3-C4).  Apply once with
the Yplus kernel (`exp (-u * k / n)`), once with the Yminus kernel
(`(-exp (-u / n)) ^ k`).  Independence between the two applications is
recovered by even/odd decoupling of the Rademacher sequence (T3.4,
tractable in Mathlib).

**Status.**  Local stepping-stone, retired the moment Mathlib /
brownian-motion lands `MeasureTheory.StochasticIntegral.deterministic_L2_kernel`
(or equivalent). -/
axiom kmt_aided_gaussian_process
    (kernel : ℝ → ℕ → ℕ → ℝ)
    (_kernel_bound : ∀ u, 0 ≤ u → ∀ k n, |kernel u k n| ≤ 1)
    (_kernel_decay : ∀ ε > 0, ∃ U > 0, ∀ n : ℕ, 1 ≤ n → ∀ u ≥ U,
      (1 / (n : ℝ)) *
        (Finset.Icc 1 n).sum (fun k => (kernel u k n) ^ 2) ≤ ε)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha : Erdos524.IsRademacherSequence a) :
    ∃ (Y : ℝ → Ω → ℝ),
      (∀ u, Measurable (Y u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Y u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n, a k ω * kernel u k n) -
          Y u ω| ≤ Real.log (n + 1) / Real.sqrt n)

end Erdos524.Helpers
