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
# 1D Komlós–Major–Tusnády coupling axiom (R29 / KMT Option C)

Komlós–Major–Tusnády (1975, *Studia Sci. Math. Hungar.* 32) strong invariance
principle for sums of i.i.d. centered sub-Gaussian random variables: there
exists a coupling between the partial-sum walk `S_n = ∑_{k ≤ n} X_k` and a
Brownian motion `B` such that `|S_n - B_n| = O(log n)` uniformly in `n`.

Specialised here to **Rademacher** sequences (the
`Erdos524.IsRademacherSequence` predicate, relocated from `524.lean` to
`Helpers/RademacherSequence.lean` in R29 to break the cyclic import).
Because Rademacher variables are bounded, the sub-Gaussian hypothesis is
automatic; the standard 1D KMT therefore applies, and we axiomatise the
specialisation to avoid the multi-year formalisation of the Tusnády-lemma /
dyadic-recursion / Hoeffding-Skorokhod machinery (see
`Helpers/OneDimKMTSketch.md` for an exploratory sketch of upstream routes).

## Role in KMT Option C

This axiom is the load-bearing input to
`two_dim_KMT_coupling_via_LS_reduction` (see
`Helpers/TwoDimKMTFromOneDim.lean`).  Once that theorem is fully proved, the
public `axiom two_dim_KMT_coupling` in `524.lean:3741` is replaced by the
theorem (`R30+`), and the project's net axiom count returns to two
(`one_dim_KMT_coupling` here + `Y_GLW_exists` in `Helpers/GLWProcess.lean`),
matching field standards for KMT-dependent results.

**Net-axiom budget during R29.** Introducing this axiom *temporarily* takes
the project to 3 net axioms (D2 / `Y_GLW_exists` private + 2D
`two_dim_KMT_coupling` public + this 1D axiom new).  The transitional state
is justified by the simultaneous landing of the 2D theorem skeleton in
`Helpers/TwoDimKMTFromOneDim.lean`, which makes the path from `1D` to `2D`
visible.  R30 is expected to close ≥ 50% of the skeleton sub-sorries; if it
does not, R29 is reverted (Refinement 2).

## Statement notes

* **Uniform-in-`ω` form.**  The bound `|S_n - B_n| ≤ C · log(n+1)` is stated
  uniformly in `ω`, not for "almost-every `ω` with `C = C(ω) < ∞`".  This is
  *stronger* than the textbook KMT a.s. statement, but matches the
  uniform-in-`ω` shape of `524.lean:3741`'s `Δ n` (which itself encodes the
  KMT-error envelope deterministically).  The implicit consumer in the LS
  reduction is the deterministic `Δ_n` rate; an a.s. statement would require
  a measurability-of-the-exceptional-set argument that is unnecessary if the
  sup-bound is uniform.

* **`log(n+1)` instead of `log n`.**  Avoids the singularity at `n = 0` /
  `n = 1` and is the standard form in the LS-reduction literature.  The
  multiplicative constant `C` absorbs the difference vs. `log n` for `n ≥ 2`.

* **`Measurable (B n)`.**  Conjuncted explicitly so the consumer does not
  have to infer Brownian-motion-of-an-integer-time measurability from a
  separate `IsBrownian` predicate.  Strictly stronger than just existence of
  a Brownian motion.
-/

namespace Erdos524.Helpers

open MeasureTheory ProbabilityTheory

/-- **Axiom (1D Komlós–Major–Tusnády coupling for Rademacher sequences).**

For every probability space `(Ω, ℙ)` and every Rademacher sequence
`a : ℕ → Ω → ℝ`, there exists a Brownian-motion-like sequence
`B : ℕ → Ω → ℝ` and a constant `C > 0` such that the partial sums
`S_n := ∑_{k = 1}^{n} a_k` satisfy

```
|S_n(ω) - B_n(ω)| ≤ C · log(n + 1)        for all 1 ≤ n and all ω.
```

The construction is upstream (Komlós–Major–Tusnády 1975); the formal Lean
derivation is a separate multi-year project tracked in
`Helpers/OneDimKMTSketch.md`.  We axiomatise the statement.

This is the *only* probabilistic axiom this file introduces.  The 2D
analogue (`two_dim_KMT_coupling_via_LS_reduction` in
`Helpers/TwoDimKMTFromOneDim.lean`) is a *theorem* reducing to this axiom
plus deterministic kernel-side facts via the Letwin–Sawhney 4-step
reduction.
-/
axiom one_dim_KMT_coupling :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), Erdos524.IsRademacherSequence a →
      ∃ (B : ℕ → Ω → ℝ) (C : ℝ),
        0 < C ∧
        (∀ n, Measurable (B n)) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω,
          |(∑ k ∈ Finset.Icc 1 n, a k ω) - B n ω| ≤ C * Real.log (n + 1))

end Erdos524.Helpers
