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

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation

/-!
# `IsRademacherSequence` predicate

The `Erdos524.IsRademacherSequence` structure was originally declared in
`524.lean` (between the file's load-bearing `open MeasureTheory …` block and
the `randomPoly` / `supNorm` definitions).  R29 / KMT Option C requires
helper files (`OneDimKMT`, `TwoDimKMTFromOneDim`) to mention the predicate
in their statements while themselves being **imported** by `524.lean` — so
the predicate is relocated here, behind a tiny non-cyclic dependency on
`Mathlib.Probability.Independence.Basic`.

Re-export is achieved by `524.lean` importing this file; the `Erdos524`
namespace is unchanged from the consumer's perspective.
-/

namespace Erdos524

open MeasureTheory ProbabilityTheory

/--
A sequence `a : ℕ → Ω → ℝ` is an i.i.d. Rademacher sequence if the random
variables `a k` are mutually independent and each takes values `1` and `-1`
with probability `1/2`.
-/
structure IsRademacherSequence
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) : Prop where
  /-- The random variables `(a k)` are mutually independent. -/
  indep : ProbabilityTheory.iIndepFun (fun k : ℕ => a k) ℙ
  /-- Each `a k` is a measurable function. -/
  measurable (k : ℕ) : Measurable (a k)
  /-- Each `a k` takes value `1` with probability `1/2`. -/
  prob_pos (k : ℕ) : ℙ {ω | a k ω = 1} = 1 / 2
  /-- Each `a k` takes value `-1` with probability `1/2`. -/
  prob_neg (k : ℕ) : ℙ {ω | a k ω = -1} = 1 / 2

end Erdos524
