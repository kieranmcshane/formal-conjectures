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

namespace Erdos524
namespace Helpers

open MeasureTheory ProbabilityTheory

/-- Bridge from independence of random variables to independence of preimage
events. If `f i : Ω → α i` are mutually independent measurable random
variables, then the preimage sets `f i ⁻¹' A i` are mutually independent (as
sets) for any family of measurable sets `A i`. -/
theorem iIndepSet_preimage_of_iIndepFun
    {ι Ω : Type*} {α : ι → Type*}
    {mΩ : MeasurableSpace Ω} {mα : ∀ i, MeasurableSpace (α i)}
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {f : ∀ i, Ω → α i}
    (hf : ProbabilityTheory.iIndepFun f μ)
    (hmeas : ∀ i, Measurable (f i))
    {A : ∀ i, Set (α i)} (hA : ∀ i, MeasurableSet (A i)) :
    ProbabilityTheory.iIndepSet (fun i => f i ⁻¹' A i) μ := by
  have hmeas_pre : ∀ i, MeasurableSet (f i ⁻¹' A i) := fun i => (hmeas i) (hA i)
  rw [iIndepSet_iff_meas_biInter hmeas_pre]
  intro s
  exact hf.measure_inter_preimage_eq_mul s (fun i _ => hA i)

end Helpers
end Erdos524
