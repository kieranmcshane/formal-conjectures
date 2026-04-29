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

import FormalConjectures.ErdosProblems.Helpers.GLWHierApprox
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Phase 2 / Node 4 — Discrete vs continuous box-probability comparison

For a real-valued process `Y : ℝ → Ω → ℝ` (in particular the GLW process
`Y_GLW` whose existence is asserted by Node 1B's stepping-stone axiom), we
relate two events:

* **Continuous box** — `{ω | ∀ u ∈ [0, T], |Y u ω| ≤ ε}` (sample-path
  small-ball over a compact time-interval);
* **Discrete box** — `{ω | ∀ i : Fin m × Fin m, |Y (hierTimes m i) ω| ≤ ε}`
  (the event we can analyse using the helper, since `K_GLW_matrix m` lives
  on the discrete index set).

This file ships **two deterministic set inclusions** between the events.
Both inclusions hold path-by-path; no probability hypothesis is used.

* `Y_box_continuous_subset_discrete` — the upper direction. Trivial set
  inclusion provided every `hierTimes m i ∈ [0, T]`.
* `Y_box_discrete_modulus_subset_continuous` — the lower direction. Uses
  a modulus-of-continuity event `Y_modulus_event` parameterised by `δ ∈ (0,1)`:
  if (a) every discrete value `|Y(hierTimes_i)|` is bounded by `(1-δ)ε`, and
  (b) every continuous time `u ∈ [0, T]` has a discrete neighbour
  `hierTimes_i` with `|Y(u) - Y(hierTimes_i)| ≤ δε`, then the continuous
  box at threshold `ε` holds.

The probabilistic content (the modulus event has high probability for the
GLW process — Borell + Kolmogorov–Chentsov) is the work of Node 6, not
Node 4. Node 4 isolates the deterministic combinatorics so Node 6 can
compose it with the Gaussian concentration bound.

The `Y_GLW` process from Node 1B is **not** referenced; everything is
parameterised over a generic `Y`. Once `Y_GLW_exists` ships, Node 6
extracts the existential and instantiates these set inclusions at the
specific `Y_GLW`.
-/

namespace Erdos524.Helpers
open Set

variable {Ω : Type*} (Y : ℝ → Ω → ℝ)

/-! ## Continuous and discrete box events -/

/-- Continuous box event — the path of `Y(·, ω)` stays bounded by `ε`
on `[0, T]`. -/
def Y_continuous_box (T ε : ℝ) : Set Ω :=
  {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, |Y u ω| ≤ ε}

/-- Discrete box event — the discrete sample `Y(hierTimes m i, ω)` is
bounded by `ε` for every index `i`. -/
def Y_discrete_box (m : ℕ) (ε : ℝ) : Set Ω :=
  {ω | ∀ i : Fin m × Fin m, |Y (hierTimes m i) ω| ≤ ε}

/-- The deterministic modulus-of-continuity event used by the lower
inclusion: every continuous time `u ∈ [0, T]` has a discrete neighbour
`hierTimes_i ∈ [0, T]` with `|Y(u) - Y(hierTimes_i)| ≤ δε`. -/
def Y_modulus_event (m : ℕ) (T δ ε : ℝ) : Set Ω :=
  {ω | ∀ u ∈ Set.Icc (0 : ℝ) T, ∃ i : Fin m × Fin m,
        hierTimes m i ∈ Set.Icc (0 : ℝ) T ∧
        |Y u ω - Y (hierTimes m i) ω| ≤ δ * ε}

/-! ## Upper inclusion — continuous box ⊆ discrete box

Trivial; just specialize the universal quantifier to `u = hierTimes m i`. -/

theorem Y_box_continuous_subset_discrete
    (m : ℕ) (T ε : ℝ)
    (h_in_T : ∀ i : Fin m × Fin m, hierTimes m i ∈ Set.Icc (0 : ℝ) T) :
    Y_continuous_box Y T ε ⊆ Y_discrete_box Y m ε := by
  intro ω hω i
  exact hω _ (h_in_T i)

/-! ## Lower inclusion — (discrete box at `(1-δ)ε`) ∩ modulus event ⊆ continuous box

Pure triangle inequality on the path: `|Y u| ≤ |Y u - Y(hierTimes_i)| +
|Y(hierTimes_i)| ≤ δε + (1-δ)ε = ε`. -/

theorem Y_box_discrete_modulus_subset_continuous
    (m : ℕ) (T δ ε : ℝ) :
    Y_discrete_box Y m ((1 - δ) * ε) ∩ Y_modulus_event Y m T δ ε ⊆
    Y_continuous_box Y T ε := by
  intro ω hω u hu
  obtain ⟨h_disc, h_mod⟩ := hω
  obtain ⟨i, _h_in_T, h_close⟩ := h_mod u hu
  have h_disc_i : |Y (hierTimes m i) ω| ≤ (1 - δ) * ε := h_disc i
  -- Triangle inequality: |Y u| ≤ |Y u - Y(hierTimes_i)| + |Y(hierTimes_i)|.
  have h_tri : |Y u ω| ≤
      |Y u ω - Y (hierTimes m i) ω| + |Y (hierTimes m i) ω| := by
    have h_split :
        Y u ω = (Y u ω - Y (hierTimes m i) ω) + Y (hierTimes m i) ω := by ring
    calc |Y u ω|
        = |(Y u ω - Y (hierTimes m i) ω) + Y (hierTimes m i) ω| := by
              rw [← h_split]
      _ ≤ |Y u ω - Y (hierTimes m i) ω| + |Y (hierTimes m i) ω| := abs_add_le _ _
  linarith

/-! ## Convenience corollary

Repackages the two-piece inclusion into a single set-relation form usable
by Node 6 when it composes this with the modulus-event probability bound. -/

theorem Y_continuous_box_le_discrete_via_modulus
    (m : ℕ) (T δ ε : ℝ)
    (h_in_T : ∀ i : Fin m × Fin m, hierTimes m i ∈ Set.Icc (0 : ℝ) T) :
    Y_continuous_box Y T ε ⊆ Y_discrete_box Y m ε ∧
    Y_discrete_box Y m ((1 - δ) * ε) ∩ Y_modulus_event Y m T δ ε ⊆
      Y_continuous_box Y T ε :=
  ⟨Y_box_continuous_subset_discrete Y m T ε h_in_T,
   Y_box_discrete_modulus_subset_continuous Y m T δ ε⟩

end Erdos524.Helpers
