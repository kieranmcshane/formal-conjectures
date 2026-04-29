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

import FormalConjectures.ErdosProblems.Helpers.V1FieldsRoundup

/-!
# Phase 2 Round 4 — Tiny final lemmas.
-/

namespace Erdos524.Helpers

theorem hierGrid_sum_pos_explicit (m : ℕ) (i j : Fin m × Fin m) :
    0 < hierGrid m i + hierGrid m j := hierGrid_sum_pos m i j

theorem hierGrid_pos_explicit (m : ℕ) (i : Fin m × Fin m) : 0 < hierGrid m i :=
  hierGrid_pos m i

end Erdos524.Helpers
