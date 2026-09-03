/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Lonely runner conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Lonely_runner_conjecture)
-/

namespace LonelyRunnerConjecture

namespace CompositeTerminalRigidity

/-- A vector of fourteen residues modulo fifteen, represented by their standard
representatives in `Fin 15`. -/
abbrev ResidueVector := Fin 14 → Fin 15

/-- A phase pattern records one of the fifteen bins occupied by each of the
fourteen coordinates. -/
abbrev PhasePattern := Fin 14 → Fin 15

/-- The residue vector has affine reduction modulo `q`, with slope `slope`.
The coordinate `i : Fin 14` represents the mathematical index `i + 1`. -/
def IsAffineMod (q : ℕ) (a : ResidueVector) (slope : ZMod q) : Prop :=
  ∀ i, ((a i).val : ZMod q) = slope * (i.val + 1)

/-- The gcd escape clause fails modulo `q`: after omitting any one coordinate,
some remaining coordinate is still nonzero modulo `q`. -/
def SurvivesEveryOmission (q : ℕ) (a : ResidueVector) : Prop :=
  ∀ omitted, ∃ i, i ≠ omitted ∧ ((a i).val : ZMod q) ≠ 0

/-- The residue vector blocks a phase pattern for the given multiplier when at
least one coordinate lands in boundary bin zero or fourteen. -/
def Blocks (multiplier : ℕ) (a : ResidueVector) (b : PhasePattern) : Prop :=
  ∃ i, (multiplier * (a i).val + (b i).val) % 15 = 0 ∨
    (multiplier * (a i).val + (b i).val) % 15 = 14

/-- Every phase pattern in `patterns` is blocked by `a`. -/
def BlocksEvery (multiplier : ℕ) (patterns : Set PhasePattern)
    (a : ResidueVector) : Prop :=
  ∀ b ∈ patterns, Blocks multiplier a b

/-- The exact finite certificate needed at a multiplier: blocking every robust
phase pattern forces an affine reduction modulo `q`. -/
def FiniteRigidityCertificate (q multiplier : ℕ) (patterns : Set PhasePattern) : Prop :=
  ∀ a, BlocksEvery multiplier patterns a → ∃ slope : ZMod q, IsAffineMod q a slope

/-- A fourteen-coordinate vector modulo `15 * 17 = 255`. -/
abbrev LiftVector17 := Fin 14 → Fin 255

/-- The explicit improper level-fifteen lift at `p = 17`. -/
def counterexample17_lift : LiftVector17 :=
  ![120, 240, 105, 225, 90, 40, 75, 246, 60, 180, 45, 12, 30, 235]

/-- A level-fifteen grid witness at `p = 17` keeps every product residue between
`17` and `238`, inclusive. These are exactly the residues at circular distance
at least `1 / 15` from zero modulo `255`. -/
def HasLevelFifteenGridWitnessAt17 (u : LiftVector17) : Prop :=
  ∃ j : Fin 255, ∀ i, 17 ≤ (j.val * (u i).val) % 255 ∧
    (j.val * (u i).val) % 255 ≤ 238

/-- The displayed vector is a lift of `(1, ..., 14)` modulo seventeen. -/
@[category test, AMS 11]
theorem counterexample17_is_tight_lift :
    ∀ i, (counterexample17_lift i).val % 17 = i.val + 1 := by
  native_decide

/-- Exact exhaustive verification that the displayed vector has no witness on
the 255-point level-fifteen grid. -/
@[category test, AMS 11]
theorem counterexample17_has_no_grid_witness :
    ¬ HasLevelFifteenGridWitnessAt17 counterexample17_lift := by
  unfold HasLevelFifteenGridWitnessAt17 counterexample17_lift
  native_decide

/-- Residues modulo fifteen of the explicit `p = 17` lift. -/
def counterexample17_residues : ResidueVector :=
  ![0, 0, 0, 0, 0, 10, 0, 6, 0, 0, 0, 12, 0, 10]

/-- The listed residue vector is exactly the reduction modulo fifteen of the
explicit lift. -/
@[category test, AMS 11]
theorem counterexample17_residues_eq_reduction :
    ∀ i, (counterexample17_residues i).val = (counterexample17_lift i).val % 15 := by
  native_decide

/-- Exact verification that the explicit lift also evades the gcd clause: after
any omission there remains a nonzero coordinate modulo both three and five. -/
@[category test, AMS 11]
theorem counterexample17_survives_every_omission :
    SurvivesEveryOmission 3 counterexample17_residues ∧
      SurvivesEveryOmission 5 counterexample17_residues := by
  constructor <;> unfold SurvivesEveryOmission counterexample17_residues <;> native_decide

/-- Failure of the gcd escape clause supplies a coordinate which is nonzero
modulo `q`. -/
@[category API, AMS 11]
lemma exists_nonzero_mod_of_survives_every_omission {q : ℕ} {a : ResidueVector}
    (h : SurvivesEveryOmission q a) : ∃ i, ((a i).val : ZMod q) ≠ 0 := by
  obtain ⟨i, -, hi⟩ := h 0
  exact ⟨i, hi⟩

/-- An affine slope modulo `q` is nonzero when some coordinate of the vector is
nonzero modulo `q`. -/
@[category API, AMS 11]
lemma affine_slope_ne_zero {q : ℕ} {slope : ZMod q} {a : ResidueVector}
    (haffine : IsAffineMod q a slope)
    (hnonzero : ∃ i, ((a i).val : ZMod q) ≠ 0) : slope ≠ 0 := by
  rintro hslope
  obtain ⟨i, hi⟩ := hnonzero
  have h := haffine i
  simp only [hslope, zero_mul] at h
  exact hi h

/-- The arithmetic kernel of the composite-modulus terminal argument.

If a fourteen-coordinate residue vector survives every omission modulo both
three and five, and its reductions are affine modulo both primes, then no
coordinate can vanish modulo fifteen. The key point is that a zero coordinate
at mathematical index `i + 1` would force that index to be divisible by both
three and five, which is impossible for an index from one through fourteen. -/
@[category research solved, AMS 11]
theorem no_zero_coordinate_of_affine_mod_three_and_five (a : ResidueVector)
    (h3survives : SurvivesEveryOmission 3 a)
    (h5survives : SurvivesEveryOmission 5 a)
    (h3affine : ∃ slope : ZMod 3, IsAffineMod 3 a slope)
    (h5affine : ∃ slope : ZMod 5, IsAffineMod 5 a slope) :
    ∀ i, a i ≠ 0 := by
  obtain ⟨slope3, h3affine⟩ := h3affine
  obtain ⟨slope5, h5affine⟩ := h5affine
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hslope3ne : slope3 ≠ 0 :=
    affine_slope_ne_zero h3affine (exists_nonzero_mod_of_survives_every_omission h3survives)
  have hslope5ne : slope5 ≠ 0 :=
    affine_slope_ne_zero h5affine (exists_nonzero_mod_of_survives_every_omission h5survives)
  intro i hi
  have h3 := h3affine i
  have h5 := h5affine i
  simp only [hi, Fin.val_zero, Nat.cast_zero] at h3 h5
  have hindex3 : ((i.val + 1 : ℕ) : ZMod 3) = 0 :=
    by simpa using (mul_eq_zero.mp h3.symm).resolve_left hslope3ne
  have hindex5 : ((i.val + 1 : ℕ) : ZMod 5) = 0 :=
    by simpa using (mul_eq_zero.mp h5.symm).resolve_left hslope5ne
  have hdiv3 : 3 ∣ i.val + 1 := (ZMod.natCast_eq_zero_iff _ _).mp hindex3
  have hdiv5 : 5 ∣ i.val + 1 := (ZMod.natCast_eq_zero_iff _ _).mp hindex5
  obtain ⟨k3, hk3⟩ := hdiv3
  obtain ⟨k5, hk5⟩ := hdiv5
  omega

/-- Contradictory form of `no_zero_coordinate_of_affine_mod_three_and_five`,
matching the final step of the proposed level-fifteen terminal proof. -/
@[category research solved, AMS 11]
theorem affine_mod_three_and_five_terminal_contradiction (a : ResidueVector)
    (hzero : ∃ i, a i = 0)
    (h3survives : SurvivesEveryOmission 3 a)
    (h5survives : SurvivesEveryOmission 5 a)
    (h3affine : ∃ slope : ZMod 3, IsAffineMod 3 a slope)
    (h5affine : ∃ slope : ZMod 5, IsAffineMod 5 a slope) : False := by
  obtain ⟨i, hi⟩ := hzero
  exact no_zero_coordinate_of_affine_mod_three_and_five a h3survives h5survives
    h3affine h5affine i hi

/-- The terminal contradiction with the two finite rigidity certificates made
explicit. Multiplier five yields affine structure modulo three, while
multiplier three yields affine structure modulo five. This theorem isolates
the exhaustive 270-pattern verification as the only computational input to
the final arithmetic step. -/
@[category research solved, AMS 11]
theorem terminal_contradiction_of_finite_rigidity
    (patterns : Set PhasePattern) (a : ResidueVector)
    (hzero : ∃ i, a i = 0)
    (h3survives : SurvivesEveryOmission 3 a)
    (h5survives : SurvivesEveryOmission 5 a)
    (hblocks3 : BlocksEvery 3 patterns a)
    (hblocks5 : BlocksEvery 5 patterns a)
    (hrigidity3 : FiniteRigidityCertificate 3 5 patterns)
    (hrigidity5 : FiniteRigidityCertificate 5 3 patterns) : False := by
  exact affine_mod_three_and_five_terminal_contradiction a hzero h3survives h5survives
    (hrigidity3 a hblocks5) (hrigidity5 a hblocks3)

end CompositeTerminalRigidity

/--
Consider $n$ runners on a circular track of unit length. At the initial time
$t = 0$, all runners are at the same position and start to run; the runners'
speeds are constant, all distinct, and may be negative. A runner is said to be
lonely at time $t$ if they are at a distance (measured along the circle) of at
least $\frac 1 n$ from every other runner. The lonely runner conjecture states that each
runner is lonely at some time, no matter the choice of speeds.
-/
@[category research open, AMS 11]
theorem lonely_runner_conjecture (n : ℕ)
    (speed : Fin n ↪ ℝ) (lonely : Fin n → ℝ → Prop)
    (lonely_def :
      ∀ r t, lonely r t ↔
        ∀ r2 : Fin n, r2 ≠ r →
        dist (t * speed r : UnitAddCircle) (t * speed r2) ≥ 1 / n)
    (r : Fin n) : ∃ t ≥ 0, lonely r t := by
  sorry

end LonelyRunnerConjecture
