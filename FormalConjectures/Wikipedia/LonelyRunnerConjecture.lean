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

import FormalConjectures.Wikipedia.LonelyRunnerConjecture.FiniteRigidity

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

/-- Convert a bounded bit-vector modular identity into the corresponding
identity in `ZMod`. The bounds record that the eight-bit calculations in the
finite certificate do not overflow. -/
@[category API, AMS 11]
lemma bitVec_mod_eq_zmod {q : ℕ} (hq : 0 < q) (hq8 : q < 8) (x y k : ℕ)
    (hk : k < 15)
    (h : (BitVec.ofNat 3 (x % q)).zeroExtend 8 =
      (BitVec.ofNat 3 (y % q)).zeroExtend 8 * BitVec.ofNat 8 k %
        BitVec.ofNat 8 q) :
    (x : ZMod q) = (y : ZMod q) * k := by
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_mul,
    BitVec.toNat_umod] at hn
  have hq256 : q < 256 := lt_trans hq8 (by norm_num)
  have hx8 : x % q < 8 := lt_trans (Nat.mod_lt _ hq) hq8
  have hx256 : x % q < 256 := lt_trans (Nat.mod_lt _ hq) hq256
  have hy8 : y % q < 8 := lt_trans (Nat.mod_lt _ hq) hq8
  have hy256 : y % q < 256 := lt_trans (Nat.mod_lt _ hq) hq256
  have hk256 : k < 256 := lt_trans hk (by norm_num)
  have hprod : (y % q) * k < 256 := by
    nlinarith [Nat.mod_lt y hq]
  simp only [Nat.mod_eq_of_lt hq256, Nat.mod_eq_of_lt hx8, Nat.mod_eq_of_lt hx256,
    Nat.mod_eq_of_lt hy8, Nat.mod_eq_of_lt hy256, Nat.mod_eq_of_lt hk256,
    Nat.mod_eq_of_lt hprod] at hn
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  change x % q = y * k % q
  simpa [Nat.mul_mod] using hn

/-- Reduce the fourteen standard representatives modulo `q` into the
three-bit representation used by the finite certificate. -/
def residuesMod (q : ℕ) (a : ResidueVector) : BVResidueVector where
  c0 := BitVec.ofNat 3 ((a 0).val % q)
  c1 := BitVec.ofNat 3 ((a 1).val % q)
  c2 := BitVec.ofNat 3 ((a 2).val % q)
  c3 := BitVec.ofNat 3 ((a 3).val % q)
  c4 := BitVec.ofNat 3 ((a 4).val % q)
  c5 := BitVec.ofNat 3 ((a 5).val % q)
  c6 := BitVec.ofNat 3 ((a 6).val % q)
  c7 := BitVec.ofNat 3 ((a 7).val % q)
  c8 := BitVec.ofNat 3 ((a 8).val % q)
  c9 := BitVec.ofNat 3 ((a 9).val % q)
  c10 := BitVec.ofNat 3 ((a 10).val % q)
  c11 := BitVec.ofNat 3 ((a 11).val % q)
  c12 := BitVec.ofNat 3 ((a 12).val % q)
  c13 := BitVec.ofNat 3 ((a 13).val % q)

@[category API, AMS 11]
lemma residuesModThree_allLt (a : ResidueVector) : AllLt 3 (residuesMod 3 a) := by
  have hthree : (3 : BitVec 3).toNat = 3 := by decide
  simp only [AllLt, residuesMod, BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat,
    hthree]
  omega

@[category API, AMS 11]
lemma residuesModFive_allLt (a : ResidueVector) : AllLt 5 (residuesMod 5 a) := by
  have hfive : (5 : BitVec 3).toNat = 5 := by decide
  simp only [AllLt, residuesMod, BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat,
    hfive]
  omega

/-- The bit-vector affine conclusion modulo three implies the semantic
`ZMod 3` affine conclusion. -/
@[category API, AMS 11]
lemma affineModThree_to_isAffine (a : ResidueVector)
    (h : AffineModThree (residuesMod 3 a)) :
    IsAffineMod 3 a ((a 0).val : ZMod 3) := by
  unfold AffineModThree at h
  rcases h with
    ⟨⟨⟨h0, h1, h2⟩, ⟨⟨h3, h4⟩, h5, h6⟩⟩,
      ⟨⟨h7, h8, h9⟩, ⟨⟨h10, h11⟩, h12, h13⟩⟩⟩
  intro i
  have hbit :
      (BitVec.ofNat 3 ((a i).val % 3)).zeroExtend 8 =
        (BitVec.ofNat 3 ((a 0).val % 3)).zeroExtend 8 * BitVec.ofNat 8 (i.val + 1) %
          BitVec.ofNat 8 3 := by
    fin_cases i <;> simp only [residuesMod] at * <;> assumption
  have hz := bitVec_mod_eq_zmod (by norm_num) (by norm_num) (a i).val (a 0).val
    (i.val + 1) (by omega) hbit
  simpa only [Nat.cast_add, Nat.cast_one] using hz

/-- The bit-vector affine conclusion modulo five implies the semantic
`ZMod 5` affine conclusion. -/
@[category API, AMS 11]
lemma affineModFive_to_isAffine (a : ResidueVector)
    (h : AffineModFive (residuesMod 5 a)) :
    IsAffineMod 5 a ((a 0).val : ZMod 5) := by
  unfold AffineModFive at h
  rcases h with
    ⟨⟨⟨h0, h1, h2⟩, ⟨⟨h3, h4⟩, h5, h6⟩⟩,
      ⟨⟨h7, h8, h9⟩, ⟨⟨h10, h11⟩, h12, h13⟩⟩⟩
  intro i
  have hbit :
      (BitVec.ofNat 3 ((a i).val % 5)).zeroExtend 8 =
        (BitVec.ofNat 3 ((a 0).val % 5)).zeroExtend 8 * BitVec.ofNat 8 (i.val + 1) %
          BitVec.ofNat 8 5 := by
    fin_cases i <;> simp only [residuesMod] at * <;> assumption
  have hz := bitVec_mod_eq_zmod (by norm_num) (by norm_num) (a i).val (a 0).val
    (i.val + 1) (by omega) hbit
  simpa only [Nat.cast_add, Nat.cast_one] using hz

/-- Concrete computational blocking condition for multiplier five. -/
def BlocksCertifiedMultiplierFive (a : ResidueVector) : Prop :=
  BlocksRobustMultiplierFive (residuesMod 3 a)

/-- Concrete computational blocking condition for multiplier three. -/
def BlocksCertifiedMultiplierThree (a : ResidueVector) : Prop :=
  BlocksRobustMultiplierThree (residuesMod 5 a)

/-- The verified multiplier-five certificate supplies the semantic affine
conclusion modulo three. -/
@[category research solved, AMS 11]
theorem blocksCertifiedMultiplierFive_forces_affineModThree (a : ResidueVector)
    (h : BlocksCertifiedMultiplierFive a) :
    ∃ slope : ZMod 3, IsAffineMod 3 a slope := by
  refine ⟨((a 0).val : ZMod 3), affineModThree_to_isAffine a ?_⟩
  exact blocks_robust_multiplier_five_forces_affine_mod_three (residuesMod 3 a)
    (residuesModThree_allLt a) h

/-- The verified multiplier-three certificate supplies the semantic affine
conclusion modulo five. -/
@[category research solved, AMS 11]
theorem blocksCertifiedMultiplierThree_forces_affineModFive (a : ResidueVector)
    (h : BlocksCertifiedMultiplierThree a) :
    ∃ slope : ZMod 5, IsAffineMod 5 a slope := by
  refine ⟨((a 0).val : ZMod 5), affineModFive_to_isAffine a ?_⟩
  exact blocks_robust_multiplier_three_forces_affine_mod_five (residuesMod 5 a)
    (residuesModFive_allLt a) h

/-- Terminal contradiction with the concrete 270-pattern certificates wired
in. Unlike `terminal_contradiction_of_finite_rigidity`, this theorem has no
abstract finite-rigidity hypotheses. -/
@[category research solved, AMS 11]
theorem terminal_contradiction_of_certified_patterns (a : ResidueVector)
    (hzero : ∃ i, a i = 0)
    (h3survives : SurvivesEveryOmission 3 a)
    (h5survives : SurvivesEveryOmission 5 a)
    (hblocks3 : BlocksCertifiedMultiplierThree a)
    (hblocks5 : BlocksCertifiedMultiplierFive a) : False := by
  exact affine_mod_three_and_five_terminal_contradiction a hzero h3survives h5survives
    (blocksCertifiedMultiplierFive_forces_affineModThree a hblocks5)
    (blocksCertifiedMultiplierThree_forces_affineModFive a hblocks3)

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
