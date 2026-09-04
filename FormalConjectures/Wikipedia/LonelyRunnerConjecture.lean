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

/-- A fourteen-coordinate level-fifteen lift modulo `15 * p`. -/
abbrev LiftVector (p : ℕ) := Fin 14 → Fin (15 * p)

/-- A lift represents the tight row `(1, ..., 14)` modulo `p`. -/
def IsTightLift (p : ℕ) (u : LiftVector p) : Prop :=
  ∀ i, (u i).val % p = i.val + 1

/-- A level-fifteen grid witness keeps every product residue in the closed
interval from `p` to `14 * p`. -/
def HasLevelFifteenGridWitness (p : ℕ) (u : LiftVector p) : Prop :=
  ∃ j : Fin (15 * p), ∀ i,
    p ≤ (j.val * (u i).val) % (15 * p) ∧
      (j.val * (u i).val) % (15 * p) ≤ 14 * p

/-- The level-fifteen gcd escape clause. Since the only prime factors of
fifteen are three and five, this is the concrete form needed here. -/
def HasLevelFifteenGcdEscape {p : ℕ} (u : LiftVector p) : Prop :=
  ∃ omitted, (∀ i, i ≠ omitted → 3 ∣ (u i).val) ∨
    (∀ i, i ≠ omitted → 5 ∣ (u i).val)

/-- Properness at level fifteen: either the gcd clause or the finite-grid
witness clause succeeds. -/
def IsLevelFifteenProper (p : ℕ) (u : LiftVector p) : Prop :=
  HasLevelFifteenGcdEscape u ∨ HasLevelFifteenGridWitness p u

/-- Standard representatives modulo fifteen of a lifted vector. -/
def liftResidues {p : ℕ} (u : LiftVector p) : ResidueVector :=
  fun i ↦ ⟨(u i).val % 15, Nat.mod_lt _ (by norm_num)⟩

@[simp, category API, AMS 11]
lemma liftResidues_val {p : ℕ} (u : LiftVector p) (i : Fin 14) :
    (liftResidues u i).val = (u i).val % 15 := rfl

/-- If all residues modulo fifteen are nonzero, the grid point `j = p`
(corresponding to time `1 / 15`) is already a witness. -/
@[category API, AMS 11]
theorem gridWitness_of_all_residues_nonzero {p : ℕ} (hp : 0 < p)
    (u : LiftVector p) (hnonzero : ∀ i, liftResidues u i ≠ 0) :
    HasLevelFifteenGridWitness p u := by
  refine ⟨⟨p, by nlinarith⟩, ?_⟩
  intro i
  have hmodpos : 0 < (u i).val % 15 := by
    have hne : (u i).val % 15 ≠ 0 := by
      intro hzero
      apply hnonzero i
      apply Fin.ext
      simpa only [liftResidues, Fin.val_zero] using hzero
    omega
  have hmodle : (u i).val % 15 ≤ 14 := by
    have := Nat.mod_lt (u i).val (by norm_num : 0 < 15)
    omega
  have hproduct : (p * (u i).val) % (15 * p) = p * ((u i).val % 15) := by
    simpa only [Nat.mul_comm] using Nat.mul_mod_mul_left p (u i).val 15
  rw [hproduct]
  constructor <;> nlinarith

/-- Failure of the gcd escape clause implies the omission-survival condition
modulo three for the residue vector. -/
@[category API, AMS 11]
lemma survivesModThree_of_no_gcdEscape {p : ℕ} {u : LiftVector p}
    (hno : ¬ HasLevelFifteenGcdEscape u) :
    SurvivesEveryOmission 3 (liftResidues u) := by
  intro omitted
  have hnotall : ¬ ∀ i, i ≠ omitted → 3 ∣ (u i).val := by
    intro hall
    exact hno ⟨omitted, Or.inl hall⟩
  push_neg at hnotall
  obtain ⟨i, hne, hndiv⟩ := hnotall
  refine ⟨i, hne, ?_⟩
  intro hzero
  have hdmod : 3 ∣ (u i).val % 15 := by
    exact (ZMod.natCast_eq_zero_iff ((u i).val % 15) 3).mp (by simpa using hzero)
  apply hndiv
  rw [Nat.dvd_iff_mod_eq_zero] at hdmod ⊢
  calc
    (u i).val % 3 = ((u i).val % 15) % 3 :=
      (Nat.mod_mod_of_dvd (u i).val (by norm_num : 3 ∣ 15)).symm
    _ = 0 := hdmod

/-- Failure of the gcd escape clause implies the omission-survival condition
modulo five for the residue vector. -/
@[category API, AMS 11]
lemma survivesModFive_of_no_gcdEscape {p : ℕ} {u : LiftVector p}
    (hno : ¬ HasLevelFifteenGcdEscape u) :
    SurvivesEveryOmission 5 (liftResidues u) := by
  intro omitted
  have hnotall : ¬ ∀ i, i ≠ omitted → 5 ∣ (u i).val := by
    intro hall
    exact hno ⟨omitted, Or.inr hall⟩
  push_neg at hnotall
  obtain ⟨i, hne, hndiv⟩ := hnotall
  refine ⟨i, hne, ?_⟩
  intro hzero
  have hdmod : 5 ∣ (u i).val % 15 := by
    exact (ZMod.natCast_eq_zero_iff ((u i).val % 15) 5).mp (by simpa using hzero)
  apply hndiv
  rw [Nat.dvd_iff_mod_eq_zero] at hdmod ⊢
  calc
    (u i).val % 5 = ((u i).val % 15) % 5 :=
      (Nat.mod_mod_of_dvd (u i).val (by norm_num : 5 ∣ 15)).symm
    _ = 0 := hdmod

/-- A fourteen-coordinate vector modulo `15 * 17 = 255`. -/
abbrev LiftVector17 := LiftVector 17

/-- The explicit improper level-fifteen lift at `p = 17`. -/
def counterexample17_lift : LiftVector17 :=
  ![120, 240, 105, 225, 90, 40, 75, 246, 60, 180, 45, 12, 30, 235]

/-- A level-fifteen grid witness at `p = 17` keeps every product residue between
`17` and `238`, inclusive. These are exactly the residues at circular distance
at least `1 / 15` from zero modulo `255`. -/
def HasLevelFifteenGridWitnessAt17 (u : LiftVector17) : Prop :=
  HasLevelFifteenGridWitness 17 u

/-- The displayed vector is a lift of `(1, ..., 14)` modulo seventeen. -/
@[category test, AMS 11]
theorem counterexample17_is_tight_lift :
    IsTightLift 17 counterexample17_lift := by
  unfold IsTightLift counterexample17_lift
  native_decide

/-- Exact exhaustive verification that the displayed vector has no witness on
the 255-point level-fifteen grid. -/
@[category test, AMS 11]
theorem counterexample17_has_no_grid_witness :
    ¬ HasLevelFifteenGridWitnessAt17 counterexample17_lift := by
  unfold HasLevelFifteenGridWitnessAt17 HasLevelFifteenGridWitness counterexample17_lift
  native_decide

/-- Exact verification that the displayed lift also fails the gcd escape
clause itself, stated directly on the lifted coordinates. -/
@[category test, AMS 11]
theorem counterexample17_has_no_gcd_escape :
    ¬ HasLevelFifteenGcdEscape counterexample17_lift := by
  unfold HasLevelFifteenGcdEscape counterexample17_lift
  native_decide

/-- The displayed vector is genuinely improper at level fifteen. -/
@[category test, AMS 11]
theorem counterexample17_is_improper :
    ¬ IsLevelFifteenProper 17 counterexample17_lift := by
  rw [IsLevelFifteenProper, not_or]
  exact ⟨counterexample17_has_no_gcd_escape,
    counterexample17_has_no_grid_witness⟩

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

/-- For multiplier three, a boundary bin uniquely determines the residue
modulo five; `none` marks bins that can never be boundary bins. -/
def badResidueForThree : Fin 15 → Option (BitVec 3) :=
  ![some 0, none, some 4, some 4, none, some 3, some 3, none,
    some 2, some 2, none, some 1, some 1, none, some 0]

/-- Bit-vector form of a boundary-bin event for multiplier three. -/
def EncodedBadThree (x : ℕ) (b : Fin 15) : Prop :=
  match badResidueForThree b with
  | none => False
  | some r => BitVec.ofNat 3 (x % 5) = r

/-- A semantic boundary-bin event for multiplier three implies its compact
bit-vector encoding. -/
@[category API, AMS 11]
lemma encodedBadThree_of_bad (x : ℕ) (b : Fin 15)
    (h : (3 * x + b.val) % 15 = 0 ∨ (3 * x + b.val) % 15 = 14) :
    EncodedBadThree x b := by
  have hreduce : (3 * x + b.val) % 15 = (3 * (x % 5) + b.val) % 15 := by
    have hmul : (3 * x) % 15 = 3 * (x % 5) := by
      simpa using Nat.mul_mod_mul_left 3 x 5
    rw [Nat.add_mod, hmul, Nat.add_mod]
    omega
  rw [hreduce] at h
  have hx := Nat.mod_lt x (by norm_num : 0 < 5)
  fin_cases b <;> simp [EncodedBadThree, badResidueForThree] at h ⊢
  all_goals rcases h with h | h
  all_goals try omega
  all_goals
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_ofNat]
    norm_num
    omega

/-- For multiplier five, a boundary bin uniquely determines the residue
modulo three. -/
def badResidueForFive : Fin 15 → Option (BitVec 3) :=
  ![some 0, none, none, none, some 2, some 2, none, none,
    none, some 1, some 1, none, none, none, some 0]

/-- Bit-vector form of a boundary-bin event for multiplier five. -/
def EncodedBadFive (x : ℕ) (b : Fin 15) : Prop :=
  match badResidueForFive b with
  | none => False
  | some r => BitVec.ofNat 3 (x % 3) = r

/-- A semantic boundary-bin event for multiplier five implies its compact
bit-vector encoding. -/
@[category API, AMS 11]
lemma encodedBadFive_of_bad (x : ℕ) (b : Fin 15)
    (h : (5 * x + b.val) % 15 = 0 ∨ (5 * x + b.val) % 15 = 14) :
    EncodedBadFive x b := by
  have hreduce : (5 * x + b.val) % 15 = (5 * (x % 3) + b.val) % 15 := by
    have hmul : (5 * x) % 15 = 5 * (x % 3) := by
      simpa only [Nat.mul_comm] using Nat.mul_mod_mul_right 5 x 3
    rw [Nat.add_mod, hmul, Nat.add_mod]
    omega
  rw [hreduce] at h
  have hx := Nat.mod_lt x (by norm_num : 0 < 3)
  fin_cases b <;> simp [EncodedBadFive, badResidueForFive] at h ⊢
  all_goals rcases h with h | h
  all_goals try omega
  all_goals
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_ofNat]
    norm_num
    omega

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

/-- The grid fraction `r / p` realizes a phase pattern when every fractional
coordinate lies in the bin recorded by that pattern. This integral inequality
form avoids any rounding convention at cell boundaries. -/
def RealizesPhase (p r : ℕ) (b : PhasePattern) : Prop :=
  ∀ i, (b i).val * p ≤ 15 * ((r * (i.val + 1)) % p) ∧
    15 * ((r * (i.val + 1)) % p) < ((b i).val + 1) * p

/-- A realized phase whose translated bins all lie between one and thirteen
produces an actual level-fifteen grid witness. -/
@[category API, AMS 11]
lemma gridWitness_of_realized_good_phase {p s r : ℕ} (hp900 : 900 < p)
    (u : LiftVector p) (htight : IsTightLift p u) (b : PhasePattern)
    (hphase : RealizesPhase p r b)
    (hgood : ∀ i, 1 ≤ (s * (liftResidues u i).val + (b i).val) % 15 ∧
      (s * (liftResidues u i).val + (b i).val) % 15 ≤ 13) :
    HasLevelFifteenGridWitness p u := by
  have hp : 0 < p := by omega
  let j : Fin (15 * p) :=
    ⟨(s * p + 15 * r) % (15 * p), Nat.mod_lt _ (by nlinarith)⟩
  refine ⟨j, ?_⟩
  intro i
  let a := (liftResidues u i).val
  let v := (r * (i.val + 1)) % p
  let d := 15 * v - (b i).val * p
  let z := (s * a + (b i).val) % 15
  have hi : i.val + 1 < p := by omega
  have hup : (u i).val ≡ i.val + 1 [MOD p] := by
    show (u i).val % p = (i.val + 1) % p
    rw [Nat.mod_eq_of_lt hi]
    exact htight i
  have hua : (u i).val ≡ a [MOD 15] := by
    exact (Nat.mod_modEq (u i).val 15).symm
  have hfirst : s * p * (u i).val ≡ s * p * a [MOD 15 * p] := by
    have h := (hua.mul_left' p).mul_left s
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hsecond : 15 * r * (u i).val ≡ 15 * r * (i.val + 1) [MOD 15 * p] := by
    have h := (hup.mul_left' 15).mul_left r
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hrv : 15 * r * (i.val + 1) ≡ 15 * v [MOD 15 * p] := by
    have h := (Nat.mod_modEq (r * (i.val + 1)) p).symm.mul_left' 15
    simpa only [v, Nat.mul_assoc] using h
  have htotal :
      (s * p + 15 * r) * (u i).val ≡ s * p * a + 15 * v [MOD 15 * p] := by
    have h := hfirst.add (hsecond.trans hrv)
    simpa only [Nat.add_mul, Nat.mul_assoc] using h
  have hreal := hphase i
  change (b i).val * p ≤ 15 * v ∧ 15 * v < ((b i).val + 1) * p at hreal
  have hd_eq : (b i).val * p + d = 15 * v := Nat.add_sub_of_le hreal.1
  have hd_lt : d < p := by
    have hupp : 15 * v < (b i).val * p + p := by nlinarith [hreal.2]
    omega
  have hz := hgood i
  change 1 ≤ z ∧ z ≤ 13 at hz
  have hdp : d < 15 * p := by nlinarith
  have hsum_lt : p * z + d < 15 * p := by nlinarith
  have hbase : (p * (s * a + (b i).val)) % (15 * p) = p * z := by
    simpa only [z, Nat.mul_comm] using
      Nat.mul_mod_mul_left p (s * a + (b i).val) 15
  have hright : (s * p * a + 15 * v) % (15 * p) = p * z + d := by
    have heq : s * p * a + 15 * v = p * (s * a + (b i).val) + d := by
      rw [← hd_eq]
      ring
    rw [heq, Nat.add_mod, hbase, Nat.mod_eq_of_lt hdp, Nat.mod_eq_of_lt hsum_lt]
  have hres : ((s * p + 15 * r) * (u i).val) % (15 * p) = p * z + d := by
    unfold Nat.ModEq at htotal
    rw [hright] at htotal
    exact htotal
  change p ≤ (j.val * (u i).val) % (15 * p) ∧
    (j.val * (u i).val) % (15 * p) ≤ 14 * p
  simp only [j, Nat.mod_mul_mod]
  rw [hres]
  constructor <;> nlinarith

/-- Conversely, if a realized phase does not produce a grid witness, at least
one coordinate must occupy boundary bin zero or fourteen. -/
@[category API, AMS 11]
lemma blocks_of_no_gridWitness_of_realizesPhase {p s r : ℕ} (hp900 : 900 < p)
    (u : LiftVector p) (htight : IsTightLift p u) (b : PhasePattern)
    (hphase : RealizesPhase p r b)
    (hno : ¬ HasLevelFifteenGridWitness p u) :
    Blocks s (liftResidues u) b := by
  by_contra hblocks
  apply hno
  apply gridWitness_of_realized_good_phase (s := s) (r := r) hp900 u htight b hphase
  intro i
  rw [Blocks] at hblocks
  push_neg at hblocks
  have hi := hblocks i
  have hmodlt :
      (s * (liftResidues u i).val + (b i).val) % 15 < 15 :=
    Nat.mod_lt _ (by norm_num)
  constructor <;> omega

/-- The remaining phase-realisation bridge for a modulus `p`: if a tight lift
has no grid witness, its residue vector blocks all 270 certified patterns for
both multipliers. -/
def CertifiedPhaseBridge (p : ℕ) : Prop :=
  ∀ u : LiftVector p, IsTightLift p u → ¬ HasLevelFifteenGridWitness p u →
    BlocksCertifiedMultiplierThree (liftResidues u) ∧
      BlocksCertifiedMultiplierFive (liftResidues u)

/-- Once the phase-realisation bridge is supplied, every tight lift is proper.
This is the sharp conditional endpoint: all finite rigidity, coercion, gcd,
and terminal arithmetic obligations are discharged internally. -/
@[category research solved, AMS 11]
theorem levelFifteenProper_of_certifiedPhaseBridge {p : ℕ} (hp : 0 < p)
    (hbridge : CertifiedPhaseBridge p) (u : LiftVector p) (htight : IsTightLift p u) :
    IsLevelFifteenProper p u := by
  by_contra hproper
  rw [IsLevelFifteenProper, not_or] at hproper
  obtain ⟨hnoGcd, hnoGrid⟩ := hproper
  have hzero : ∃ i, liftResidues u i = 0 := by
    by_contra h
    push_neg at h
    exact hnoGrid (gridWitness_of_all_residues_nonzero hp u h)
  obtain ⟨hblocks3, hblocks5⟩ := hbridge u htight hnoGrid
  exact terminal_contradiction_of_certified_patterns (liftResidues u) hzero
    (survivesModThree_of_no_gcdEscape hnoGcd)
    (survivesModFive_of_no_gcdEscape hnoGcd) hblocks3 hblocks5

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
