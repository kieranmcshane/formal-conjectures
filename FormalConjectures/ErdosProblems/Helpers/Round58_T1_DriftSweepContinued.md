# Round 58 T1.1 — Continued drift error catalog (Errors C/D/E) + Claims Verification Table

**Branch**: `r46-track-a-mge-posdef`, mainline-only.

**HEAD pre-T2.1**: `1e813c3` (R57 close).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Round type**: Variante 1, single round, mainline. R58 alternate-track
drift-fix sweep CONTINUATION of R55. R55 closed Errors A/B (Type A); R58
revisits Errors C/D/E (deferred as Type B/C in R55) to determine whether
deeper investigation reveals Type A fixes.

---

## Claims Verification Table (BINDING — discipline rule #6)

| # | Claim | VERIFIED? | Citation | Notes |
|---|-------|-----------|----------|-------|
| 1 | Error C `508.lean:99` Pairwise simp drift exact site | **VERIFIED** | `508.lean:99` `simp [pairwise_fin_succ_iff_of_isSymm, Fin.forall_fin_succ]` flagged unused | Goal `Pairwise (Fin 3 → Fin 3 → Prop)` not closed; both simp lemmas exist in Mathlib but require `[IsSymm _ R]` which Lean cannot synthesize for the anonymous lambda |
| 2 | Error D `26.lean:74` lia/grind tactic drift exact site | **VERIFIED** | `26.lean:74` `lia` after `simp [multiplesOf_eq_univ A h, Set.partialDensity]` | Goal `↑n * (↑n)⁻¹ = 1` (real); grind e-matching lacks `mul_inv_cancel₀` |
| 3 | Error E `HartshorneConjecture.lean:69` SheafOfModules.Hom field rename | **VERIFIED** | `HartshorneConjecture.lean:69` `map f := f.hom` | Mathlib `SheafOfModules.Hom` has field `val` (per `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:46 val : X.val ⟶ Y.val`); `.hom` no longer exists |
| 4 | Mainline R49+R51+R53+R56 axioms preserved | **VERIFIED — pre-R58** | AXIOM_INVENTORY R49-R56 | No regression planned; all candidate fixes are non-524 files |
| 5 | A1-A5 axioms preserved | **VERIFIED — pre-R58** | `524.lean` | No 524 file touched in T2.1 |
| 6 | R57 Q1c Full close preserved | **VERIFIED — pre-R58** | `Helpers/MultivariateSmallBallUpper.lean:238` | Q1c track infrastructure not touched in T2.1 |
| 7 | TC8 retirement track-c separately preserved | **VERIFIED — pre-R58** | track-c-1dkmt branch | Mainline doesn't touch this branch |
| 8 | R55 alternate-track build state (Errors A/B) preserved | **VERIFIED — pre-R58** | `Wikipedia/DiameterSimpleFiniteGroups.lean`, `1141.lean` | No regression in R58 candidates |

---

## Build error catalog (HEAD `1e813c3`, per-file `lake env lean`)

### Error C — `FormalConjectures/ErdosProblems/508.lean:98-101`

```
error: unsolved goals
⊢ Pairwise fun i j =>
    ((![!₂[0, 0], !₂[1, 0], !₂[1 / 2, √3 / 2]] i).ofLp 0 - ...).ofLp 0 - ...) ^ 2 +
    ((... ).ofLp 1 - ...) ^ 2 = 1
+ warnings: simp args `pairwise_fin_succ_iff_of_isSymm`, `Fin.forall_fin_succ`,
  `div_pow` flagged unused
```

**Classification**: **Type A** (Mathlib simp-lemma drift, fixable via 1-token replacement).

**Root cause**: `pairwise_fin_succ_iff_of_isSymm` requires `[IsSymm _ R]`
typeclass instance. Lean cannot synthesize this for an anonymous
`fun i j => squared_distance = 1` — the relation IS symmetric
arithmetically, but no IsSymm instance is auto-derived. Mathlib also
provides `pairwise_fin_succ_iff` (no IsSymm requirement, `Pairwise.lean:62`)
which decomposes `Pairwise R` over `Fin (n+1)` into all three branches
without symmetry. Switching to this version + `Fin.forall_fin_succ`
should close the goal.

**Proposed fix** (~1-token, single line, P~0.75):

Replace `pairwise_fin_succ_iff_of_isSymm` → `pairwise_fin_succ_iff` at
line 99. The `Fin.forall_fin_succ` then enumerates all (i, j) ≠ pairs.
The remaining `simp [UnitDistancePlaneGraph, ...]; norm_num` chain
handles arithmetic.

**LOC**: +0 net (1-token rename).

**Sorry retirement potential**: ZERO. `HadwigerNelsonAtLeastThree`
(`@[category high_school]` test-tier), not a TAG'd sorry. Build unblock
only.

### Error D — `FormalConjectures/ErdosProblems/26.lean:74`

```
error: `grind` failed
case grind
n : ℕ, hn : n ≥ 1, h_1 : ¬↑n * (↑n)⁻¹ = 1
⊢ False
```

**Classification**: **Type A** (tactic-set drift, fixable via direct
`mul_inv_cancel₀` substitution).

**Root cause**: After `simp [multiplesOf_eq_univ A h, Set.partialDensity]`,
the goal is `(↑n : ℝ) * (↑n)⁻¹ = 1` (or equivalent ratio form). The `lia`
tactic delegates to `grind`'s e-matching, which doesn't have
`mul_inv_cancel₀` patterns registered. Replace `lia` with explicit
`mul_inv_cancel₀` application using `(↑n : ℝ) ≠ 0` from `1 ≤ n`.

**Proposed fix** (+2 LOC, single block, P~0.80):

Replace
```lean
| simp [multiplesOf_eq_univ A h, Set.partialDensity]
| lia
```
with
```lean
| have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
| simp [multiplesOf_eq_univ A h, Set.partialDensity, div_self hn']
```

(After T2.1 attempt: simp's normal form is `↑n / ↑n = 1`, not
`↑n * (↑n)⁻¹ = 1` — `div_self` is the correct closer, not
`mul_inv_cancel₀`.)

**LOC**: +2 net.

**Sorry retirement potential**: ZERO. `isBehrend_of_contains_one`
(`@[category test]` test-tier), not a TAG'd sorry. Build unblock only.

### Error E — `FormalConjectures/Paper/HartshorneConjecture.lean:69`

```
error: Invalid field `hom`: The environment does not contain
`SheafOfModules.Hom.hom`
```

**Classification**: **Type A** (Mathlib API rename, fixable via 1-token
field rename).

**Root cause**: `SheafOfModules.Hom` structure in current Mathlib pin
(`Algebra/Category/ModuleCat/Sheaf.lean:44`) has field `val : X.val ⟶ Y.val`,
NOT `hom`. The `.hom` field name was renamed/removed in a Mathlib refactor.
Mathlib's own usage in `PushforwardContinuous.lean:47` and
`ChangeOfRings.lean:41` confirms the new pattern: `f.val`.

**Proposed fix** (~1-token, single line, P~0.90):

Replace `map f := f.hom` → `map f := f` at line 69.

(After T2.1 attempt: `f.val : X.carrier.val ⟶ Y.carrier.val` is one
level too deep — the expected type for the InducedCategory `map` is
`X.carrier ⟶ Y.carrier`, which `f` itself supplies directly via the
`InducedCategory _ VectorBundles.carrier` instance. The original `.hom`
field name was a now-removed coercion; the InducedCategory pattern uses
the morphism directly without projection.)

**LOC**: +0 net (1-token rename).

**Sorry retirement potential**: ZERO. `VectorBundles.toModule` is a
`def`, not a sorry. Build unblock only.

---

## R58 T2.1 dispatch decision

**Apply 3 Type A fixes** (Errors C, D, E), totaling ~3 net LOC across 3
files. All are **build unblocks**, NOT sorry retirements:

1. **508.lean** — `pairwise_fin_succ_iff_of_isSymm` → `pairwise_fin_succ_iff`. P~0.75.
2. **26.lean** — replace `lia` with explicit `mul_inv_cancel₀ hn'` block. P~0.80.
3. **HartshorneConjecture.lean** — `f.hom` → `f.val`. P~0.90.

**Net debt change projected**: 0 sorries / 0 axioms / 0 items at gate
(unchanged). Mainline 19 → 19, project total 39 → 39. **3 alternate-track
build unblocks** (uplift from R55 mid-distribution outcome).

Joint P(all 3 Full): ~0.55. P(≥2 Full): ~0.85. P(≥1 Full): ~0.97.

---

## Anti-mismatch hygiene (8/8)

1. Three non-524 files modified (`508.lean`, `26.lean`, `HartshorneConjecture.lean`).
2. No new helpers / no namespace pollution / no `@[simp]` attributes added.
3. No new imports needed (all replacements use already-imported Mathlib API).
4. Mathlib pin `25ce633136` confirmed contains: `pairwise_fin_succ_iff`
   (`Logic/Pairwise.lean:62`), `mul_inv_cancel₀` (`Algebra/Group/Basic.lean`),
   `Nat.one_le_iff_ne_zero` (used in `Mathlib/Tactic/DeriveEncodable.lean`),
   `SheafOfModules.Hom.val` (`Algebra/Category/ModuleCat/Sheaf.lean:46`).
5. Track branches not touched (mainline only).
6. R49/R51/R53/R56/A1-A5 axioms untouched (no helper file edited).
7. R57 Q1c Full close untouched.
8. Q1a/b/c track-c/track-d alternate-track infrastructure not modified.

---

## End of T1.1.
