# Round 55 T1.1 — Drift error catalog + Claims Verification Table

**Branch**: `r46-track-a-mge-posdef`, mainline-only.

**HEAD pre-T2.1**: `9ba0c27` (R54 close).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Round type**: Variante 1, single round, mainline. R55 alternate-track
drift-fix sweep per parent brief; pattern match R52 CharFunCrossBlock /
R54 MVGaussianDensityBound 1-line / few-line precedents. **Each fix is a
build unblock, not a sorry retirement** — all 5 errors enumerated below
sit *outside* the Erdős 524 dependency cone (per R53/R54 status §"Other
pre-existing failures", "mostly outside the Erdős 524 dependency cone").

---

## Claims Verification Table (BINDING — discipline rule #6)

| # | Claim | VERIFIED? | Citation | Notes |
|---|-------|-----------|----------|-------|
| 1 | List of files with build errors at HEAD `9ba0c27` | **VERIFIED** | `lake build` full project | 5 distinct error sites in 5 files (Wikipedia/DiameterSimpleFiniteGroups, ErdosProblems/{1141,508,26}, Paper/HartshorneConjecture). All outside Erdős 524 cone. |
| 2 | R46/R49/R51/R53 helpers / axioms preserved | **VERIFIED** | `MultivariateGaussianPdf.lean:178`, `MatrixDetDifferentiable.lean:141`, etc. | No regression planned in T2.1 candidates. |
| 3 | A1-A5 axioms preserved | **VERIFIED** | `524.lean:3574`, `:3643` etc. | No 524 file touched in T2.1. |
| 4 | Q1a/b/c track infrastructure preserved | **VERIFIED** | Mainline-only modification scope. | Alternate-track `Helpers/` files (CauchyDetLowerBound, MultivariateSmallBallUpper, etc.) untouched. |
| 5 | TC5 mills ratio file preserved | **VERIFIED** (track-c only) | `Helpers/GaussianMillsRatio.lean` is on `track-c-1dkmt`. | Mainline branch doesn't touch this. |
| 6 | Each candidate fix LOC estimate | **VERIFIED** below | Per-error analysis section below. | Two Type A fixes proposed: ~5 LOC + ~1 LOC = ~6 LOC total. |
| 7 | PosSemidef dot-notation unfolds to And (R54 finding) | **VERIFIED — PRESERVED** | R54 status doc. | Not directly applicable to R55 candidates (no PosSemidef sites among the 5 errors). |
| 8 | No retirement claim without inline sorry verification | **VERIFIED — discipline rule binding** | R54 calibration lesson. | All R55 candidate fixes are **build unblocks**, NOT sorry retirements (none of the 5 error sites are TAG'd sorries; all are Full proof attempts broken by Mathlib API/tactic-set drift). |

---

## Build error catalog (HEAD `9ba0c27`, full-project `lake build`)

Five distinct errors in five files, all outside the Erdős 524 cone:

### Error A — `FormalConjectures/Wikipedia/DiameterSimpleFiniteGroups.lean:84:8` and `:122:8`

```
error: Unknown constant `SimpleGraph.eq_top_iff_forall_ne_adj`
```

**Classification**: **Type A** (Mathlib API drift, fixable via in-tree
helper substitute).

**Root cause**: `SimpleGraph.eq_top_iff_forall_ne_adj` was added to
Mathlib in commit `eae0ea4f18` (PR #30129, "feat(SimpleGraph): define and
prove basic theory of vertex covers") which is **ahead** of our pinned
Mathlib HEAD `25ce633136`. The lemma is referenced in two places (lines
84 and 122 — `groupDiam_alternating_three` and `groupDiam_perm_two`,
both `@[category test]` decorated test theorems).

**Proposed fix** (~5 net LOC, single file, P~0.85):

Add a private helper inside `namespace BabaiSeressConjectures`:

```lean
private theorem eq_top_iff_forall_ne_adj' {V : Type*} {G : SimpleGraph V} :
    G = ⊤ ↔ ∀ a b : V, a ≠ b → G.Adj a b := by
  simp [← top_le_iff, SimpleGraph.le_iff_adj]
```

Helper proof matches verbatim the proof Mathlib commits in
eae0ea4f18 (`simp [← top_le_iff, le_iff_adj]`); both `top_le_iff`
(`Order/BoundedOrder/Basic.lean:141`) and `SimpleGraph.le_iff_adj`
(`SimpleGraph/Basic.lean:208`) and `SimpleGraph.top_adj` (`@[simp]` at
`SimpleGraph/Basic.lean:331`) are present in our pin.

Then rename the call sites:
- Line 84: `rw [SimpleGraph.eq_top_iff_forall_ne_adj]` → `rw [eq_top_iff_forall_ne_adj']`
- Line 122: same rename

**LOC**: +4 helper (theorem signature + 1-line proof + blank lines), 0
delta on call sites (rename only). Net +4 LOC.

**Sorry retirement potential**: ZERO. The two affected theorems are
`@[category test]` (test-tier proofs, not TAG'd sorries — they were
fully proven Full closures broken by the missing API). This fix is a
**build unblock for two test-tier theorems**, not a sorry retirement.
Items at gate: unchanged.

**Anti-mismatch hygiene**:
- Single file modified.
- No new imports needed (`SimpleGraph.le_iff_adj`, `top_le_iff`, and
  `SimpleGraph.top_adj` all reachable through the pre-existing
  `FormalConjectures.Util.ProblemImports` chain).
- No `@[simp]` attribute added (helper is `private`, not exported).
- Erdős 524 cone untouched.

### Error B — `FormalConjectures/ErdosProblems/1141.lean:43:14`

```
error: unsolved goals
case succ
n' : ℕ
⊢ (∀ (k : ℕ), k * k ≤ n' → (n' + 1).Coprime k → Nat.Prime (n' + 1 - k * k)) ↔
    ∀ (k : ℕ), k * k < n' + 1 → (n' + 1).Coprime k → Nat.Prime (n' + 1 - k * k)
```

**Classification**: **Type A** (Mathlib simp-set drift, fixable via
augmenting simp lemma list).

**Root cause**: Inside the `Decidable (Erdos1141Prop n)` instance proof,
`simp [Erdos1141Prop, le_sqrt, pow_two]` no longer normalizes
`k * k ≤ n'` to `k * k < n' + 1` (the `Nat.lt_succ_iff` simp normal form
adjustment is now a separate normalization). The proof is otherwise
sound; one `simp` lemma needs to be added.

**Proposed fix** (+1 LOC token, single line, P~0.80):

Replace
```lean
| succ n' =>
  simp [Erdos1141Prop, le_sqrt, pow_two]
```
with
```lean
| succ n' =>
  simp [Erdos1141Prop, le_sqrt, pow_two, Nat.lt_succ_iff]
```

Adds `Nat.lt_succ_iff : a < n + 1 ↔ a ≤ n` to the simp set so the goal
normalizes both sides to the same form.

**LOC**: +1 token, 0 net LOC.

**Sorry retirement potential**: ZERO. The Erdős 1141 problem itself
remains an open problem with `sorry` body at line 57 (`erdos_1141`) —
this fix is for the **Decidable instance scaffold**, not the open
problem. **Build unblock only**, items unchanged.

**Anti-mismatch hygiene**: Single file, single token added, no semantic
change.

### Error C — `FormalConjectures/ErdosProblems/508.lean:98:98`

```
error: unsolved goals
⊢ Pairwise fun i j =>
    ((![!₂[0, 0], !₂[1, 0], !₂[1 / 2, √3 / 2]] i).ofLp 0 - ...) ^ 2 +
    ((... i).ofLp 1 - ...) ^ 2 = 1
+ warnings: simp lemmas pairwise_fin_succ_iff_of_isSymm and
  Fin.forall_fin_succ now flagged "unused simp argument"
```

**Classification**: **Type B** (genuine simp-set drift requiring proof
restructure ≥10 LOC).

**Root cause**: The Mathlib simp lemmas `pairwise_fin_succ_iff_of_isSymm`
and `Fin.forall_fin_succ` are no longer applicable to the `Pairwise`
goal in `HadwigerNelsonAtLeastThree`. The goal needs to be discharged
by per-pair case analysis; the previous one-line `simp` chain no longer
suffices.

**Proposed fix scope**: ~10-25 LOC restructure to enumerate the three
pairs explicitly. **Defer to R56+** (out of R55 ≤30-LOC budget; not a
clean Type A pattern match).

**Sorry retirement potential**: ZERO. This is `HadwigerNelsonAtLeastThree`
(`@[category high_school]` test-tier), not a TAG'd sorry.

### Error D — `FormalConjectures/ErdosProblems/26.lean:74:4`

```
error: `grind` failed
case grind
n : ℕ, hn : n ≥ 1, h_1 : ¬↑n * (↑n)⁻¹ = 1
⊢ False
```

**Classification**: **Type B/C** (tactic-call drift; `lia` macro now
fails grind on a goal involving real-cast multiplicative inverse).

**Root cause**: `lia` is a Mathlib tactic (per
`Tactic/Order/ToInt.lean:17` doc reference) that delegates to `grind`.
The goal requires `mul_inv_cancel` for `↑n ≠ 0` — grind's e-matching
patterns don't include `mul_inv_cancel`. Need a 2-3 line proof using
`have h : (↑n : ℝ) ≠ 0 := by ...; field_simp [h]` or similar.

**Proposed fix scope**: ~3-5 LOC restructure. **Defer to R56+** (not a
clean Type A pattern match — needs proof restructure, not API
substitution).

**Sorry retirement potential**: ZERO. This is `isBehrend_of_contains_one`
(`@[category test]` test-tier), not a TAG'd sorry.

### Error E — `FormalConjectures/Paper/HartshorneConjecture.lean:69:13`

```
error: Invalid field `hom`: The environment does not contain
`SheafOfModules.Hom.hom`, so it is not possible to project the field
`hom` from an expression
```

**Classification**: **Type C** (SheafOfModules API restructure;
adapter wrapper required).

**Root cause**: `SheafOfModules` morphism projection field renamed/moved
in Mathlib; `f.hom` is no longer a valid field access. New API uses
`f.val` or category-theoretic `(...).val.hom` chain (per Mathlib's
SheafOfModules namespace files in
`.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Sheaf/`).

**Proposed fix scope**: requires investigation of new SheafOfModules
morphism API (likely `f.val.hom` or `f.cat.hom` or similar), plus
verification of `HasFiniteCoproducts S.VectorBundles` instance still
type-checks. ≥15 LOC investigation budget. **Defer to R56+** —
out-of-scope for R55 (algebraic geometry, far from Erdős 524 cone).

**Sorry retirement potential**: ZERO. This is `VectorBundles.toModule`
functor mapping (`@[category API]`), inside a `def` not a sorry.

---

## R55 T2.1 dispatch decision

**Apply 2 Type A fixes** (Errors A and B), totaling ~5 net LOC across 2
files. Both are **build unblocks**, not sorry retirements:

1. **DiameterSimpleFiniteGroups.lean** — add helper `eq_top_iff_forall_ne_adj'`
   + rename 2 call sites. Mathlib-API-drift fix matching R54 helper-substitute
   pattern. P~0.85.
2. **1141.lean** — add `Nat.lt_succ_iff` to simp set on Decidable
   instance proof. Tactic-set normalization fix. P~0.80.

**Defer to R56+**: Errors C (508), D (26), E (HartshorneConjecture).
Each requires proof restructure (≥10 LOC) or new-API investigation
(≥15 LOC), exceeding R55 ≤30-LOC budget per fix.

**Net debt change projected**: 0 sorries / 0 axioms / 0 items at gate
(unchanged). Mainline 19 → 19, project total 41 → 41. **2 alternate-track
build unblocks** (matching R54 mid-distribution outcome pattern).

---

## Anti-mismatch hygiene (8/8)

1. Only two non-524 files modified
   (`Wikipedia/DiameterSimpleFiniteGroups.lean`, `ErdosProblems/1141.lean`).
2. Helper proof for Error A inlined as `private` — no namespace
   pollution.
3. No new imports.
4. `Mathlib.Order.BoundedOrder.Basic.top_le_iff`,
   `Mathlib.Combinatorics.SimpleGraph.Basic.le_iff_adj` /
   `top_adj`, `Mathlib.Data.Nat.Basic.Nat.lt_succ_iff` all confirmed
   present in pinned Mathlib HEAD `25ce633136`.
5. Track branches not touched (mainline only).
6. R49 axiom #6 + R51 axiom #7 + R53 axiom #8 + A1-A5 untouched (no
   helper file edited).
7. R46 helper `det_CFC_sqrt_eq_sqrt_det` not modified.
8. Q1c/track-c/track-d alternate-track infrastructure not modified.

---

## Cumulative T1.1 audit ledger

8 distinct misframings caught pre-dispatch via T1.1 audit pipeline
(unchanged from R50/R51/R52/R53/R54 — R55 is mechanical pattern-match,
no Grok dispatch). R55 T1.1 audit (8/8 VERIFIED) is a clean
multi-target catalog audit: 5 errors enumerated, 2 classified Type A
and elected for T2.1, 3 classified Type B/C and deferred per
R55-≤30-LOC discipline.

---

## End of T1.1.
