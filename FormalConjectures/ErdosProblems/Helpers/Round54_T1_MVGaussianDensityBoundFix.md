# Round 54 — T1.1 Audit: MVGaussianDensityBound.lean:199 PosSemidef.det_sqrt API drift fix

**Round**: R54 V1 (mainline mechanical retirement, R52 CharFunCrossBlock pattern precedent).
**Branch**: `r46-track-a-mge-posdef`.
**HEAD pin**: `fbc1843` (R53 close).
**File**: `FormalConjectures/ErdosProblems/Helpers/MVGaussianDensityBound.lean`.
**Target call site**: line 199 (inside `realMatrixSqrt_det`, lines 195–200).
**R46 helper pin**: `FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean:178` (`det_CFC_sqrt_eq_sqrt_det`).

## 1. Pre-fix verbatim context (lines 187–200)

```lean
/-! ## Round 9 — Determinant of the symmetric square root

For a PosDef matrix `M`, the symmetric square root `realMatrixSqrt M` (= `CFC.sqrt M`)
has determinant `Real.sqrt (det M)`. This follows from
`Matrix.PosSemidef.det_sqrt` (Mathlib `Analysis/Matrix/Order.lean`), specialised
to the field `ℝ`: `RCLike.sqrt` of a real argument is `Real.sqrt`.
-/

theorem realMatrixSqrt_det [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    (realMatrixSqrt M).det = Real.sqrt M.det := by
  unfold realMatrixSqrt
  rw [hM.det_sqrt]
  exact RCLike.sqrt_real
```

## 2. Pre-fix `lake env lean` output (verbatim)

```
warning: brownian-motion: repository '/Users/.../formal-conjectures/.lake/packages/brownian-motion' has local changes
FormalConjectures/ErdosProblems/Helpers/MVGaussianDensityBound.lean:199:9: error(lean.invalidField): Invalid field `det_sqrt`: The environment does not contain `And.det_sqrt`, so it is not possible to project the field `det_sqrt` from an expression
  hM
of type
  M.IsHermitian ∧ ∀ (x : n →₀ ℝ), 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj
FormalConjectures/ErdosProblems/Helpers/MVGaussianDensityBound.lean:197:48: error: unsolved goals
n : Type u_1
inst✝¹ : Fintype n
inst✝ : DecidableEq n
M : Matrix n n ℝ
hM : M.PosSemidef
⊢ (CFC.sqrt M).det = √M.det
```

Two errors:
- **199:9** — `hM.det_sqrt` dot-notation fails. The elaborator unfolds `Matrix.PosSemidef` to its underlying `And` (Hermitian ∧ quadratic-form-nonneg) shape and then cannot project `.det_sqrt`. Either Mathlib's `Matrix.PosSemidef.det_sqrt` was removed/renamed (API drift), or the elaboration path no longer reaches it via dot notation.
- **197:48** — fallback unsolved goal `(CFC.sqrt M).det = √M.det` after `unfold realMatrixSqrt`.

## 3. Claims Verification Table (post-T1.1)

| # | Claim | Status | Citation |
|---|-------|--------|----------|
| 1 | `MVGaussianDensityBound.lean:199` build error on `PosSemidef.det_sqrt` API drift | **VERIFIED** | `lake env lean` output above; error literally cites `det_sqrt` invalid-field at 199:9 |
| 2 | R46 helper `det_CFC_sqrt_eq_sqrt_det` available | **VERIFIED** | `MultivariateGaussianPdf.lean:178–196`: `theorem det_CFC_sqrt_eq_sqrt_det {S : Matrix ι ι ℝ} (hS : S.PosSemidef) : (CFC.sqrt S).det = Real.sqrt S.det` |
| 3 | R46 helper signature compatible with line 199 use site | **VERIFIED** | `realMatrixSqrt M := CFC.sqrt M` (def at `CholeskyExistence.lean:41`). After `unfold realMatrixSqrt`, goal is `(CFC.sqrt M).det = √M.det`. Helper conclusion is `(CFC.sqrt S).det = Real.sqrt S.det`. Hypothesis match: local `hM : M.PosSemidef` ↔ helper requires `hS : S.PosSemidef`. Direct application — no adapter required |
| 4 | Local fix scope ≤ 15 LOC | **VERIFIED** | 2-line body change + 1 import line + 1-line docstring update = ~4 LOC. Well under R52 1-line precedent's bound |
| 5 | No regression on 8 critical targets | TO VERIFY in T2.2 | Will run `lake build` post-fix on the 8 targets |
| 6 | R51 axiom #7 MGE preserved | **VERIFIED (no change planned)** | Touching only `realMatrixSqrt_det` body and import line; MGE axiom in same file at unrelated theorem |
| 7 | R53 axiom #8 Matrix.det.differentiable preserved | **VERIFIED (no change planned)** | Different file (`MatrixDetDifferentiable.lean`); not touched |
| 8 | A1–A5 + #6 axioms preserved | **VERIFIED (no change planned)** | Different files; not touched |

## 4. Fix recipe (T2.1)

**Edit 1 — add import** (after existing `import FormalConjectures.ErdosProblems.Helpers.MVGaussianRotation` at line 15):

```lean
import FormalConjectures.ErdosProblems.Helpers.MultivariateGaussianPdf
```

Cycle check: `MultivariateGaussianPdf.lean` imports only `BrownianMotion.Gaussian.MultivariateGaussian` + Mathlib modules — no cycle with `MVGaussianDensityBound`'s chain (`GaussianBoxBounds → GaussianPDFBounds + StandardMVGaussianBox`, `MVGaussianRotation → MVGaussianPushforward + MVGaussianFromPosDef + StandardMVDensityBound`).

**Edit 2 — replace lines 198–200** body of `realMatrixSqrt_det`:

```lean
  unfold realMatrixSqrt
  rw [hM.det_sqrt]
  exact RCLike.sqrt_real
```

with:

```lean
  unfold realMatrixSqrt
  exact det_CFC_sqrt_eq_sqrt_det hM
```

**Edit 3 — update preceding docstring** (lines 187–193) to cite the R46 helper instead of the deprecated Mathlib lemma:

> Replace the `Matrix.PosSemidef.det_sqrt`/`RCLike.sqrt_real` reference with a citation to R46 helper `det_CFC_sqrt_eq_sqrt_det` at `MultivariateGaussianPdf.lean:178`.

## 5. Sorry / axiom impact

- **Sorry retirement**: this is a Full theorem `realMatrixSqrt_det` whose proof was broken by Mathlib API drift, NOT a sorry being closed. Pre-R54 mainline gate sorries: 11. Post-R54 expected: still 11 (build unblock, not retirement).
- **Axiom delta**: 0 (no new axioms; no axiom touched).
- **Items**: 19 → 19 (no change). Best case as projected by plan (-1 sorry) does not materialize because line 199 is a non-sorry Full attempt.
- **Outcome class**: Mid (P~0.35 in plan distribution) — clean fix, no sorry retirement, alternate-track unblock.

## 6. Downstream-consumer unblock

Consumers of `realMatrixSqrt_det` in this file (read at HEAD `fbc1843`):
- `realMatrixSqrt_det_pos` (line 202) — `rw [realMatrixSqrt_det hM.posSemidef]`.
- `realMatrixSqrt_det_ne_zero` (line 208) — uses `_pos`.
- `realMatrixSqrt_isUnit` (line 214) — uses `_ne_zero`.
- `volume_realMatrixSqrt_mulVec_preimage` (line 244) — uses `_det_ne_zero`.

All four downstream Full theorems in `MVGaussianDensityBound.lean` are gated on `realMatrixSqrt_det` compiling. Restoring this lemma re-enables this file's build path entirely.

## 7. Build-target baseline (8 critical, to re-check post-fix in T2.2)

Per R54 plan + AXIOM_INVENTORY.md trajectory:
- `MultivariateGaussianCDF`
- `MultivariateGaussianPdf`
- `PhaseAUpperBound`
- `MatrixDetDifferentiable`
- `GLWLowerProof`
- `GLWUpperProof`
- `«524»`
- `GLWSmallBallShortcut`

Plus the modified file: `MVGaussianDensityBound`.

## 8. Risks / honesty notes

- **Confirmed** the build was already failing on `MVGaussianDensityBound.lean:199` at HEAD `fbc1843`. The plan's Claim 5 ("8 critical targets remain green") is consistent with this since `MVGaussianDensityBound` is **not** in the 8-target list — it was already known to be broken, hence the R54 priority.
- **No sorry will be retired**. The plan's "best case (-1 mainline)" is unrealizable for this specific line because line 199 sits in a Full proof attempt, not a sorry. R54 lands as **alternate-track unblock**, not item retirement. AXIOM_INVENTORY arithmetic stays at items 19, sorries 11, axioms 8, project total 41.
- **Anti-mismatch hygiene**: only one file modified (`MVGaussianDensityBound.lean`). R46 helper signature pinned and re-verified at `MultivariateGaussianPdf.lean:178`.
