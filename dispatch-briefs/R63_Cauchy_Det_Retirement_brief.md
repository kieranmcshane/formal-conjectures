# Round R63 brief — Cauchy det identity + retire `glw_det_lower_bound`

**Type**: Closure round, axiom retirement.
**Dispatch surface**: `r46-track-a-mge-posdef` worktree, mainline. Schedule **post-R61-A and post-R62** (depends on R61-A having axiomatised `glw_det_lower_bound`, and R62 ideally landed for net-debt accounting cleanliness — but R63 can also run in parallel with R62 if FS coordination allows).
**Scope binding (Q7)**: R63 = formalise the classical Cauchy determinant identity in Lean, then apply it to the GLW hierarchical Cauchy matrix to prove the explicit lower bound `det(glwMatrixA m hm) ≥ (240·e)^{-2m³}`. This retires axiom #6 `glw_det_lower_bound`. Net : -1 axiom.

---

## Pre-flight context

R61-A axiomatised `glw_det_lower_bound` (paper-stated value `(240·e)^{-2m³}` from Gao–Li–Wellner 2010 §4 Lemma 4.2 second half) under hybrid (c) Path A pragmatic. Grok strategic pre-flight (Probe 2) returned a 40–60 LOC estimate for the Cauchy determinant identity in Lean via Vandermonde + multilinearity, with high confidence the standard Mathlib `Matrix.vandermonde_det` API is ergonomic enough. R63 retires the axiom on the back of that estimate, single-round.

**Why retire the axiom** : Probe 2 showed it's mathematically feasible. Probe 4 (gate-feasibility reconciliation) showed retiring this axiom is one of 4 items needed to bring mainline ledger from 19 to the gate threshold of 8 — with R63 it's reachable, without it, it isn't.

---

## Mandatory floor

### T1.0 — paper recheck (Full, per `feedback_paper_recheck_t10`)
The Cauchy determinant identity statement (textbook ; paper-fetch from the Krattenthaler 1999 survey "Advanced Determinant Calculus" §2.2 OR direct derivation from Vandermonde) :

> **Cauchy determinant.** For any `n` and any pairwise distinct `x_1, …, x_n, y_1, …, y_n` such that `x_i + y_j ≠ 0` for all `i, j`,
>
> `det(1/(x_i + y_j))_{i,j=1..n} = ∏_{1 ≤ i < j ≤ n} (x_j − x_i)(y_j − y_i) / ∏_{i,j=1..n} (x_i + y_j)`

Document verbatim in audit doc. Cite Krattenthaler 1999 (https://arxiv.org/abs/math/9902004) as the canonical reference if Track A wants a paper-fetch beyond the well-known statement.

For the GLW application : the matrix `glwMatrixA m hm` is `1/(δ_i + δ_j)` with `δ` the hierarchical grid `δ_{m·p+q} = 4^{p+m}·(m+q)`. So `x_i = y_i = δ_i` (symmetric Cauchy). Substitute into the identity and bound the resulting expression.

### T1.1 — Mathlib API audit (Full)
Document in `Helpers/TrackA_R63_T1_CauchyDetAudit.md` :

- **Verify Mathlib API at pin `25ce633136`** :
  - `Matrix.vandermonde` and `Matrix.vandermonde_det` : confirmed present (Mathlib has both ; Vandermonde det formula `∏_{i < j}(v j - v i)`).
  - `Matrix.det_succ_row_zero` (Laplace expansion) : confirmed present.
  - `Matrix.det_apply` (Leibniz form) : confirmed present.
  - `Matrix.det_smul`, `Matrix.det_diagonal` : standard.
  - Row-scaling lemma : `Matrix.det_updateRow_smul` or via `Matrix.det_mul`.
  - `Finset.prod_Ioi_succAbove` or analog for the `∏_{i<j}` re-indexing : check exact name.
- **Probe 2 strategy lock** : Route 1 (Vandermonde + multilinearity). Multiply each row of the Cauchy matrix by `∏_j (x_i + y_j)` ; the resulting matrix has columns expressible as polynomials in `y_j` ; extract Vandermonde det in `y_j` ; symmetric argument for `x_i` ; combine.
- **Strategy not bound** : if Route 1 surfaces unexpected friction (e.g., the polynomial extraction step doesn't compose cleanly), Route 2 (Schur complement / Dodgson condensation, 50–80 LOC per Probe 2) is the fallback.

### T2.1 — Cauchy determinant identity, abstract form (Full)
New file `Helpers/CauchyDeterminant.lean` (or appended to `GLWSmallBallShortcut.lean` if it stays under ~700 LOC), containing :

```lean
/-- Classical Cauchy determinant identity. For `x, y : Fin n → K` with all
    `x_i + y_j` invertible, the determinant of the matrix `(1/(x i + y j))` factors
    as a Vandermonde-type product. Proof via Vandermonde + multilinearity (Krattenthaler
    1999 Route 1, Probe 2 verdict). -/
theorem Matrix.det_cauchy {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K)
    (h_diag_x : Function.Injective x)
    (h_diag_y : Function.Injective y)
    (h_sum : ∀ i j, x i + y j ≠ 0) :
    Matrix.det (fun i j => (1 : K) / (x i + y j)) =
      (∏ p ∈ Finset.univ.offDiag.filter (fun p => p.1 < p.2),
        (x p.2 - x p.1) * (y p.2 - y p.1)) /
      (∏ i, ∏ j, (x i + y j)) := by
  sorry  -- TC10 lesson : strategy proposed = Vandermonde + multilinearity
```

Budget : **40–60 LOC** per Probe 2 estimate. **Risk band : low** if Mathlib's `Matrix.vandermonde_det` ergonomically composes with row-scaling.

### T2.2 — Apply to GLW hierarchical grid, prove lower bound (Full)
Replace the existing `axiom glw_det_lower_bound` with a `theorem` body :

```lean
/-- **Gao-Li-Wellner 2010 §4 Lemma 4.2 (second half)**. The structured Cauchy
    matrix on the hierarchical grid satisfies the explicit determinant lower bound.
    Proved in R63 via the Cauchy determinant identity + grid bound chain
    (R61-A axiomatisation now retired). -/
theorem glw_det_lower_bound (m : ℕ) (hm : 0 < m) :
    Matrix.det (glwMatrixA m hm) ≥ (240 * Real.exp 1) ^ (-2 * (m : ℤ) ^ 3) := by
  -- Step 1: apply Matrix.det_cauchy with x = y = hierarchicalGrid
  -- Step 2: simplify using grid distinctness (4^{p+m}(m+q) is strictly
  --         increasing in (p, q) lex order)
  -- Step 3: bound ∏_{i<j}(δ_j - δ_i)² / ∏_{i,j}(δ_i + δ_j) from below
  --         by (240·e)^{-2m³} via explicit grid product manipulation
  sorry  -- BODY ~150-300 LOC
```

**Strategy** :
1. Apply `Matrix.det_cauchy` with `x = y = hierarchicalGrid m hm` (the hypothesis `Function.Injective` follows from the grid being strictly increasing : `δ_{m·p+q} = 4^{p+m}·(m+q)` is monotone in lex order on `(p, q)`).
2. Simplify the resulting `det = (∏_{i<j}(δ_j - δ_i)²) / (∏_{i,j}(δ_i + δ_j))`.
3. Lower-bound numerator and upper-bound denominator using explicit grid values.
4. Match against the paper's `(240·e)^{-2m³}` bound. Paper's derivation (§4 / Lemma 4.2) walks this chain ; we reproduce it.

Budget : **150–300 LOC**. **Risk band : medium** — the grid-product manipulation is paper-faithful but requires careful `Finset.prod` re-indexing.

### T3 — build verification (Full)
- Targeted : `lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut` and `lake build FormalConjectures.ErdosProblems.Helpers.CauchyDeterminant` (if separate file). Must be green at <90 s each.
- Counter-check : grep callers of `glw_det_lower_bound` and confirm they all still compile (the axiom-to-theorem swap is type-preserving).

### T4 — push (Full)
- Single commit on `r46-track-a-mge-posdef` : "R63 Cauchy det identity Full + retire `glw_det_lower_bound` axiom".
- Push to `fork`.
- Append R63 status to `BACKGROUND.md` with axiom count update (10 → 9 if R61-A landed, otherwise count as appropriate).

---

## Out of scope (explicit binding)

- Cauchy det identity general-form Mathlib upstreaming (PR to mathlib4) — possible follow-up, not this round.
- Other Cauchy-matrix downstream applications — none exist in this project, but the identity becomes available.
- A4 / A5 retirement (those happen in R62, before this round).
- Carter-Pollard chain — separate Track C, TC11+.

---

## Calibration

- **Total budget** : 190–360 LOC bodies (T2.1 + T2.2). T1.0 + T1.1 + T3 + T4 are zero-LOC verification.
- **Realistic wall-clock** : 3–4 build cycles. T2.1 (Cauchy identity) is the cleaner half ; T2.2 (GLW grid application) is where most cycle-1 friction will surface.
- **Risk band** : medium. T2.2 grid-product manipulation has some unknown territory ; budget +20% if first cycle hits `Finset.prod` re-indexing pain.
- **Closure tier** : real. **Net debt change R62 → R63 : -1 axiom (drops `glw_det_lower_bound`).** Mainline ledger 16 → 15 (assuming R62 landed). Project total decreases by 1.
- **Cross-track FS discipline** : not applicable. Mainline-only round, no `lake update`, no pin bump. Track C TC12+ can run concurrently.

---

## Pre-flight checks (run before commit)

```sh
fc-main
git status
git branch --show-current                                                # r46-track-a-mge-posdef
lakecache
grep -rn "glw_det_lower_bound" --include="*.lean" --exclude-dir=.lake .   # callers
lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut 2>&1 | tail -10
```

---

## Artefact list

- `FormalConjectures/ErdosProblems/Helpers/CauchyDeterminant.lean` (new, optional ; or append to GLWSmallBallShortcut).
- `FormalConjectures/ErdosProblems/Helpers/GLWSmallBallShortcut.lean` — modified (axiom → theorem).
- `FormalConjectures/ErdosProblems/Helpers/TrackA_R63_T1_CauchyDetAudit.md` — new audit.
- `BACKGROUND.md` — appended R63 status.

End brief.
