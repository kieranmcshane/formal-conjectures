# R60 — T1 audit (mainline, `r46-track-a-mge-posdef`)

Audit grounding for the GLW twin closure round R60 (per(A) = 1 +
Lemma 4.1 perturbation). Pins assumed: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd` (carried through R59).

Per the brief's Strategy-substitution clause (TC9 lesson):
*"document rationale in audit doc T1.1 BEFORE writing the body, not
post-hoc"*. This audit invokes that clause, and goes one level
deeper: the issue surfaced is not Strategy-A vs Strategy-B, but a
**claim/definition mismatch** in the R59 infrastructure that the
R59 audit doc itself flagged as not-independently-verified
(`TrackA_R59_T1_GrepAudit.md` lines 94–108). R60 body work is
**halted at T1.1** pending user dispatch on resolution path.

---

## T1.1a — Mathlib API verification at pin

| Identifier | Status | Pin location | R60 use |
|---|---|---|---|
| `Matrix.permanent` | ✅ | `LinearAlgebra/Matrix/Permanent.lean:32` | per body |
| `Matrix.permanent_one` | ✅ | `LinearAlgebra/Matrix/Permanent.lean:45` | per body |
| `Matrix.permanent_diagonal` | ✅ | `LinearAlgebra/Matrix/Permanent.lean:35` | per body (diag-shortcut Strategy B candidate) |
| `Matrix.permanent_unique` (n=1) | ✅ | `LinearAlgebra/Matrix/Permanent.lean:58` | m=1 sanity |
| `Matrix.permanent_eq_elem_of_card_eq_one` | ✅ | `LinearAlgebra/Matrix/Permanent.lean:66` | m=1 sanity |
| `Matrix.det_apply` | ✅ | `LinearAlgebra/Matrix/Determinant/Basic.lean:63` | Lemma 4.1 |
| `Matrix.det_apply'` | ✅ | `LinearAlgebra/Matrix/Determinant/Basic.lean:67` | Lemma 4.1 |
| `Finset.sum_le_card_nsmul` / crude bound analogs | (deferred) | — | per body Strategy-A step 3 |
| `Matrix.det_succ_row` | (deferred — only needed if Strategy-B fallback) | — | Lemma 4.1 fallback |

`Matrix.permanent` definition at pin (lines 30–32 of
`Permanent.lean`):
```
def permanent (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i
```
No alternating signs. Sum over all `Fintype.card n)!` permutations,
each contributing a product of n entries.

Note that the brief's references "`Matrix.permanent_eq_sum_over_perm`"
and "`Finset.sum_le_card_mul_max`" do not exist verbatim at pin —
the closest forms are the unfold of `Matrix.permanent` itself (the
sum is the definition, not a separate lemma) and
`Finset.sum_le_card_nsmul` / `Finset.sum_le_sum`. Recoverable, but
flagging the brief's identifier names as approximate.

---

## T1.1b — paper recheck

**Status: BLOCKED at dispatch.** The R59 audit doc explicitly
records (lines 94–108):

> *"Per the R59 brief, the paper recheck was performed by Cowork
> during brief composition, NOT independently re-verified at
> dispatch time. WebFetch / external paper retrieval is out of
> scope for this round. **If R60–R61 surface a mismatch with the
> paper while filling bodies, the calibration should be revisited
> and the formulas in `glwMatrixA` / `glw_lemma_4_2_paper_specs`
> updated** (this is signature-only work, no consumer file consumes
> them at R59 close)."*

R60 dispatch is also without external paper access. The audit
below proceeds by **internal computational checks** of the R59
infrastructure against the R60 brief's stated claims.

---

## T1.2 — claim/definition consistency check (NEW finding)

The R59 infrastructure encodes (`GLWSmallBallShortcut.lean:362–367`):

```lean
noncomputable def glwMatrixA (m : ℕ) (hm : 0 < m) :
    Matrix (Fin (m * m)) (Fin (m * m)) ℝ :=
  fun i j =>
    let δi := hierarchicalGrid m hm i
    let δj := hierarchicalGrid m hm j
    if i = j then δi * δj else Real.exp (-(δi * δj))
```

with `hierarchicalGrid m hm i = 4·m / (m + ((i.val % m) + 1))`
(`GLWSmallBallShortcut.lean:325–327`).

The R59 sig (`GLWSmallBallShortcut.lean:386–390`) claims:

```
Matrix.permanent (glwMatrixA m hm) = 1 ∧
(glwMatrixA m hm).det = (32 : ℝ) ^ m * ((240 : ℝ) * Real.exp (-3)) ^ m
```

### Computational disproof of `permanent = 1`

**m = 1**:
- Grid: `δ_0 = 4·1 / (1 + (0%1 + 1)) = 4/2 = 2`.
- Matrix: `glwMatrixA 1 hm = [[δ_0 · δ_0]] = [[4]]` (1×1).
- Permanent: by `permanent_eq_elem_of_card_eq_one`, `perm = A 0 0 = 4`.
- **Claimed:** `permanent = 1`. **Actual:** `permanent = 4`.
- Mismatch: factor of 4.

**m = 2**:
- Grid (4 entries via flat encoding):
  - `δ_0 = 8 / (2 + (0%2 + 1)) = 8/3 ≈ 2.667`
  - `δ_1 = 8 / (2 + (1%2 + 1)) = 8/4 = 2`
  - `δ_2 = 8 / (2 + (2%2 + 1)) = 8/3`
  - `δ_3 = 8 / (2 + (3%2 + 1)) = 8/4 = 2`
- Diagonal: `δ_i^2 ∈ {64/9, 4, 64/9, 4} = {7.111, 4, 7.111, 4}`.
- Off-diagonal sample: `A_{01} = exp(−δ_0·δ_1) = exp(−16/3) ≈ 4.83 × 10⁻³`.
- Numerical permanent (sum of 4! = 24 products): **≈ 809.1**.
- **Claimed:** `permanent = 1`. **Actual:** ~809.

The mismatch is **not numerical noise**: it is structural. Identity-
permutation contribution alone is `∏ A_ii = (64/9)·4·(64/9)·4 ≈ 202`,
already 200× the claimed value.

### Why no normalization can save the claim

Row/column scaling: scaling row `i` by `c_i` multiplies the
permanent by `∏ c_i`. To force `A_ii = 1`, scale row `i` by `1/δ_i^2`:
this divides the permanent by `∏ δ_i^2`. For m=1, `per(A) = 4`,
divide by `δ_0^2 = 4`, get `1`. ✓ (trivially, since A becomes [[1]]).
For m=2, dividing by `∏ δ_i^2 = (64/9)·4·(64/9)·4 ≈ 202` gives
`per(A_normalized) ≈ 4.0`, **not 1**. So even with diagonal-1
normalization, the claim fails.

### Why the brief's Strategy A is mathematically broken

Brief Strategy A "5 steps":
> 1. Diag = 1, off-diag ≤ `r` (computational, grid evaluation).
> 2. Lower bound from id-perm + non-negativity.
> 3. Crude upper `per(A) ≤ n! · max_{i,j} a_{ij}^n`.
> 4. Plug grid constants: `n! · r^n ≤ 1` for `n = m^2`, `r ≤ (2m^4)^{-1}`.
> 5. `le_antisymm` to conclude.

Even on a hypothetical "fixed" matrix with `A_ii = 1` and
`A_ij ∈ [0, r]` for `i ≠ j` and `r > 0`, the crude bound at step 3
gives `max_{i,j} a_{ij} = max(1, r) = 1` (since diagonal = 1), so
`n! · max^n = n!`, not `n! · r^n`. The chain `n! · r^n ≤ 1` does
not bound the permanent. The strategy proves `per(A) ≥ 1` via
step 2 but cannot prove `per(A) ≤ 1` via steps 3–4.

A genuine `per(A) = 1` proof for a matrix with `A_ii = 1` and any
`A_ij > 0` for some `i ≠ j` is impossible: the identity permutation
contributes 1, and at least one other permutation contributes a
strictly positive product, so `per(A) > 1` strictly.

The only matrix shapes consistent with `per(A) = 1` and the brief's
strategy are: (a) the identity matrix, or (b) any matrix with
`A_ij = 0` for all `i ≠ j` and `∏ A_ii = 1`. Neither matches the
R59 `glwMatrixA` definition.

### Likely root cause

Either (or both):

- **(R-1)** The R59 paper-recheck mis-read the GLW 2010 §4 matrix
  entries. The actual paper matrix may have a different diagonal
  (e.g. `1`) and/or different off-diagonal scaling, and the
  `permanent = 1` claim only holds for the actual paper form.
- **(R-2)** The R59 paper-recheck mis-read the Lemma 4.2 conclusion.
  The actual paper claim about `permanent(A)` may be a different
  value (or a different functional, e.g. a normalized permanent or
  a permanent of `A − I`) that happens to equal 1 for the actual
  paper matrix.

Without arXiv:1001.0200v1 access at dispatch, neither root cause
can be pinned. The R59 uncertainty flag (lines 94–108 of
`TrackA_R59_T1_GrepAudit.md`) explicitly anticipated this exact
scenario and authorized signature-level revision in R60.

---

## T1.3 — Lemma 4.1 perturbation: independent assessment

`glw_lemma_4_1_perturbation` (`GLWSmallBallShortcut.lean:409–416`)
is the second R60 closure target. **It is independent of the
`glwMatrixA` / `permanent = 1` issue above** — it is a generic
square-matrix perturbation inequality on arbitrary `A B : Matrix ι ι ℝ`
with `B ≤ A` entrywise and `0 ≤ B` entrywise.

### Mathematical content

Statement:
```
det B ≥ det A − (∑ k, (∑ l, B k l) · rowSup A k) · permanent A.
```

Quick sanity (1×1, ι = Fin 1): `det B = B 0 0`, `det A = A 0 0`,
`∑ k, (∑ l, B k l) · rowSup A k = B 0 0 · A 0 0`, `permanent A = A 0 0`.
RHS = `A 0 0 − B 0 0 · A 0 0 · A 0 0 = A 0 0 (1 − B 0 0 · A 0 0)`.
Inequality: `B 0 0 ≥ A 0 0 (1 − B 0 0 · A 0 0)`, i.e.
`B 0 0 ≥ A 0 0 − B 0 0 · A 0 0^2`, i.e.
`B 0 0 (1 + A 0 0^2) ≥ A 0 0`.

Take `A 0 0 = 2`, `B 0 0 = 0` (allowed: `B ≤ A`, `B ≥ 0`).
`LHS = 0`, `RHS = 2 (1 − 0) = 2`. **0 ≥ 2 is false.**

The 1×1 case **disproves** the perturbation inequality as stated.
Either `B ≤ A` entrywise needs strengthening (e.g. PSD-order, or
spectral comparison), or the RHS needs a different scalar (e.g.
the paper may quantify `(A - B)` rather than `B` on the RHS, or
use a row-sum of `(A - B)` instead of `B`).

### Likely correct paper form (speculative)

The paper's Lemma 4.1 is plausibly something like
```
det A − det B ≤ (∑ k, (∑ l, (A k l − B k l)) · rowSup A k) · permanent A,
```
i.e. the perturbation is `(A - B)`, not `B`, on the RHS sum. With
`A 0 0 = 2`, `B 0 0 = 0`: RHS = `(2 − 0) · 2 · 2 = 8`,
`det A − det B = 2 − 0 = 2`, and `2 ≤ 8` holds. ✓

But this is **speculation without paper access**. The R59 sig
encodes `B k l` on the RHS (not `A k l − B k l`), and the
1×1 counterexample above shows that form is not provable.

---

## T1.4 — verdict

Both R60 closure targets have **claim-level issues** independent of
proof strategy:

1. `glw_lemma_4_2_paper_specs` permanent half: the claim
   `permanent (glwMatrixA m hm) = 1` is **false for m=1** (perm = 4)
   and **false for m=2** (perm ≈ 809). Either the matrix definition
   or the claimed value is wrong relative to GLW 2010 §4.

2. `glw_lemma_4_1_perturbation`: the inequality as stated is
   **false for ι = Fin 1, A = [[2]], B = [[0]]** (LHS 0, RHS 2).
   The RHS likely needs `(A - B)` instead of `B`, but this is
   speculation without paper access.

**Recommendation: HALT R60 body work pending user dispatch.**

R59 explicitly authorized signature-level revision in this exact
scenario. The brief's Q7 scope binding ("R60 = bodies … ONLY")
implicitly assumed the R59 sigs were paper-faithful; that
assumption fails empirically.

### Resolution paths (for user)

- **(P-A)** **Paper-faithfulness recheck**: user fetches GLW 2010
  arXiv:1001.0200v1 §4, confirms exact matrix entries + Lemma 4.2
  conclusion + Lemma 4.1 perturbation form. R60 then refines the
  R59 signatures to match (sig-level work, ~30–60 LOC), and the
  bodies stage to R61+ depending on revised difficulty.

- **(P-B)** **Re-derive from in-tree alternates**: the mainline
  contains 5909+ LOC alternate Q1a/b/c track (`CauchyDetLowerBound`,
  `CharFunCrossBlock`, `MultivariateSmallBallUpper`,
  `SurgicalDensityAtZero`, `EsseenSmoothing`, `GaussianHierCauchyBox`)
  per the R50 chain-mismatch finding. Reuse those instead of GLW 2010
  §4 forms.

- **(P-C)** **Refine claims to what the R59 matrix actually
  satisfies**: e.g. compute `permanent (glwMatrixA m hm)` symbolically
  in Lean (likely a complicated expression involving `δ_i^2` products
  + exp-tail corrections), state Lemma 4.2 as that value, retire the
  `= 1` form. This makes the round still infra-flavored (sig revision
  + value characterization) rather than closure.

- **(P-D)** **Defer R60 to R61+**: leave the R59 sorries in place,
  use R60 cycle for a different track (e.g. accelerate R62 A4/A5
  prep, or sweep Track D).

Tier (P-A) is the highest-information-yield. Tier (P-D) is the
cheapest. The author of this audit recommends (P-A) if paper access
is available, otherwise (P-D) — **(P-C) is mathematically valid
but framing it as "closure" would violate the
`feedback_erdos524_framing` discipline (closure-tier language for
infra work)**.

---

## T1.5 — what was NOT done in R60 dispatch (attempt 1)

Per the §T1.4 verdict, the following attempt-1 brief tasks were not
executed:

- T2.1 (`per(A) = 1` body): not written. Claim disproved.
- T2.2 (Lemma 4.1 body): not written. Inequality disproved.
- T2.3 (build verification): not run (no body to verify).
- T2.4 (commit + push): not run.
- BACKGROUND.md R60 status section: not appended.

Round halted at T1.1 for user dispatch.

---

## T1.6 — paper-faithful resolution (R60 attempt 2 — INFRA round)

User dispatched a corrected R60 brief (sig revision, NOT closure)
with verbatim arXiv:1001.0200v1 §4 paper data fetched via Cowork.
Attempt 2 executes path **(P-A)** from §T1.4. Bodies remain `sorry`
and are re-tagged for R61 destinations; net debt unchanged (sorry
count constant, axiom count constant, Stub retirements 0).

### Verbatim corrections (6, against R59)

| # | Item | R59 (paper-incorrect) | R60 attempt-2 (paper-exact) |
|---|---|---|---|
| 1 | Dimension `n` | `m²` ✓ | `m²` ✓ (no change) |
| 2 | Grid `δ_{m·p+q}` | `4·m / (m + q)` | `4^{p+m} · (m+q)` |
| 3 | Matrix `A` entries | diag `δ_i²`, off-diag `exp(−δ_i·δ_j)` | Cauchy: `1 / (δ_i + δ_j)` |
| 4 | Auxiliary matrix `B` | (absent) | `b_{ij} = exp(−δ_i − δ_j) · a_{ij}` |
| 5 | Lemma 4.2 conclusions | `per(A) = 1 ∧ det(A) = 32^m·(240·e^{-3})^m` | `per(A) ≤ 1 ∧ det(A) ≥ (240·e)^{-2m³}`; **both inequalities** |
| 6 | Lemma 4.1 perturbation | `det B ≥ det A − (∑_k (∑_l B k l) · rowSup A k) · per A` (RHS uses `B` raw) | `det(a − b) ≥ det a − (∑_k max_l (b_{kl}/a_{kl})) · per a` (RHS uses `(a − b)` and a max-RATIO) |

### Empirical sanity at m=1 (R60 attempt-2 sigs)

- Grid: `δ_{0·1+1} = 4^{0+1} · (1+1) = 4·2 = 8`. (Brief value matches.)
- Matrix `A = [[1/(8+8)]] = [[1/16]]`. `permanent = 1/16 = 0.0625`.
  **`0.0625 ≤ 1` ✓**.
- Det lower bound at m=1: `(240·e)^{-2·1³} = 1/(240·e)² ≈ 2.35 × 10⁻⁶`.
  `det(A) = 1/16 = 0.0625 ≥ 2.35e-6` **✓**.
- Lemma 4.1 (ι = Fin 1, `a = [[2]]`, `b = [[0.5]]`): `0 < a, 0 < b < a` ✓.
  - LHS: `det(a − b) = 1.5`.
  - `max_l (b_{0l}/a_{0l}) = 0.5/2 = 0.25`. Sum over `k = 0`: `0.25`.
  - `per(a) = 2`.
  - RHS: `det(a) − 0.25 · 2 = 2 − 0.5 = 1.5`.
  - `1.5 ≥ 1.5` **✓** (equality at this case).

### Mathlib API additions (vs §T1.1a)

| Identifier | Status | Pin location | R60-attempt-2 use |
|---|---|---|---|
| `Real.exp` | ✅ | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | det lower bound |
| `(_ : ℝ) ^ (_ : ℤ)` (`zpow`) | ✅ | derived via `LinearOrderedField` | det exponent |
| `_ / _` on ℝ | ✅ | trivial | Cauchy entry, Lemma 4.1 ratio |
| `Finset.sup'` (with explicit `nonempty`) | ✅ | as §T1.1a | Lemma 4.1 row-max-ratio (inlined) |

### Status

R60 attempt 2 = INFRASTRUCTURE round (sig revision against verbatim
paper). Bodies stage to R61. Net debt R59 → R60: 0/0/0 (TAGs migrate
from `R60-*` / `R61-*` destinations to `R61-*` only; sorry count
constant). The R59 helper `Matrix.rowSup` becomes dead code (paper
Lemma 4.1 uses a `b/a` ratio sup, not a row max of `A` alone) and is
removed in attempt 2.

### Calibration lesson (memory-worthy)

When a brief is drafted from Cowork-derived paper recall (no
independent verification at draft time), the next round's audit
MUST fetch the paper before writing any body. R59's hedge clause
(`TrackA_R59_T1_GrepAudit.md` lines 94–108) authorised exactly
this revision; the attempt-1/attempt-2 split is the audit-first
discipline working as intended.

---

End audit.
