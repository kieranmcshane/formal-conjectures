# R61 — T1 audit (mainline, `r46-track-a-mge-posdef`)

Audit grounding for the GLW closure round R61 (Path A pragmatic): `per(a) ≤ 1`
body Full + `glw_lemma_4_1_perturbation` body Full + `glw_det_lower_bound`
axiomatized with paper citation. Pins assumed: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd` (carried through R60).

Per the brief's Strategy-substitution clause (TC9 / TC10 lesson): if a
strategy substitution surfaces, document rationale in this T1.1 audit
BEFORE writing the body. R61 audit invokes that clause for
`glw_lemma_4_1_perturbation` (see §T1.3 — substitution from the brief's
multilinear-expansion-with-sign-cancellation strategy A to a cleaner
positive-product induction strategy A').

---

## T1.0 — paper recheck

R60 attempt-2 audit (`Helpers/TrackA_R60_T1_PerLemma41Audit.md` §T1.6) is
the verbatim arXiv:1001.0200v1 §4 source-of-truth at the project pin. The
R61 brief reconfirms targets:

| target | paper claim | R60-attempt-2 sig (current file) | drift? |
|---|---|---|---|
| `per(a) ≤ 1` | Lemma 4.2 first half (inequality) | `Matrix.permanent (glwMatrixA m hm) ≤ 1` (`GLWSmallBallShortcut.lean:367`) | none |
| `det(a) ≥ (240·e)^{-2m³}` | Lemma 4.2 second half | `(glwMatrixA m hm).det ≥ (240 * Real.exp 1) ^ (-2 * (m : ℤ) ^ 3)` (`GLWSmallBallShortcut.lean:368-369`) | none |
| `glw_lemma_4_1_perturbation` | Lemma 4.1, ratio-perturbation form | `det(fun i j => a i j - b i j) ≥ det a - (∑ k, sup'_l (b k l / a k l)) * per a` (`GLWSmallBallShortcut.lean:390-399`) | none |

T1.0 verdict: **no drift vs R60 audit**. Sigs are paper-faithful per the
R60 attempt-2 verbatim corrections (table at audit §T1.6). Proceed.

---

## T1.1 — Mathlib API verification at pin

| Identifier | Status | Pin location | R61 use |
|---|---|---|---|
| `Matrix.permanent` (def: `∑ σ : Perm n, ∏ i, M (σ i) i`) | VERIFIED | `LinearAlgebra/Matrix/Permanent.lean:32` | per body, Lemma 4.1 body |
| `Matrix.det_apply` (`det = ∑ σ, sgn σ • ∏ i, M (σ i) i`) | VERIFIED | `LinearAlgebra/Matrix/Determinant/Basic.lean:63` | Lemma 4.1 body |
| `Finset.prod_le_prod` (nonneg `f g`, `f ≤ g` ⇒ `∏ f ≤ ∏ g`) | VERIFIED | `Algebra/Order/BigOperators/Ring/Finset.lean:43` | per body crude bound, Lemma 4.1 ratio bound |
| `Finset.prod_le_pow_card` | VERIFIED | `Algebra/Order/BigOperators/Group/Finset.lean:211` | per body crude bound |
| `Finset.le_sup'` / `Finset.sup'_le` | VERIFIED | `Data/Finset/Lattice/Fold.lean:736 / :729` | Lemma 4.1 ratio bound |
| `Nat.factorial_le_pow` (`n! ≤ n^n`) | VERIFIED | `Data/Nat/Factorial/Basic.lean:181` | per body arithmetic |
| `Fintype.card_perm` (`#Perm α = (#α)!`) | VERIFIED | `Data/Fintype/Perm.lean:159` | per body card-of-perm-set |
| `Real.exp` / `Real.exp_pos` | VERIFIED | `Analysis/SpecialFunctions/Exp.lean` | det axiom statement |
| `(_ : ℝ) ^ (_ : ℤ)` (`zpow`) | VERIFIED | derived | det axiom exponent (`-2 * m^3`) |
| `Equiv.Perm.sign_def` / `sign_one` (sgn ∈ {-1, +1}, `|sgn σ • r| = |r|`) | VERIFIED | `GroupTheory/Perm/Sign.lean` | Lemma 4.1 sgn-bound step |

Brief's references "`Matrix.permanent_le_*`" — **not present at pin**.
Crude bound is derived from the `Matrix.permanent` definition directly
(unfold + `Finset.prod_le_prod` + `Finset.sum_le_card_nsmul` /
`Finset.sum_const`).

Brief's references "`Matrix.det_succ_row` / `Matrix.det_eq_sum_perm`" —
`det_apply` (cited above) is the direct Leibniz form and supersedes
the brief's mention of multilinear expansion lemmas. The Lemma 4.1
body uses `det_apply` to expand both `det a` and `det (a − b)` and
operates on the per-σ Leibniz term `sgn σ • ∏ i, M (σ i) i`.

---

## T1.2 — `per(a) ≤ 1` strategy commitment (Strategy A, no substitution)

Brief Strategy A is mathematically sound and Lean-ergonomic. No
substitution. Proof outline:

1. **Min grid value** (`hierarchicalGrid m hm i ≥ 4^m · (m+1)`): direct
   from `δ_i = 4^{p+m} · (m+q)` with `p ≥ 0, q ≥ 1` ⇒ `4^{p+m} ≥ 4^m`
   and `m+q ≥ m+1`. Uses `pow_le_pow_right_of_le_one`'s dual or
   `pow_le_pow_right` (mono in exponent for base ≥ 1).
2. **Max matrix entry** (`A i j ≤ 1/(2·4^m·(m+1))`): from step 1,
   `δ_i + δ_j ≥ 2·4^m·(m+1)`, hence `1/(δ_i + δ_j) ≤ 1/(2·4^m·(m+1))`
   via `one_div_le_one_div_of_le` (or `div_le_div_of_nonneg_left`).
3. **Crude permanent bound** (`per A ≤ (m²)! · (max entry)^{m²}`):
   unfold `Matrix.permanent`; for each σ, `∏ i, A (σ i) i ≤ (max)^{m²}`
   via `Finset.prod_le_prod` (entries pos, bounded by max) +
   `Finset.prod_const`. Then `∑_σ (max)^{m²} = #Perm · (max)^{m²} =
   (m²)! · (max)^{m²}` via `Finset.sum_const` + `Fintype.card_perm`.
4. **Final inequality** (`(m²)! · (max)^{m²} ≤ 1`): equivalent to
   `(2·4^m·(m+1))^{m²} ≥ (m²)!`. Chain:
   - `(m²)! ≤ (m²)^{m²}` via `Nat.factorial_le_pow`.
   - `m² ≤ 4^m` for `m ≥ 1` (induction; m=1: 1≤4, step: `(m+1)² =
     m²+2m+1 ≤ 4·4^m = 4^{m+1}` since `2m+1 ≤ 3·4^m` for m ≥ 1).
   - `m² ≤ 4^m ≤ 2·4^m·(m+1)` (since `2(m+1) ≥ 1`).
   - Hence `(m²)^{m²} ≤ (2·4^m·(m+1))^{m²}` via `Nat.pow_le_pow_left`.

LOC budget: ~150-200 (steps 1-2 ~25 LOC, step 3 ~50 LOC, step 4 ~75
LOC including the `m² ≤ 4^m` induction).

Risks:
- **(a)** Cast bookkeeping ℕ ↔ ℝ is the dominant pain. Mitigation:
  prove key arithmetic facts in ℕ, cast at the end.
- **(b)** `Finset.prod_le_prod` requires nonneg on both sides; both are
  positive for the Cauchy entries (denominators positive sums of grid
  values). Direct.

## T1.3 — `glw_lemma_4_1_perturbation` strategy substitution (A → A')

Brief Strategy A: **multilinear column expansion** + sign-tracking
across `(-1)^|S|` cross-terms. Step 6 ("higher-order |S|≥2 terms
absorbed via sign control") is the documented cycle-1 risk.

**Sign-tracking is mathematically the wrong frame.** The Leibniz
expansion `∏_i (a_(σi,i) - b_(σi,i))` distributes pointwise into
`∑_S (-1)^|S| ∏_S b · ∏_{∉S} a`, but multiplying by `sgn σ` and
summing gives `det(a-b) = ∑_S (-1)^|S| det(N_S)` where `N_S` is a
mixed matrix. For arbitrary positive matrices, `det(N_S)` for
`|S| ≥ 2` is not sign-controlled, so the brief's "absorb into
|S|=1 estimate" is non-trivial to formalize.

**Strategy A' (substitution, mathematically cleaner):** prove the
inequality at the *pointwise* level on each Leibniz product, before
the σ-sum. Concretely:

For positive reals `x_1, ..., x_n` and `0 ≤ y_i ≤ x_i`:

```
∏_i x_i − ∏_i (x_i − y_i) ≤ ∑_k y_k · ∏_{i ≠ k} x_i.    (★)
```

**Proof of (★)** by induction on `Finset.card s`:
- Base (`s = ∅`): both sides 0.
- Step (`s = insert k s'`, `k ∉ s'`): expand
  `x_k · ∏_{s'} x − (x_k − y_k) · ∏_{s'} (x − y) =
   x_k · (∏_{s'} x − ∏_{s'} (x − y)) + y_k · ∏_{s'} (x − y)`,
  apply IH to first term, use `∏_{s'} (x − y) ≤ ∏_{s'} x` for second.

(★) is ~30-40 LOC.

**Apply (★) per σ** with `x_i := a (σi) i`, `y_i := b (σi) i`:
`∏_i a (σi) i − ∏_i (a (σi) i − b (σi) i) ≤ ∑_k b (σk) k · ∏_{i ≠ k} a (σi) i`.

**Key sign step** (cleaner than brief's cross-term tracking):
```
det a − det(a − b) = ∑_σ sgn σ • [∏_i a (σi) i − ∏_i (a (σi) i − b (σi) i)]
                  ≤ ∑_σ |sgn σ • ...|
                  = ∑_σ (∏_i a (σi) i − ∏_i (a (σi) i − b (σi) i))
                                                       [since term ≥ 0 by (★)'s positivity context]
                  ≤ ∑_σ ∑_k b (σk) k · ∏_{i ≠ k} a (σi) i              [apply (★)]
                  ≤ ∑_σ ∑_k r_k · a (σk) k · ∏_{i ≠ k} a (σi) i        [b ≤ r · a entrywise]
                  = ∑_k r_k · ∑_σ ∏_i a (σi) i                          [Fubini + factor]
                  = (∑_k r_k) · per a
```

where `r_k := sup'_l (b_{kl}/a_{kl})` and the second-to-last step
uses `b_{σk,k} ≤ r_k · a_{σk,k}` (from `Finset.le_sup'` applied at
`l = k` after the `div_le_iff`).

The `|sgn σ • r| = |r|` step uses the fact that `sgn σ • r = ±r`
and `|r| = r` when `r ≥ 0`. Concretely: `det a − det(a-b) ≤ ∑_σ
(∏ a − ∏(a-b))` is shown by `abs_sum_le_sum_abs` + per-term
`|sgn σ • t| = |t| = t` (when `t ≥ 0`).

LOC budget: ~30-40 LOC for (★) + ~50-80 LOC for the σ-sum
aggregation = ~80-120 LOC. **Matches brief budget**, with the
risk profile shifted from sign-tracking on |S|≥2 cross terms (hard
to formalize) to nonneg-product manipulation (easier).

**Why substitute now, not in cycle 2:** the brief's sign-control
recipe is mathematically valid only with extra structure (e.g. PSD
or specific positivity that propagates through |S|≥2 minor
expansions); this audit's positive-product induction handles
*any* `0 < b < a` entrywise, matches the sig's hypothesis exactly,
and is the textbook form for first-order matrix-perturbation
inequalities.

Risks under A':
- **(a)** The pointwise step uses `0 ≤ ∏ a − ∏(a-b)` (each factor
  nonneg). Direct from `0 < a-b ≤ a` entrywise.
- **(b)** Fubini swap on `∑_σ ∑_k` ↔ `∑_k ∑_σ`: standard,
  `Finset.sum_comm`.
- **(c)** `∑_σ a (σk) k · ∏_{i≠k} a (σi) i = per a`: by reindexing,
  `a (σk) k · ∏_{i≠k} a (σi) i = ∏_i a (σi) i` (multiply back the
  erased factor). So `∑_σ ∏_i a (σi) i = per a` directly. ~5 LOC.

---

## T1.4 — `glw_det_lower_bound` axiom block

Statement (per brief T2.1):

```lean
/-- Axiom: explicit determinant lower bound from Gao-Li-Wellner 2010 §4
    Lemma 4.2 (second half). Paper-stated value `(240·e)^{-2m³}`. Proof
    requires the Cauchy determinant identity (NOT in Mathlib at pin
    `25ce63313608`) plus telescoping over the hierarchical grid, ~500-700
    LOC + ~30-60 LOC Cauchy det. Axiomatized under hybrid (c) Path A
    pragmatic per BACKGROUND.md R52 gate decision. -/
axiom glw_det_lower_bound (m : ℕ) (hm : 0 < m) :
    Matrix.det (glwMatrixA m hm) ≥ (240 * Real.exp 1) ^ (-2 * (m : ℤ) ^ 3)
```

Inserted in the `Erdos524.Helpers.GLWSmallBallShortcut` namespace block
introduced for the R59→R60 paper-faithful sigs (after `glwMatrixB`,
before `glw_lemma_4_2_paper_specs`).

Axiom inventory: was 9, becomes **10** post-R61.

The det lower bound's body is genuinely 500-700 LOC + a from-scratch
Cauchy determinant identity (~30-60 LOC); the project's R52 gate
decision authorises Path A (axiomatize a paper-stated quantitative
bound) when the pure-body alternative is high-stall-risk in a single
round.

---

## T1.5 — Sub-checkpointing (Q7 binding)

- T+0:30: ✅ T1.1 audit (this doc complete).
- T+1:00: T2.1 axiom block insertion.
- T+2:30: T2.2 `per(a) ≤ 1` body Full.
- T+4:00: T2.3 `glw_lemma_4_1_perturbation` body Full (Strategy A').
- T+4:30: T3 build verification.
- T+5:00: T4 push + BACKGROUND.md update.
- Hard stop T+5:30.

---

## T1.6 — Confidence (Q7 calibrated)

| Outcome | Region | P(Full) raw | Calibrated |
|---|---|---|---|
| T1.1 audit (this doc) | computational | 1.00 | 1.00 |
| T2.1 axiom block | mechanical | 0.99 | 0.99 |
| T2.2 per body Full | semi-populated | 0.75 | **0.65** (cast bookkeeping risk) |
| T2.3 Lemma 4.1 body Full (Strategy A') | semi-populated | 0.70 | **0.60** (positive-product induction is cleaner than sign-tracking but still ~80-120 LOC) |
| T3 build green | computational | 0.95 | 0.92 |
| T4 push + BACKGROUND update | mechanical | 0.95 | 0.95 |

Joint floor (mandatory tasks): ~0.55. Best case (P~0.40):
both bodies Full, axiom in, build green, BACKGROUND.md updated → R61
delivers brief's target -2 sorries + 1 axiom = -1 net debt.

---

## T1.7 — Out of scope (Q7 binding)

- `det(a) ≥ (240·e)^{-2m³}` body proper (axiomatized this round).
- A4 (`gao_li_wellner_small_ball_lower`) retirement — staged R62.
- A5 (`gao_li_wellner_small_ball_upper`) retirement — staged R62.
- Carter-Pollard Track C — separate, TC11+.
- Mainline modifications outside `GLWSmallBallShortcut.lean` and
  `BACKGROUND.md`.
- R50 historical sub-Stubs (`glw_lemma_4_1_deferred_paper`,
  `glw_lemma_4_2_deferred_paper`) — preserved as conservative-shape
  deferral records, no retirement.

---

## T1.8 — Anti-patterns explicitly forbidden (per brief)

- Multi-step Carter-Pollard assembly (Q7 binding).
- Skip cache check (R61 dispatch confirms `lake exe cache get` is a
  user-managed concern; not run by dispatch as the worktree is
  pre-built).
- Skip Claims Verification Table (this doc is the table).
- Modify TC1-TC8 / TC9-TC10 Full theorems.
- Modify mainline OR track-d outside the targeted helper.
- Push to wrong branch.
- Plan doc as substitute for code.
- Strategy substitution post-hoc (this audit invokes the
  TC10-protocol substitution clause for Lemma 4.1 BEFORE writing
  the body — see §T1.3).

End audit.
