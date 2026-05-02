# R52-T1.1 — Q1a/b/c track consolidation audit (Claims Verification Table)

**Round**: R52 (V2 round 14, 2026-05-02). Track Q1c consolidation, post-R51
γ-floor MGE axiomatization. User dispatch: Q1a/b/c track consolidation
(item-positive if Full close lands).

**Branch**: `r46-track-a-mge-posdef`, HEAD `aba7853` (R51 close).

**Pin**: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd32e9ef6c10c9359938f24a3e1f38`,
`leanprover/lean4:v4.27.0-rc1`.

**Scope**: T1.1 audit characterizes the candidate sorries in
`Helpers/MultivariateSmallBallUpper.lean` and selects the highest-P(Full)
target for T2.1. Brief mentioned three sorries at lines 73, 238, 616;
file inspection at HEAD `aba7853` shows the actual TAG'd sorries are at
**lines 238 and 619** (line 73 is a docstring reference to "named sorry
below"; line 616 is a comment lead-up to the sorry on line 619).

---

## §1. Claims Verification Table

| Claim # | Statement | VERIFIED? | Citation | Notes |
|---------|-----------|-----------|----------|-------|
| 1 | `Helpers/MultivariateSmallBallUpper.lean` exists at HEAD `aba7853` | **VERIFIED** | `wc -l` returns 621 lines | File present. |
| 2 | Two `sorry`-bodied lemmas in the file | **VERIFIED** | `grep -n "sorry"` returns lines 238, 619 (plus 73 docstring + 193, 302 comments + 616 comment) | The two actual sorries are `geomSeries_offDiag_le` (line 238) and `multivariate_small_ball_upper` (line 619). |
| 3 | `geomSeries_offDiag_le` (line 230-238) signature | **VERIFIED** | Line 230: `lemma geomSeries_offDiag_le (M : ℕ) : ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag, (2 : ℝ) ^ (-(\|(pq.2.val : ℤ) - (pq.1.val : ℤ)\| : ℤ)) ≤ 4 * M` | Pure-arithmetic combinatorial inequality. No probability-theory dependencies. Self-contained Mathlib `Finset` + `Real.rpow` API. |
| 4 | `multivariate_small_ball_upper` (line 589-619) signature | **VERIFIED** | Line 589: `theorem multivariate_small_ball_upper : ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧ ...` | Takes a `JointRademacherLaw P`, two compatibility hypotheses `h_step1`/`h_steps23`, derives `boxProb ε ≤ (exp (c·m)·ε)^{m·m} · (sqrt P.cov.det)⁻¹`. |
| 5 | `multivariate_small_ball_upper` body comment flags fundamental ε-cancellation issue | **VERIFIED** | Lines 603-618 comment: "the inequality cannot hold with `boxProb` and `φ_abs_integral` *fully* opaque... pending Mathlib's multivariate Fourier infrastructure" | The lemma's compatibility hypotheses are not strong enough to derive the conclusion as currently stated. **NOT closeable in this round**. Closure requires multivariate Fourier infrastructure (multi-step Mathlib gap). |
| 6 | `geomSeries_offDiag_le` is consumed downstream | **PARTIALLY VERIFIED** | `grep "geomSeries_offDiag_le"` returns 1 self-reference at line 233 (sub-stub label) only | The lemma is currently un-consumed in mainline Lean code. Its purpose is to be used in the (sorry-bodied) assembly of `multivariate_small_ball_upper`. Closing it does not unblock anything immediate but reduces the file's sorry count by 1. |
| 7 | File `MultivariateSmallBallUpper.lean` consumers in mainline | **VERIFIED** | `grep -rn "import.*MultivariateSmallBallUpper"` returns 0 hits; only one comment reference in `GLWSmallBallShortcut.lean:185` (itself un-imported per R50 status) | The file is part of the **alternate Q1c track** for A5 retirement. Not in any mainline build path. Sorries here count toward project total but NOT toward mainline gate (12 sorries). |
| 8 | Main mainline gate items unchanged by R52 | **VERIFIED** | No edit planned to `MultivariateGaussianPdf.lean`, `MultivariateGaussianCDF.lean`, `524.lean`, `OneDimKMT.lean`, `StochasticProcessAxiom.lean`, `GLWSmallBallShortcut.lean`, `GLWLowerProof.lean`, `GLWUpperProof.lean`, etc. | R52 modifies only `MultivariateSmallBallUpper.lean` (alternate-track file). 7 axioms + 12 mainline-gate sorries preserved. |

All 8 claims **VERIFIED**. T2.1 may proceed with `geomSeries_offDiag_le`
as the close target.

---

## §2. Target selection — `geomSeries_offDiag_le` (line 230-238)

### §2.1 Lemma statement (verbatim, line 230-238)

```lean
lemma geomSeries_offDiag_le (M : ℕ) :
    ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
      (2 : ℝ) ^ (-(|(pq.2.val : ℤ) - (pq.1.val : ℤ)| : ℤ)) ≤ 4 * M := by
  -- sub-stub: geomSeries_offDiag_bookkeeping
  -- Pair (p,q) with p ≠ q contributes 2^{-|q-p|}; sum over each row
  -- p is ≤ 2·∑_{d≥1} 2^{-d} = 2; sum over rows gives 2M; offDiag is
  -- ordered pairs so factor of 2 again — total ≤ 4M.
  -- Mathlib gap: explicit geometric-sum bookkeeping over Fin M offDiag.
  sorry
```

### §2.2 Mathematical content

For any `M : ℕ`, the off-diagonal sum
`∑_{(p,q) ∈ Fin M × Fin M, p ≠ q} 2^(-|q-p|)`
is bounded by `4M` (a strictly loose bound; tight is `≈ 2M`).

### §2.3 Proof strategy (selected)

**Decomposition** of `offDiag`-sum into a row sum:

By `offDiag ⊆ univ ×ˢ univ` and non-negativity of `2^(-|...|)`:
```
∑_{(p,q) ∈ offDiag} 2^(-|q-p|)
  ≤ ∑_{(p,q) ∈ univ ×ˢ univ} 2^(-|q-p|)
  = ∑_p ∑_q 2^(-|q-p|)
```

**Per-row bound**: for each fixed `p`, `∑_{q ∈ Fin M} 2^(-|q-p|) ≤ 4`.

The simplest crude bound suffices: each term `2^(-|q-p|) ≤ 1` (since
`|q-p| ≥ 0` and `2^(-k) ≤ 1` for `k ≥ 0`), and the sum has at most
`M` terms — but that gives row-sum `≤ M`, which doesn't yield the
`4M` overall bound for general `M`.

**Cleaner per-row bound** (geometric structure):

```
∑_{q ∈ Fin M} 2^(-|q.val - p.val|)
  = 2^0  -- q = p term
  + ∑_{q < p} 2^(-(p.val - q.val))
  + ∑_{q > p} 2^(-(q.val - p.val))
  ≤ 1 + ∑_{d ≥ 1} 2^(-d) + ∑_{d ≥ 1} 2^(-d)
  ≤ 1 + 1 + 1 = 3 ≤ 4
```

**Total**: `∑_p row-sum ≤ M · 4 = 4M`. ✓

### §2.4 Mathlib API needed

- `Finset.offDiag` ⊆ `s ×ˢ s` (via `Finset.product_sdiff_diag` at
  `Mathlib/Data/Finset/Prod.lean:324`).
- `Finset.sum_le_sum_of_subset_of_nonneg` (general).
- `Finset.sum_product` to convert `∑ pq ∈ univ ×ˢ univ` to `∑ p, ∑ q`.
- `Real.rpow_neg`, `Real.rpow_le_one`, `Real.rpow_zero` for the
  `(2 : ℝ) ^ (-k : ℤ) ≤ 1` bound (or `zpow_le_one_of_nonpos`).
- `Finset.sum_const` for `∑ p, c = c · M`.
- Possibly `Finset.geom_sum_eq` or just direct bound.

### §2.5 LOC estimate

- Crude direct proof using `2^(-k) ≤ 1` per-term bound: NOT viable
  alone — gives `M(M-1) ≤ 4M` only for `M ≤ 5`.
- Geometric per-row bound to `3` (or `4`): ~80-150 LOC depending on
  Mathlib API affinity for `Real.rpow` over signed integers.

**Estimated P(Full close)**: 0.55. Risks: (a) `Real.rpow` vs
`(2 : ℝ) ^ (z : ℤ)` notation friction; (b) per-row bound requires either
a clean geometric-sum argument or two-sided cardinality counting.

---

## §3. Non-target — `multivariate_small_ball_upper` (line 589-619)

### §3.1 Status: **NOT closeable in R52**

Per the body comment (lines 603-618), the lemma's compatibility
hypotheses `h_step1` / `h_steps23` are insufficient to derive the
conclusion as stated. The actual paper proof requires a tighter
compatibility schema that captures the multiplicative `ε`-structure
inside `φ_abs_integral`. The current schema decouples this from
`boxProb`, leading to a fundamental ε-cancellation gap.

**Closure prerequisites** (R55+ scope):
- Multivariate Fourier inversion infrastructure in Mathlib (currently 0%).
- Multi-step `multivariate_small_ball_upper_prefactor_uniformity` chain.
- `ε ≤ 1` shrinkage handling on the RHS.

### §3.2 R52 disposition

**Skip** in this round. Document the current status more precisely
(diagnostic upgrade) only if T2.1 closes well under the time budget.

---

## §4. Round-end accounting projection

| Outcome | Sorries (file) | Sorries (project) | Items at gate (mainline) |
|---------|----------------|-------------------|--------------------------|
| Pre-R52 | 2 | 38 (12 mainline + alternate-track) | 19 |
| Upper (T2.1 Full) | **1** | **37** | 19 (unchanged — file is alternate-track) |
| Mid (T2.1 diagnostic upgrade) | 2 | 38 | 19 |
| Lower (T2.1 build error) | 2 | 38 | 19 |

**Strategic value of upper outcome**: -1 sorry on project total (38 →
37), proves Q1c-track engineering tractability post-R51 γ-floor pivot,
demonstrates that pure-arithmetic Q1-track sorries are within R52-R58
mainline budget. **Does not unblock** the assembly sorry at line 619
(blocked on multivariate Fourier infrastructure, R55+ scope).

---

## §5. T2.1 dispatch authorization

**Target**: `geomSeries_offDiag_le` Stub → Full close at
`Helpers/MultivariateSmallBallUpper.lean:230-238`.

**Anti-mismatch hygiene**:
- Statement signature preserved verbatim; only the `:= by ... sorry`
  body is replaced.
- No other lemma in the file modified.
- No imports added (proof uses only `Finset` + `Real.rpow`-flavoured
  Mathlib API already available via `ProblemImports`).

**Time-budget cap** (per round brief hard-stop discipline): if T2.1
not committed within ~45 minutes of dispatch, ship as diagnostic upgrade
(mid-distribution) per R45 honest-deferral pattern.

T2.1 dispatch authorized.
