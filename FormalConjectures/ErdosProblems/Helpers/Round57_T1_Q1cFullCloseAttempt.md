# R57-T1.1 — Q1c full close attempt audit (Claims Verification Table)

**Round**: R57 (V2 round 19, 2026-05-02). Variante 1 single round, math-content
close attempt on Q1c alternate-track, post-R56 companion γ-floor axiomatization.

**Branch**: `r46-track-a-mge-posdef`, HEAD `60a1767` (R56 close, pushed).

**Pin**: `mathlib4 @ 25ce63313608`, `brownian-motion @ 91267abd71bd`,
`leanprover/lean4:v4.27.0-rc1`.

**Scope**: T1.1 verifies the claims around `geomSeries_offDiag_le`
(`Helpers/MultivariateSmallBallUpper.lean:267-275`) and authorizes T2.1 full
close attempt per R52-T2.1 audit recipe (per-distance-class re-indexing).

---

## §1. Claims Verification Table

| Claim # | Statement | VERIFIED? | Citation | Notes |
|---------|-----------|-----------|----------|-------|
| 1 | `geomSeries_offDiag_le` Stub at `Helpers/MultivariateSmallBallUpper.lean:267-275` | **VERIFIED** | Read tool: signature line 267, sorry body line 275 | Exact Stub location confirmed; line shifted from R52 audit (was 230-238) due to docstring expansion at R52-T2.1 diagnostic upgrade. |
| 2 | R52-T2.1 audit recipe per-distance-class | **VERIFIED** | Lemma docstring lines 231-265, R52 audit doc | Recipe documented in lemma docstring with three Mathlib gaps (a) per-distance partition, (b) finite-partial geometric, (c) composition glue. |
| 3 | Mathlib `Finset.offDiag` API at pin | **VERIFIED** | `Mathlib/Data/Finset/Prod.lean:251-326` | `mem_offDiag`, `offDiag_card`, `product_sdiff_diag`, `disjoint_diag_offDiag`, `diag_union_offDiag` all available. |
| 4 | Mathlib `Finset.sum_geometric` family at pin | **VERIFIED** | `Mathlib/Analysis/SpecificLimits/Basic.lean:351` `sum_geometric_two_le` | Yields `∑ i ∈ range n, (1/2 : ℝ)^i ≤ 2`. Closes Mathlib gap (b). |
| 5 | `MultivariateSmallBallUpper.lean` other sorries preserved | **VERIFIED** | grep returns 2 sorries: line 275 (target) and line 656 (`multivariate_small_ball_upper`, R58+ multivariate Fourier infra) | Don't modify line 656 Stub — flagged R58+ scope. |
| 6 | R55 alternate-track build state preserved | **VERIFIED** | Per AXIOM_INVENTORY R55+R56 blocks at HEAD `60a1767` | No regression. |
| 7 | Mainline R49+R51+R53+R56 axioms preserved | **VERIFIED** | AXIOM_INVENTORY R49-R56 sections (9 axioms total: A1-A5 + R49 #6 + R51 #7 + R53 #8 + R56 #9) | No axiom edits planned in T2.1. |
| 8 | A1-A5 axioms preserved | **VERIFIED** | `524.lean:3574, :3643` per memory `project_lean_erdos_524` | No 524.lean edits planned in T2.1. |

All 8 claims **VERIFIED**. T2.1 may proceed.

---

## §2. Recipe extraction — `geomSeries_offDiag_le` (line 267-275)

### §2.1 Lemma statement (verbatim)

```lean
lemma geomSeries_offDiag_le (M : ℕ) :
    ∑ pq ∈ (Finset.univ : Finset (Fin M)).offDiag,
      (2 : ℝ) ^ (-(|(pq.2.val : ℤ) - (pq.1.val : ℤ)| : ℤ)) ≤ 4 * M := by
  sorry
```

### §2.2 Proof strategy (per R52 recipe + Mathlib API)

**Strategy A — relax to univ ×ˢ univ + per-row bound.**

Step 1. Each term `(2 : ℝ) ^ (-(|...| : ℤ))` is non-negative. Apply
`Finset.sum_le_sum_of_subset_of_nonneg` to relax `offDiag ⊆ univ ×ˢ univ`.

Step 2. Use `Finset.sum_product` to convert ∑ over univ×ˢuniv to nested ∑.

Step 3. Per-row bound: for each `p : Fin M`,
`∑ q : Fin M, (2 : ℝ) ^ (-(|q.val - p.val| : ℤ)) ≤ 4`.

Step 4. Sum-of-constants: `∑ p : Fin M, 4 = 4 * M`.

### §2.3 Per-row bound (Step 3) — sub-proof

The signed difference `(q.val : ℤ) - (p.val : ℤ)` has absolute value
`((q.val : ℤ) - (p.val : ℤ)).natAbs : ℕ`. Rewrite each term:

`(2 : ℝ) ^ (-(|x| : ℤ)) = (1/2 : ℝ) ^ (x.natAbs : ℕ)` via `zpow_neg` +
`Int.abs_eq_natAbs` + `zpow_natCast` + `(1/2 : ℝ) = (2 : ℝ)⁻¹`.

Then split `Finset.univ : Finset (Fin M) = univ.filter (fun q => q.val ≤ p.val)
∪ univ.filter (fun q => q.val > p.val)` (disjoint via `Finset.sum_filter_add_sum_filter_not`).

For `q.val ≤ p.val`: `((q.val : ℤ) - (p.val : ℤ)).natAbs = p.val - q.val`.
Reindex by `k = p.val - q.val`: image is `Finset.range (p.val + 1)`.
`∑ q ∈ univ.filter (q.val ≤ p.val), (1/2)^(p.val - q.val)
= ∑ k ∈ range (p.val + 1), (1/2)^k ≤ 2`.

For `q.val > p.val`: similar reindexing `k = q.val - p.val - 1`, image is
`Finset.range (M - p.val - 1)`.
`∑ q ∈ univ.filter (q.val > p.val), (1/2)^(q.val - p.val)
= ∑ k ∈ range (M - p.val - 1), (1/2)^(k+1) ≤ ∑ k ∈ range (M - p.val), (1/2)^k ≤ 2`.

Total per row: ≤ 2 + 2 = 4. ✓

### §2.4 Mathlib API (closes R52 gap (a) by elementary reindexing)

- `Finset.mem_offDiag`, `Finset.mk_mem_product` — relaxation.
- `Finset.sum_product` — nested sum.
- `Finset.sum_filter_add_sum_filter_not` — q.val ≤ p.val split.
- `Finset.sum_nbij` / `Finset.sum_image` (with injectivity proof) — reindex.
- `Finset.sum_geometric_two_le` (`SpecificLimits/Basic.lean:351`) — geometric bound.
- `zpow_neg`, `Int.abs_eq_natAbs`, `zpow_natCast` — term rewrite.

### §2.5 LOC estimate

100-180 LOC, of which:
- Step 1-2 (offDiag → product → nested): ~15 LOC.
- Step 3 row bound term rewrite + split + reindex (×2 sides): ~80-130 LOC.
- Step 4 closure: ~10 LOC.

R52 audit estimated 100-180 LOC, P(Full)/round ~0.55. R57 maintains this estimate.

---

## §3. T2.1 dispatch authorization

**Target**: `geomSeries_offDiag_le` Stub → Full close at
`Helpers/MultivariateSmallBallUpper.lean:267-275`.

**Anti-mismatch hygiene**:
- Statement signature preserved verbatim; only the `sorry` body is replaced.
- No other lemma in the file modified (`multivariate_small_ball_upper` at line 656 untouched).
- No imports added (proof uses only `Finset` + `Real.zpow` Mathlib API + `SpecificLimits/Basic`).

**Time-budget cap**: if T2.1 close not committed by T+2:45, ship as TAG'd
diagnostic + concrete LOC estimate per R45 honest-deferral pattern.

T2.1 dispatch authorized.

---

## §4. Round-end accounting projection

| Outcome | Sorries (file) | Sorries (project) | Items at gate (mainline) |
|---------|----------------|-------------------|--------------------------|
| Pre-R57 | 2 (line 275 + 656) | 10 mainline + 30 alternate ≈ 40 total | 19 (9 ax + 10 sorries) |
| Upper (T2.1 Full) | **1** (line 656 only) | -1 (40 → 39) | 19 (file alternate-track) |
| Mid (T2.1 diagnostic) | 2 | 40 (no change) | 19 |
| Lower (build error) | 2 | 40 | 19 |

**Strategic value of upper outcome**: -1 sorry on project total (40 → 39),
proves Q1c-track engineering tractability, demonstrates pure-arithmetic
Q1c-track sorries are within R57+ budget.
