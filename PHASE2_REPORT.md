# Phase 2 Round-2 Report

**HEAD:** `fe23136 feat: K_GLW vs hierCauchyG determinant bridge` on `kmc-erdos-gaussian-smallball`.

## This round's commits

```
fe23136 feat: K_GLW vs hierCauchyG determinant bridge (Node 6 prereq)
4b6a3cf feat: hierCauchyG entrywise + determinant positivity facts (Node 6 prereq)
e94a294 feat: matrix-perturbation determinant lemma (Node 6 prerequisite)
```

## Per-task status

* **Task 1** (matrix-perturbation det lemma) — **DONE**. `Helpers/MatrixDetPerturbation.lean` 206 LOC: `abs_prod_sub_prod_le` (telescoping product) + `abs_det_sub_det_le` (Leibniz + per-permutation telescoping). Pure linear algebra, no PosDef needed (sup-norm version, cleaner than original op-norm spec).
* **Task 2** (V1 instance prereqs) — **2/8 fields-worth done**. Shipped `HierCauchyFacts.lean` (5 lemmas: entrywise unfolding/positivity/symmetry/upper bound + det positivity) and `KGLWHierCauchyDet.lean` (3 lemmas: K_GLW vs hierCauchyG det bridge specialised to the Node 2 entrywise bound, M=1 corollary). The full V1 instance still needs an actual multivariate Gaussian construction, which is the gap.
* **Task 3** (theorem signatures) — **NOT STARTED**. Without a V1 instance, the theorem proofs would need stubs.
* **Task 4** (524.lean axiom replacement) — **NOT STARTED**. Blocked on Task 3.

## Net counts (unchanged from previous report)

Axioms 4 (`Y_GLW_exists` + 3 unchanged GLW/KMT). Sorrys 0.

## Outcome vs ladder

Above **Acceptable** (Task 1 fully done), below **Good** (only 2/8 V1 prereqs vs the "2-4" target).

## Next session

Task 2 cont: pick Mathlib's multivariate Gaussian path or build one locally (~300-500 LOC) so a V1 instance with `cov := hierCauchyG m` becomes constructible; once that lands, Task 3's GLW theorems fall out of `gaussian_grid_smallball_*_final` + `K_GLW_hierCauchy_det_close_unit_M` + Node 4 discretization.
