# Track C round 9 — T1.1 audit (Carter-Pollard Step 1: Beta tail integral representation)

**Read-only audit, opened TC9 round at HEAD `10e379d` (TC8 closure: Mills `_antitone` Full + Stirling Robbins Full).**

## Cache state

`lake exe cache get`: completed (7753 files unpacked, no fresh downloads from origin).

## TC9 scope (Q7 iterative micro-step binding)

**Step 1 ONLY**: prove the Beta-integral representation of the binomial tail polynomial. Specifically:

**Statement target** (real-polynomial form, factored to defer `PMF.binomial` connection to TC10):

For `k m : ℕ` with `1 ≤ k ≤ m` and `p : ℝ` with `0 ≤ p ≤ 1`,

```
Σ_{j=k}^{m} C(m, j) · p^j · (1-p)^(m-j)
   = (m! / ((k-1)! · (m-k)!)) · ∫_0^p x^(k-1) · (1-x)^(m-k) dx
```

This is the classical *incomplete-Beta-as-binomial-tail* identity (Pearson 1934 / De Morgan / standard probability), specialized to natural-number exponents on the integrand so that `Real.rpow` is not required.

**PMF connection (NOT in scope this round)**: a one-line `simp`-with-`PMF.binomial_apply` corollary at TC10 will lift this to `(PMF.binomial p h m).toMeasure {i | k ≤ (i : ℕ)}`, then specialize to `p = 1/2`, `m = 2n` for the Carter-Pollard tail-case midpoint comparison.

## Claims Verification Table (BINDING — Q7 protocol)

| # | Claim | VERIFIED? | Citation | Notes |
|---|-------|-----------|----------|-------|
| 1 | TC7 `realBeta_eq_Gamma_ratio` Full preserved | VERIFIED | `Helpers/RealBeta.lean:74-105` post-TC7 | Building block for TC10 normalizing-constant rewrite |
| 2 | TC2 `quantile_transform_finite_moment` Full preserved | VERIFIED | `Helpers/OneDimKMT.lean` post-TC2 (Layer 2) | Building block for `tusnady_base_polynomial` µ'-a.e. lift |
| 3 | TC8 Mills `_antitone` + Stirling Robbins Full preserved | VERIFIED | `Helpers/GaussianMillsRatio.lean:272-313` (`_antitone`) + `Helpers/StirlingTwoSided.lean:224-230` (Robbins) post-TC8 | No regression |
| 4 | Mathlib IBP API at pin: `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` | VERIFIED | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:111` | Available if Pascal+IBP induction route taken |
| 5 | Mathlib Pascal's identity API: `Nat.choose_succ_succ` / `Nat.succ_mul_choose_eq` | VERIFIED | `Mathlib/Data/Nat/Choose/Basic.lean:61` (`choose_succ_succ`) + `:138` (`succ_mul_choose_eq`) | Latter gives `succ n * choose n k = choose (succ n) (succ k) * succ k`; together with `(n - k) * choose n k = n * choose (n-1) k` for telescoping |
| 6 | Mathlib `Nat`-exponent `pow` derivative: `HasDerivAt.pow` | VERIFIED | `Mathlib/Analysis/Calculus/Deriv/Pow.lean:117` | `HasDerivAt (f^n) (n * f x ^ (n-1) * f') x` — no `Real.rpow` needed since `(k-1)` and `(m-k)` are natural |
| 7 | Mathlib FTC right-endpoint: `intervalIntegral.integral_hasDerivAt_right` | VERIFIED | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:727` | `(d/du) ∫_a^u f x = f u` at `u = b` given integrability + continuity |
| 8 | Mathlib derivative-matching: `eq_of_has_deriv_right_eq` | VERIFIED | `Mathlib/Analysis/Calculus/MeanValue.lean:378` | Two functions with same right-derivative on `[a,b)` and same value at `a` are equal on `[a,b]` |
| 9 | Mathlib `Finset.sum_Ico_succ_top` API exists at pin | VERIFIED | Used in `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1034`, `Mathlib/Data/Nat/Choose/Factorization.lean:78`, `Mathlib/Data/Nat/Multiplicity.lean:149` | Needed for the telescoping-sum manipulation |
| 10 | mainline + track-d preserved | VERIFIED — pre-TC9 | mainline R57 HEAD (per project memory), track-d CLOSED | No cross-branch contamination this round |

## Proof strategy choice — derivative matching, NOT Pascal+IBP induction

**Brief recipe (Pascal + IBP induction)** : induct on `m`, use Pascal's identity to split `C(m, j) = C(m-1, j) + C(m-1, j-1)`, then IBP the integrand. Produces an inductive proof but with two-variable bookkeeping (`m` AND `k`).

**Chosen route — derivative matching** (cleaner; Carter-Pollard 2004 §3 footnote 3): Define both sides as functions of `p` on `[0, 1]`. Show they are differentiable with the same derivative `(m! / ((k-1)!(m-k)!)) · p^(k-1) · (1-p)^(m-k)`, and equal at `p = 0` (both 0 since `k ≥ 1`). Apply `eq_of_has_deriv_right_eq`.

**Why derivative matching wins**:

1. **Single induction** (on `j` for the telescoping sum), not double.
2. **No two-variable bookkeeping** — both functions are over `p`, with `m, k` fixed parameters.
3. **The telescoping identity is cleaner**: each `T_j(p) := C(m,j) · p^j · (1-p)^(m-j)` has derivative `T_j'(p) = S_j(p) - S_{j+1}(p)` where `S_j(p) := m · C(m-1, j-1) · p^(j-1) · (1-p)^(m-j)` (using the algebraic identities `j · C(m, j) = m · C(m-1, j-1)` and `(m-j) · C(m, j) = m · C(m-1, j)`). The sum then telescopes: `Σ_{j=k}^{m} T_j' = S_k - S_{m+1}`, with `S_{m+1} = 0` since `C(m-1, m) = 0`. Result: `m · C(m-1, k-1) · p^(k-1) · (1-p)^(m-k) = (m! / ((k-1)! · (m-k)!)) · p^(k-1) · (1-p)^(m-k)`.
4. **FTC right gives the integral side directly**: `(d/dp) ∫_0^p x^(k-1) (1-x)^(m-k) dx = p^(k-1) (1-p)^(m-k)` by `integral_hasDerivAt_right` + integrand continuity.

**Reverted Pascal+IBP path documentation**: the Pascal+IBP induction is mathematically valid and would yield the same identity; the choice here is an *implementation* preference based on Lean ergonomics.

## Step-by-step recipe (T2.1)

**Step A** — define `binomialPolyTail (m k : ℕ) (p : ℝ) : ℝ := Σ j ∈ Finset.Ico k (m+1), C(m, j) · p^j · (1-p)^(m-j)`.

**Step B** — auxiliary algebraic identity: `j · C(m, j) = m · C(m-1, j-1)` for `1 ≤ j ≤ m` (use `Nat.succ_mul_choose_eq` rewritten); `(m - j) · C(m, j) = m · C(m-1, j)` for `j ≤ m` (use `Nat.choose_mul_succ_eq` adjacent or direct manipulation).

**Step C** — termwise derivative: for each `j`, `HasDerivAt (T_j) (T_j' p) p` where `T_j' p = j · C(m, j) · p^(j-1) · (1-p)^(m-j) - (m-j) · C(m, j) · p^j · (1-p)^(m-j-1)`. Combine `HasDerivAt.pow` on `p` and `(1-p)` chains, `HasDerivAt.mul`, `HasDerivAt.const_mul`.

**Step D** — sum derivative: `HasDerivAt (binomialPolyTail m k) (Σ_{j=k}^m T_j' p) p` via `HasDerivAt.fun_sum`/`HasDerivAt.sum`. Then telescope: define `S_j p := m · C(m-1, j-1) · p^(j-1) · (1-p)^(m-j)`; show termwise `T_j' p = S_j p - S_{j+1} p`; sum collapses to `S_k p - S_{m+1} p = m · C(m-1, k-1) · p^(k-1) · (1-p)^(m-k)` (using `C(m-1, m) = 0`).

**Step E** — RHS derivative: define `betaPartialIntegral (m k : ℕ) (p : ℝ) := ∫ x in (0:ℝ)..p, x^(k-1) * (1-x)^(m-k)`. Apply `integral_hasDerivAt_right` with continuity of the integrand (polynomial → continuous). Multiply by constant `(m! / ((k-1)!(m-k)!)) = m · C(m-1, k-1)` (`Nat`-cast lemma).

**Step F** — initial condition: at `p = 0`, both sides are `0`. LHS: each `T_j 0 = 0` for `j ≥ 1` (since `0^j = 0`), and the sum starts at `j = k ≥ 1`. RHS: `∫_0^0 _ = 0`.

**Step G** — combine: `eq_of_has_deriv_right_eq` over `[0, 1]`. Specialize to `p ∈ [0, 1]`.

**LOC estimate**: Step A 10 LOC, Step B 30 LOC, Step C 50 LOC, Step D 80 LOC (telescoping algebra is the bulk), Step E 30 LOC, Step F 10 LOC, Step G 30 LOC. **Total 240 LOC, within 160-300 calibrated band.**

## Sub-checkpointing

- T+0:30: ✅ T1.1 audit (this doc).
- T+2:30: T2.1 `binomial_tail_beta_integral` Full or honest sub-Stub.
- T+3:00: T2.2 build + status doc.
- T+3:30: T2.3 push.
- Hard-stop T+4:00.

## Confidence updates (Q7 calibrated, structural risks flagged)

| Outcome | Region | P(Full) raw | Calibrated |
|---------|--------|-------------|------------|
| T1.1 audit | computational | 0.95 | 1.00 (this doc complete) |
| T2.1 Step 1 Full (derivative-matching route) | semi-populated | 0.65 | **0.55 calibrated** (derivative-matching cleaner than Pascal+IBP) |
| T2.2 build + status | computational | 0.95 | 0.95 |
| T2.3 push | mechanical | 0.95 | 0.95 |

**Joint mandatory floor**: ~0.65.

**Structural risks (Q7 binding, flagged up-front)**:

- (a) **Telescoping-sum algebra in Step D**: each `T_j' p = S_j - S_{j+1}` requires three rewrites (binomial-coefficient identity + power algebra + sign). Risk: a Lean-level `ring`-resistance might force manual restructuring (~30 extra LOC). **Mitigation**: factor as separate lemma `T_j_deriv_eq_S_diff`, prove once, use in sum.
- (b) **Algebraic identity `(m - j) · C(m, j) = m · C(m-1, j)`** (Step B): needs `j ≤ m` hypothesis to be valid. Available in Mathlib as `Nat.choose_mul_succ_eq` indirect — may need a 5-10 LOC manual proof via `Nat.factorial` decomposition. **Mitigation**: write standalone lemma; if Mathlib has it under a different name, simplify.
- (c) **`(1-p)^(m-j)` derivative**: needs `HasDerivAt (fun p => 1-p)` chained with `HasDerivAt.pow`. Should be ergonomic via `(hasDerivAt_id _).const_sub _ |>.pow _`. **Mitigation**: pre-write helper `oneSubPow_hasDerivAt` (~5 LOC).
- (d) **Boundary `S_{m+1} = 0`**: `C(m-1, m) = 0` by `Nat.choose_eq_zero_of_lt`. Trivial.

**Distribution (post-T1.1)**:
- Best (P~0.35): Step 1 Full → +1 Full theorem (NEW), no sorry change.
- Mid (P~0.30): Step 1 partial — telescoping lemma Full but final assembly hits friction → ship close-modulo-rewrite TAG'd Stub with concrete Mathlib gap.
- Mid-low (P~0.25): induction on `j` for telescope blocks → ship structural lemma Full (`T_j_deriv_eq_S_diff`) + diagnostic for the final assembly.
- Lower (P~0.10): Mathlib API gap on FTC integrability of polynomial integrand `x^(k-1)(1-x)^(m-k)` → diagnostic + LOC re-estimate for TC10+.

## What is NOT in scope this round (Q7 binding)

- Step 2 Stirling prefactor for the bulk-case binomial-coefficient asymptotic.
- Steps 3-6 of the full Carter-Pollard assembly (Taylor expansion + bulk/tail split + envelope).
- `tusnady_base_polynomial` body sub-sorry (line 506 of `OneDimKMT.lean`) — TC11+ scope.
- Layer 3 Hungarian dyadic step body close (TC10+ scope).
- Layer 4 SupError attempt (TC10+ scope).
- Mainline OR track-d modifications.
- TC1-TC8 closure modifications.

## Anti-patterns explicitly forbidden (per brief)

- Multi-step Carter-Pollard assembly attempt (Q7 binding).
- Skip cache check.
- Skip Claims Verification Table.
- Modify TC1-TC8 Full theorems.
- Modify mainline OR track-d.
- Push to wrong branch.
- Plan doc as substitute for code.
