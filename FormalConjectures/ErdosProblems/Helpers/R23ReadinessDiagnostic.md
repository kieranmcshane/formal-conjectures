# R23 Readiness Diagnostic

**Round to plan:** R23.
**Predecessor:** `r22-finish` (commits R22 T3.2 / T4.x / T5.1 partial,
plus R22BuildStatus + R22APIScoping).
**Pins after R22:** `formal-conjectures @ r22-finish`,
`brownian-motion @ 91267ab`, `mathlib @ 25ce633136`.

## R22 leftover

`Helpers/GLWGaussianProjectiveLimit.lean` has **one open sorry** at
`tsum_Cp_T_explicit_lt_top_R22`. Discharging it retires the
`Y_GLW_exists` axiom (transitively a `theorem` since R15, with the
single `sorryAx` traced to the summability bound). R22 closed
the entire conjunct-9 chain modulo this sorry; the Lean plumbing for
the BC step + floor argument + continuity-transfer is in place.

R23's core mission: discharge `tsum_Cp_T_explicit_lt_top_R22` and
trigger the **first axiom retirement of the project** (+500 pts).

## Prioritised blockers (R23 attack order)

### Blocker A (load-bearing) — `tsum_Cp_T_explicit_lt_top_R22`

**Statement to prove**:
```lean
private theorem tsum_Cp_T_explicit_lt_top_R22 :
    (∑' T : ℕ, Cp_T_explicit T) < ∞
```

**Mathematical content (Grok-validated, R22APIScoping Commitment C):**

`Cp_T_explicit T = (Real.toNNReal (1/(2T³)) : ℝ≥0∞) * constL ↥(Set.Ico T (T+1)) (6(T+1)) 1 2 2 (1/4) Set.univ`.

`constL` from `BrownianMotion.Continuity.KolmogorovChentsovInequality.lean:142`:
```
constL T c d p q β U = 2^(2p+5q+1) * c * (diam U + 1)^(q-d)
  * ∑'k, 2^(k(βp - (q-d))) * (4^d * ofReal (logb 2 c.toReal + (k+2)d)^q + Cp d p q)
```

For our `(p, q, d, β) = (2, 2, 1, 1/4)`:
- `2^(2p+5q+1) = 2^15` (constant).
- `c = c_T = 6(T+1)`. **Linear in T.**
- `(diam U + 1)^(q-d) = (1+1)^1 = 2` since `diam (Set.univ : Set ↥(Ico T (T+1))) ≤ 1`.
- Inner tsum: `∑'k, 2^(-k/2) * (4 * (logb 2 c_T + k+2)^2 + Cp 1 2 2)`.

The dyadic factor `2^(-k/2)` decays geometrically. The polynomial-in-k
factor `(logb 2 c_T + k+2)^2 ≤ 2 (logb 2 c_T)^2 + 2(k+2)^2` (by `(a+b)^2 ≤ 2a²+2b²`).
Hence the inner tsum is bounded by `K_dyad * ((log T)^2 + 1)` for some
absolute `K_dyad`.

So `constL ≤ 2^15 * 6(T+1) * 2 * K_dyad * ((log T)^2 + 1)`.

Combined: `Cp_T_explicit T ≤ K_const * (T+1) * ((log T)^2 + 1) / T³`
`= O((log T)² / T²)`. p = 2 series with log² factor: summable
(`∑ (log T)² / T² < ∞`).

**Estimated LOC**: 150–200. Sub-steps:

* **A.1**: bound the inner dyadic tsum.
  ```lean
  lemma constL_inner_tsum_le (c : ℝ≥0∞) (hc : c ≠ ∞) :
      ∑' k, 2^(k * (-1/2 : ℝ)) * (4 * (ofReal (logb 2 c.toReal + (k+2)))^2 + Cp 1 2 2)
        ≤ K_dyad * ((logb 2 c.toReal)^2 + 1)
  ```
  Strategy: split as `≤ ∑' k, 2^(-k/2) * (8 * (logb)^2 + 8(k+2)^2 + Cp)`,
  then sum each piece via `summable_geometric` and
  `summable_polynomial_pow_geometric`. ~80 LOC.

* **A.2**: explicit `constL` polynomial bound.
  ```lean
  lemma constL_le_poly (T : ℕ) :
      constL ↥(Set.Ico T (T+1)) (6(T+1)) 1 2 2 (1/4) Set.univ
        ≤ K_constL * (T+1) * ((Real.log T)^2 + 1)
  ```
  Apply A.1 + `EMetric.diam ≤ 1` + arithmetic. ~50 LOC.

* **A.3**: combine `M_T = 1/(2T³)` with A.2 and apply
  `Real.summable_one_div_nat_pow_log_pow` (or build from
  `Real.summable_one_div_rpow`). ~30 LOC.

* **A.4**: `tsum_Cp_T_explicit_lt_top_R22` falls out as 5 LOC of
  `ENNReal.tsum_le_tsum` + finiteness arithmetic.

**Estimated build iterations: 8-15.** The dyadic-tsum-bound step is
the iteration-heavy piece (Mathlib's tsum-of-polynomial-times-geometric
machinery is finicky).

### Blocker B (axiom retirement headline) — `Y_GLW_exists`

**Statement**: `#print axioms Y_GLW_exists` shows only
`propext / Classical.choice / Quot.sound`.

After Blocker A discharges, this is automatic: the chain
`Y_GLW_exists → glwGaussianLimit_Y_GLW_existence → conjunct 9 →
BC_block_sup_R22 → tsum_Cp_T_explicit_lt_top_R22` becomes sorry-free.

**Estimated effort**: 5 minutes after A lands. Verify with
`#print axioms`.

**Project bonus on success**: +500 (first axiom retirement of the
project).

### Blocker C (cosmetic) — clean up unused-tactic warnings

R22 ships with three `'push_cast' tactic does nothing` warnings and
one unused-simp-argument warning in the GLWGaussianProjectiveLimit
file. None are correctness issues; remove them in a one-line cleanup
commit. ~5 LOC.

## Other open project frontiers (parallel, unblocked by R23)

* **`two_dim_KMT_coupling`** axiom in `524.lean:3741` — independent of
  GLW; awaits one-dim KMT scaffolding (see `OneDimKMTSketch.md`,
  `TwoDimKMTRetirement.md`). Substantial multi-round project.

* **Phase 2 / Node 3 (Gaussian-grid small-ball)** — sub-grid BB1
  retired at commit `2afe1b8` on `add-erdos-524`. Two sorries remain
  (Schur, lower assembly). Future-blocker for axiom A1 retirement
  (independent axiom branch, not the GLW one).

* **Phase A (Slepian inequality)** — Mathlib gap. Slepian for
  centered Gaussian processes is not in Mathlib at HEAD; would
  unlock several Erdős-524 sub-results.

## R23 success criteria

1. `Helpers/GLWGaussianProjectiveLimit.lean` builds with **0 sorries**.
2. `#print axioms Y_GLW_exists` shows ONLY
   `propext / Classical.choice / Quot.sound`.
3. The +500 project bonus is triggered (first axiom retirement of
   the project).
4. `Helpers/AxiomRetirementCelebration.md` documents the closure
   with full citation chain
   `Y_GLW_exists → glwGaussianLimit_Y_GLW_existence → conjuncts 1-9
   → modification → glwCovMatrixNN → R13/R14/.../R22/R23`.

## Calibration suggestion for R23 manifest

R22 manifest projected 300-550 pts and landed at 620 (above range).
R22's strong outcomes:
- **T3.2 Full** (the load-bearing 55%-prediction): 200 pts (+90 over
  expectation).
- **T4.1, T4.2 Full** (mechanical bridges): 140 pts.

R22's miss: summability sorry blocks T5.1 Full and T5.2 Stub. This
is the precise gap R23 should close.

R23 should:

* **Cap A as 1 task at 250 pts** (sub-blockers A.1-A.4 combined).
  Realistic Full probability: **0.65** (the math is done; the Lean
  plumbing on dyadic tsum bounds is the gating factor).
* **Cap B (axiom retirement) at 100 pts**, gated on A. Realistic
  Full probability conditional on A: 0.95.
* **+500 project bonus** on B Full. Joint probability: 0.65 × 0.95 ≈
  0.62 → ~62% chance of axiom retirement this round.

## Strategic ordering

1. R23 V1: `lake build` r22-finish HEAD sanity (~5 min).
2. R23 T1.1: API scoping doc validating the `constL` polynomial
   bound math (~15 min).
3. R23 T2.1: `constL_inner_tsum_le` (Blocker A.1, ~30-60 min).
4. R23 T2.2: `constL_le_poly` (Blocker A.2, ~20-30 min).
5. R23 T3.1: `tsum_Cp_T_explicit_lt_top_R22` discharge (Blocker A.3
   + A.4, ~20-30 min).
6. R23 T4.1: Whole-file zero-sorry verification (~5 min).
7. R23 T4.2: `#print axioms Y_GLW_exists` clean (~5 min).
8. R23 T5.1: `AxiomRetirementCelebration.md` (~30 min, only if T4.2
   Full).
9. R23 T6.1: `R24ReadinessDiagnostic.md` (next frontier — Phase A
   Slepian or `two_dim_KMT`).
10. R23 T7.1: Push.

## Skin-in-the-game suggestion for R23

Concentrate on Blocker A.1 (`constL_inner_tsum_le`). This is the
new load-bearing piece — A.2, A.3, A.4 are mechanical given A.1.

If A.1 stalls 8+ build attempts, the round caps at Partial on A;
T5.1 and the bonus are deferred.

## Estimated R23 effort

| Blocker | LOC | Build iterations | Difficulty |
|---------|-----|-------------------|------------|
| A.1 (inner dyadic tsum) | 80 | 5-8 | Hard (polynomial-times-geometric) |
| A.2 (constL polynomial bound) | 50 | 3-4 | Medium |
| A.3 (Cp_T summability) | 30 | 2-3 | Easy |
| A.4 (tsum_Cp_T_explicit_lt_top discharge) | 5 | 1 | Trivial |
| B (axiom retirement headline) | 5 | 1 | Trivial |
| **Total** | **170** | **12-17 builds** | **Medium-Hard overall** |

R23 should target ~170 LOC of new Lean and ~15 build iterations.
Realistic if R23 grades A as a single "Full" task at 250 pts; B at
100 pts; bonus +500.

End of R23 readiness diagnostic.
