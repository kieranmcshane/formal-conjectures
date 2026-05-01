# R32 / T1.1 — Axiom + sorry inventory

**Read-only audit.** No Lean code modifications in R32. This document
inventories every `axiom` declaration and every `sorry` placeholder in the
formal-conjectures repository that is reachable from the 524 mainline,
together with first-touch round and propagation surface.

Search predicates used:

```
grep -rn -E '^[[:space:]]*(axiom|private axiom|noncomputable axiom)[[:space:]]+[A-Za-z_]' \
  FormalConjectures/ --include='*.lean'
grep -rn -E '^[[:space:]]*sorry$|[[:space:]]:= sorry$|[[:space:]]:= by[[:space:]]+sorry' \
  FormalConjectures/ErdosProblems/ --include='*.lean'
```

(Plus a broader `sorry`-token scan to capture inline `sorry` in tactic mode.)

## A. Pure `axiom` declarations (3, all in `Helpers/`)

| # | Symbol | File:line | Visibility | Round introduced | Status |
|---|--------|-----------|------------|------------------|--------|
| A1 | `Cp_T_explicit_pointwise_axiom` | `Helpers/GLWGaussianProjectiveLimit.lean:2070` | `private` (file-local) | R27 (Option D bascule, hash `a478910`) | active, propagates into `Y_GLW_exists` chain via `tsum_Cp_T_explicit_lt_top_R22` |
| A2 | `one_dim_KMT_coupling` | `Helpers/OneDimKMT.lean:101` | semi-public (namespace `Erdos524.Helpers`) | R29 (KMT Option C mandatory floor, hash `5e0d8d5`) | declared, **no Lean-level invocation found** in tree (only documentation references); see T2.1 |
| A3 | `kmt_aided_gaussian_process` | `Helpers/StochasticProcessAxiom.lean:80` | semi-public (namespace `Erdos524.Helpers`) | R30 (KMT Option C — public 2D-KMT axiom retired via stepping-stone, hash `f0567e9`) | active, the actual load-bearing axiom for the 2D KMT chain (4× indirect consumers in 524.lean via `two_dim_KMT_coupling`) |

`grep` confirms there are no other `axiom` / `constant` / `unsafe axiom`
/ `opaque` declarations in `FormalConjectures/ErdosProblems/`. The string
"axiom is gone" at `524.lean:3740` is a comment fragment inside the docstring
of the **theorem** (not axiom) `two_dim_KMT_coupling`.

`Y_GLW_exists` is a **theorem** at `Helpers/GLWProcess.lean:130` (retired from
axiom status in R15, hash `4531bea`). Its body is the term
`glwGaussianLimit_Y_GLW_existence` in `Helpers/GLWGaussianProjectiveLimit.lean:2220`,
which depends on `glwGaussianLimit_isKolmogorovProcess` and
`exists_glwBrownianModification` in the same file. Spot-check: lines 2220-2386
contain no `sorry` token. The 4 sorries in `GLWGaussianProjectiveLimit.lean`
(lines 2000, 2017, 2031, 2042) are confined to **dead R26 sub-lemmas**
(`constL_unit_block_le`, `inner_tsum_AMQM_bound`,
`Cp_T_explicit_le_log_sq_div_succ_sq`, `Cp_T_explicit_le_K_div_three_halves_R26`)
that were superseded by the R27 D2 axiom (A1) and have **zero in-tree
consumers** (verified by grep). Recommendation for R33: delete the 4 dead
lemmas to retire 4 false-positive sorries.

## B. Theorem-with-sorry (live), 524-mainline-relevant

| # | Symbol | File:line of body sorry | Round introduced | Consumed by |
|---|--------|--------------------------|------------------|-------------|
| B1 | `LS_independent_yplus_yminus` | `Helpers/TwoDimKMTFromOneDim.lean:213` | R30 stretch (T3.4, hash `f0567e9`) | `two_dim_KMT_coupling_via_LS_reduction` (TwoDimKMTFromOneDim.lean:283) → `theorem two_dim_KMT_coupling` (524.lean:3741) → 4 consumers in 524.lean (3926, 4081, 4229, 4605) |
| B2 | `IsRademacherSequence_a_even` | `Helpers/TwoDimKMTFromOneDim.lean:442` | R31 (T2.2, infrastructure) | `LS_yplus_via_even` (TwoDimKMTFromOneDim.lean:480) — no current downstream consumer; planned for R33 corrected-form path |
| B3 | `IsRademacherSequence_a_odd` | `Helpers/TwoDimKMTFromOneDim.lean:454` | R31 (T2.2, infrastructure) | `LS_yminus_via_odd` (TwoDimKMTFromOneDim.lean:498) — no current downstream consumer |

## C. Theorem-with-sorry (dead R26), no in-tree consumer

| # | Symbol | File:line of body sorry | Round introduced | Status |
|---|--------|--------------------------|------------------|--------|
| C1 | `constL_unit_block_le` | `Helpers/GLWGaussianProjectiveLimit.lean:2000` | R26 | superseded by A1; no consumer |
| C2 | `inner_tsum_AMQM_bound` | `Helpers/GLWGaussianProjectiveLimit.lean:2017` | R26 | superseded; no consumer |
| C3 | `Cp_T_explicit_le_log_sq_div_succ_sq` | `Helpers/GLWGaussianProjectiveLimit.lean:2031` | R26 | superseded; no consumer |
| C4 | `Cp_T_explicit_le_K_div_three_halves_R26` | `Helpers/GLWGaussianProjectiveLimit.lean:2042` | R26 | superseded; no consumer |

## D. Theorem-with-sorry, 524.lean main statements

| # | Symbol | File:line of body sorry | Round introduced | Notes |
|---|--------|--------------------------|------------------|-------|
| D1 | (anonymous, in 524.lean main proof skeleton) | `524.lean:3541` | pre-R13 | Karhunen–Loève + entropy gap; doc says "actual Mathlib gap" |
| D2 | (anonymous, in 524.lean main proof skeleton) | `524.lean:3614` | pre-R13 | Gaussian density LOWER bound dual; doc references Round-9-closure context |

## E. Theorem-with-sorry, other Helper files (not on the active 524 chain)

These are reachable in principle but not consumed by `theorem erdos_524`'s
discharge chain. Inventoried for completeness; **not in scope for R32 T3.1
consistency analysis** unless promoted by T2.1 findings.

| File | Sorry count | Notes |
|------|-------------|-------|
| `Helpers/EsseenSmoothing.lean` | 19 | R28-introduced session batch; not on 524 active chain |
| `Helpers/SurgicalDensityAtZero.lean` | 13 | Pre-R13 helper file; not currently invoked by the GLW chain |
| `Helpers/GLWLowerProof.lean` | 2 (lines 328, 340) | Comment at line 63 says "main bound at a single documented sorry on the Karhunen–Loève + entropy", and the sorries do feed into 524.lean:3614 path indirectly via `gao_li_wellner_small_ball_lower` |
| `Helpers/GLWUpperProof.lean` | 1 (line 285) | Documented sorry; line 58 doc says "at most ONE documented sorry on a precise Mathlib gap" |
| `Helpers/MultivariateSmallBallUpper.lean` | 2 (lines 238, 619) | Not imported by 524.lean directly |
| `Helpers/YGLWFromBrownianMotion.lean` | 1 (line 3083) | The documentation-block `Y_GLW_exists_from_brownian_motion` *roadmap* — note: the actual `Y_GLW_exists` discharge uses `glwGaussianLimit_Y_GLW_existence`, not this skeleton; the line-3083 sorry sits inside a planning code-block under heading "Roadmap" |

## F. Other Erdős problem files (out-of-scope for R32 audit)

`524_remarks.tex` mentions axioms in tex prose only. Other Erdős problems
(234.lean, 263.lean, 633.lean, 1082.lean, 12.lean, 326.lean, 849.lean, etc.)
contain `sorry` placeholders but are independent of 524 and unaffected by
foundational issues in the 524 axiom chain.

## Summary

- **3 active pure axioms** (A1, A2, A3).
- **3 live sorry-bearing theorems on 524's active chain** (B1, B2, B3 — though
  B2/B3 have no current downstream consumer in `r30-finish`).
- **4 dead R26 sorries** (C1-C4) that should be retired in R33 cleanup.
- **2 main-statement sorries** in 524.lean itself (D1, D2) that pre-date R13
  and are documented as "actual Mathlib gap" (Karhunen–Loève + entropy).
- **5 helper files** (E) carry additional sorries not on the active discharge
  chain; flagged for awareness but out-of-scope.

T2.1 will extract consumer-usage patterns for A1-A3 and B1; T3.1 will run the
internal-consistency hypothesis test on A1, A2, A3, and on the *theorem*
`two_dim_KMT_coupling` (whose statement R31 already classified as
contradictory).
