# R17 Build Status — `r17-finish` HEAD

Generated at the close of R17. Per-file build state for all GLW
helpers and Phase A scaffolding modified or read in this round.

## Ground truth (V1 verification)

R16 files all built green at `r16-finish` HEAD:

```
✔ [3038/3041] Built ...PhaseAUpperBound (10s)
✔ [3039/3041] Built ...GLWGaussianProjectiveLimit (11s)
✔ [3040/3041] Built ...GLWProcess (1.6s)
✔ [3041/3041] Built ...GLWProcessPredicate (1.8s)
Build completed successfully (3041 jobs).
```

V2 trivial: no fixes needed.

## R17 progress in `GLWGaussianProjectiveLimit.lean`

| Item | Symbol | Status pre-R17 | Status post-R17 |
|------|--------|----------------|-----------------|
| O3.5 a | `integral_glwGaussianProjectiveFamily`         | absent | Full ✓ |
| O3.5 b | `integral_id_glwGaussianProjectiveFamily`      | absent | Full ✓ |
| O3.5 c | `covariance_eval_glwGaussianProjectiveFamily`  | absent | Full ✓ |
| O3.5 d | `variance_eval_glwGaussianProjectiveFamily`    | absent | Full ✓ |
| O3.5 e | `hasLaw_eval_glwGaussianProjectiveFamily`      | absent | Full ✓ |
| O3.5 f | `hasLaw_eval_sub_eval_glwGaussianProjectiveFamily` | absent | Full ✓ |
| O3.5 g | `hasLaw_eval_glwGaussianLimit`                 | absent | Full ✓ |
| O3.5 h | `hasLaw_eval_sub_eval_glwGaussianLimit`        | absent | Full ✓ |
| O3.5 i | `covariance_eval_glwGaussianLimit`             | absent | Full ✓ |
| O4 / T1.1 | `glwGaussianLimit_isKolmogorovProcess`     | structured sorry on `kolmogorovCondition` | Full ✓ |
| O5 conj 3 / T1.2 | `Integrable (Y u)`                  | structured sorry | Full ✓ |
| O5 conj 4 / T1.3 | `Integrable (Y u * Y v)`            | structured sorry | Full ✓ |
| O5 conj 5 / T1.4 | `∫ Y u = 0`                         | structured sorry | Full ✓ |
| O5 conj 6 / T1.5 | `∫ Y u * Y v = K_GLW u v`           | structured sorry | Full ✓ |
| O5 conj 7 / T1.6 | joint Gaussianity                   | structured sorry | Full ✓ |
| O5 conj 8 / T1.7 | continuous paths                    | structured sorry | structured sorry (witness refactor pending) |
| O5 conj 9 / T1.8 | tail decay                          | structured sorry | structured sorry (Borell + BC blocker) |

**Net:** 9 new sorry-free helper lemmas + 6 conjuncts dissolved + the
load-bearing K-C condition for the projection process.
`glwGaussianLimit_Y_GLW_existence` now has **2 remaining sorries**
(conjuncts 8, 9), down from 7.

## Other GLW files

Untouched by R17 (still build green from R16):

* `GLWProcess.lean` — the `Y_GLW_exists` theorem references
  `glwGaussianLimit_Y_GLW_existence` directly; its sorries-mod-bridge
  count is now 2.
* `GLWProcessPredicate.lean` — read-only.
* `PhaseAUpperBound.lean` — Phase A scaffolding; signatures only.
* `YGLWConstruction.lean` — paper-proof base; not touched.
* `YGLWFromBrownianMotion.lean` — kernel/PSD bridge; not touched.

## Cumulative axiom posture

The two remaining sorries in `glwGaussianLimit_Y_GLW_existence`
prevent T1.9 (`#print axioms Y_GLW_exists` clean). The other axioms
(`two_dim_KMT_coupling` and the dead-code Wiener/Itô pair) are not
on the GLW path; T1.9 is gated solely on conjuncts 8 + 9.

## R18 candidate priorities (rough)

1. Witness refactor for conjunct 8 — replace
   `fun u ω ↦ ω u.toNNReal` with the K-C continuous modification
   `Y' : NNReal → (NNReal → ℝ) → ℝ` from
   `exists_modification_holder` (kolmogorov-extension-4).
   Re-prove conjuncts 3-7 via `Y' =ᵐ (fun ω ↦ ω ·)`.
2. Tail decay — port a Borell-TIS instance + Borel-Cantelli on the
   integer ladder `T = 1, 2, 3, …`.
3. After (1)+(2), expect `#print axioms Y_GLW_exists` to print only
   `propext / Classical.choice / Quot.sound`.
