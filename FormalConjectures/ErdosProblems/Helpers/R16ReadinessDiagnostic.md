# R16 readiness diagnostic — post-R15

R15 closed Phase 1 (kernel-generic projective limit O1-O3 Full,
O4-O5 Stub) and Phase 2 (axiom Y_GLW_exists retired to theorem; full
524.lean cascade green). This file enumerates the remaining blockers
that R16 must address to close the projective-limit construction
sorry-free and to start ramping the next axiom.

## Blocker 1 — O4 K-C threshold lift (`q > p`)

**Status.** `glwGaussianLimit_isKolmogorovProcess` is currently a
structured-sorry stub stating exponents `(p, q, M) = (2, 2, 1)`. The
arithmetic content (`E[(X_s - X_t)²] ≤ |s - t|²`) is fully in scope
via `glwCovMatrixNN_pairwise_diff_quadratic_le_sq`, but the
Kolmogorov-Chentsov continuous-modification theorem on a 1-D index
requires `q > p · d = p` strictly.

**R16 fix recipe.**

1. State the bound at `(p, q, M) = (4, 2, 3)` instead — i.e. use the
   4-th moment.
2. Apply the centered Gaussian moment formula `E[X⁴] = 3 E[X²]²` to
   reduce the 4-th moment to the squared 2-nd moment.
3. Plug in the existing `_le_sq` Hölder bound, square it, multiply by 3.

Estimated cost: 30-50 LOC. The `multivariateGaussian` 4-th-moment
formula is not yet in `MultivariateGaussian.lean`, so this may require
a small Mathlib-side helper (or a sur-mesure inline derivation via
`integral_charFun_mul_sq` and the bilinear-Gaussian moment generating
function).

**Watch-item.** If the BM-side `IsKolmogorovProcess.modification`
lemma already lands in mathlib by R16 with a public, type-class-driven
`q > p · d`-aware version, the recipe simplifies to a 1-line apply. If
not, R16 may need to either prove a self-contained K-C continuous-mod
result for the GLW-specific kernel (~60 LOC) or upstream the 4-th
moment formula.

## Blocker 2 — O5 9-conjunct fill-in

**Status.** `glwGaussianLimit_Y_GLW_existence` is a structured-sorry
stub. The signature is correct (matches the `Y_GLW_exists` axiom
1-to-1), but the proof body delegates to `sorry`. Eight of the nine
conjuncts are 1-2 line projects from `multivariateGaussian` lemmas
(see GLWGaussianProjectiveLimit.md "R16 work"). The continuous-paths
conjunct depends on Blocker 1 (O4 lift). The tail-decay conjunct is
**independent** of O4 — it uses Borell's inequality applied to
`sup_{u ∈ [T, T+1]} |Y u|` plus Borel-Cantelli on the integer grid.

**R16 fix recipe.**

1. Pin the witness `(Ω, μ) = (NNReal → ℝ, glwGaussianLimit)`,
   `Y u ω := ω ⟨u.toNNReal, by simp⟩` for `u ≥ 0` (lifting a separate
   "extend by 0 below 0" boilerplate is ~5 lines).
2. Project each conjunct to its multivariateGaussian counterpart via
   `hasLaw_restrict_glwGaussianLimit`.
3. The tail-decay step is the only "self-contained 30 LOC" segment;
   the rest are 1-3 line projections.

Estimated cost: 80-120 LOC, half of which is the tail-decay Borell
argument.

**Watch-item.** The witness shape `Y u ω := ω ⟨u.toNNReal, _⟩` only
covers `u ≥ 0`; for `u < 0` the GLW process is irrelevant (kernel
domain is `ℝ≥0 × ℝ≥0`), but the `Y_GLW_exists` axiom statement
quantifies over all `u : ℝ`. The trivial extension `Y u ω := 0` for
`u < 0` is harmless because all consumer conjuncts (covariance,
centeredness, integrability) are quantified over `0 ≤ u, 0 ≤ v`. The
only conjunct touching all `u : ℝ` is `Measurable (Y u)`, which is
trivially `measurable_const` for the negative branch.

## Blocker 3 — IsGLWProcess re-wrap

**Status.** The R15 dependency cycle (GLWProcessPredicate imports
GLWProcess imports GLWGaussianProjectiveLimit) was resolved by stating
O5 in the 9-conjunct shape rather than as `IsGLWProcess`. Once O5
lands, downstream consumers will want a 1-line wrap:
`IsGLWProcess`-from-9-conjunct lifting.

**R16 fix recipe.**

1. In `GLWProcessPredicate.lean`, add a corollary
   `isGLWProcess_from_existence` that takes the 9-conjunct existential
   and produces `∃ (Ω, μ, Y), IsGLWProcess Y` via field projections.
2. Update `isGLWProcess_exists_full` to call this directly via
   `Y_GLW_exists`.

Estimated cost: 5-10 LOC. Already prototyped in
`GLWProcessPredicate.lean:isGLWProcess_exists_full`.

## Blocker 4 (downstream) — KMT-coupling Yplus discharge

**Status.** `GLWUpperProof.lean:285` and `GLWLowerProof.lean:301`
reference an `IsGLWProcess Yplus` hypothesis for the KMT-coupled
process — Yplus lives on a different probability space than the
Y_GLW witness, and currently uses a separate axiom. After R16's O5
fill, the cleanest discharge is a **Skorokhod-style transfer** of the
Y_GLW witness onto the KMT space, OR refactoring the KMT-coupling
prerequisites to phrase them in terms of distribution-equivalent
covariance properties only.

This is the next axiom-retirement target after Y_GLW_exists. R16 is
the first round where it becomes attackable, since it depends on
having a concrete `Y_GLW` witness (post-R16-O5) to transfer.

## Calibration band note

R15's design fixed R14's calibration miss by adding tiered partial
credit on every outcome ≥ 50 pts. The cumulative partial-credit floor
this round is ~290 pts even if every item lands at Partial only —
which is a structural improvement over R14's 47% binary outcome.
R16's design should preserve the same tier-on-everything pattern,
since it forecloses the "skip the headline" rational option.
