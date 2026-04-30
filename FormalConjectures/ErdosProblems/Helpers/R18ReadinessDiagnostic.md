# R18 Readiness Diagnostic

Closing-of-R17 diagnostic listing the **prioritized** open work that
will turn into the R18 manifest. Each blocker carries a "blocking
relation" so the Cowork side can sequence cleanly.

## Blocker 1 (priority A) — Conjunct 8: continuous-path witness refactor

**State:** `glwGaussianLimit_Y_GLW_existence` carries the witness
`fun u ω ↦ ω u.toNNReal`. The function `u ↦ ω u.toNNReal` is *not*
continuous on ℝ for a typical `ω : NNReal → ℝ` drawn from
`glwGaussianLimit` — the projection process is a-priori only a
modification, not a continuous one.

**Resolution path:**

1. Apply `BrownianMotion/Continuity/KolmogorovChentsov.lean`:
   `exists_modification_holder` (single-tier form, since we have
   `(p, q, M) = (2, 2, 1)` with `q > d = 1`) to
   `glwGaussianLimit_isKolmogorovProcess`.
2. The resulting `Y' : NNReal → (NNReal → ℝ) → ℝ` is measurable in
   each coordinate, satisfies `Y' t =ᵐ[glwGaussianLimit] (· t)`, and
   has continuous paths in each `ω`.
3. Replace the witness with `fun u ω ↦ Y' u.toNNReal ω`. Since
   `Real.toNNReal : ℝ → NNReal` is continuous, the composed function
   `u ↦ Y' u.toNNReal ω` is continuous on ℝ.
4. Re-prove conjuncts 3-7 by ae-equality transfer:
   `Integrable.congr`, `integral_congr_ae`, etc. The covariance
   `∫ Y u * Y v = K_GLW u v` survives because pointwise products of
   ae-equal functions agree ae.

**Estimated effort:** ~150 LOC / 1 wave.

**Unblocks:** T1.9 (`#print axioms Y_GLW_exists` clean) — currently
the dominant blocker; everything else in Phase 1 is done.

## Blocker 2 (priority A) — Conjunct 9: tail decay (Borell + BC)

**State:** the existential `∀ ε > 0, ∀ᵐ ω, ∃ T₀, ∀ u ≥ T₀, |Y u ω| ≤ ε`
is mathematically correct (`K_GLW(u, u) → 0` and Borell-TIS bound on
suprema), but no Lean proof.

**Resolution path:**

1. Prove a Borell-TIS instance for the marginal supremum
   `sup_{u ∈ [T, T+1]} |ω u.toNNReal|` under `glwGaussianLimit`.
   Bound: `P(sup ≥ t) ≤ 2 exp(-t²/(2σ_T²))` with
   `σ_T² = sup_{u ∈ [T, T+1]} K_GLW(u, u) ≤ 1/(2T)` (existing
   `K_GLW_var_le_recip` from `YGLWConstruction.lean`).
2. Apply Borel-Cantelli on the integer ladder `T = 1, 2, 3, …`:
   `∑_T P(sup_{[T, T+1]} |Y| > ε) < ∞` for any ε > 0.
3. Conclude almost-sure tail decay.

**Mathlib gap:** Borell-TIS for general centred Gaussian processes is
only partially in Mathlib. May need an elementary route for the GLW
kernel using the explicit `K_GLW(u, u) ≤ 1/(2u)` bound and
union-bound over a finite ε-net of `[T, T+1]`.

**Estimated effort:** ~200 LOC / 2 waves.

**Unblocks:** T1.9 (`#print axioms` clean) — second of the two
gating sorries.

## Blocker 3 (priority B) — Phase A: Slepian comparison

**State:** signature placeholders exist in `PhaseAUpperBound.lean`
(`Slepian_GLW_vs_OU` and the corresponding `gaussianDensity` sign
lemma).

**Resolution path:**

1. Density-monotonicity sub-lemma (the elementary route):
   for jointly Gaussian `(X, Y)` and `(X', Y')` with
   `Var X = Var X', Var Y = Var Y'`, and `Cov(X, Y) ≤ Cov(X', Y')`,
   the joint density `p(x, y; ρ)` is monotone in ρ ⇒
   `P(X ≤ a, Y ≤ b)` is monotone in ρ.
2. Slepian then follows by integrating along a path of covariances
   from the GLW pair to the OU pair (both PSD, both with the same
   diagonal — since Var = K_GLW(u, u) for both).

**Mathlib gap:** Slepian comparison theorem is not in Mathlib. The
density-monotone form has elementary proofs (Pitt 1977, Joag-Dev
1983) that don't require multivariate Gaussian apparatus.

**Estimated effort:** ~300 LOC / 3 waves.

**Unblocks:** Phase A upper bound (currently scaffold-only).

## Blocker 4 (priority B) — Phase A: Sudakov-Fernique bound

**State:** signature stub.

**Resolution path:** standard SF reduction:
`E[sup_{[0, T]} X] ≤ E[sup_{[0, T]} X']` when
`E[(X_t - X_s)²] ≤ E[(X'_t - X'_s)²]`. Standard proof via the
incremental-Slepian application along a Gaussian interpolation
`Z_t(λ) = √(1-λ) X_t + √λ X'_t`.

**Depends on:** Blocker 3 (Slepian).

**Estimated effort:** ~150 LOC.

**Unblocks:** Phase A upper bound, given Slepian.

## Blocker 5 (priority C) — Two-dim KMT retirement

**State:** `two_dim_KMT_coupling` is one of the still-load-bearing
axioms. Letwin-Sawhney's "1-D KMT applied twice" approach is
documented in R14's diagnostic; an explicit Lean port has not been
attempted.

**Mathlib gap:** 1-D KMT is **not** in Mathlib at HEAD (rescanned
2026-04-30 — see `TwoDimKMTRetirement.md`). Even with a 1-D KMT
proof in Lean, the 2-D coupling adds a substantial coordinate-by-
coordinate construction that hasn't been touched.

**Estimated effort:** ~1000 LOC / 6+ waves.

**Unblocks:** the +500 cumulative project bonus for
`two_dim_KMT_coupling` retirement.

## Summary

| # | Blocker | Priority | Effort | Unblocks |
|---|---------|----------|--------|----------|
| 1 | Conj 8 witness refactor | A | 150 LOC | T1.9 (`#print axioms`) |
| 2 | Conj 9 tail decay | A | 200 LOC | T1.9 (`#print axioms`) |
| 3 | Slepian comparison | B | 300 LOC | Phase A upper bound |
| 4 | Sudakov-Fernique | B | 150 LOC | Phase A upper bound |
| 5 | Two-dim KMT | C | 1000+ LOC | A2-axiom retirement |

R18's natural focus is Blockers 1+2 (which together close out
Y_GLW_exists axiom retirement) and Blocker 3 (which begins the
Phase A upper-bound proof in earnest).
