# Two-dim KMT coupling — retirement roadmap

**Status: BLOCKED on 1D KMT (R16 pre-flight finding).**

This document describes the planned retirement of the
`axiom two_dim_KMT_coupling` (524.lean:3741) — the second of the two
GLW-chain axioms (the first, `Y_GLW_exists`, was retired in R15 and
remains modulo structured-sorry transcription in
`Helpers/GLWGaussianProjectiveLimit.lean`).

## Axiom statement (current)

```
axiom two_dim_KMT_coupling :
    ∀ a : ℝ, 0 < a →
      ∃ ε : ℝ, 0 < ε ∧
        -- 2-D Rademacher → Gaussian strong invariance principle
        -- with logarithmic error bound on a fixed grid scale `a`.
        ...
```

The mathematical content is the **2-D analogue of the
Komlós–Major–Tusnády (KMT) coupling**: there is an explicit coupling
between the Rademacher partial-sum walk on `ℤ²` and a 2-D Gaussian
random walk such that the L^∞ error grows at most logarithmically in
the time horizon. This is the load-bearing tool by which the Phase 2
node-3 small-ball estimate (`Helpers/GaussianGridSmallBall.lean`) is
transferred from the Gaussian to the Rademacher side.

## Retirement strategy: 1D KMT applied twice (Letwin–Sawhney)

The standard route to 2-D KMT is **not** to re-prove the coupling from
scratch, but to apply the 1-D KMT coupling **separately** to each
coordinate of the 2-D walk. This is the **Letwin–Sawhney** approach:

> *Letwin & Sawhney (2025), arXiv:2604.19294, Lemma 4.7.* For
> Rademacher random walks on `ℤ²` with independent coordinates, the
> joint coupling error is bounded by the sum of the per-coordinate
> 1-D KMT errors, plus a residual `O(1)` term controlling the
> covariance mismatch on the off-diagonal.

In our setting the two coordinates of the 2-D walk are independent
(by construction in 524.lean §11, where the 2-D structure comes from
*two* independent copies of the 1-D Rademacher walk), so the
covariance-mismatch residual vanishes and the proof is just two
applications of 1-D KMT plus a triangle inequality.

## Pre-flight finding (R16 O5)

A scan at the current pin (`mathlib @ 25ce63313608`,
`brownian-motion @ 91267abd71bd`,
`kolmogorov_extension4 @ 2c2b44e55251`) found:

| Search target | Location | Found? |
|---|---|---|
| `KMT`, `Komlós–Major`, `Komlós-Major-Tusnády` | `mathlib/Mathlib/Probability/**` | **NO** |
| `Komlós–Major–Tusnády` | `brownian-motion/BrownianMotion/**` | **NO** |
| `strong invariance principle` (1-D, partial sums) | `mathlib/Mathlib/Probability/StrongLaw.lean` | only weak law / SLLN — **NO KMT** |
| `Skorokhod embedding` | `mathlib`, `brownian-motion` | **NO** |
| `Donsker invariance principle` | `mathlib`, `brownian-motion` | **NO** |
| `Komlos.lean` in `brownian-motion` | `BrownianMotion/StochasticIntegral/Komlos.lean` | **YES — but this is the L¹-convex Komlós lemma, NOT the KMT coupling theorem** |
| `Rademacher`, `subGaussian`, `Hoeffding` | `mathlib/Mathlib/Probability/Moments/SubGaussian.lean` | **moment bounds only — not KMT** |

**Conclusion: 1D KMT is not formalized in our toolchain.** The
Letwin-Sawhney route is therefore the wrong reduction at this pin —
even after the LS reduction the 1D leaves are themselves unproven.

## Implications for retirement

The retirement of `two_dim_KMT_coupling` is **gated on prior
formalisation of 1D KMT**, which in turn is a Mathlib-PR-scale
contribution (estimated 800-1500 LOC). Until 1D KMT lands upstream:

* **Short-term (R17–R20).** The axiom remains in 524.lean. Downstream
  consumers (524.lean:3925 endpoint reparametrisation) continue to
  import the axiom directly.
* **Medium-term Mathlib PR roadmap.** The most promising upstream path
  is to formalise the **Hoeffding-style Skorokhod embedding** first
  (which factors through subGaussian moment bounds, already partly in
  `Mathlib/Probability/Moments/SubGaussian.lean`); the 1D KMT then
  follows by the Skorokhod construction.
* **Long-term (R21+).** Once 1D KMT is upstream, the LS reduction in
  this file becomes a 30-50 LOC Lean proof:
  ```
  theorem two_dim_KMT_coupling_via_two_1D_KMT (a : ℝ) (ha : 0 < a) :
      ∃ ε : ℝ, 0 < ε ∧ ... := by
    obtain ⟨ε₁, hε₁_pos, hε₁⟩ := mathlib_1D_KMT a ha   -- coordinate 1
    obtain ⟨ε₂, hε₂_pos, hε₂⟩ := mathlib_1D_KMT a ha   -- coordinate 2
    refine ⟨ε₁ + ε₂, by linarith, ?_⟩
    -- triangle inequality on the L∞ joint error
    sorry
  ```

## Why the brief's "branch B" applies

Brief R16 §Phase 2 says:
> If O5 finds 1D KMT NOT available → O7 Stub + O12 (document) + jump
> to Phase 3.

That is the path we take in R16. Concretely:

* **O6 (1D KMT-twice proof)**: Stub — the proof structure is recorded
  in this file (above), but no Lean signature is added because the
  load-bearing mathlib lemma does not exist.
* **O7 (replace axiom)**: Stub — the axiom remains in 524.lean. We do
  not introduce a `theorem two_dim_KMT_coupling` with a sorry body
  because that would degrade auditability without semantic gain; the
  axiom form is more honest.
* **O8 (cascade green)**: N/A — no consumer-facing change in 524.lean.
* **O12 (this document)**: Full — written.

## Cross-references

* `524.lean:3741` — the live axiom statement.
* `524.lean:3874, 3925` — the two consumers of the axiom (
  `endpoint_reparametrization + two_dim_KMT_coupling` chain).
* `Helpers/GaussianGridSmallBall.lean` — the Gaussian-side small-ball
  estimate that the 2-D KMT coupling transfers to the Rademacher side.
* `Helpers/GLWLowerProof.lean` — the eventual consumer of the
  Rademacher-side small-ball estimate (Phase 2 GLW lower bound).

## Import map (for the eventual retirement)

When 1D KMT lands upstream, the retirement proof will need:

* `Mathlib.Probability.???` — 1D KMT statement (TBD upstream).
* `Mathlib.Probability.IndepFun` — independence of the two coordinates.
* `Mathlib.Topology.MetricSpace.Pseudo.Basic` — L∞ metric on `ℝ²`.

No new dependency on `brownian-motion` or `kolmogorov_extension4`.

## R17 upstream re-scan (2026-04-30)

Re-scanned mathlib HEAD and `brownian-motion` HEAD at the time of R17
close. **No 1D KMT primitive has appeared upstream.** Specifically:

* `Mathlib.Probability` — searched for "KMT", "Komlos", "Major",
  "Tusnady", "strong invariance", "Hungarian construction": zero hits
  in any guise. The closest existing infrastructure is
  `Mathlib.Probability.Moments.SubGaussian` (which only covers the
  log-MGF side of the inequality, not the coupling).
* `brownian-motion/BrownianMotion` — the only continuity result is
  Kolmogorov-Chentsov; there is no Skorokhod embedding nor any KMT.
  The library is squarely focused on Gaussian processes and the
  Kolmogorov extension.
* `kolmogorov-extension-4` — this is a measure-theoretic projective
  extension library; it has nothing to do with KMT and there is no
  prospect of adding KMT here. (It is a pure Banach-Steinhaus-style
  measure construction.)

**Implication:** the projection that R14's `O6` had hinted at —
"wait for upstream KMT and then port" — has not advanced. R18's
options for unblocking `two_dim_KMT_coupling` remain:

1. Wait further (R19+) and accept that the axiom remains in place.
2. Take a Skorokhod-via-explicit-CDF route (writes a much more
   elementary 1D coupling proof but at high LOC cost — see
   `OneDimKMTSketch.md` in this directory).
3. Commission an upstream PR for `Mathlib.Probability.KMT` if a
   Lean-friendly proof of the 1D KMT theorem with logarithmic error
   surfaces in the literature.

R17 leaves this file at the same Stub posture: documenting the
state, not changing it. The axiom `two_dim_KMT_coupling` stands
load-bearing, with two dependent consumers in `524.lean`.

## Outcome label

* **R14 O6**: Stub.
* **R17 re-scan**: Stub (no upstream change).
* **R18 next action**: see `R18ReadinessDiagnostic.md` Blocker 5.
