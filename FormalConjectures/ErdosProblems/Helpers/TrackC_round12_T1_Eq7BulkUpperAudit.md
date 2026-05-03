# Track C round 12 — eq. (7) / bulk upper audit

**Date:** 2026-05-03. **Branch:** `tc12-cdx-bulk-upper`.
**Base:** `track-c-1dkmt` at `efe78d7`.

## T1.0 paper recheck

Fetched Carter--Pollard 2004 from arXiv (`math/0508606`) before writing
Lean bodies, per `feedback_paper_recheck_t10`.

The paper text around §2 eq. (7) confirms the brief's target shape:

```text
P{X ≥ k} = e^∆ sqrt(N/(2π)) ∫_0^1 e^{N h(s)-Nε²/2} ds,
where ∆ = log(1 + N^{-1}) + Λ - 1/2 log(1 - ε²) - N ε⁴ γ(ε).
```

The §4 upper-bound paragraph also matches the brief: the Taylor estimate
gives `h(s) ≤ ε²/2 - (s+ε)²/2` for `0 < s < 1`, and the paper states that
the right-hand side of approximation (9) is an upper bound because the
integrand is nonnegative on `(1, ∞)`, yielding
`P{X ≥ k} ≤ e^∆ Φ̄(ε√N)`.

## T1.1 local API / state audit

Baseline build:

```text
lake build FormalConjectures.ErdosProblems.Helpers.CarterPollardHFunction
```

completed successfully on the base worktree.

Important local mismatch with the TC12 brief: `bin_tail_beta_integral` and
`bin_tail_h_integral` are not present as declarations/placeholders in
`CarterPollardHFunction.lean` at `efe78d7`. The TC12 work therefore has to
add declarations rather than replace existing placeholder bodies.

Relevant in-tree APIs:

| Item | Status |
|---|---|
| `binomial_tail_beta_integral` | Present in `Helpers/BinomialTailBeta.lean`; gives the beta-integral identity for `binomialPolyTail m k p`. |
| `carterPollardH_taylor_upper_bound` | Present and Full in `Helpers/CarterPollardHFunction.lean`; gives `h(ε,s) ≤ ε²/2 - (s+ε)²/2` for `0 ≤ s < 1`. |
| Gaussian tail notation | Mathlib has `gaussianPDFReal`; this project defines Mills-tail primitives via `gaussianMillsRatioReal`, but there is no `Real.Gaussian.compl_cdf` API matching the brief's pseudocode. |

## Bridge-gap audit

The exact downstream consumer theorem in the TC12 brief contains a
nonexistent Gaussian-tail name and requires evaluating a translated/scaled
Gaussian integral over `(0,∞)`. That is real analysis work, but it is local
calculus/integration infrastructure, not a multi-year upstream gap. The safe
first closure is the pointwise exponential domination:

```lean
exp (N*h(ε,s) - N*ε^2/2) ≤ exp (-(N*(s+ε)^2)/2)
```

for `0 ≤ N`, `0 ≤ ε`, `0 ≤ s`, `s < 1`. This is exactly the Taylor-bound
payload needed before the interval-integral and Gaussian-tail evaluation
steps.

Follow-up implementation note (Codex continuation on the same branch):
after the first TC12 pass landed the pointwise bridge, the monotone
interval-integral consequence was also closed on compact prefixes
`[0, r]`, `r < 1`:

```lean
theorem carterPollardH_exp_bulk_upper_interval_prefix
    {N ε r : ℝ} (hN0 : 0 ≤ N) (hε0 : 0 ≤ ε) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ s in (0 : ℝ)..r, Real.exp (N * carterPollardH ε s - N * ε ^ 2 / 2) ≤
      ∫ s in (0 : ℝ)..r, Real.exp (-(N * (s + ε) ^ 2) / 2)
```

This deliberately stops before the improper-limit / Gaussian-tail
evaluation. It is the safe Restatement-(ii) bulk-upper body fragment: no
`Real.Gaussian.compl_cdf` is fabricated, no endpoint continuity at `s = 1`
is assumed, and no new sorry is introduced.

## Disposition

Proceed with additive Full lemmas on `tc12-cdx-bulk-upper`, without using
`sorry` and without fabricating the missing `Real.Gaussian.compl_cdf` API.

Final landed state on this branch:

| Lean artefact | Status |
|---|---|
| `bin_tail_beta_integral_half_poly` | Full |
| `carterPollardH_exp_bulk_upper_pointwise` | Full |
| `carterPollardH_exp_bulk_upper_interval_prefix` | Full |

`lake build FormalConjectures.ErdosProblems.Helpers.CarterPollardHFunction`
is green after all three.
