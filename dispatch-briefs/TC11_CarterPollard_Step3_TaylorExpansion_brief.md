# Round TC11 brief — Carter-Pollard Step 3 (Taylor expansion of h-function)

**Type**: Closure round, Track C / Carter-Pollard chain.
**Dispatch surface**: `track-c-1dkmt` worktree at `~/Documents/formal-conjectures-track-c/`, HEAD `4dea634` (post-TC10).
**Scope binding (Q7)**: TC11 = paper's §2 h-function definition + cubic Taylor bound `h(s) ≤ ε²/2 − (s+ε)²/2` ONLY. Bulk/tail integral split (§4 main argument) staged TC12. Mills composition (§3 reuse) staged TC13. `tusnady_base_polynomial` envelope assembly staged TC14.

---

## T1.0 — paper recheck (verbatim, fetched arXiv:math/0508606 / Yale PDF Tusnady3.pdf)

**Reference**: Carter, A.V. and Pollard, D. (2004), "Tusnády's inequality revisited," *Annals of Statistics* 32(6), 2731–2741. DOI 10.1214/009053604000000733. Authors' PDF: http://www.stat.yale.edu/~pollard/Papers/Tusnady3.pdf. arXiv preprint: math/0508606.

### Paper actual structure (NOT brief's "Steps 3-6" labelling)

The paper is organized by sections, not by numbered "Steps":

| Paper section | Content | Lean status |
|---|---|---|
| §1 Introduction | Tusnády original `\|X-Y\| ≤ 1 + Z²/8`; beta integral repn (2); Stirling formula (3) | Beta integral done in TC9; Stirling done in TC10 + TC8 Robbins |
| §2 Outline of method | Reformulation `P{X≥k} = (n choose ...)·∫_0^{1/2} e^{NH(t)} dt`; Stirling reduction → integral form (7) `P{X≥k} = e^Δ √(N/2π) ∫_0^1 e^{Nh(s) − Nε²/2} ds`; Taylor heuristic (8) `h(s) = -εs - (1/2)s² + (1/6)s³h'''(s*)`; main approximation (9) | **TC11+ scope** (this brief covers the Taylor part of (8)) |
| §3 Tails of normal distributions | Lemma 1: `ρ, r, Ψ` functions; bounds (i), (ii), (iii); Mills-ratio inequalities | **DONE in TC6 + TC8** (`_truncation`, `_pos`, `_antitone`) |
| §4 Details of proof for Theorem 1 | Rigorous Taylor with `h'''(s) ≤ 0`, `h''(s) ≤ -2`; bound on (η,1) tail; choice `12η² + η = ε_N`; final inequality (11) | **TC11 (this round) + TC12** |
| §5 Details of proof for Theorem 2 | Two-case argument (small ε vs moderate ε); δ₁, δ₂ from quadratic equations; uses Lemma 1 inequalities | **TC13+** |

### Theorem 1 (verbatim, paper page 3)

> **Theorem 1.** Let X have a Bin(n, 1/2) distribution, with n ≥ 28. Define
>
> γ(ε) = [(1+ε) log(1+ε) + (1-ε) log(1-ε) - ε²] / 24 = Σ_{r=0}^∞ ε^{2r} / [(2r+3)(2r+4)],
>
> an increasing function with γ(0) = 1/12 and γ(1) = -1/2 + log 2 ≈ 0.1931. Define ε = (2K-N)/N where K = k-1 and N = n-1. Define λn as in (3). Then there is a constant C such that
>
> P{X ≥ k} = Φ̄(ε√N) exp(An(ε))
>
> where
>
> An(ε) = -N ε⁴ γ(ε) − (1/2) log(1 − ε²) − λn-k + rk    and    -C log N ≤ N rk ≤ C
>
> for all ε corresponding to the range n/2 < k ≤ n - 1.

### Theorem 2 (verbatim, paper page 3)

> **Theorem 2.** Let zk = 2(βk − n/2)/√n and ε = (2K − N)/N. Let S(ε) = √(1 + 2ε² γ(ε)) for γ(ε) as in Theorem 1. Then, for some constant C' and n ≥ 28,
>
> zk = ε√N S(ε) + [log(1 − ε²) + 2λn-k] / (2√N S(ε)) + θk
>
> with -C'(ε√N + 1) ≤ Nθk ≤ C'(ε√N + log N) for all ε corresponding to the range n/2 < k ≤ n-1.

### The polynomial-bound consequence (verbatim, paper page 4, inequality (5))

> -C₁/√n + C₂ |k - n/2|³ / n² ≤ βk - k + 1/2 ≤ C₃ log n / √n + C₄ |k - n/2|³ / n²
>
> for n/2 ≤ k ≤ n and all n. For the quantile coupling between an X distributed Bin(n, 1/2) and a Y = n/2 + √n Z/2 distributed N(n/2, n/4), it follows that there is a positive constant C for which
>
> X - n/2 ≤ C + |Y - n/2|    and    |X - Y| ≤ C + (C/n²) |X - n/2|³.

This (5) is what the user's `tusnady_base_polynomial` (TC5 universal constants A=0.6, C=1, parameterized for Bin(2n, 1/2) + N(0, n/2)) corresponds to. **Paper's argument: §2 outline → §3 Mills bounds → §4 Theorem 1 → §5 Theorem 2 → consequence (5).** The Lean assembly mirrors this chain.

### h-function and Taylor bound (verbatim, paper page 5, equations (7)-(8))

> Define h(s) := H((1-s)/2) - H(1/2). The function H(·) is concave on (0,1)... On the range of integration, H(t) - H(K/N) is never greater than
>
> H(1/2) - H(K/N) = -(1/2)(1+ε)log(1+ε) - (1/2)(1-ε)log(1-ε) = -(1/2)ε² - ε⁴γ(ε).
>
> The concave function h(s) := H((1-s)/2) - H(1/2) achieves its maximum value of zero at s = 0 and
>
> P{X ≥ k} = e^Δ √(N/(2π)) ∫_0^1 e^{Nh(s) - Nε²/2} ds                                  (7)
>
> where Δ = log(1 + N⁻¹) + Λ - (1/2) log(1 - ε²) - Nε⁴γ(ε).
>
> ...
>
> Taylor expansion of h(s) about s = 0 and concavity of h(·) show that the exponent Nh(s) drops off rapidly as s moves away from zero. Indeed,
>
> h(s) = -εs - (1/2)s² + (1/6)s³ h'''(s*)    with 0 < s* < s
>
>      ≈ (1/2)ε² - (1/2)(s + ε)²    for s near zero.                                       (8)

### Cubic remainder bound (verbatim, paper page 7, §4 first paragraph)

> To make the proof rigorous, we need to replace the approximation in the Taylor expansion (8) by upper and lower bounds involving the third derivative
>
> h'''(s) = (1-ε)/(1+s)³ - (1+ε)/(1-s)³ = -[6s + 2s² + ε(2 + 6s²)] / (1-s²)³.
>
> The derivative of this function is negative for all s. Thus
>
> h'''(s) ≤ h'''(0) = -2ε    for 0 < s < 1
>
> and
>
> h(s) ≤ (1/2)ε² - (1/2)(s + ε)²    for 0 < s < 1.

**This last bound `h(s) ≤ ε²/2 - (s+ε)²/2 for 0 < s < 1` is the TC11 closure target.**

---

## Mapping paper → existing Lean helpers

| Paper artefact | Lean helper (current) | Notes |
|---|---|---|
| Beta integral (2) | `binomial_tail_beta_integral` (TC9) | exact match; just needs `p = 1/2` specialisation downstream |
| Stirling formula (3), upper bound | `factorial_le_stirling_robbins` (TC8) | better than paper needs (Robbins exp(1/(12n))) |
| Stirling formula (3), lower bound | `Stirling.le_factorial_stirling` (Mathlib) | direct |
| Stirling prefactor for `(n choose K)` | composition of TC10 `stirling_prefactor_bound` + Real.exp | paper uses `(N/(2π))^{1/2} · 4^N · exp(Λ)` form; we have the elementary bound, may need a tighter version for Theorem 1 |
| §3 Mills bounds (i), (ii), (iii) | `gaussianMillsRatioReal_pos` (TC7), `_truncation` (TC6), `_antitone` (TC8) | paper uses `ρ(x) = φ/Φ̄`, `r(x) = ρ(x) - x`, `Ψ(x) = -log Φ̄(x)`; our Mills `m(x) = (∫_x^∞ φ)/φ(x) = Φ̄(x)/φ(x) = 1/ρ(x)`. Reciprocal relationship — bridge needed but trivial |
| Real Beta function | `realBeta_eq_Gamma_ratio` (TC7) | `B(k, m-k+1) = (k-1)!(m-k)! / m!` |
| h(s) function definition | **TC11 NEW** | not present yet; ~10-15 LOC |
| h''(s) explicit form, ≤ -2 | **TC11 NEW** | ~30-50 LOC |
| h'''(s) explicit form, ≤ 0 (and ≤ -2ε) | **TC11 NEW** | ~30-50 LOC |
| `h(s) ≤ ε²/2 - (s+ε)²/2` | **TC11 NEW** (closure target) | ~40-80 LOC via Taylor + h''' bound |

---

## Mandatory floor

### T1.1 — Mathlib API audit (Full)
Document in `Helpers/TrackC_round11_T1_TaylorAudit.md`:

- **Verify Mathlib pin** `25ce633136`:
  - `Real.log` : present.
  - `HasDerivAt` for `Real.log` : `Real.log_hasDerivAt`, `Real.deriv_log` (verify exact name at pin).
  - `HasDerivAt.add`, `HasDerivAt.const_mul`, `HasDerivAt.neg`, `HasDerivAt.div_const` : all standard.
  - Polynomial-style derivative chain for `(1+s)^(-3)` and `(1-s)^(-3)` : likely needs `HasDerivAt.zpow` or `hasDerivAt_inv_pow`. Verify.
  - `taylor_mean_remainder` or analog : verify existence at pin (key for the Taylor inequality).
  - `Set.Ioo` API for the hypothesis `0 < s < 1`.
- **Two strategies**:
  - **Strategy A** (Taylor with explicit Lagrange remainder): Use `taylor_mean_remainder_lagrange` (or analog) on `h` over `[0, s]`, with the third derivative bound. ~80-130 LOC.
  - **Strategy B** (direct `h''` bound + `h(0) = 0` + integral / antiderivative): Bound `h(s) - h(0) - s·h'(0) - (s²/2)·h''(0)` via integration of `h'''(t)` bound. Cleaner if `taylor_mean_remainder` is awkward. ~60-100 LOC.
  - Audit chooses based on which Mathlib API is present and ergonomic. Document choice in T1.1 BEFORE T2.x (TC10 lesson — strategy bound at audit time, not post-hoc).

### T2.1 — Define `h` function (Full)
New file `Helpers/CarterPollardHFunction.lean`, OR append to `BinomialTailBeta.lean` if it stays under ~700 LOC. File naming preference: standalone for clean isolation, since downstream (TC12 bulk/tail) will also live in this file.

```lean
/-- The Carter-Pollard h-function from arXiv:math/0508606 §2 eq (7).
    `h(ε, s) := H((1-s)/2; ε) - H(1/2; ε)` where
    `H(t; ε) = (1/2)(1+ε)·log(2t) + (1/2)(1-ε)·log(2(1-t))`
    (paper writes `2H(t) = (1+ε) log t + (1-ε) log(1-t)`; we factor explicitly).
    Equivalently:
    `h(ε, s) = (1/2)(1+ε)·log(1-s) + (1/2)(1-ε)·log(1+s)`
    via the substitution `(1-s)/2`. -/
noncomputable def carterPollardH (ε s : ℝ) : ℝ :=
  (1/2) * (1 + ε) * Real.log (1 - s) + (1/2) * (1 - ε) * Real.log (1 + s)

/-- `h(ε, 0) = 0`. -/
lemma carterPollardH_zero (ε : ℝ) : carterPollardH ε 0 = 0 := by
  unfold carterPollardH; simp

/-- `h'(ε, 0) = -ε`. (First derivative at 0.) -/
lemma carterPollardH_deriv_zero (ε : ℝ) :
    (deriv (carterPollardH ε)) 0 = -ε := by
  sorry  -- TC11 sub-step
```
~30-50 LOC for definition + 2 trivial lemmas.

### T2.2 — Third derivative explicit form + bound (Full)
```lean
/-- Explicit form of `h'''(ε, s)` for `s ∈ (-1, 1)`. -/
lemma carterPollardH_iteratedDeriv_three (ε : ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDeriv 3 (carterPollardH ε) s
      = -(6*s + 2*s^2 + ε*(2 + 6*s^2)) / (1 - s^2)^3 := by
  sorry  -- TC11 sub-step

/-- `h'''(ε, s) ≤ 0` for `0 ≤ s < 1` and `0 ≤ ε`. -/
lemma carterPollardH_iteratedDeriv_three_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    iteratedDeriv 3 (carterPollardH ε) s ≤ 0 := by
  sorry  -- TC11 sub-step
```
~50-80 LOC. The explicit derivative chain is mechanical (logs + power rule + algebra).

### T2.3 — Cubic Taylor bound (Full, **closure target**)
```lean
/-- **Carter-Pollard 2004 §4 Taylor bound**: `h(ε, s) ≤ ε²/2 - (s+ε)²/2` for `0 ≤ s < 1`, `0 ≤ ε ≤ 1`.
    Used downstream in §4's proof of Theorem 1 (TC12 scope). -/
theorem carterPollardH_taylor_upper_bound
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    carterPollardH ε s ≤ ε^2 / 2 - (s + ε)^2 / 2 := by
  sorry  -- TC11 closure target
```
~40-80 LOC. Strategy: Taylor expansion of `h` around `s = 0` to order 3 with Lagrange remainder; substitute `h(0) = 0`, `h'(0) = -ε`, `h''(0) = -1`, and use `h'''(t) ≤ 0` to drop the cubic remainder.

### T3 — build verification (Full)
- Targeted: `lake build FormalConjectures.ErdosProblems.Helpers.CarterPollardHFunction` (or `BinomialTailBeta` if appended). Must be green at <90 s.

### T4 — push (Full)
- Single commit on `track-c-1dkmt`: "TC11 Carter-Pollard Step 3 — h-function definition + cubic Taylor bound (Full)".
- Push to `fork`.
- Append TC11 section to `Helpers/TrackCStatus.md`.

---

## Definitions

- **Full**: signature present, body fully proved (0 sorry inside body), file compiles, single-target build green.
- **Sub-Stub**: TAG'd sorry inside larger Full body — counts as deferred sub-claim. NOT used this round (TC11 = clean Full, no sub-stubs).

---

## Out of scope (explicit binding)

- Paper §2 eq (7) reformulation `P{X≥k} = e^Δ √(N/2π) ∫_0^1 e^{Nh-Nε²/2} ds` — TC12 scope (uses TC9 beta integral + TC10 Stirling + TC11 h-function).
- Paper §4 bulk/tail split with `12η² + η = ε_N` choice — TC12 scope.
- Paper §3 Mills composition (already DONE TC6/TC8; just needs reciprocal-bridge `m(x) = 1/ρ(x)` adapter — TC13 scope).
- Paper §5 Theorem 2 derivation — TC13 scope.
- Inequality (5) consequence and `tusnady_base_polynomial` envelope assembly — TC14 scope (chains TC11, TC12, TC13).
- A2 (`one_dim_KMT_coupling`) retirement — TC15+.

---

## Calibration

- **Total budget**: 130-200 LOC (T2.1 + T2.2 + T2.3). T1 + T3 + T4 are zero-LOC verification.
- **Realistic wall-clock**: 2-3 build cycles. T2.2 (third derivative explicit form) is the most mechanical; T2.3 (Taylor bound) is the closure-tier work where strategy choice matters.
- **Risk band**: low. All required APIs (`HasDerivAt`, `iteratedDeriv`, `Real.log`, `Set.Ioo` / `Ico`) are core Mathlib. The cubic algebra `h'''(s) = -[6s+2s²+ε(2+6s²)]/(1-s²)³` is pure `ring`/`field_simp` once the chain rule is unwound.
- **Closure tier**: real. Net debt change TC10 → TC11: **+0 sorries** (3 NEW Full theorems / lemmas + 1 NEW def, no sub-stubs introduced if Strategy A or B closes cleanly). +1 NEW Full theorem `carterPollardH_taylor_upper_bound` + 2 supporting Full lemmas + 1 Full def.
- **Cross-track FS discipline**: not applicable. Track-c-only round, no `lake update`, no pin bump. R61-A (mainline) can run concurrently in mainline worktree.

---

## Pre-flight checks (run before commit)

```sh
fc-c
git status
git branch --show-current                                          # track-c-1dkmt
lakecache
lake build FormalConjectures.ErdosProblems.Helpers.BinomialTailBeta 2>&1 | tail -10  # TC9+TC10 still green
```

---

## Artefact list

- `FormalConjectures/ErdosProblems/Helpers/CarterPollardHFunction.lean` (NEW) OR appended to `BinomialTailBeta.lean`.
- `FormalConjectures/ErdosProblems/Helpers/TrackC_round11_T1_TaylorAudit.md` (new audit).
- `FormalConjectures/ErdosProblems/Helpers/TrackCStatus.md` (TC11 section appended).

---

## Strategy proposal vs binding (TC9-TC10 lesson)

Brief proposes Strategy A (`taylor_mean_remainder_lagrange`) as default if Mathlib has it ergonomically; Strategy B (direct integration of h''' bound) as fallback. Track C dispatch is free to substitute on (a) audit-surfaced Mathlib gap on `taylor_mean_remainder`, OR (b) cycle-1 friction on either strategy. Document choice in audit T1.1 BEFORE writing T2.3 — not post-hoc.

---

## TC12+ preview (Probe-4-revised)

After TC11 lands `carterPollardH_taylor_upper_bound` + h-function infrastructure :

- **TC12** = bulk/tail split + Laplace upper/lower bounds on `∫ exp(N · h(s)) ds`. Case split `[0, η)` vs `[η, ∞)` with `η = Θ(log N / (ε N))`, Taylor-with-remainder on bulk, crude exponential decay on tail. **~400 LOC across 2-3 rounds.**
- **TC13** = ρ(x) and r(x) Mills-bridge inequalities + monotonicity + sharp ratio bounds `Φ̄(x+δ)/Φ̄(x) ≥ exp(δ ρ(x))`. **~300 LOC, 1 round.**
- **TC14** = envelope + final cutpoint approximation `z_k = ε γ(ε) + O(log N / √N)` + close `tusnady_base_polynomial` body. **~300 LOC across 1-2 rounds.**

**Total Carter-Pollard chain (TC11 → TC14) : 900-1600 LOC across 5-6 rounds** per Grok Probe 4 calibrated estimate (revised up from initial 580-1000 / 4 rounds).

After TC14 closes `tusnady_base_polynomial`, the cascade proceeds : TC15 (Hungarian dyadic step body), TC16 (Layer 4 SupError), TC17+ (main `oneDimKMT` assembly retiring `one_dim_KMT_coupling` axiom #2). TC15 → TC17+ realistic budget : 500-900 LOC across 4 rounds (also revised up by Grok).

## Grok-provided starter file

A ~140 LOC TC11 starter is available in `outputs/CarterPollardHFunction_TC11_starter.lean`. It includes :

- `H` and `h` definitions matching paper §2 / §4 notation exactly.
- 7 sub-lemma signatures with TAG'd sorries : `h_zero` (Full, ~5 LOC), `h_deriv_zero` (~15 LOC), `h_second_deriv_zero` (~20 LOC), `h_third_deriv_neg` (~25 LOC), `h_concave` (~30 LOC), `bin_tail_beta_integral` bridge from TC9 (~30 LOC), `bin_tail_h_integral` bridge to TC12 (~20 LOC placeholder).
- Mathlib pin compatibility checked against `25ce63313608` style.

Track C may import this starter directly or use it as a structural template ; if substituted, document rationale in T1.1 BEFORE writing body (TC10 protocol).

End brief.
