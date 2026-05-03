# Track C round 11 — T1.1 audit (Carter-Pollard Step 3: h-function + cubic Taylor bound)

**Read-only audit, opened TC11 round at HEAD `7327028` (TC10 fixup; functionally TC10 closure `4dea634` + a doc-only commit "Carter–Pollard 1986 → 2004").**

## Cache state

`lake exe cache get`: completed (7753 files unpacked, no fresh downloads from origin).

## TC9/TC10 regression sanity

`lake build FormalConjectures.ErdosProblems.Helpers.BinomialTailBeta`: **GREEN** (Build completed successfully, 2624 jobs). TC9 `binomial_tail_beta_integral` Full + TC10 `stirling_prefactor_bound` Full + `PMF.binomial` bridge Full all preserved.

## TC11 scope (Q7 iterative micro-step binding)

**Step 3 ONLY** (paper §2 eq (8) Taylor heuristic + paper §4 first paragraph rigorous bound):

For `ε ∈ [0, 1]`, define the Carter–Pollard h-function

```
h(ε, s) := H((1-s)/2; ε) - H(1/2; ε)
        = (1/2)(1+ε) · log(1-s) + (1/2)(1-ε) · log(1+s)
```

(see derivation below for reduction `H((1-s)/2) − H(1/2)` → `(1/2)(1+ε) log(1−s) + (1/2)(1−ε) log(1+s)`).

**Closure target** (paper page 7, §4 first paragraph):

```
∀ ε ∈ [0, 1], ∀ s ∈ [0, 1),  h(ε, s) ≤ ε²/2 - (s+ε)²/2.
```

Note `ε²/2 − (s+ε)²/2 = −εs − s²/2`, so the closure target equivalently reads `h(ε, s) ≤ −εs − s²/2`.

**Auxiliary mid-Stage** (T2.2): explicit form and sign of `h'''(ε, s)` for `s ∈ (-1, 1)`.

**NOT in scope**: paper §2 eq (7) reformulation `P{X≥k} = e^Δ √(N/2π) ∫_0^1 e^{Nh−Nε²/2} ds` (TC12), bulk/tail split with `12η² + η = ε_N` choice (TC12), Mills reciprocal-bridge `m(x) = 1/ρ(x)` adapter (TC13), Theorem 2 §5 derivation (TC13), inequality (5) consequence and `tusnady_base_polynomial` envelope assembly (TC14), Layer 3 dyadic step body (TC15+), Layer 4 SupError (TC16+), mainline OR track-d modifications.

## ⚠️ Paper typo flag (mathematically critical)

**The paper page 7 prints**

```
h'''(s) = -[6s + 2s² + ε(2 + 6s²)] / (1−s²)³
```

**The correct expression is**

```
h'''(s) = -[6s + 2s³ + ε(2 + 6s²)] / (1−s²)³
       = -2 · [3s + s³ + ε(1 + 3s²)] / (1−s²)³.
```

Verification (recomputed from `h(ε, s) = (1/2)(1+ε) log(1−s) + (1/2)(1−ε) log(1+s)`):

- `h'(s) = -(1+ε)/(2(1−s)) + (1−ε)/(2(1+s))`, with `h'(0) = -ε`. ✓ (paper agrees, eq (8) coefficient of `s`)
- `h''(s) = -(1+ε)/(2(1−s)²) - (1−ε)/(2(1+s)²)`, with `h''(0) = -1`. ✓ (paper agrees, eq (8) coefficient of `s²/2`)
- `h'''(s) = (1−ε)/(1+s)³ - (1+ε)/(1−s)³`. ✓ (paper agrees on the unfactored form, p. 7 line 1)
- Common-denominator: `(1−ε)(1−s)³ - (1+ε)(1+s)³` over `(1−s²)³`.
  - `(1−s)³ = 1 − 3s + 3s² − s³`, `(1+s)³ = 1 + 3s + 3s² + s³`.
  - `[(1−s)³ − (1+s)³] − ε[(1−s)³ + (1+s)³] = (−6s − 2s³) − ε(2 + 6s²) = −[6s + 2s³ + ε(2 + 6s²)]`.

**Cross-check at s=1/2, ε=1/2**:
- Direct: `h'''(1/2) = (1/2)/(27/8) − (3/2)/(1/8) = 4/27 − 12 = −320/27 ≈ −11.852`.
- Correct formula: `−[3 + 1/4 + (1/2)(2 + 3/2)] / (3/4)³ = −5 · 64/27 = −320/27`. ✓
- Paper-as-printed: `−[3 + 1/2 + (1/2)(2 + 3/2)] · 64/27 = −5.25 · 64/27 = −336/27 ≈ −12.444`. **MISMATCH** (paper typo).

**Both forms still satisfy `h'''(s) ≤ 0` and `h'''(s) ≤ −2ε` for `s ∈ [0, 1)`, `ε ∈ [0, 1]`** (the qualitative claims used in the paper §4 are unaffected). The paper's §4 only uses `h'''(s) ≤ 0` to drop the cubic term, and `h'''(0) = −2ε` for the bulk-integral bound (TC12 scope), neither of which depends on which monomial appears in the bracket.

**Lean implementation will use the corrected form** `h'''(ε, s) = −2 · (3s + s³ + ε(1 + 3s²)) / (1 − s²)³`. We will NOT attempt to reproduce the paper-as-printed expression. The audit doc + commit message both flag the typo.

## Claims Verification Table (BINDING — Q7 protocol)

| # | Claim | VERIFIED? | Citation | Notes |
|---|-------|-----------|----------|-------|
| 1 | TC9 `binomial_tail_beta_integral` Full preserved | VERIFIED | `Helpers/BinomialTailBeta.lean` post-TC9 + TC10 fixup; targeted build green at this HEAD | No regression |
| 2 | TC10 `stirling_prefactor_bound` Full preserved + PMF.binomial bridge | VERIFIED | `Helpers/BinomialTailBeta.lean` post-TC10; targeted build green | No regression |
| 3 | TC8 Mills `_antitone` + Stirling Robbins Full preserved | VERIFIED | `Helpers/GaussianMillsRatio.lean` + `Helpers/StirlingTwoSided.lean` post-TC8; not in current target build but transitively imported | No regression |
| 4 | Mathlib `Real.hasDerivAt_log` at pin | VERIFIED | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:52` | `theorem Real.hasDerivAt_log (hx : x ≠ 0) : HasDerivAt Real.log x⁻¹ x` |
| 5 | Mathlib `HasDerivAt.log` at pin | VERIFIED | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:112` | `(hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => log (f y)) (f' / f x) x` |
| 6 | Mathlib `Real.contDiffAt_log` at pin | VERIFIED | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:74` | `ContDiffAt ℝ n log x ↔ x ≠ 0` — gives full smoothness for the chain |
| 7 | Mathlib `taylor_mean_remainder_lagrange` at pin | VERIFIED | `Mathlib/Analysis/Calculus/Taylor.lean:323` | Sig: `(hx : x₀ < x) (hf : ContDiffOn ℝ n f (Icc x₀ x)) (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) → ∃ x' ∈ Ioo x₀ x, f x − taylorWithinEval f n (Icc x₀ x) x₀ x = iteratedDerivWithin (n+1) f (Icc x₀ x) x' · (x − x₀)^(n+1) / (n+1)!` |
| 8 | Mathlib `iteratedDerivWithin_eq_iteratedDeriv` at pin | VERIFIED | `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:70` | `(hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x ∈ s) → iteratedDerivWithin n f s x = iteratedDeriv n f x`. Bridges `taylorWithinEval` (in Lagrange theorem) to `iteratedDeriv` (which is what we naturally compute for `h(ε, s)`). |
| 9 | Mathlib `uniqueDiffOn_Icc` at pin | VERIFIED | Used at `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean:526` (and Faa di Bruno, ODE PicardLindelof) | Standard `(h : a < b) → UniqueDiffOn ℝ (Icc a b)`. |
| 10 | Mathlib `HasDerivAt.add`, `.const_mul`, `.const_sub`, `.sub_const`, `.log` | VERIFIED | `Mathlib/Analysis/Calculus/Deriv/Add.lean:71, :122, :440, :471` (chain rules); `Log/Deriv.lean:112` | All standard, ergonomic combinators. |
| 11 | mainline + track-d preserved | VERIFIED — pre-TC11 | mainline `r46-track-a-mge-posdef` HEAD `daf3d9d` (per project memory), track-d CLOSED | No cross-branch contamination this round |

## Strategy choice — Strategy A (Lagrange remainder via `taylor_mean_remainder_lagrange`)

**Brief proposed**: Strategy A `taylor_mean_remainder_lagrange` (~80–130 LOC) vs Strategy B direct integration of the `h'''` bound (~60–100 LOC).

**Audit verdict — choose A**, for the following reasons:

1. **API ergonomics confirmed**: `taylor_mean_remainder_lagrange` exists at the pin with exactly the signature we need (verified at `Taylor.lean:323`). The hypotheses `ContDiffOn ℝ 2 f (Icc 0 s)` and `DifferentiableOn ℝ (iteratedDerivWithin 2 f (Icc 0 s)) (Ioo 0 s)` are both delivered for `f = carterPollardH ε` by `Real.contDiffAt_log` (since `1−s ≠ 0` and `1+s ≠ 0` on `[0, s]` ⊆ `[0, 1)`) composed with the linear-affine substitutions `s ↦ 1−s`, `s ↦ 1+s` and constant-multiply-add combinators. The chain assembles in one `fun_prop`-or-explicit-combinator pipeline.
2. **Bridge to `iteratedDeriv` is one-line**: `iteratedDerivWithin_eq_iteratedDeriv` (`Defs.lean:70`) gives equality at any interior or qualifying boundary point given `UniqueDiffOn` + `ContDiffAt`. We apply it three times (for n = 0, 1, 2) on the Taylor expansion side at `x₀ = 0` to convert `taylorWithinEval` into `f(0) + s·deriv f 0 + (s²/2)·iteratedDeriv 2 f 0`. Then `f(0) = 0`, `deriv f 0 = -ε`, `iteratedDeriv 2 f 0 = -1` reduce the Taylor polynomial to `−εs − s²/2`. Once on the remainder side, the same bridge converts `iteratedDerivWithin 3 f (Icc 0 s) s*` to `iteratedDeriv 3 f s* = h'''(ε, s*)`, which we bound `≤ 0` from the explicit form.
3. **Strategy B (direct integration of `h'''` bound)** would require either FTC (`integral_eq_sub_of_hasDerivAt`) twice, or a `Convex.inner_le_iff` style monotonicity + integral inequality. Both routes work but require more glue (~80–130 LOC, comparable to A in practice but with no shared infrastructure with the rest of the Calculus library). Strategy A reuses existing Mathlib `taylor_*` infrastructure, so the LOC count is lower and the strategy is more idiomatic.
4. **Failure mode for A is well-defined**: if the `DifferentiableOn` hypothesis on `iteratedDerivWithin 2 f (Icc 0 s)` is awkward to discharge inside `Ioo 0 s` (the iterated-derivative-within-set on the Lagrange-form requires `n+1`-times differentiable, not just ContDiff), we have a clear fallback: prove `ContDiffOn ℝ 3 (carterPollardH ε) (Icc 0 s)` (one extra order, still gated by `s < 1`) and apply `ContDiffOn.differentiableOn`. This adds ~5 LOC, not a strategy switch.

**Decision binding**: Strategy A is chosen and binding before T2.x. If Strategy A surfaces a Mathlib-level gap discovered post-audit, we **stop, re-audit, and write a Stub with diagnostic** — we do NOT silently switch to Strategy B mid-round.

## Step-by-step recipe (T2.x)

### T2.1 — Define `carterPollardH` + boundary lemmas (~30–50 LOC)

```lean
/-- Carter–Pollard h-function (arXiv:math/0508606 §2 eq (8)).

Definition is the substitution of the binary entropy
  `H(t; ε) = (1/2)(1+ε) · log(2t) + (1/2)(1-ε) · log(2(1-t))`
at `t = (1-s)/2`, minus its value at `t = 1/2`. After cancellation of the
constant logs, this reduces to:

  `h(ε, s) = (1/2)(1+ε) · log(1-s) + (1/2)(1-ε) · log(1+s)`.

The function is concave on `(-1, 1)` and achieves its maximum (=0) at `s = 0`. -/
noncomputable def carterPollardH (ε s : ℝ) : ℝ :=
  (1 / 2) * (1 + ε) * Real.log (1 - s) + (1 / 2) * (1 - ε) * Real.log (1 + s)

/-- `h(ε, 0) = 0`. -/
@[simp] lemma carterPollardH_zero (ε : ℝ) : carterPollardH ε 0 = 0 := by
  unfold carterPollardH; simp

/-- Closed form for the first derivative: `h'(ε, s) = -(1+ε)/(2(1-s)) + (1-ε)/(2(1+s))`.
    Used to evaluate `h'(ε, 0) = -ε`. -/
lemma carterPollardH_hasDerivAt
    {s : ℝ} (hs1 : s < 1) (hs2 : -1 < s) (ε : ℝ) :
    HasDerivAt (carterPollardH ε)
      (-(1 + ε) / (2 * (1 - s)) + (1 - ε) / (2 * (1 + s))) s := by
  -- Build via HasDerivAt.add of two const_mul·log·affine chains.
  have h1ne : (1 : ℝ) - s ≠ 0 := by linarith
  have h2ne : (1 : ℝ) + s ≠ 0 := by linarith
  -- ... (chain via Real.hasDerivAt_log + HasDerivAt.const_sub / .const_add + HasDerivAt.const_mul)
  sorry  -- T2.1 implementation

/-- `h'(ε, 0) = -ε`. -/
lemma carterPollardH_deriv_zero (ε : ℝ) :
    deriv (carterPollardH ε) 0 = -ε := by
  have := (carterPollardH_hasDerivAt (s := 0) (by norm_num) (by norm_num) ε).deriv
  simpa using this
```

LOC: ~10 def + ~5 zero-lemma + ~25 first-derivative `HasDerivAt` chain + ~5 deriv-zero corollary = ~45 LOC.

### T2.2 — Second / third iterated derivative (~50–80 LOC)

```lean
/-- Second derivative: `h''(ε, s) = -(1+ε)/(2(1-s)²) - (1-ε)/(2(1+s)²)`.
    `h''(ε, 0) = -1`. -/
lemma carterPollardH_hasDerivAt_deriv
    {s : ℝ} (hs1 : s < 1) (hs2 : -1 < s) (ε : ℝ) :
    HasDerivAt (deriv (carterPollardH ε))
      (-(1 + ε) / (2 * (1 - s)^2) - (1 - ε) / (2 * (1 + s)^2)) s := by
  sorry  -- T2.2 implementation

lemma carterPollardH_iteratedDeriv_two_zero (ε : ℝ) :
    iteratedDeriv 2 (carterPollardH ε) 0 = -1 := by
  sorry  -- via iteratedDeriv_succ + carterPollardH_hasDerivAt_deriv at s=0

/-- Third derivative explicit form: `h'''(ε, s) = -2 · (3s + s³ + ε(1 + 3s²)) / (1 - s²)³`
    for `s ∈ (-1, 1)`. **Note**: the paper (arXiv:math/0508606 page 7) prints
    `-(6s + 2s² + ε(2 + 6s²)) / (1-s²)³`, which is a typo for `-(6s + 2s³ + ε(2 + 6s²))`.
    The qualitative claims `h'''(s) ≤ 0` and `h'''(0) = -2ε` are unaffected. -/
lemma carterPollardH_iteratedDeriv_three
    {s : ℝ} (hs1 : s < 1) (hs2 : -1 < s) (ε : ℝ) :
    iteratedDeriv 3 (carterPollardH ε) s
      = -2 * (3 * s + s^3 + ε * (1 + 3 * s^2)) / (1 - s^2)^3 := by
  sorry  -- T2.2 implementation: chain h'' deriv, then ring-normalise

/-- `h'''(ε, s) ≤ 0` for `s ∈ [0, 1)`, `ε ∈ [0, 1]`. -/
lemma carterPollardH_iteratedDeriv_three_nonpos
    {ε : ℝ} (hε : 0 ≤ ε) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    iteratedDeriv 3 (carterPollardH ε) s ≤ 0 := by
  rw [carterPollardH_iteratedDeriv_three (by linarith) (by linarith) ε]
  -- Numerator `-2 · (3s + s³ + ε(1 + 3s²)) ≤ 0` since bracket ≥ 0.
  -- Denominator `(1 - s²)³ > 0` since `s² < 1`.
  -- Use `div_nonpos_of_nonpos_of_nonneg` or `div_nonpos`.
  sorry  -- T2.2 implementation
```

LOC: ~25 second-deriv `HasDerivAt` + ~10 `iteratedDeriv 2 = -1` corollary + ~30 third-deriv explicit form (chain rule + `ring`) + ~15 nonpos bound = ~80 LOC.

### T2.3 — Cubic Taylor bound, **closure target** (~40–80 LOC)

```lean
/-- **Carter–Pollard 2004 §4 cubic Taylor bound** (arXiv:math/0508606 page 7).

    For `ε ∈ [0, 1]` and `s ∈ [0, 1)`,
    `h(ε, s) ≤ ε²/2 - (s + ε)²/2 = -εs - s²/2`. -/
theorem carterPollardH_taylor_upper_bound
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    carterPollardH ε s ≤ ε^2 / 2 - (s + ε)^2 / 2 := by
  -- Reduce target: ε²/2 - (s+ε)²/2 = -εs - s²/2 (by `ring`).
  rcases eq_or_lt_of_le hs0 with hseq | hspos
  · -- s = 0: h(ε, 0) = 0 = -ε·0 - 0²/2 = ε²/2 - (0+ε)²/2.
    subst hseq; simp; ring_nf
  -- s > 0: apply taylor_mean_remainder_lagrange with n=2 on [0, s].
  have hUDO : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) s) := uniqueDiffOn_Icc hspos
  have hCD3 : ContDiffOn ℝ 3 (carterPollardH ε) (Set.Icc 0 s) := by
    -- ContDiffOn ℝ 3 of (1/2)(1+ε)·log(1-·) + (1/2)(1-ε)·log(1+·) on Icc 0 s ⊆ (-1, 1).
    sorry
  have hCD2 : ContDiffOn ℝ 2 (carterPollardH ε) (Set.Icc 0 s) :=
    hCD3.of_le (by norm_num)
  have hDiff2 : DifferentiableOn ℝ
      (iteratedDerivWithin 2 (carterPollardH ε) (Set.Icc 0 s)) (Set.Ioo 0 s) := by
    -- ContDiffOn ℝ 3 ⇒ DifferentiableOn (iteratedDerivWithin 2) on Ioo 0 s.
    sorry
  obtain ⟨s', hs'mem, hsTaylor⟩ :=
    taylor_mean_remainder_lagrange hspos hCD2 hDiff2
  -- Convert taylorWithinEval and iteratedDerivWithin to iteratedDeriv at boundary points.
  -- LHS-of-Taylor identity: f(s) = taylorPoly + remainder
  -- taylorPoly = f(0) + s·(deriv f 0) + (s²/2)·(iteratedDeriv 2 f 0) = 0 - εs - s²/2
  -- remainder = (iteratedDeriv 3 f s') · s³ / 6 ≤ 0 by carterPollardH_iteratedDeriv_three_nonpos
  -- ⇒ f(s) ≤ -εs - s²/2 = ε²/2 - (s+ε)²/2.
  sorry  -- T2.3 implementation: bridge + bound + ring close
```

LOC: ~5 boundary `s = 0` case + ~10 `UniqueDiffOn` + ~10 `ContDiffOn` chain (or ~15 if Mathlib needs explicit log composition) + ~10 `DifferentiableOn iteratedDerivWithin 2` + ~5 invoke Lagrange + ~25 bridge `taylorWithinEval` and `iteratedDerivWithin 3` to elementary form + ~10 ring close = ~75 LOC.

**Total T2.x estimate**: 45 + 80 + 75 = **200 LOC**, at the upper end of the brief's 130-200 calibrated band. **Risk band**: low; everything is core Mathlib, no exotic dependencies.

## Sub-checkpointing

- T+0:30: ✅ T1.1 audit (this doc).
- T+1:30: T2.1 `carterPollardH` def + 0/1st-deriv-zero lemmas Full.
- T+2:45: T2.2 second-deriv + third-deriv explicit form + nonpos bound Full.
- T+3:30: T2.3 Taylor bound Full (closure target).
- T+3:45: T3 build verification.
- T+4:00: T4 status doc + commit + push.
- Hard-stop T+5:00.

## Confidence updates (Q7 calibrated, structural risks flagged)

| Outcome | Region | P(Full) raw | Calibrated |
|---------|--------|-------------|------------|
| T1.1 audit | computational | 0.95 | 1.00 (this doc complete) |
| T2.1 `carterPollardH` def + h'(0) = -ε Full | computational | 0.85 | **0.80 calibrated** (chain rule with two affine substitutions × const_mul × log) |
| T2.2 third-deriv explicit form Full | semi-computational | 0.70 | **0.60 calibrated** (≥3 chain-rule steps + ring; potential `field_simp` resistance with `(1-s²)^3` denominator) |
| T2.2 third-deriv nonpos bound Full | computational | 0.90 | **0.85 calibrated** (positivity argument once form is in hand) |
| T2.3 Taylor bound Full (closure target) | semi-populated | 0.65 | **0.55 calibrated** (Lagrange + bridge + boundary case; modest novelty in `iteratedDerivWithin → iteratedDeriv` ergonomics) |
| T3 build + status | computational | 0.95 | 0.95 |
| T4 push | mechanical | 0.95 | 0.95 |

**Joint Full closure (T2.1 + T2.2 + T2.3)**: 0.80 · 0.60 · 0.85 · 0.55 ≈ **0.22 raw all-Full**; ~0.45 with at least 2 of 3 main lemmas Full and 1 honest sub-Stub.

**Mandatory floor**: T1.1 Full + T2.1 def Full + T3 + T4 = ~0.85 (audit + def + build verification + push are all near-deterministic).

**Structural risks (Q7 binding, flagged up-front)**:

- (a) **Boundary derivative-evaluation friction at `s = 0`**: `iteratedDerivWithin 2 f (Icc 0 s) 0` at the LEFT endpoint of `Icc 0 s` is a within-set 2nd derivative; bridging to `iteratedDeriv 2 f 0 = -1` requires `iteratedDerivWithin_eq_iteratedDeriv` with `0 ∈ Icc 0 s` and `ContDiffAt ℝ 2 (carterPollardH ε) 0`. The latter is automatic (`Real.contDiffAt_log` at `1 ± 0 = 1 ≠ 0`). Should be a 1-2 line discharge. **Mitigation**: pre-write `carterPollardH_contDiffAt` as a top-level lemma if friction surfaces.
- (b) **Mathlib `taylor_mean_remainder_lagrange` strict-inequality `x₀ < x` requirement**: the boundary case `s = 0` cannot use Lagrange directly. **Mitigation**: explicit `rcases eq_or_lt_of_le hs0` split (already in skeleton above); the `s = 0` branch reduces to `h(ε, 0) = 0 ≤ -0 - 0 = 0` by `simp; ring`.
- (c) **`(1-s²)³` ring-resistance**: `(1-s)³ · (1+s)³ = (1-s²)³` may need explicit `mul_pow` + `mul_comm` rather than blind `ring`. **Mitigation**: write the third-deriv chain in terms of `(1-s)³` and `(1+s)³` separately, then unify with a one-line `ring_nf` at the end.
- (d) **`DifferentiableOn (iteratedDerivWithin 2 f (Icc 0 s)) (Ioo 0 s)`**: this is the awkward Lagrange-hypothesis. **Mitigation**: derive from `ContDiffOn ℝ 3 f (Icc 0 s)` via `ContDiffOn.differentiableOn_iteratedDerivWithin` or analogous. If the lemma name differs, fall back to `ContDiffOn ℝ ∞ f (Icc 0 s)` (since `Real.log` is `C^∞` on `(-1, 1)`) and extract.
- (e) **`HasDerivAt.const_mul` vs `HasDerivAt.mul_const` ergonomics**: ensure the right combinator is used so that the constant `(1/2)(1±ε)` propagates correctly. **Mitigation**: prefer `(hf.const_mul c)` form; if reversed, swap with `mul_comm`.

**Distribution (post-T1.1)**:
- Best (P~0.30): T2.1 + T2.2 + T2.3 all Full → +1 NEW Full theorem (`carterPollardH_taylor_upper_bound`) + 5 NEW supporting Full lemmas + 1 NEW Full def, no sub-stub introduced.
- Mid-A (P~0.30): T2.1 + T2.2 Full, T2.3 partial (Lagrange invoked but bridge or boundary case hits friction) → ship close-modulo-bridge TAG'd Stub with concrete Mathlib gap (e.g., the precise `iteratedDerivWithin_eq_iteratedDeriv` invocation).
- Mid-B (P~0.20): T2.1 Full, T2.2 third-deriv explicit form Full but nonpos bound or Taylor bound hits ring-resistance → ship algebraic Full lemmas + diagnostic for the analytic close.
- Lower (P~0.20): chain-rule infrastructure for `(1-s)`-substitution surfaces a non-obvious Mathlib gap → diagnostic + LOC re-estimate for TC11 retry.

## What is NOT in scope this round (Q7 binding)

- Paper §2 eq (7) reformulation `P{X≥k} = e^Δ √(N/2π) ∫_0^1 e^{Nh(s) - Nε²/2} ds` — TC12 scope (uses TC9 beta integral + TC10 Stirling + TC11 h-function).
- Paper §4 bulk/tail split with `12η² + η = ε_N` choice — TC12 scope.
- Paper §3 Mills composition (already DONE TC6/TC8; just needs reciprocal-bridge `m(x) = 1/ρ(x)` adapter — TC13 scope).
- Paper §5 Theorem 2 derivation — TC13 scope.
- Inequality (5) consequence and `tusnady_base_polynomial` envelope assembly — TC14 scope.
- A2 (`one_dim_KMT_coupling`) retirement — TC15+.
- `tusnady_base_polynomial` body sub-sorry, Layer 3 dyadic step body, Layer 4 SupError — TC11 NOT in scope; deferred to TC14+/TC15+/TC16+.
- Mainline OR track-d modifications.
- TC1–TC10 closure modifications.
- `taylor_mean_remainder_lagrange` re-proof or adapter (we use Mathlib's directly).

## Anti-patterns explicitly forbidden (per brief)

- Multi-step Carter–Pollard assembly attempt (Q7 binding to Step 3 only).
- Skip cache check.
- Skip Claims Verification Table.
- Modify TC1–TC10 Full theorems.
- Modify mainline OR track-d.
- Push to wrong branch.
- Plan doc as substitute for code.
- Silent strategy switch from A → B mid-round (per Track C dispatch protocol; if A fails, ship Stub with diagnostic).
- Reproducing the paper's typo `2s²` in the Lean third-deriv explicit form.

## Cross-track FS discipline (V2-cluster lesson)

**Not applicable**: Track-c-only round, no `lake update`, no pin bump, no `.lake/packages/*` checkout, no shared-FS write outside the `track-c-1dkmt` worktree. R61-A or any mainline round can run concurrently in `~/Documents/formal-conjectures/` without interference.

End audit.
