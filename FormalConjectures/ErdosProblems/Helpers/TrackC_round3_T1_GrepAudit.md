# Track C round 3 — T1.1 grep audit + Tusnády math verification

**Round:** Track C round 3 (parallel-track, branch `track-c-1dkmt`).
**Date:** 2026-05-02.
**Branch HEAD pre-TC3:** `7f25b84` (TC2 closure: Layer 2 `quantile_transform_finite_moment` Full close).
**Per process Q4 ii:** local Claude grep audit FIRST, Grok recipe SECOND with explicit uncertainty flagging on any math edge case.
**Per TC3 brief addendum (mismatch #13):** worktree setup is RECOMMENDED, conditional cap only on (worktree-absent ∧ collision-occurred).

## 0. Summary verdicts

| Check | Status | Risk to TC3 |
| --- | --- | --- |
| Worktree setup `../formal-conjectures-track-c` | ✅ created clean | low (collision risk reduced) |
| TC1 + TC2 commits present on branch | ✅ `15192f1`, `f018aea`, `7f25b84` | none |
| Layer 3 signature in `OneDimKMT.lean:384-410` | ✅ present, TC1-locked | low |
| Mathlib measure-theoretic Binomial Bin(n, 1/2) on ℝ | ❌ absent (only `PMF` on `Fin (n+1)`) | **moderate** — base-case signature must work around |
| Mathlib `gaussianReal : ℝ → ℝ≥0 → Measure ℝ` | ✅ present (`Distributions/Gaussian/Real.lean`) | none |
| Mathlib `Tusnady*` / `Hungarian*coupling*` / `KMT` | ❌ absent (grep hit count: 0) | expected |
| brownian-motion `Skorokhod*` | ❌ absent | already known (Layer 1 gap) |
| brownian-motion `Komlos.lean` | ⚠️ **MISLEADING NAME** — Komlós L¹ lemma, NOT KMT | none, but flag for future |
| Mathlib `IdentDistrib` + `IdentDistribIndep` | ✅ present | none — coupling-as-equivalence usable |
| `GaussianParametricAnalysis.lean` (R46 mainline) | ❌ absent on branch | none — orthogonal |
| Grok Tusnády recipe math soundness | ⚠️ **MATH SUBTLETY** — 8th misframing | **moderate** |

## 1. Worktree precondition (addendum-compliant)

`git worktree add ../formal-conjectures-track-c track-c-1dkmt` succeeded at session start. Working directory is `/Users/kieranmcshane/Documents/formal-conjectures-track-c`, branch `track-c-1dkmt`, HEAD `7f25b84`. `git status` clean. The conditional cap from skin-in-the-game item 1 does not trigger. Filesystem-collision discipline (memory `feedback_v2_cluster_filesystem_discipline`) honoured: TC3 work is committed in worktree, never touches mainline file state.

Caveat: `.lake/packages/` is shared with mainline (lake stores artefacts at the gitdir level, not per-worktree). For T2.3 `lake build`, this is acceptable for a *read-mostly* T1.1 + T2.1 sub-Stub round; if T2.1 had touched lake-affecting files (lakefile, lean-toolchain, lake-manifest) the shared state would be a hazard. T2.1 closure plan does not touch any of those files, so risk is low.

## 2. Mathlib API state (pinned, verified by grep)

### 2.1 Binomial distribution

- `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean`: defines `binomial : ℝ≥0 → (h : p ≤ 1) → ℕ → PMF (Fin (n + 1))`. Lemmas: `binomial_apply`, `binomial_apply_zero/last/self`, `binomial_one_eq_bernoulli`. Total surface: 6 declarations.
- **No measure-theoretic version** on `ℝ` (i.e., no `binomialReal : ℕ → ℝ≥0 → Measure ℝ` analogous to `gaussianReal`). To use Bin(2n, 1/2) as a measure on ℝ we must construct it ad-hoc as `(binomial (1/2 : ℝ≥0) (by norm_num) (2*n)).toMeasure.map ((↑) : Fin (2n+1) → ℝ)`.
- Coupling consequence: T2.1 *cannot* state Tusnády's lemma directly in the form "`B ~ Bin(2n, 1/2)`, `Z ~ N(0, n/2)`, `|B - n - Z| ≤ ...`" without first introducing a measure-theoretic Bin-on-ℝ wrapper.

### 2.2 Gaussian distribution

- `Mathlib/Probability/Distributions/Gaussian/Real.lean`: full measure-theoretic API. `gaussianReal : ℝ → ℝ≥0 → Measure ℝ`. PDF, integrability, characteristic function, scaling/translation laws all present.
- Cross-track: `Distributions/Gaussian/Fernique.lean` (~31KB) and `Distributions/Gaussian/Basic.lean` (~11KB) for multivariate / functional aspects — not needed for TC3.
- `BrownianMotion/Gaussian/Gaussian.lean` (brownian-motion package) extends to projective limits; not needed for TC3 (Tusnády base is 1-dim).

### 2.3 Coupling / IdentDistrib / Skorokhod

- `Mathlib/Probability/IdentDistrib.lean` + `IdentDistribIndep.lean`: identical-distribution predicate available. Usable for stating Tusnády as "exists `(B, Z)` on a coupled space with `B.law = Bin(2n, 1/2)` and `Z.law = N(0, n/2)` and pointwise bound ...".
- **No Skorokhod embedding** in either Mathlib or brownian-motion (already established in TC1 audit `TrackC_T1_OneDimKMTAudit.md`).
- **`Komlos.lean` in brownian-motion** is **NOT** the Komlós-Major-Tusnády theorem despite the suggestive filename — it is *Komlós's L¹ lemma* (Banach-style result on convex combinations of L¹-bounded sequences). Header verified: "Authors: Rémy Degenne", imports `Mathlib.Probability.Moments.Basic`, exports `komlos_convex`/`komlos_norm`/`komlos_ennreal`. Flagged here for the misframing-ledger in case future Grok recipes confuse the two.

### 2.4 Stopping times / Optional Sampling

- `Mathlib/Probability/Process/Stopping.lean` + `Mathlib/Probability/Martingale/OptionalSampling.lean`: stopping-time machinery present at standard mathematical level.
- `BrownianMotion/StochasticIntegral/OptionalSampling.lean` extends to BM-specific case. Not consumed by TC3 (Layer 1 work, not Layer 3).

## 3. Math correctness audit — Tusnády's lemma (the 8th misframing)

### 3.1 Round prompt's stated form

The TC3 brief cites:
> Tusnády's lemma (KMT 1975 + Massart 2002): For `B ~ Bin(2n, 1/2)`, there exists a coupling with `Z ~ N(0, n/2)` such that `|B - n - Z| ≤ C (1 + log n)` almost surely, with explicit constant `C`.

### 3.2 Literature verification

- **Komlós–Major–Tusnády 1975, Studia Sci. Math. Hungar. 32**: original paper does NOT state Tusnády's lemma per-step in `O(log n)` form. The per-step bound there is implicit in the dyadic recursion.
- **Tusnády 1977, "A study of the Statistical Hypothesis Generated by the Strong Law of Large Numbers"**: per-step bound is `|B - n - Z| ≤ 1 + Z²/n` (polynomial in `Z`, not log).
- **Bretagnolle–Massart 1989** + **Massart 2002 "Strong approximation for multivariate empirical and related processes via KMT constructions"**: refines per-step to explicit polynomial form `|B - n - Z| ≤ A + B · |Z|/√n + C · Z²/n` for explicit constants `A, B, C` (Mason-Zhou 2012 review).
- **Carter–Pollard 2004 "Tusnády's inequality revisited"**: pointwise bound `|B - n - Z| ≤ 0.6 + Z²/n` with explicit constant.

### 3.3 What the `O(log n)` form actually is

The "almost surely `O(log n)`" bound is **not** a pure per-step Tusnády result. It emerges from the **combination** of:
1. Per-step polynomial Tusnády bound (the Bretagnolle–Massart form), AND
2. **Almost-sure tail control** on the Gaussian `Z` via Borel–Cantelli I: a.s., for all sufficiently large `n`, `|Z_n| ≤ √(2 (1+ε) log n)`. Substituting into the polynomial bound gives `|B - n - Z| ≤ A + B · √(2 (1+ε) log n)/√n + C · 2(1+ε) log n / n = O(log n / n) + O(log n)^{1/2} / √n`, which integrates over the dyadic chain to the `O(log N)` running-sup error.

The pure pointwise per-step `O(log n)` bound does NOT hold uniformly in `(B, Z)` pairs without restriction to typical sets (probability tending to 1).

### 3.4 8th misframing (cumulative ledger update)

- Ledger pre-TC3: 7 (per `R48-T1.1 (revision)` — TC1 Galois iff was 5th, R48 Path γ' was 6th, R48 T2.1 abort was 7th).
- **8th** (this round): TC3 brief Tusnády statement conflates per-step polynomial bound with chain-level a.s. log bound. The mismatch is moderate (not catastrophic): the consequence form is correct as a *signature*, but T2.1 *body* cannot derive the pure log form without invoking Layer 4's Borel–Cantelli machinery, creating a circular dependency if attempted in TC3.

### 3.5 T2.1 corrective plan

T2.1 should state Tusnády's base case in the **polynomial per-step form** (Carter–Pollard 2004 / Bretagnolle–Massart 1989):

```lean
theorem tusnady_base_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (B Z : Ω' → ℝ) (A C : ℝ),
      IsProbabilityMeasure μ' ∧ 0 < A ∧ 0 < C ∧
      Measurable B ∧ Measurable Z ∧
      -- B has Bin(2n, 1/2) law (centred to remove +n term in bound).
      μ'.map B = (binomial (1/2 : ℝ≥0) (by norm_num) (2*n)).toMeasure.map (Nat.cast) ∧
      -- Z is centred Gaussian with variance n/2.
      μ'.map Z = gaussianReal 0 ((n / 2 : ℝ).toNNReal) ∧
      -- Per-step polynomial coupling bound (Carter-Pollard / Bretagnolle-Massart).
      ∀ ω', |B ω' - n - Z ω'| ≤ A + C * (Z ω')^2 / n
```

Body sub-Stub'd with `TAG[TrackC-Layer3-Tusnady-base-polynomial]` citing concrete Mathlib gap (no measure-theoretic Bin on ℝ, requires PMF→Measure wrapper) and concrete math gap (Stirling-formula precision, Mills ratio for Gaussian PDF). The body close is multi-round (TC4-TC5).

The Layer 3 *consumer-form* signature `hungarian_dyadic_coupling` in `OneDimKMT.lean:384-410` is unchanged — its uniform-in-ω log bound is the chain-level consequence form, which is what consumers (Layer 4 → Main) need. T2.1 polynomial form feeds the chain *inside* the Layer 3 body proof (TC4 work).

## 4. TC1 signature double-check

`hungarian_dyadic_coupling` signature (`OneDimKMT.lean:384-410`):
- Hypotheses: `iIndepFun a ℙ`, centred, unit variance.
- Conclusion: existential coupling space with per-dyadic-scale uniform-in-ω' bound `|S' (2^k) ω' - B (2^k) ω'| ≤ C * Real.log ((2^k : ℕ) + 1)` for all `k ≥ 1` and all `ω'`.
- **Verdict**: signature is consumer-correct. Quantifier order `∀ k, ∀ ω'` (uniform in ω' for each k) matches Layer 4's consumption pattern (inner-to-outer dyadic chain). Constant `C` is shared across scales, also correct.
- Caveat: the `∀ ω'` form is the *deterministic* envelope, equivalent to "all ω' outside a measure-zero set" only on a redefinition of `Ω'` to exclude the exceptional set. This is fine for the consumer (Layer 4 proof can absorb the redefinition) but adds an `Exists.intro` step inside the TC4 closure.

No signature change for TC3.

## 5. T2.2 dyadic recursion signature plan

The TC1-locked `hungarian_dyadic_coupling` IS the dyadic recursion signature. T2.2 in TC3 brief asks for a *separate* recursion-step signature that captures one-step-of-dyadic-recursion, callable from inside the Layer 3 body. Plan:

```lean
theorem hungarian_dyadic_step (k : ℕ) (hk : 1 ≤ k) :
    -- "Given a coupling at scale 2^(k-1), refine to scale 2^k via Tusnády"
    ...
```

Body sub-Stub'd, TAG'd `TrackC-Layer3-Hungarian-dyadic-step`. T2.2 outcome = signature locked + docstring describing recursion plan. Body is TC4 scope.

## 6. Cross-track synergy

- `GaussianParametricAnalysis.lean` from R46 mainline: **ABSENT on branch** (consistent with TC2 audit). No cross-track import opportunity for TC3.
- `RademacherSequence.lean` (R29 helper): present, 2.1KB. Provides `IsRademacherSequence` predicate consumed by `axiom one_dim_KMT_coupling` (the Rademacher-specialised axiom that the TC1-4 cluster aims to retire).

## 7. Anti-mismatch hygiene compliance

Every Mathlib lemma to be invoked in T2.1 sub-Stub docstring is grep-verified above:
- `gaussianReal`, `gaussianPDF`, `gaussianReal_apply` ✅ in pinned Mathlib.
- `binomial` (PMF) ✅ in pinned Mathlib.
- `IdentDistrib` ✅ in pinned Mathlib.
- `Measure.map`, `Measure.ext_of_Iic` ✅ in pinned Mathlib.
- No invented or hallucinated lemma names.

## 8. T2.1 risk assessment update

| Outcome | P(Full) | Notes |
| --- | --- | --- |
| T2.1 base case Full close (per-step polynomial form) | 0.10 | Requires Stirling-formula precision + Mills ratio + measure-theoretic Bin construction; multi-week math-engineering. |
| T2.1 honest sub-Stub with concrete diagnostic | 0.85 | Concrete Mathlib gaps + math-content blockers identified above. |
| T2.1 mistaken Full attempt with `O(log n)` form | --- | **NOT to be attempted** — circular dependency. |

Recommended action: ship signature + body sub-Stub'd with anchored docstring tracing the polynomial form + concrete diagnostic. This is the honest mid-distribution outcome (P ~ 0.65 in TC3 brief).
