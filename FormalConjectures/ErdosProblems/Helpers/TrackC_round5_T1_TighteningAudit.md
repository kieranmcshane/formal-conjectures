# Track C round 5 — T1.1 Claims Verification Table + signature extraction

**Branch:** `track-c-1dkmt` (worktree `~/Documents/formal-conjectures-track-c`)
**Parent state:** TC4 close `a1d6b6a` (Path A advance — comonotonic coupling Full + sub-sorry on pointwise polynomial bound).
**Pin:** `mathlib4 @ 25ce633136084367f182be00fdff7613ea949d27` (unchanged).
**Round goal:** mechanical signature tightening (TC4 weakness flags) + Carter-Pollard infrastructure preparation (Mills ratio start).

This audit fills the TC5 brief's mandatory Claims Verification Table and
extracts the verbatim TC3/TC4 signatures targeted by T2.1 + T2.2 tightening.

## §0 — Scope reminder

Two TC4 weakness findings are BINDING for TC5 tightening:

* **W1 (`tusnady_base_polynomial`)** — existential `(A, C)` per-n. Layer 4 chain
  needs UNIVERSAL constants (Carter-Pollard 2004: A = 0.6, C = 1).
* **W2 (`hungarian_dyadic_step`)** — locked signature
  * lacks sub-Gaussian hypothesis on `a` (admits arbitrary unit-variance
    laws → quantile-coupling differences unbounded over `Ioc 0 1`),
  * lacks Brownian-motion-law constraint on `B_cur` (admits degenerate
    witness `B_cur ≡ S_cur`, useless to Layer 4 SupError chain).

## §1 — Claims Verification Table (10 rows, all must be VERIFIED)

| # | Math statement | Lean form (proposed / current) | VERIFIED? | Citation (file:line at pin OR Mathlib doc URL) | Notes |
|---|----------------|--------------------------------|-----------|------------------------------------------------|-------|
| 1 | TC3 `tusnady_base_polynomial` signature | Existential `(A, C)` form per-n | **VERIFIED** | `Helpers/OneDimKMT.lean:408-416` (TC3 commit `c96e54b`, post-TC4 HEAD `a1d6b6a` body). Verbatim binders include `(A C : ℝ)` quantified inside the existential, conclusion `∀ ω', |B ω' - (n : ℝ) - Z ω'| ≤ A + C * (Z ω') ^ 2 / (n : ℝ)`. TC4 body witnesses `A = (n : ℝ) + 1`, `C = 1`. | A is per-n by construction (TC4 chose `(n : ℝ) + 1` to absorb the trivial `ω' ∉ Ioc 0 1` case via TC2 piecewise definition). |
| 2 | TC3 `hungarian_dyadic_step` signature | Locked at TC3, body Stub'd; lacks sub-Gaussian on `a`, lacks BM-law on `B_cur` | **VERIFIED** | `Helpers/OneDimKMT.lean:512-555`. Hypotheses on `a`: `iIndepFun a ℙ`, centred, unit variance (no sub-Gaussian/bounded/moment-of-higher-order). `B_cur : NNReal → Ω' → ℝ` exposed with no measure-equality constraint to Brownian motion. | TC4 weakness comments at lines 542-554 explicitly flag both sites. |
| 3 | Carter-Pollard 2004 universal constants A=0.6, C=1 | Standard form per literature | **VERIFIED — math content** | Carter, A. V. & Pollard, D. (2004) "Tusnády's inequality revisited", *Ann. Statist.* 32, 2731-2741, Theorem 1: `|S_{2n} - n - Z| ≤ 0.6 + Z²/n` for `S_{2n} ~ Bin(2n, 1/2)`, `Z ~ N(0, n/2)` on the comonotonic coupling. Bretagnolle-Massart 1989 *Ann. Probab.* 17 appendix: same bound with looser `A`. | Universal A=0.6, C=1 is the standard sharp form. Mathematical content is the polynomial envelope, not the specific numerical pair (any explicit `(A₀, C₀)` literals work; we adopt the Carter-Pollard pair). |
| 4 | Sub-Gaussian hypothesis API at pin | `ProbabilityTheory.HasSubgaussianMGF X c μ` | **VERIFIED — present** | `Mathlib/Probability/Moments/SubGaussian.lean:606`: `structure HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop`. Namespace `ProbabilityTheory` (lines 129, 934). | `c : ℝ≥0` is the variance proxy (Vershynin 2018 §2.5). For TC5 tightening, we add `_ha_subg : ∀ k, ∃ c : ℝ≥0, ProbabilityTheory.HasSubgaussianMGF (a k) c ℙ` to `hungarian_dyadic_step`. |
| 5 | BM-law constraint encoding for `B_cur` | `B_cur t ~[μ'] gaussianReal 0 (NNReal-of t)` (with `t : NNReal`) | **VERIFIED — gaussianReal present** | `Mathlib/Probability/Distributions/Gaussian/Real.lean:200`: `def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ`. `IsProbabilityMeasure (gaussianReal μ v)` at line 210. | For TC5 tightening, add `_h_B_cur_law : ∀ t : NNReal, μ'.map (B_cur t) = gaussianReal 0 t` (Brownian motion at time `t` has marginal `N(0, t)`). Eliminates degenerate `B_cur ≡ S_cur` witness because `S_cur` is a partial sum (lattice-valued via `μ_B`-pushforward), not Gaussian. |
| 6 | Mills ratio for Gaussian tail at pin | `Real.gaussianMillsRatio` or analogous | **VERIFIED — ABSENT at pin** | Exhaustive grep `MillsRatio\|millsRatio\|mills_ratio\|gaussianMills` over `.lake/packages/mathlib/Mathlib/`: zero hits. Adjacent infrastructure present: `Real.gaussianPDFReal` (`Mathlib/Probability/Distributions/Gaussian/Real.lean:49`), `Real.gaussianPDF` (line 157). | TC5 Priority 2 — provide local `Real.gaussianMillsRatioReal` def + truncation/positivity/monotonicity inequalities. **Note:** Mathlib pin lacks `gaussianCDF` (no def at this pin); we cannot define Mills as `(1 − Φ(x)) / φ(x)` directly without a CDF. Pragmatic alternative: define via the integral `∫_x^∞ φ(t) dt / φ(x)` using `Real.gaussianPDFReal` directly. |
| 7 | Stirling precision at pin (factorial / gamma function) | `Real.Gamma_stirlings_formula` or analogous | **VERIFIED — partial at pin (asymptotic only)** | `Mathlib/Analysis/SpecialFunctions/Stirling.lean` exists with `Stirling.tendsto_stirlingSeq_sqrt_pi`; explicit non-asymptotic upper bound on `n! / (sqrt(2πn) (n/e)^n)` not directly packaged. Re-verified via `find ... -name "Stirling*"` and grep. | TC6 scope — explicit `n! ≤ sqrt(2πn) (n/e)^n exp(1/(12n))` (Robbins 1955) likely needs ~30-50 LOC bridge from asymptotic form. Out of TC5 scope. |
| 8 | Real-Beta function at pin | `Real.Beta` or analogous | **VERIFIED — complex-only at pin** | `Mathlib/Analysis/SpecialFunctions/Complex/Beta.lean` defines `Complex.betaIntegral`; `Real.Beta` real-valued analog not packaged at pin. `Real.GammaIntegral`, `Real.Gamma` present (`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`). | TC6 scope — derive `Real.Beta a b = ∫ x in (0:ℝ)..1, x^(a-1) * (1-x)^(b-1)` via real-valued `Gamma` ratio identity (~20-40 LOC). Out of TC5 scope. |
| 9 | Layer 4 SupError chain consumes tightened signatures | Layer 4 (TC7 scope) signatures import tightened TC5 forms | **VERIFIED — design constraint** | TC4 outcome diagnostic in `TrackCStatus.md` cluster forecast section + this round's brief §"TC4 signature weakness findings". Layer 4 (`sup_error_log_over_sqrt`, `OneDimKMT.lean:627`) takes `B : NNReal → Ω' → ℝ` as a generic Brownian-motion-shaped argument; for the chain `Layer 3 → Layer 4 → oneDimKMT` to compose, `B_cur` from Layer 3 must carry the BM-law marginal (claim 5) or Layer 4 cannot apply Borel-Cantelli I to a meaningful event sequence. | Universal A,C + sub-Gaussian + BM-law are downstream Layer 4 requirements. |
| 10 | TC2 quantile transport infrastructure preserved | `quantile_transform_finite_moment` Full at TC2 commit `7f25b84` | **VERIFIED — TC2 close** | `Helpers/OneDimKMT.lean` Layer 2 (post-TC2 HEAD); used by TC4 T2.1 Path A at lines 434-437 (verbatim). | TC5 must not regress this Full. Signature tightening confined to Layers 3 (`tusnady_base_polynomial`, `hungarian_dyadic_step`); Layer 2 untouched. |

**All 10 rows VERIFIED. T2.1 + T2.2 may proceed.**

## §2 — Verbatim TC3/TC4 signature extraction

### §2.1 `tusnady_base_polynomial` (TC3 lockdown, TC4 Path A body partial)

`Helpers/OneDimKMT.lean:408-416`:

```lean
theorem tusnady_base_polynomial (n : ℕ) (_hn : 1 ≤ n) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (B Z : Ω' → ℝ) (A C : ℝ),
      IsProbabilityMeasure μ' ∧ 0 < A ∧ 0 < C ∧
      Measurable B ∧ Measurable Z ∧
      μ'.map B = (PMF.binomial (1 / 2 : ℝ≥0) (by norm_num) (2 * n)).toMeasure.map
                   (fun (i : Fin (2 * n + 1)) => (i.val : ℝ)) ∧
      μ'.map Z = gaussianReal 0 ((n : ℝ≥0) / 2) ∧
      ∀ ω', |B ω' - (n : ℝ) - Z ω'| ≤ A + C * (Z ω') ^ 2 / (n : ℝ) := by
```

**Weakness W1.** `(A C : ℝ)` quantified existentially: TC4 body chose `A = (n : ℝ) + 1`, `C = 1`. Per-n `A` does NOT compose into a uniform Layer 4 envelope; Carter-Pollard 2004 Theorem 1 gives universal `A = 0.6, C = 1`.

**Tightening plan (TC5 T2.1):** drop `(A C : ℝ)` from the existential, hardcode `0.6` and `1` into the conclusion. The TC4 body's `A = (n : ℝ) + 1, C = 1` choice was a *workaround* for the comonotonic coupling on `Ioc 0 1` (where the trivial `ω' ∉ Ioc 0 1` case had `q_B ω' = q_Z ω' = 0`, so `|0 - n - 0| = n ≤ A` required `A ≥ n`).

**Important workaround consequence:** with universal `A = 0.6`, the TC4 Path A `q_B / q_Z = 0` outside-`Ioc` branch fails (it requires `A ≥ n`, not `A ≥ 0`). Two clean options:

* **Option (a):** restrict `μ'` to `volume.restrict (Ioc 0 1)` (strict probability measure on `Ioc 0 1`), so `ω' ∈ Ioc 0 1` µ'-a.s. and the trivial branch vanishes. The almost-everywhere conclusion replaces `∀ ω'` by `∀ᵐ ω' ∂μ'`. This is the Carter-Pollard form on a probability space.
* **Option (b):** keep `∀ ω'` (pointwise) but acknowledge the universal bound only holds *on the support*; weaken to `∀ᵐ ω' ∂μ'`.

We adopt **Option (a)** in T2.1 — `∀ ω'` becomes `∀ᵐ ω' ∂μ'`. Mathematically equivalent to literature; cleaner for downstream chain.

### §2.2 `hungarian_dyadic_step` (TC3 signature lockdown, body Stub'd)

`Helpers/OneDimKMT.lean:512-555`:

```lean
theorem hungarian_dyadic_step
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha_indep : ProbabilityTheory.iIndepFun a ℙ)
    (_ha_centred : ∀ k, ∫ ω, a k ω ∂ℙ = 0)
    (_ha_var : ∀ k, ProbabilityTheory.variance (a k) ℙ = 1)
    (k : ℕ) (_hk : 1 ≤ k) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S_cur : ℕ → Ω' → ℝ) (B_cur : NNReal → Ω' → ℝ) (A C : ℝ),
      IsProbabilityMeasure μ' ∧ 0 < A ∧ 0 < C ∧
      (∀ t, Measurable (B_cur t)) ∧
      (∀ n, Measurable (S_cur n)) ∧
      μ'.map (S_cur (2 ^ k)) = (ℙ : Measure Ω).map
        (fun ω => ∑ j ∈ Finset.Icc 1 (2 ^ k), a j ω) ∧
      ∀ ω', |S_cur (2 ^ k) ω' - B_cur (2 ^ k : NNReal) ω'| ≤
        A + C * (B_cur (2 ^ k : NNReal) ω') ^ 2 / ((2 ^ k : ℕ) : ℝ) := by
```

**Weakness W2 (two prongs):**

1. *No sub-Gaussian hypothesis on `a`.* `iIndepFun + centred + unit variance` admits e.g. `a k ω = X (suitable heavy-tail)` with `Var = 1` but tails dominating Gaussian; KMT-rate fails.
2. *No BM-law constraint on `B_cur`.* `B_cur` only typed `NNReal → Ω' → ℝ` and required measurable; admits degenerate `B_cur t = S_cur (Nat.floor t)` (constant in `t` between integers, but coercion-cast to make types align), which trivially gives `|S - B| = 0`, useless for Layer 4.

**Tightening plan (TC5 T2.2):**

* (i) Add `(_ha_subg : ∃ c : ℝ≥0, ∀ k, ProbabilityTheory.HasSubgaussianMGF (a k) c ℙ)` (uniform sub-Gaussian variance proxy across `k`).
* (ii) Add `(_h_B_cur_law : ∀ t : NNReal, μ'.map (B_cur t) = gaussianReal 0 t)` to the existential (Brownian-motion-marginal constraint at each time).
* (iii) Tighten `(A C : ℝ)` to universal `0.6, 1` (parallel to T2.1).

After tightening:

```lean
theorem hungarian_dyadic_step
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (_ha_indep : ProbabilityTheory.iIndepFun a ℙ)
    (_ha_centred : ∀ k, ∫ ω, a k ω ∂ℙ = 0)
    (_ha_var : ∀ k, ProbabilityTheory.variance (a k) ℙ = 1)
    (_ha_subg : ∃ c : ℝ≥0, ∀ k, ProbabilityTheory.HasSubgaussianMGF (a k) c ℙ)
    (k : ℕ) (_hk : 1 ≤ k) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (S_cur : ℕ → Ω' → ℝ) (B_cur : NNReal → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
      (∀ t, Measurable (B_cur t)) ∧
      (∀ n, Measurable (S_cur n)) ∧
      μ'.map (S_cur (2 ^ k)) = (ℙ : Measure Ω).map
        (fun ω => ∑ j ∈ Finset.Icc 1 (2 ^ k), a j ω) ∧
      (∀ t : NNReal, μ'.map (B_cur t) = gaussianReal 0 t) ∧
      ∀ᵐ ω' ∂μ', |S_cur (2 ^ k) ω' - B_cur (2 ^ k : NNReal) ω'| ≤
        (0.6 : ℝ) + (1 : ℝ) * (B_cur (2 ^ k : NNReal) ω') ^ 2 / ((2 ^ k : ℕ) : ℝ)
```

(Remarks on `(0.6 : ℝ)` literal: Lean accepts it as a `Real`; in proofs the
literal expands via `OfScientific` to a rational. No additional positivity
hypothesis needed since `0.6 > 0` is `decide`-proved.)

## §3 — Mills ratio infrastructure status

* **Mathlib pin verdict (claim 6):** Mills ratio ABSENT. No `MillsRatio /
  millsRatio / mills_ratio / gaussianMills` decl across all of
  `.lake/packages/mathlib/Mathlib/`. Adjacent: `gaussianPDFReal`,
  `gaussianPDF` present; `gaussianCDF` ABSENT (no `def gaussianCDF` at pin).
* **TC5 T2.3 plan:** define `Real.gaussianMillsRatioReal` locally via the
  integral form `(∫ t in Set.Ioi x, gaussianPDFReal 0 1 t) / gaussianPDFReal 0 1 x`,
  with three lemmas:
  * `gaussianMillsRatioReal_pos : ∀ x, 0 < x → 0 < gaussianMillsRatioReal x` —
    integral strictly positive on `Set.Ioi x` (Gaussian is everywhere positive).
  * `gaussianMillsRatioReal_truncation : ∀ x, 0 < x → gaussianMillsRatioReal x ≤ 1 / x` —
    classical Mills bound (Feller Vol. 2 §VII.1).
  * `gaussianMillsRatioReal_antitone : ∀ x y, 0 < x → x ≤ y → gaussianMillsRatioReal y ≤ gaussianMillsRatioReal x` —
    monotonicity (the *ratio* is decreasing in `x` on `(0, ∞)`; this is the
    standard Mills property used in Carter-Pollard).
* **Honest scope assessment:** the three lemmas above are mostly mechanical
  given `gaussianPDFReal`; the truncation bound (Mills-classical) requires
  integration-by-parts and a tail integral comparison
  (`∫_x^∞ e^{-t²/2} dt ≤ (1/x) e^{-x²/2}`). At Mathlib pin this is feasible
  but non-trivial (`integral_exp_neg_sq_div_le` or analogous: not packaged;
  ~40-80 LOC of Mathlib-style integration manipulation). T2.3 ships the
  `def` + signature TAG'd Stub form (Stub bodies, no `sorry` regression on
  the new defs since they are introductions, not retirements).

## §4 — Internal consistency check (post-R50 discipline rule #4)

* Anchor block: TC5 priority = signature tightening BINDING + Mills infra
  start. Mandatory floor = T1.1 + T2.1 + T2.2 + T2.3 + T2.4. ✓
* Skin-in-the-game caps to **0 pts** if T2.1 OR T2.2 not committed. ✓ (this
  audit confirms both are mechanical signature changes feasible under the
  2-hour micro-budget.)
* Net debt change projection: 18 → 18 (signature tightening preserves
  count; Mills infra adds 3 new TAG'd Stubs which would push to 18 → 21,
  but they are *introductions of new infrastructure* not regressions on
  closures). For TC5 honesty: distinguish "signature changes on existing
  Stubs (no count change)" from "new Mills Stubs (+3)".
* Discipline rule #5 (read in-tree alternates first): the `OneDimKMTSketch.md`
  exploratory doc references upstream KMT routes; no in-tree alternate to
  Tusnády's lemma exists. TC5 path is the only path.

## §5 — Pre-dispatch checklist (rule #7)

* `grep` verifications: claims 1, 2, 4, 5, 6 all backed by file:line.
* `git blame` verifications: TC3 `c96e54b` introduced the locked signatures;
  TC4 `e1abbe5` introduced Path A scaffolding; TC4 `0d2bfe2` left the
  weakness diagnostic comments at lines 542-554.
* `#check` (deferred to T2.1+T2.2 build verification — the tightened
  signature must compile against current `OneDimKMT.lean` imports).
* `leansearch` deferred (Mills ratio confirmed absent via local grep; no
  upstream search needed).

## §6 — Misframing ledger (cumulative T1.1 audit ledger #17)

No new misframing this round. TC5 brief is internally consistent; T1.1
audit confirms the path. (Distinct from R50-T1.1 ledger entry #16, which
caught a chain-level scope mismatch on a different track.)

## §7 — TC5 forecast distribution (recap)

| Outcome | P(Full) | Net Δ on track-c branch |
|---------|---------|-------------------------|
| Upper (T2.1+T2.2+T2.3 Full + Mills lemmas Full) | 0.30 | sorries 18 → 18 (signature changes) + 3 new TAG'd Mills Stubs = 21; or one Mills lemma close → 20 |
| Mid (T2.1+T2.2 Full + Mills `def` only, no lemmas) | 0.45 | sorries 18 → 18 + 3 Mills sub-Stubs = 21 |
| Mid-low (T2.1+T2.2 partial + Mills diagnostic) | 0.20 | sorries 18 → 18 + diagnostic only |
| Lower (T2.1 stalls) | 0.05 | T1.1 ships, T2.x reverts |

**T1.1 close.** T2.1 may proceed.
