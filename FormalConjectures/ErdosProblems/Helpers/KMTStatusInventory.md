# KMT Scaffolding Inventory (Calibration Pass)

**Out-of-band, read-only.** Goal: produce a calibrated baseline for
`two_dim_KMT_coupling` retirement so R24+ planning is data-grounded.
Pass conducted 2026-04-30 against current `r23-finish` HEAD
(post-R22; `mathlib @ 25ce63313608`, `brownian-motion @ 91267abd71bd`,
`kolmogorov_extension4 @ 2c2b44e55251`).

## 1. Existing artifacts inventory

### 1a. Project `.lean` references (all comment / consumer-side; no
KMT-formalization code)

| File | Line | Kind | Status |
|---|---|---|---|
| `524.lean` | 3741 | `axiom two_dim_KMT_coupling` | **stated (axiom)** |
| `524.lean` | 3925, 4080, 4228 | three call sites of the axiom | consumers |
| `Helpers/GLWUpperProof.lean` | 55, 249–276 | `obtain ⟨Yplus, …⟩ := two_dim_KMT_coupling …`; `BLOCKER` comments around `IsGLWProcess Yplus` | consumer |
| `Helpers/GLWLowerProof.lean` | 26, 291–333 | mirror consumer (`Yminus`) | consumer |
| `Helpers/CubicSubseqAsymptotics.lean` | 471 | `kmt_error_negligible_at_loglog_cube_root` — asymptotic of error rate `log(log n / √n)` | **theorem (Full)** — error-rate consumer; **does not formalize KMT itself** |
| `Helpers/MultivariateSmallBallUpper.lean:28`, `CharFunCrossBlock.lean:25`, `CauchyDetLowerBound.lean:25` | comment refs | "no-Gaussian / no-KMT path" — replacement strategy notes | ambiguous (commentary) |

**No `.lean` file in the project contains a KMT theorem
signature, statement, skeleton, or partial proof.** The only KMT-shaped
Lean object in the entire toolchain is the `axiom` in `524.lean:3741`.

### 1b. Upstream packages

| Location | Hit | Verdict |
|---|---|---|
| `.lake/packages/brownian-motion/BrownianMotion/StochasticIntegral/Komlos.lean` | `komlos_convex`, `komlos_norm`, `komlos_ennreal` | **L¹-convex Komlós lemma**, NOT the KMT coupling. Used in `DoobMeyer.lean` for martingale uniform-integrability. Easy to misread by name. |
| `.lake/packages/brownian-motion/BrownianMotion/**` | `KMT`, `Tusnady`, `Skorokhod`, `strongInvariance`, `Donsker` | **zero hits.** Library is Gaussian-process / KC-continuity / stoch-integral focused. |
| `.lake/packages/mathlib/Mathlib/Probability/**` | same set | **zero hits.** Closest infra: `SubGaussian.lean` (log-MGF + Chernoff), `Process/Stopping.lean`, `StrongLaw.lean` (only WLLN/SLLN). |

## 2. Document inventory

* `Helpers/OneDimKMTSketch.md` — **165 lines, R17 deliverable.**
  Paper sketch only (no Lean code). Three proof routes (Skorokhod
  embedding / direct quantile / Tusnády-dyadic). Recommends route 3
  (~800 LOC). Verdict: "exploratory; full proof at least a 6-month
  engagement". Hypothetical Mathlib import map included.
* `Helpers/TwoDimKMTRetirement.md` — **171 lines, R14 originator,
  R17 re-scan.** Status doc tracking the axiom's retirement
  posture as Stub across R14→R17. Documents the **Letwin–Sawhney
  reduction** (arXiv:2604.19294 Lemma 4.7): 2D KMT = two
  independent 1D KMTs + triangle inequality, **30–50 LOC** once 1D
  KMT exists upstream.
* `Helpers/SubGaussianMomentScoping.md` — **102 lines, R17 T8.2
  Stub.** Scopes the sub-Gaussian Mathlib gaps (no
  bounded→subGauss instance, no Bernstein, no clean iid-sum
  corollary). Estimates 1300 LOC across 6 sub-PRs for the
  Skorokhod / Tusnády route to land 1D KMT upstream + the 2D
  coupling.

R17 attempted to either advance KMT or close the door on it; landed
both at Stub posture and produced these three docs as the R-round
output. **No subsequent round (R18–R22) has touched KMT.**

## 3. Skorokhod embedding state

* **Mathlib:** there is NO Skorokhod embedding theorem. The names
  matching `Skorokhod` in Mathlib refer to the unrelated
  measure-theoretic *Skorokhod representation* (Polish-space random
  variable construction), not the embedding of random walks into
  Brownian motion. Confirmed by `find` + grep across
  `Mathlib/Probability`.
* **brownian-motion:** stopping-time machinery exists
  (`StochasticIntegral/OptionalSampling.lean`,
  `LocalMartingale.lean`) and is used for stochastic integration.
  But there is no Skorokhod embedding (no construction of
  `τ_n : Ω → ℝ≥0` such that `B_{τ_n}` matches the law of `S_n`).
* **Strong invariance / Donsker:** zero hits in either package.
* **Stochastic-process coupling lemmas:** none beyond projective-limit
  consistency (Kolmogorov extension).

**Verdict: 0% Skorokhod / strong-invariance infrastructure
upstream**, exactly as the R17 docs report. No advance since R16.

## 4. Axiom statement (`524.lean:3741`)

```lean
axiom two_dim_KMT_coupling :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∃ (Yplus Yminus : ℝ → Ω → ℝ) (Δ : ℕ → ℝ),
        (∀ u, Measurable (Yplus u)) ∧ (∀ u, Measurable (Yminus u)) ∧
        (∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
          |((1 : ℝ) / Real.sqrt n) *
              (∑ k ∈ Finset.Icc 1 n, a k ω * Real.exp (-u * k / n)) -
            Yplus u ω| ≤ Δ n) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
          |((1 : ℝ) / Real.sqrt n) *
              (∑ k ∈ Finset.Icc 1 n, a k ω * (-Real.exp (-u / n)) ^ k) -
            Yminus u ω| ≤ Δ n) ∧
        ProbabilityTheory.IndepFun
          (fun ω : Ω => fun u : ℝ => Yplus u ω)
          (fun ω : Ω => fun u : ℝ => Yminus u ω) ℙ ∧
        (∀ ω, Continuous (fun u : ℝ => Yplus u ω)) ∧
        (∀ ω, Continuous (fun u : ℝ => Yminus u ω)) ∧
        (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yplus u ω| ≤ ε) ∧
        (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Yminus u ω| ≤ ε)
```

**Nine conjuncts.** Inhabiting it requires (i) constructing two
independent Itô-integral processes `Y±(u) = ∫₀¹ (±e^{-us}) dB±(s)`
on an enriched space carrying Brownian motions `B±`; (ii) proving
the coupling bound `|Z^±_n − Y^±| ≤ log(n+1)/√n` uniformly in
`u ≥ 0` and `ω` — the load-bearing 1D-KMT-applied-twice content;
(iii) sample-path continuity + tail decay (these flow from
brownian-motion's KC infrastructure once the Itô construction is
in place).

## 5. Honest gap-and-effort estimate

| Axis | Available now | Missing |
|---|---|---|
| 1D KMT statement | — | not in mathlib, not in brownian-motion |
| 1D KMT proof | — | 0% (any of 3 routes) |
| Skorokhod embedding (random walks → BM) | — | 0% |
| Strong invariance principle | — | 0% (Donsker also 0%) |
| Stopping-time martingale moment bounds | partial in BM library | quantitative tail control gap |
| Sub-Gaussian theory needed by Tusnády / Skorokhod | partial (`SubGaussian.lean` log-MGF + Chernoff) | bounded→subGauss instance, iid-sum corollary, Bernstein |
| Tusnády's lemma | — | 0% |
| Edgeworth / Berry-Esseen | — | 0% |
| Itô integral against a deterministic L² kernel (the Y± construction) | partial in BM library (`StochasticIntegral/`) | needs L²-kernel specialization |
| 2D-from-1D LS reduction | — | **30–50 LOC, but gated on 1D KMT** |
| Error-rate asymptotic absorption (`kmt_error_negligible_at_loglog_cube_root`) | **Full** | — |

**LOC estimate to retire `two_dim_KMT_coupling` Full:** ~1100–1500
LOC (per `SubGaussianMomentScoping.md`'s 6-sub-PR breakdown).
Dominant cost: 1D KMT itself (Tusnády route ≈ 800 LOC of new
infra; Skorokhod route ≈ 1000–1500 LOC).

**Major missing pieces (in order of structural depth):**
1. 1D KMT: 0%. Load-bearing.
2. Skorokhod embedding: 0%. Needed for one of the 1D-KMT routes.
3. Tusnády's lemma + Edgeworth-style binomial-Gaussian
   approximation: 0%. Needed for the other 1D-KMT route.
4. Sub-Gaussian iid-sum & bounded-implies-subGauss bridges: missing.
5. The 2D-from-1D LS reduction (~30–50 LOC) — trivial **once 1D
   exists**.

**Weakened axiom (Option D):** the downstream consumer in
`polynomial_sup_small_ball_{upper,lower}` absorbs the error rate
through `kmt_error_negligible_at_loglog_cube_root`. The axiom could
be weakened from `Δ_n ≤ log(n+1)/√n` to `Δ_n = O(n^{-α})` for any
fixed `α > 0` and the cubic-subseq downstream proof would still
go through (the absorption is super-polynomial). LOC delta: marginal
(~5–10%). The bottleneck is the *coupling existence*, not the rate.
**A weakened axiom is not a structural shortcut.**

**Sub-axiom approach (Option C):** factor the 9-conjunct axiom into
- `axiom one_dim_KMT_coupling` — single 1D coupling statement
  (Komlós–Major–Tusnády 1975, peer-reviewed for 50 years), and
- `theorem two_dim_KMT_coupling : … := by …` — proved from the 1D
  axiom via two applications + independence + sample-path
  regularity.

Per `TwoDimKMTRetirement.md:84-92`, the LS-reduction body is **30–50
LOC**. Sample-path regularity (continuity + tail) is recoverable
from `brownian-motion`'s KC infrastructure and the existing R22
patterns in `GLWGaussianProjectiveLimit.lean`. **Total LOC: ~50–150,
spread over 1–3 sub-PRs.** Structurally feasible; the 1D KMT axiom
is mathematically lighter than the 2D form (one peer-reviewed 1975
result vs a Chojecki-specific 2D refinement) and matches the standard
expositional posture of the field.

## 6. Round-count calibration

Rate assumption: ~200–400 LOC nets / round at ~60% manifest
realisation → ~120–240 effective LOC / round. Novel-formalization
overhead (cross-cutting Mathlib API gaps, blueprint-style
infrastructure) typically adds ~30–40% rework.

| Option | LOC | Rounds (realistic) | Notes |
|---|---|---|---|
| **A — Full upstream-quality KMT** | 1300–1500 | **15–25** | Cowork's existing estimate is in this range. Includes Tusnády or Skorokhod, all sub-Gaussian fixes, the 2D coupling. |
| **B — KMT specialised for 524.lean (Rademacher only)** | 1100–1300 | **12–22** | Saves ~10–15% by skipping general sub-Gaussian → Rademacher specialisation; ditto for Tusnády (Bin(n,1/2) is exactly the Rademacher target). Same order as A. |
| **C — Sub-axiom decomposition (`one_dim_KMT_coupling` axiom + 2D theorem)** | **50–150** | **2–3** | LS reduction body is documented (`TwoDimKMTRetirement.md:84`). Splits one 9-conjunct axiom into (a) a peer-reviewed 1D axiom (mathematical content unchanged from Option A's gap, but cleanly factored) + (b) a theorem. **Strictly improves auditability** at zero formalization cost beyond the bridge. |
| **D — Weakened-axiom rate** | 1050–1450 | 12–22 | Saves negligible LOC since the bottleneck is the coupling theorem, not the error rate. Not recommended unless the bridge for the weakened consumer is also being touched. |

**Conclusion.** Cowork's "15–30 rounds" estimate is calibrated
correctly **for Option A**, but **Option C is 5–10× cheaper** at the
cost of leaving 1D KMT as a separately-stated axiom (no
mathematical-content change vs the status quo, but improves
factoring). If retirement of the *literal* `two_dim_KMT_coupling`
axiom is the goal (without committing to upstream 1D KMT), **Option C
in 2–3 rounds is the structurally cheapest path** and is **already
fully documented** — the LS reduction body lives in
`TwoDimKMTRetirement.md:84-92` and just needs a Lean transcription.

## Cross-references

- `OneDimKMTSketch.md` — 1D KMT proof routes (R17).
- `TwoDimKMTRetirement.md` — 2D-from-1D LS reduction body
  (R14→R17, Stub).
- `SubGaussianMomentScoping.md` — Mathlib sub-Gaussian gaps for
  the Tusnády / Skorokhod routes (R17 T8.2).
- `R17ReadinessDiagnostic.md` Tier 5 — long-term roadmap entry.
- `524.lean:3656-3740` — extensive in-source axiom doc-comment with
  retirement strategy and 4-step LS roadmap.
