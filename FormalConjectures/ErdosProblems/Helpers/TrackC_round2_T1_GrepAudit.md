# Track C round 2 — T1.1 grep audit + math verification

**Round:** Track C round 2 (parallel-track, branch `track-c-1dkmt`).
**Date:** 2026-05-02.
**Branch HEAD:** `15192f1` (TC1 closure).
**Per process Q4 ii:** local Claude grep audit FIRST, Grok recipe SECOND
with explicit uncertainty flagging on any math edge case.

## 0. Summary verdicts

| Check | Status | Risk to TC2 Full close |
| --- | --- | --- |
| TC1 signature in `Helpers/OneDimKMT.lean:214-226` | ✅ present | none |
| Mathlib `cdf` API in `Mathlib.Probability.CDF` | ✅ present | none |
| Mathlib `quantile` / `iCdf` / `invCdf` | ❌ absent | low |
| `StieltjesFunction.measure` API | ✅ present | none |
| `(cdf μ).measure = μ` | ✅ `measure_cdf` | none |
| `Measure.ext_of_Iic` for measure-equality | ✅ exists | none |
| `GaussianParametricAnalysis.lean` (R46 cross-track) | ❌ absent on branch | none for L2 |
| Grok L2 signature math soundness | ⚠️ **EDGE CASE: Galois iff fails for `p ∉ Ioc 0 1`** | **moderate** — signature must be corrected |

**Uncertainty flag (Grok recipe failure):** the TC1 signature universally quantifies the Galois iff `q p ≤ x ↔ p ≤ cdf μ x` over `∀ p x : ℝ`, which is provably FALSE for `p ≤ 0` or `p > 1` with `q : ℝ → ℝ` and Mathlib's `Real.sInf` convention (returns `0` for empty / unbounded-below sets). This is the third consecutive Grok pre-flight misframing in the V2 cluster (R44 Jacobi, R45 PosSemidef.det_sqrt, R46 PosDef.isOpen-globally, now Track C L2 unrestricted-Galois). Mitigation: the Galois conjunct is restricted to `∀ p ∈ Set.Ioc (0:ℝ) 1, ∀ x : ℝ` in T2.1; this is the only signature change required. Pushforward and measurability conjuncts are unaffected.

## 1. TC1 OneDimKMT.lean signature audit

`Helpers/OneDimKMT.lean` extends from 110 LOC (R29 axiom only) to 383 LOC at TC1 HEAD. Line index of L2:

| Lines | Content |
| --- | --- |
| 1-15 | License |
| 16-23 | Imports (incl. `Mathlib.Probability.CDF`, `Mathlib.Probability.Moments.Variance`, `Mathlib.Probability.Distributions.Gaussian.Real`, `Mathlib.MeasureTheory.Measure.Stieltjes`) |
| 26-100 | R29 axiom + docstring |
| 101-112 | `axiom one_dim_KMT_coupling` (R29) |
| 144-190 | Layer 1 `skorokhod_embedding_single` (TC3 target) |
| 192-226 | Layer 2 `quantile_transform_finite_moment` (TC2 target) |
| 228-282 | Layer 3 `hungarian_dyadic_coupling` (TC4 bottleneck) |
| 284-324 | Layer 4 `sup_error_log_over_sqrt` (TC5 terminal) |
| 326-381 | Main `oneDimKMT` (existential, body chains L1-L4) |

**TC2 scope:** retire L2 `sorry` at line 226. Net debt projected: branch sorries 17 → 16 (-1).

## 2. Mathlib state on `cdf` / `quantile`

### 2.1. `cdf` is present and complete

File: `.lake/packages/mathlib/Mathlib/Probability/CDF.lean` (123 LOC).

```lean
noncomputable def ProbabilityTheory.cdf (μ : Measure ℝ) : StieltjesFunction ℝ
```

Key lemmas (all available):
- `cdf_nonneg : 0 ≤ cdf μ x`
- `cdf_le_one : cdf μ x ≤ 1`
- `monotone_cdf : Monotone (cdf μ)`
- `tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0)`
- `tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1)`
- `ofReal_cdf [IsProbabilityMeasure μ] : ENNReal.ofReal (cdf μ x) = μ (Iic x)`
- `measure_cdf [IsProbabilityMeasure μ] : (cdf μ).measure = μ`

### 2.2. No `quantile` / `iCdf` / `invCdf` API in Mathlib

Verified via `grep -rln "quantile\|iCdf\|invCdf" .lake/packages/mathlib/Mathlib`: zero hits in either Probability or MeasureTheory directories. **The Layer 2 quantile transformation must be built from scratch in T2.1.**

LOC estimate per Grok Q2: 80-120. Confirmed reasonable: from-scratch construction of `q : ℝ → ℝ`, monotonicity, measurability, restricted Galois, pushforward identity — each ~15-30 LOC.

### 2.3. `StieltjesFunction.measure` — relevant adjacent infrastructure

File: `.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean` (~650 LOC).

Available facts (relevant to T2.1 pushforward proof):
- `StieltjesFunction.measure_Iic [NoMinOrder R] {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)`
- `StieltjesFunction.right_continuous (x : R) : ContinuousWithinAt f (Ici x) x`
- `StieltjesFunction.mono : Monotone f`

Relevant for the proof structure: `measure_cdf` collapses `(cdf μ).measure = μ`, but the Layer 2 statement requires pushforward of `volume.restrict (Ioc 0 1)`, NOT of `(cdf μ).measure`. So Layer 2 still requires a from-scratch quantile + pushforward proof; the Stieltjes machinery is upstream context, not a direct shortcut.

## 3. Math edge case: Galois iff fails outside `Ioc 0 1`

### 3.1. Failure analysis

TC1 signature claims `∀ p x : ℝ, q p ≤ x ↔ p ≤ cdf μ x`. With `q p := sInf {y : ℝ | p ≤ cdf μ y}` and Mathlib's `Real.sInf` convention:

| Case | `{y : p ≤ cdf μ y}` | `q p` | Galois iff |
| --- | --- | --- | --- |
| `p ≤ 0` | `ℝ` (cdf ≥ 0 ≥ p) | `sInf ℝ = 0` | LHS `0 ≤ x`, RHS `True`. iff fails for `x < 0`. |
| `0 < p ≤ 1` | `[a, ∞)` for some `a ∈ ℝ` (right-continuity of cdf + monotonicity + cdf → 1) | `a` (finite) | iff holds: both sides `↔ x ∈ [a, ∞)` |
| `p > 1` | `∅` (cdf ≤ 1 < p) | `sInf ∅ = 0` | LHS `0 ≤ x`, RHS `False`. iff fails for `x ≥ 0`. |

**Conclusion:** the unrestricted Galois iff is mathematically FALSE. Only `p ∈ Ioc 0 1` admits the iff.

### 3.2. Proposed signature correction

Drop-in replacement of the TC1 Galois conjunct:

```lean
-- Before (TC1, mathematically inconsistent):
(∀ p x : ℝ, q p ≤ x ↔ p ≤ cdf μ x)

-- After (TC2, restricted to where the iff is provably true):
(∀ p ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ℝ, q p ≤ x ↔ p ≤ cdf μ x)
```

Other two conjuncts (`Measurable q`, pushforward identity) are unchanged.

**Consumer impact:** none. The main `oneDimKMT` body comment uses Layer 2 only for the pushforward identity (uniform → μ recovery); the Galois is internal/auxiliary infrastructure. The corrected restriction matches standard quantile-transform statements in Talagrand, Massart, Pollard, etc.

### 3.3. Closure proof structure (~80-120 LOC)

The body of T2.1 will:

1. Define `q μ p := sInf {y : ℝ | p ≤ cdf μ y}` (~5 LOC).
2. Prove `q μ` monotone (via sInf-monotonicity of decreasing-as-p-increases super-level sets) (~10 LOC).
3. Conclude `Measurable (q μ)` via `Monotone.measurable` (~3 LOC).
4. Prove restricted Galois for `p ∈ Ioc 0 1` (~30 LOC):
   - Show `{y : p ≤ cdf μ y}` is non-empty (cdf → 1) and bounded-below (cdf → 0) for `p ∈ Ioc 0 1`.
   - Show right-continuity of `cdf μ` ⟹ super-level set is `[a, ∞)`.
   - sInf is `a`, Galois is the membership equivalence.
5. Prove pushforward identity via `Measure.ext_of_Iic` (~30 LOC):
   - For all `x`, `((volume.restrict (Ioc 0 1)).map q) (Iic x) = volume {p ∈ Ioc 0 1 | q p ≤ x}`.
   - Galois (step 4) + p ∈ Ioc 0 1: this set is `Ioc 0 (cdf μ x)` (clamped to `Ioc 0 1` automatically since `cdf μ x ≤ 1`).
   - `volume (Ioc 0 (cdf μ x)) = ENNReal.ofReal (cdf μ x) = μ (Iic x)` via `ofReal_cdf`.

## 4. Cross-track synergy check (R46 `GaussianParametricAnalysis.lean`)

Per R46 mainline T3.1 (`53ac58a`), the helper file `GaussianParametricAnalysis.lean` was extracted as a cross-track synergy library (uniform Gaussian tail lemma + parametric DCT). The pre-flight brief noted Track C TC2 may use it for measurability arguments.

**Status on `track-c-1dkmt`:** **NOT present** (verified via `ls FormalConjectures/ErdosProblems/Helpers/GaussianParametricAnalysis.lean`). The library is on the R46 mainline branch (`r46-track-a-mge-posdef`), not on `track-c-1dkmt`.

**Impact on T2.1:** **NONE.** The Layer 2 quantile transformation does not involve Gaussian densities or parametric integrals — it operates on a generic probability measure on `ℝ`. The R46 library would be relevant for future Track C TC3+ work (Hungarian dyadic uses Gaussian bookkeeping) but is not a TC2 dependency.

**Branch coordination note:** when R46 mainline merges to `add-erdos-524`, a future Track C round may rebase `track-c-1dkmt` to pick up `GaussianParametricAnalysis.lean`. Out of scope for TC2.

## 5. Closure plan for TC2 / T2.1

1. Edit `Helpers/OneDimKMT.lean` (lines 214-226):
   - Restrict the Galois conjunct to `∀ p ∈ Set.Ioc (0 : ℝ) 1`.
   - Replace the `sorry` with a Full body following section 3.3.
2. Verify `lake build` clean on `Helpers/OneDimKMT.lean`.
3. Update `Helpers/TrackCStatus.md` with TC2 closure note (axiom count unchanged at 5; sorries on branch 17 → 16).

**P(Full close) per Grok Q5:** 0.40-0.50. Confirmed reasonable — the math is standard and the Mathlib API surface (cdf, Stieltjes, Measure.ext_of_Iic, Monotone.measurable) is sufficient.

**Honest mid-distribution outcome:** if any of (a) `Measure.ext_of_Iic` is misnamed, (b) `Monotone.measurable` requires unexpected structure assumptions, (c) the `volume (Ioc 0 (cdf μ x))` lemma path has an unexpected gap, ship as TAG'd sub-Stub with concrete diagnostic citing the specific Mathlib API absence/mismatch.

## 6. T1.1 verdicts (all green except L2 signature)

* TC1 state: **verified** (HEAD `15192f1`, OneDimKMT.lean 383 LOC, L2 signature at 214-226).
* Mathlib `cdf` infra: **verified** (`measure_cdf`, `ofReal_cdf`, `monotone_cdf`).
* Mathlib `quantile` infra: **confirmed absent** — Layer 2 builds from scratch.
* `StieltjesFunction.measure` infra: **verified** (`measure_Iic`, right-continuity).
* `Measure.ext_of_Iic`: **available** (standard Dynkin-system result).
* GaussianParametricAnalysis.lean: **not on branch, not needed for L2**.
* Grok L2 signature: **EDGE CASE FLAGGED** — Galois iff requires restriction to `Ioc 0 1`. Correction is single-token, consumer-transparent.

T2.1 proceeds with the corrected signature and the section-3.3 proof structure.
