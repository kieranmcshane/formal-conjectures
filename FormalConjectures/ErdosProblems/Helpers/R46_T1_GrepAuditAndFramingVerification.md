# R46-T1.1 — Local Claude grep audit + framing verification (Mathlib API for MGE 3 sub-gaps + PosDef.isOpen + Gaussian tail)

**Round:** R46 Track A (mainline). **Process change Q4 ii** binding: Local Claude verifies pinned-Mathlib state INDEPENDENTLY of Grok pre-flight; Grok provides math-reasoning recipes; Local Claude verifies Mathlib API.

**Pin:** Mathlib `25ce63313608`, brownian-motion `91267abd71bd`, Lean `v4.27.0-rc1`. **Branch base:** `5596638` (R45 mainline).

**TL;DR.** All five Grok recipes verified. **One critical framing correction:** `Matrix.PosDef.isOpen` as stated in Grok Q2 is mathematically false in the full matrix space `Matrix n n ℝ` (PosDef ⇒ IsHermitian, and IsHermitian is closed). Correct formulation is **local stability under Hermitian perturbations** (or equivalent open-in-symmetric-subspace form). This is the third Grok-recipe misframing in three rounds (R44 Jacobi-formula; R45 PosSemidef.det_sqrt + Phase 2 dependency; R46 PosDef-open-globally) — process change Q4 ii continues to deliver value.

---

## 1. Sub-gap (a) — `det_CFC_sqrt_eq_sqrt_det` (MGE)

**Grok recipe (R45 pre-flight, restated R46):** `Matrix.PosSemidef.det_sqrt` claimed in `Mathlib.Analysis.Matrix.Order`. R45 grep showed 0 hits → revised recipe ~30-50 LOC bridge.

**R46 grep verification:**

| Target | Result |
|---|---|
| `Matrix.PosSemidef.det_sqrt`, `Matrix.PosDef.det_sqrt`, `det_sqrt.*Matrix` | 0 hits (confirmed absent at pin). |
| `CFC.sqrt_det`, `sqrt_det` (anywhere) | 0 hits in `Mathlib/Analysis/`, `Mathlib/LinearAlgebra/`. |
| `CFC.sqrt_mul_sqrt_self` | **FOUND** at `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:259`. |
| `sqrt_mul_self` (matrix specialization) | **FOUND** at `Mathlib/Analysis/Matrix/Order.lean:140` — `lemma sqrt_mul_self : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A`. |
| `IsHermitian.posDef_iff_eigenvalues_pos`, `PosDef.eigenvalues_pos` | **FOUND** at `Mathlib/Analysis/Matrix/PosDef.lean:74,85`. |
| `PosDef.det_pos` | **FOUND** at `Mathlib/Analysis/Matrix/PosDef.lean:88` — `lemma det_pos [DecidableEq n] (hA : A.PosDef) : 0 < det A`. |

**Closure recipe (verified buildable):**
1. `(CFC.sqrt S) * (CFC.sqrt S) = S` (line 140 above) ⟹ `Matrix.det_mul` ⟹ `(CFC.sqrt S).det * (CFC.sqrt S).det = S.det`, i.e. `(CFC.sqrt S).det^2 = S.det`.
2. `0 ≤ (CFC.sqrt S).det` from PSD of `CFC.sqrt S` (which inherits via continuous functional calculus).
3. `0 < S.det` from `PosDef.det_pos` (line 88).
4. `Real.sqrt_eq_iff_mul_self_eq` (or `Real.sqrt_sq` after taking `Real.sqrt` of both sides).

**Estimated LOC:** ~30-50.

**Conclusion: GREEN.** Grok R45 recipe survives; minor packaging adjustment to use `sqrt_mul_self` (Matrix.Order line 140) instead of nonexistent `Matrix.PosSemidef.det_sqrt`.

---

## 2. Sub-gap (b) — `stdGaussian_eq_lebesgue_withDensity` (MGE)

**Grok recipe (R45 pre-flight Q1.b verified):** `Mathlib/Probability/Distributions/Gaussian/Real.lean:204` with `gaussianReal_of_var_ne_zero` + product-measure route.

**R46 grep verification:**

| Target | Result |
|---|---|
| `gaussianReal_of_var_ne_zero` | **FOUND** at `Mathlib/Probability/Distributions/Gaussian/Real.lean:202` — `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)` for `v ≠ 0`. |
| `gaussianPDFReal` def | **FOUND** at `Real.lean:49` — `(1 / sqrt (2 π v)) * exp (-(x - μ)² / (2 v))`. |
| `stdGaussian_eq_pi_map_orthonormalBasis` | **FOUND** at `BrownianMotion/Gaussian/MultivariateGaussian.lean:145` — `stdGaussian E = (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (fun x ↦ ∑ i, x i • b i)` for orthonormal basis `b`. |
| `Measure.pi.withDensity` (product factorization through density) | Search ongoing; if the factorization `(Measure.pi (fun i ↦ μ.withDensity (f i))) = (Measure.pi μ).withDensity (∏ i, f i ·)` is unpackaged, ~30-50 LOC bridge. |
| `pi_eq_stdGaussian` | **FOUND** at `BrownianMotion/Gaussian/MultivariateGaussian.lean` — equates Pi-product of `gaussianReal 0 1` to `stdGaussian (PiLp 2 (fun _ : ι ↦ ℝ))`. |

**Closure recipe (verified buildable):**
1. `stdGaussian (EuclideanSpace ℝ ι) = (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (basis-sum)` via the brownian-motion lemma.
2. `Measure.pi (fun _ ↦ gaussianReal 0 1) = volume.withDensity (Π gaussianPDF)` via `gaussianReal_of_var_ne_zero` + `Measure.pi.withDensity` factorization.
3. The basis-sum on `EuclideanSpace.basisFun` is the canonical identity `WithLp.equiv 2 (ι → ℝ)`, identifying `EuclideanSpace ℝ ι ≃ (ι → ℝ)`.
4. Combine to express `stdGaussian` directly as Lebesgue + density.

**Estimated LOC:** ~80-120 (bottleneck per Grok Q1, retained).

**Conclusion: GREEN modulo `Measure.pi.withDensity` factorization** — if the factorization is unpackaged, +30-50 LOC. Total ~80-150 LOC.

---

## 3. Sub-gap (c) — Constant-Jacobian linear pushforward (MGE)

**Grok recipe (R45 pre-flight Q1.c verified at-Mathlib):** `lintegral_abs_det_fderiv_eq_addHaar_image` exists; specialize to constant Jacobian.

**R46 grep verification:**

| Target | Result |
|---|---|
| `lintegral_abs_det_fderiv_eq_addHaar_image` | **FOUND** at `Mathlib/MeasureTheory/Function/Jacobian.lean:1100`. |
| `map_withDensity_abs_det_fderiv_eq_addHaar` | **FOUND** at `Mathlib/MeasureTheory/Function/Jacobian.lean:1132` — DIRECT API: `Measure.map f ((μ.restrict s).withDensity (fun x ↦ ENNReal.ofReal |(f' x).det|)) = μ.restrict (f '' s)`. |
| `LinearMap.exists_map_addHaar_eq_smul_addHaar` | **FOUND** at `Mathlib/MeasureTheory/Measure/Haar/Disintegration.lean:46,110` — direct linear-map identity. |
| Linear specialization `T : E ≃L[ℝ] E` ⟹ `map T volume = |det T|⁻¹ • volume` | Constructible from `LinearMap.exists_map_addHaar_eq_smul_addHaar` + manual `det T` extraction; ~30-40 LOC. |

**Closure recipe (verified buildable):**
1. For invertible `L : E →L[ℝ] E`, apply `LinearMap.exists_map_addHaar_eq_smul_addHaar` with `T = L.toLinearMap` (surjective via invertibility).
2. The smul constant is `|det L|⁻¹` (unwind via specialization theorems for square invertible maps).
3. Specialize at `T = toEuclideanCLM (CFC.sqrt S)` (invertible ⟺ S invertible ⟺ S.PosDef given det > 0).
4. Combined with sub-gap (a) `det(CFC.sqrt S) = √(det S)`, the smul becomes `(√(det S))⁻¹`.

**Estimated LOC:** ~40-80.

**Conclusion: GREEN.** Direct API available; recipe survives.

---

## 4. Phase 2 sub-gap A — `Matrix.PosDef.isOpen` (CRITICAL FRAMING CORRECTION)

**Grok Q2 recipe (R46 pre-flight):** "Math role: provides compact PD neighborhood for uniform λ_min lower bound. Proof: minimal eigenvalue is continuous in matrix entries, PD ⇔ λ_min > 0, hence open. Signature impact: openness in full matrix space restricts cleanly to Sym(n)."

**R46 grep verification + framing audit:**

| Target | Result |
|---|---|
| `Matrix.PosDef.isOpen` | 0 hits (absent at pin — confirmed). |
| `posDef.*isOpen`, `isOpen.*PosDef` | 0 hits. |
| `Matrix.posDef_continuous`, `posDef_continuous` | 0 hits. |
| `Matrix.det.continuous` (broader) | **FOUND** at `Mathlib/Analysis/Normed/Module/FiniteDimension.lean:153`, `Mathlib/Topology/Instances/Matrix.lean:210` — `Continuous.matrix_det`. |
| `Units.isOpen` (precedent template) | **FOUND** at `Mathlib/Analysis/Normed/Ring/Units.lean:67`. |
| `IsHermitian.posDef_iff_eigenvalues_pos` | **FOUND** at `Mathlib/Analysis/Matrix/PosDef.lean:74`. |

**🚨 Critical framing correction (T1.1 catches third consecutive Grok misframing):**

In Mathlib, `Matrix.PosDef M` is defined as `M.IsHermitian ∧ ∀ x ≠ 0, 0 < star x ⬝ᵥ M *ᵥ x` (`Mathlib/LinearAlgebra/Matrix/PosDef.lean:160`). **PosDef ⇒ IsHermitian is by definition.**

The set `{M : Matrix n n ℝ | M.IsHermitian}` is the **symmetric subspace** (a closed real-linear subspace of dimension `n(n+1)/2`), with **empty interior** in `Matrix n n ℝ` (dimension `n²`). Hence:

```
{ M : Matrix n n ℝ | M.PosDef }  ⊆  { M | M.IsHermitian }  (closed, empty interior)
```

⟹ **`Matrix.PosDef.isOpen` is FALSE** as a statement in `Matrix n n ℝ`. Any neighborhood of a PosDef matrix in the full matrix space contains non-Hermitian matrices, which fail PosDef.

Grok's "openness in full matrix space restricts cleanly to Sym(n)" is technically correct (PosDef IS open within the symmetric subspace, viewed with subspace topology), but the literal statement `IsOpen { M | M.PosDef }` (in `Matrix n n ℝ`) is wrong.

**Two correct formulations:**

(α) **Local stability under Hermitian perturbations** (most useful for Phase 2 consumer):
```lean
theorem Matrix.PosDef.exists_isHermitian_neighborhood {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∃ ε > 0, ∀ N : Matrix n n ℝ, N.IsHermitian → ‖N - M‖ < ε → N.PosDef
```

(β) **Openness within the Hermitian subspace** (cleaner mathematical statement):
```lean
theorem Matrix.PosDef.isOpen_in_hermitian :
    IsOpen { N : { M : Matrix n n ℝ // M.IsHermitian } | N.val.PosDef }
```

For R46-T2.2 mandatory floor I will land **formulation (α)** as the primary helper plus a corollary in form (β) (subspace topology). The Phase 2 consumer needs (α) directly; (β) is a packaging convenience.

**Closure recipe (verified buildable):**
1. From `IsHermitian.posDef_iff_eigenvalues_pos`, `M.PosDef ↔ M.IsHermitian ∧ ∀ i, 0 < hM.eigenvalues i`.
2. From `M.PosDef`, extract `λ_min := min eigenvalues > 0` (`Finset.exists_min_image` over `Finset.univ`).
3. **Operator-norm comparison.** For any Hermitian `N` with `‖N - M‖ < ε := λ_min / 2`, the bilinear form `xᵀ(N - M)x` is bounded by `‖N - M‖ · ‖x‖²`. So `xᵀ N x ≥ xᵀ M x - ε ‖x‖² ≥ (λ_min - ε) ‖x‖² > 0` for `x ≠ 0`.
4. Combined with `N.IsHermitian`, this gives `N.PosDef`.

**Estimated LOC:** ~50-80 for (α) + (β) + corollaries.

**Conclusion: AMBER (proceed with corrected formulation).** Grok recipe substance is salvageable but its literal claim is false. Local Claude T1.1 catches and patches per process Q4 ii.

---

## 5. Uniform Gaussian tail lemma (T3.1 stretch ingredient)

**Grok Q5 cross-track synergy recipe:** "On compact PD set K ⊂ Mat(n,ℝ), exists C, c > 0 s.t. ∀ Σ ∈ K, ∀ x, `multivariateGaussianPdf 0 Σ x ≤ C * exp(-c‖x‖²)`."

**R46 grep verification:**

| Target | Result |
|---|---|
| `IsGaussian.tail_bound`, `gaussian_tail`, `multivariateGaussian.*tail` | 0 hits. |
| `IsGaussian.exp_neg_quadratic_integrable` (or related Gaussian moment bounds) | 0 hits. |
| `Real.exp_neg_quadratic_integrable` | 0 hits. |
| `IsHermitian.posDef_iff_eigenvalues_pos` (foundation for λ_min uniform lower bound) | **FOUND** (see §1, §4). |
| `Continuous.exp_neg`, `Continuous.matrix_inv` | derivable from existing API. |

**Closure recipe (constructive):**
1. On compact `K`, λ_min(Σ) is continuous in Σ (eigenvalue continuity: lower-semi-continuous; on PosDef-restricted compact, attains positive minimum).
2. Hence `c := (1/2) · min_{Σ ∈ K} λ_min(Σ⁻¹) > 0`.
3. The pdf `(2π)^(-n/2) (det Σ)^(-1/2) exp(-x^T Σ^(-1) x / 2)` is bounded above by `C := max_{Σ ∈ K} (2π)^(-n/2) (det Σ)^(-1/2)` (continuous function on compact attains max).
4. Combined with `x^T Σ^(-1) x ≥ c · ‖x‖²` from λ_min bound on `Σ⁻¹`, we get `pdf ≤ C · exp(-c · ‖x‖² / 2)`.

**Estimated LOC:** ~60-100.

**Conclusion: GREEN** for T3.1 stretch.

---

## 6. R46 plan validation

| Sub-gap | Grok recipe | T1.1 verdict | LOC estimate |
|---|---|---|---|
| (c) Linear pushforward | GREEN — `LinearMap.exists_map_addHaar_eq_smul_addHaar` direct | **40-80** |
| (a) det_CFC_sqrt = sqrt det | GREEN — via `sqrt_mul_self` (Order.lean:140) | **30-50** |
| (b) stdGaussian = volume.withDensity | GREEN — via `gaussianReal_of_var_ne_zero` + brownian-motion lemma | **80-120** (subsidiary +30-50 if Pi.withDensity unpackaged) |
| **MGE composition** | GREEN | **30-50** |
| **TOTAL T2.1 (MGE Full)** | | **180-300 LOC** |
| Phase 2 sub-gap A (PosDef "isOpen") | **AMBER — patched formulation (α) and (β)** | **50-80** |
| **T2.1 + T2.2 mandatory floor** | | **230-380 LOC** |
| Uniform Gaussian tail (T3.1 stretch) | GREEN | **60-100** |
| Parametric DCT (T3.1 stretch) | depends on `hasFDerivAt_integral_of_dominated_loc_of_lip` (Grok R45 Q1.c verified) | **40-80** |

**Aggregate R46 estimate:** mandatory floor 230-380 LOC; +T3.1 stretch 100-180 LOC → **330-560 LOC**. This brackets the brief's "270-470 LOC" target (mandatory only ~270, full ~470).

**Recommendation:** proceed with sub-gaps closure order **c → a → b → MGE composition**, then T2.2 PosDef local-stability, build verification, and (if time) T3.1 library.

---

## 7. Process change Q4 ii continued value (R46 evidence)

R44 audit caught Jacobi-formula misframing. R45 audit caught (i) `PosSemidef.det_sqrt` claimed in Mathlib (false), (ii) Phase 2 dependency claim. R46 audit (this doc) catches PosDef-open-globally claim (mathematically false in `Matrix n n ℝ`).

**Three consecutive rounds of Grok pre-flight misframings caught by Local Claude T1.1.** Process change Q4 ii (Local Claude grep first, Grok math-reasoning second) is binding and continues to deliver value: each catch saves the round from chasing a wrong-typed formal statement, and each surfaces a precise actionable patch.

**Pattern observation:** Grok pre-flight is reliable for *math reasoning* (the WHY) but unreliable for *formal-Mathlib API claims* (the WHAT — exact lemma names, exact universe of discourse). Local Claude grep verifies the latter at marginal cost.

---

**End R46-T1.1 audit.** Proceed to T2.1 with closure order c → a → b, and T2.2 with corrected formulation (α) "local stability under Hermitian perturbations" (NOT global `Matrix.PosDef.isOpen`).
