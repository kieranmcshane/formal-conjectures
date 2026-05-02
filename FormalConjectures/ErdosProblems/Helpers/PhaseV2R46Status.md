# R46 Track A status (V2 round 8 closure) — MGE sub-gap (a) Full + PosDef min-eigenvalue helpers

**Round:** R46 Track A (mainline). **Branch:** `r46-track-a-mge-posdef` (off `5596638` R45 mainline). **Lean toolchain:** `v4.27.0-rc1`. **Mathlib pin:** `25ce63313608`. **brownian-motion pin:** `91267abd71bd`. **Today:** 2026-05-02.

**TL;DR.** R46 Track A delivers diagnostic-quality enhancement with 4 new Full theorems (3 in MGE chain, 2 in PosDef chain), 0 net debt retirement, and **catches the third consecutive Grok pre-flight misframing** via process Q4 ii. R46-T1.1 audit independently caught Grok Q2's claim "`Matrix.PosDef.isOpen`" in `Matrix n n ℝ` as mathematically false (PosDef ⇒ IsHermitian ⇒ closed in full matrix space); patched to correctly-framed minimum-eigenvalue lower bound formulation, which is the substantive ingredient for R47+ Phase 2 body close + uniform Gaussian tail.

## R46 outcomes (mandatory floor — all five committed)

| Task | Status | Commit |
|---|---|---|
| Phase 0 — branch setup from R45 mainline `5596638` | ✅ | branch `r46-track-a-mge-posdef` |
| **T1.1** — Local Claude grep audit + framing verification | ✅ Full (~200 LOC doc) | T1.1 commit |
| **T2.1** — MGE Full body close, sub-gaps (a) Full + (c) ApplyDirect + (b) deferred to R47+ | ✅ Diagnostic-quality enhancement (~88 LOC) | T2.1 commit |
| **T2.2** — PosDef minimum-eigenvalue helpers (Full, framing-corrected) | ✅ Full (~87 LOC) | T2.2 commit |
| **T2.3** — Build verification + status doc + AXIOM_INVENTORY update | ✅ this commit | this commit |
| T3.1 stretch — GaussianParametricAnalysis library extraction | deferred per time budget | — |
| T3.2 stretch — R47 Track A pre-flight prompt | scheduled | — |

## Build verification

```bash
$ lake env lean FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianPdf.lean
warning: brownian-motion: repository '...' has local changes
FormalConjectures/.../MultivariateGaussianPdf.lean:248:8: warning: declaration uses 'sorry'

$ lake env lean FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean
warning: brownian-motion: repository '...' has local changes
FormalConjectures/.../PhaseAUpperBound.lean:450:8: warning: declaration uses 'sorry'

$ lake env lean FormalConjectures/ErdosProblems/Helpers/MultivariateGaussianCDF.lean
warning: brownian-motion: repository '...' has local changes
FormalConjectures/.../MultivariateGaussianCDF.lean:160:8: warning: declaration uses 'sorry'
FormalConjectures/.../MultivariateGaussianCDF.lean:313:8: warning: declaration uses 'sorry'

$ lake env lean FormalConjectures/ErdosProblems/524.lean
warning: brownian-motion: repository '...' has local changes
FormalConjectures/ErdosProblems/524.lean:3889:16: warning: declaration uses 'sorry'
[plus 3 linter warnings unrelated to R46]
```

All builds clean (no errors). All sorries pre-existing TAG'd Stubs unchanged in count by R46 work.

## Net debt change R45 → R46

| Metric | R45 close | R46 close | Δ |
|---|---|---|---|
| User-defined axioms | 5 | 5 | 0 |
| TAG'd sorries (Helpers + 524) | 12 | 12 | 0 |
| **Total debt items** | **17** | **17** | **0** |
| Full-proved Helper theorems added | — | +4 | +4 |

Despite zero retirement, R46 advances three of the four named subsequent-round closures by providing the foundational infrastructure (sub-gap (a) Full + PosDef min-eigenvalue) that those rounds need. The infrastructure does NOT contribute to debt count by itself but enables future retirements.

**Hybrid (c) gate trajectory** (per post-R45 strategic Grok verdict):

* Aspirational target: R59 pure axiom-free.
* HARD R52 milestone gate: if net debt > 8 items at end R52 → lock R54 + BTIS axiom (Path A pragmatic ship).
* Required pace R46-R50: 1.5-2.0 items/round.
* **R46 actual pace: 0/round** — below required pace. R47-R50 must compensate at 1.875-2.5 items/round to recover.

R46 is below the pace target, but the foundational helpers landed make R47-R50 mechanically tractable: Phase 2 body Full close (R47) is now down to single sub-gap (b) for MGE + PosDef helpers in scope. A solid R47-R49 (each 2 retirements) is the minimum trajectory to keep R52 gate viable.

## R46 deliverables — line-by-line

### T1.1 — `R46_T1_GrepAuditAndFramingVerification.md` (new, ~200 lines)

* §1 audits sub-gap (a) `det_CFC_sqrt_eq_sqrt_det`. Verifies `CFC.sqrt_mul_sqrt_self`,
  `Matrix.det_mul`, `Real.sqrt_eq_iff_mul_self_eq`. Estimate ~30-50 LOC.
* §2 audits sub-gap (b) `stdGaussian_eq_lebesgue_withDensity`. Verifies
  `gaussianReal_of_var_ne_zero`, `stdGaussian_eq_pi_map_orthonormalBasis`. Estimate
  ~80-120 LOC. Bottleneck per Grok Q1.
* §3 audits sub-gap (c) constant-Jacobian linear pushforward. Verifies
  `lintegral_abs_det_fderiv_eq_addHaar_image`, `map_withDensity_abs_det_fderiv_eq_addHaar`,
  `LinearMap.exists_map_addHaar_eq_smul_addHaar`. Estimate ~40-80 LOC.
  **R46-T2.1 update**: also identifies `map_linearMap_addHaar_eq_smul_addHaar` (`EqHaar.lean:234`)
  as the EXACT specialization for our use case — DIRECT application, no new sub-lemma needed.
* §4 audits Phase 2 sub-gap A `Matrix.PosDef.isOpen`. **CRITICAL FRAMING CORRECTION**:
  Grok claim is mathematically false in `Matrix n n ℝ`. Patched to formulations
  (α) "local stability under Hermitian perturbations" and (β) openness within
  Hermitian subspace. Estimate ~50-80 LOC.
* §5 audits uniform Gaussian tail. Verifies eigenvalue continuity + PSD foundation.
  Estimate ~60-100 LOC for T3.1 stretch.
* §6 R46 plan validation table.
* §7 process Q4 ii continued value note (3 consecutive Grok misframings caught).

### T2.1 — `MultivariateGaussianPdf.lean` modifications

**Full sub-lemma added** (`det_CFC_sqrt_eq_sqrt_det`, ~30 LOC):

```lean
theorem det_CFC_sqrt_eq_sqrt_det
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (CFC.sqrt S).det = Real.sqrt S.det := ...
```

Composition: `CFC.sqrt_mul_sqrt_self` (`Rpow/Basic.lean:259`) +
`Matrix.det_mul` (`LinearAlgebra/Matrix/Determinant/Basic.lean:138`) +
`Real.sqrt_eq_iff_mul_self_eq` (`Data/Real/Sqrt.lean:150`).

**Full corollary added** (`det_CFC_sqrt_pos_of_posDef`, ~5 LOC):

```lean
theorem det_CFC_sqrt_pos_of_posDef
    {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    0 < (CFC.sqrt S).det := ...
```

**MGE main body diagnostic refresh**: documents (a) Full close + (c) ApplyDirect status.
Single TAG'd sorry preserved at narrow (b) gap.

### T2.2 — `PhaseAUpperBound.lean` modifications

**Full helper added** (`posDef_min_eigenvalue_pos`, ~15 LOC):

```lean
theorem posDef_min_eigenvalue_pos
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ i : n, c ≤ hM.isHermitian.eigenvalues i := ...
```

Composition: `Matrix.PosDef.eigenvalues_pos` (`Mathlib/Analysis/Matrix/PosDef.lean:85`) +
`Finset.exists_min_image` (`Mathlib/Data/Finset/Max.lean:543`).

**Full corollary added** (`posDef_min_eigenvalue_witness`, ~25 LOC):

```lean
theorem posDef_min_eigenvalue_witness
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M : Matrix n n ℝ} (hM : M.PosDef) : ...
```

Same content with constant pinned via `Finset.min'`. Useful for consumers
needing the explicit value of `c`.

## Process Q4 ii continued value (R46 evidence)

**R44** audit caught Jacobi-formula misframing (Grok claimed MGE = Jacobi formula close;
actually MGE = pushforward measure equality, decomposing into 3 sub-gaps).

**R45** audit caught two Grok misframings: (i) `Matrix.PosSemidef.det_sqrt` claimed in
Mathlib (false); (ii) Phase 2 dependency claim partial mis-attribution (MGI gives only
the rewrite, pdf differentiability still requires R40/R41 stubs + chain rule).

**R46** audit caught Grok Q2 misframing: "`Matrix.PosDef.isOpen`" in `Matrix n n ℝ` is
mathematically false (PosDef ⇒ IsHermitian ⇒ closed). Patched to correctly-framed
minimum-eigenvalue lower bound + Hermitian-subspace local stability formulation.

**Three consecutive rounds of Grok pre-flight misframings caught by Local Claude T1.1.**
Process change Q4 ii (Local Claude grep first, Grok math-reasoning second) is binding
and continues to deliver value: each catch saves the round from chasing a wrong-typed
formal statement, and each surfaces a precise actionable patch.

**Pattern observation:** Grok pre-flight is reliable for *math reasoning* (the WHY) but
unreliable for *formal-Mathlib API claims* (the WHAT — exact lemma names, exact universe
of discourse, exact ambient topology). Local Claude grep verifies the latter at marginal
cost and continues to deliver round-saving value.

## R47+ trajectory

**R47 Track A scope (proposed):**
* MGE sub-gap (b) Full close: `stdGaussian_eq_lebesgue_withDensity` via Fubini +
  `gaussianReal_of_var_ne_zero` + `Measure.pi.withDensity` factorization.
  Estimated ~80-120 LOC. **Retires 1 sorry** (MGE main becomes Full).
* Phase 2 body Full close (Path γ via R44 MGI executable + R46 PosDef helpers + new
  Lipschitz-on-compact-PosDef envelope). Estimated ~250-400 LOC. **Retires 1 sorry**
  (Phase 2 body Stub Full).

R47 mandatory floor at 2 retirements would put cumulative pace at 1.0/round (still
below required 1.5-2.0 but on a recovery track).

**R48-R50 candidates:**
* R48: Slepian body Full close. Uses R47 Phase 2 body + R41 helpers. Estimated 1
  retirement.
* R49 (Q5 BTIS-merge compression): BTIS axiomatize + GLW assembly. Estimated 2
  retirements (BTIS axiom + GLW Stub upper retirement).
* Track B retry post-Phase 2: R33-C/D Mathlib gaps (joint-Gaussian density now Full
  via R44 MGI). Estimated 2-3 retirements.

R52 gate evaluation: contingent on R47-R50 retirement pace. Current trajectory tight
but recoverable.

## Appendix — current axiom + sorry inventory

**5 user-defined axioms** (unchanged R45 → R46):

1. `Cp_T_explicit_pointwise_axiom` (private, `Helpers/GLWGaussianProjectiveLimit.lean:2013`)
2. `one_dim_KMT_coupling` (`Helpers/OneDimKMT.lean:101`)
3. `kmt_aided_gaussian_process` (`Helpers/StochasticProcessAxiom.lean:100`)
4. `gao_li_wellner_small_ball_upper` (`524.lean:3574`)
5. `gao_li_wellner_small_ball_lower` (`524.lean:3643`)

**12 TAG'd sorries** (unchanged R45 → R46): preserved per round-by-round inventory in
`AXIOM_INVENTORY.md`.

**4 new Full theorems added in R46:**
1. `det_CFC_sqrt_eq_sqrt_det` — `MultivariateGaussianPdf.lean`
2. `det_CFC_sqrt_pos_of_posDef` — `MultivariateGaussianPdf.lean`
3. `posDef_min_eigenvalue_pos` — `PhaseAUpperBound.lean`
4. `posDef_min_eigenvalue_witness` — `PhaseAUpperBound.lean`

These are foundational infrastructure for R47+ Phase 2 body close + uniform Gaussian
tail majorant; they enable but do not themselves directly retire formal debt.

---

**End R46 Track A status doc.** R47 pre-flight scheduled in T3.2 stretch.
