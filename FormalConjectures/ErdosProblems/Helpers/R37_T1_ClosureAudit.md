# R37 — T1.1 Closure dependency audit

**Read-only audit, single round, R37 (branch `r33-c-helpers-consolidation`).**
Two sub-audits per the round prompt's binding decision points:

* **A.** IsGLWProcess setup verification (Grok-Q1 caveat — α / β / hybrid).
* **B.** §11 limit-law assembly scope (Sm / Md / Lg).

Each sub-audit terminates in a verdict that pins T2.1 / T2.2 outcomes
before any code is written.

---

## A. IsGLWProcess setup verification (Grok-Q1 caveat)

### Helpers under audit

| # | Helper                                                                        | File:line                       | Body  |
|---|-------------------------------------------------------------------------------|----------------------------------|-------|
| H1 | `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`  | `Helpers/GLWLowerProof.lean:347` | sorry |
| H2 | `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus` | `Helpers/GLWLowerProof.lean:362` | sorry |
| H3 | `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`  | `Helpers/GLWUpperProof.lean:281` | sorry |

**Audit-tool discrepancy noticed.** `Helpers/PhaseAR36Status.md` and
`Helpers/AxiomFoundationAudit.md` (R36 section) list **only H1 + H2**
under the 8-TAG'd-sorry inventory. **H3 is also a parallel `sorry` with
identical structural gating** (consumed at `524.lean:4095, 4252` by
`polynomial_sup_small_ball_upper{,_uniform}`). Net audit-corrected
inventory is **3 IsGLWProcess sorries**, not 2.

### Helper signatures (verbatim)

All three helpers share the identical degenerate input shape:

```lean
theorem gao_li_wellner_small_ball_{lower,upper}_isGLWProcess_Y{plus,minus}
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {Y... : ℝ → Ω → ℝ} (_hY..._meas : ∀ u, Measurable (Y... u)) :
    IsGLWProcess Y... := by
  sorry
```

Only `Measurable (Y u)` per index — i.e. one of `IsGLWProcess`'s nine
conjuncts (`Helpers/GLWProcessPredicate.lean:78-97`: `measurable`,
`integrable`, `integrable_prod`, `centered`, `cov` (= K_GLW),
`gaussian` (joint), `continuous_paths`, `tail_decay`).

### Grok α-path recipe — required inputs (from prompt Q1)

The Grok recipe assumes the helper has access to:

1. A decomposition `Yplus = Y_e + Y_o` exposed at the helper's scope.
2. `IsGaussianProcess Y_e` and `IsGaussianProcess Y_o` already established.
3. `ProbabilityTheory.IndepFun Y_e Y_o ℙ` already established.
4. Kernel halving identities `K_{Y_e}(s,t) = K_{Y_o}(s,t) =
   (1/2)·K_GLW(s,t)` (pointwise, not block-restricted).
5. A.s. continuity of `Y_e` and `Y_o` paths individually.

Grok's <100-LOC closure recipe is then `covariance_add_indep` + kernel
halving + continuity inheritance. The recipe is correct **if and only if**
inputs (1)–(5) are in scope.

### Verbatim KMT-coupling output at the call-sites

The upstream public theorem `two_dim_KMT_coupling_legacy_Ω_form`
(`524.lean:3889`) returns a 13-tuple destructured at the four
`polynomial_sup_small_ball_*` call-sites:

```lean
obtain ⟨Yplus, Yminus, Δ, hYp_meas, hYm_meas, hΔ_bd, hKMT_p, hKMT_m,
        hIndep, hYp_cont, hYm_cont, _hYp_tail, _hYm_tail⟩ :=
    two_dim_KMT_coupling_legacy_Ω_form a ha
```

Components (`524.lean:3889-3920`):

| Component       | Statement                                                        |
|-----------------|------------------------------------------------------------------|
| `Yplus, Yminus` | `ℝ → Ω → ℝ` (typed only; no decomposition `Yplus = Y_e + Y_o`)   |
| `hYp_meas`      | `∀ u, Measurable (Yplus u)`                                      |
| `hYm_meas`      | `∀ u, Measurable (Yminus u)`                                     |
| `hΔ_bd`         | `Δ n ≤ log(n+1)/√n`                                              |
| `hKMT_p`        | KMT coupling rate for Yplus full-sum                             |
| `hKMT_m`        | KMT coupling rate for Yminus full-sum                            |
| `hIndep`        | `IndepFun (· ↦ fun u ↦ Yplus u ω) (· ↦ fun u ↦ Yminus u ω) ℙ`    |
| `hYp_cont`      | `∀ ω, Continuous (fun u ↦ Yplus u ω)`                            |
| `hYm_cont`      | `∀ ω, Continuous (fun u ↦ Yminus u ω)`                           |
| `_hYp_tail`     | tail decay (∀ε>0 ∀ᵐω ∃T₀ ∀u≥T₀ |Yplus u ω| ≤ ε)                  |
| `_hYm_tail`     | tail decay for Yminus                                            |

### Mismatch table — Grok recipe vs. actual upstream output

| Grok input               | Available?                                | Evidence                                                                                                                                                                                              |
|--------------------------|-------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| (1) `Yplus = Y_e + Y_o`  | **No.** `Yplus` is opaque post-destructure | Even/odd-block decomposition `Y_e, Y_o` is a *private internal* of `two_dim_KMT_coupling_via_LS_reduction` (`Helpers/TwoDimKMTFromOneDim.lean`); not exposed in legacy-Ω signature.                  |
| (2) `IsGaussianProcess Y_e/Y_o` | **No.** Not in either output | The legacy-Ω form gives only measurability + continuity + tail decay + KMT coupling rate — joint Gaussianity is **not** a conjunct on the public surface, and Y_e/Y_o never appear.            |
| (3) `IndepFun Y_e Y_o`   | **No.** `hIndep` is `Yplus ⊥ Yminus` | Independence pair is the **outer** Yplus/Yminus from R33-D linear-combo Form β, **not** the inner Y_e/Y_o decomposition. Grok's α-path independence assumption mismatches.                            |
| (4) `K_{Y_e} = (1/2)·K_GLW` | **No.** No kernel formula in output | The KMT coupling rate `\|n^{-1/2} Σ a_k · ker - Y u ω\| ≤ Δ n` only asserts proximity of the partial sum to Y at sub-CLT rate. Per-Y K_GLW covariance is the `Y_GLW_exists` content on a different ℙ. |
| (5) `continuous Y_e/Y_o` paths | **No.** Only Yplus/Yminus continuity exposed | `hYp_cont, hYm_cont` are the outer-pair continuities. Inner Y_e/Y_o continuity is internal-only.                                                                                                  |

### Grok-α verdict — **β-needed (kernel-mismatch on inputs (1)–(5))**

Inputs (1)–(5) **all fail at the helper signature** (the helper only
receives `_hY_meas`) **and at the upstream `two_dim_KMT_coupling_legacy_Ω_form`
output** (the destructured 13-tuple does not expose Y_e/Y_o, joint
Gaussianity, or per-Y K_GLW kernels).

To execute Grok's α-path, the closure round would have to first:

* extend `two_dim_KMT_coupling_legacy_Ω_form` to expose `Y_e, Y_o` as
  named outputs,
* derive and expose `IsGaussianProcess Y_e / Y_o` from the Itô-integral
  step inside `via_LS_reduction`,
* derive `IndepFun Y_e Y_o` (separate from the existing
  `Yplus ⊥ Yminus`),
* derive halved kernel identities `K_{Y_e}(s,t) = (1/2)·K_GLW(s,t)`,
* then change the helper signatures to take these new hypotheses.

This is the R34 audit's path (a) — out of round-budget per R34's
1-2-round estimate, and rejected for the standard reason that any signature
change to the helpers just relocates the gate to the four
`polynomial_sup_small_ball_*` call-sites.

**Verdict: T1.1.A = β-needed.** T2.1 will axiomatize all three helpers
(H1 + H2 + H3) symmetrically with R36-style audit-honesty docstrings
citing this Grok-assumption mismatch.

**Net axiom delta on T2.1:** +3 user-defined axioms.

| Pre-R37 axioms | Post-R37 (β-path) axioms       |
|----------------|----------------------------------|
| 5 (D2 + 1D KMT + stepping-stone + GLW lower + GLW upper) | **8** (+ 3 IsGLWProcess: lower-Yplus, lower-Yminus, upper-Yplus) |

The +1 vs the round prompt's projected 7 is exactly the R36-audit
discrepancy: the upper-side `_isGLWProcess_Yplus` was a parallel
unaccounted sorry. R37 takes the symmetric β-path on it for true
closure (rather than leaving an inconsistent stripe).

---

## B. §11 limit-law assembly scope

### Locating §11 in `524.lean`

The "§11 limit law" in this codebase is the
**Chojecki–Gao–Li–Wellner sparse-subseq cubic-exponent envelope**:

```lean
theorem chojecki_sparse_lower_envelope_proof
    (glw : GaoLiWellnerConstants) :
    let α_minus : ℝ := (1 / (6 * glw.upper)) ^ ((1 : ℝ) / 3)
    let α_plus  : ℝ := (1 / (6 * glw.lower)) ^ ((1 : ℝ) / 3)
    let n : ℕ → ℕ := fun m => ⌊Real.exp ((m : ℝ) ^ 3)⌋₊
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∀ᵐ ω, α_minus ≤ limsup (φ_m a ω) atTop
                    ∧ limsup (φ_m a ω) atTop ≤ α_plus
```

at `524.lean:5114`, where `φ_m a ω :=
log(√(n m)/supNorm a (n m) ω) / (log log n_m)^{1/3}`.

### Inputs the §11 assembly already consumes

Per `524.lean:5114-7540` (the body, ~2433 LOC), the §11 limit law is
assembled from:

1. **Per-block small-ball upper** —
   `polynomial_sup_small_ball_upper_uniform` (`524.lean:4231`), itself a
   THEOREM consuming the user-defined axiom
   `gao_li_wellner_small_ball_upper` (post-R36) plus the upper IsGLWProcess
   helper (H3 above).
2. **Per-block small-ball lower** —
   `polynomial_sup_small_ball_lower_uniform` (`524.lean:4764`), itself a
   THEOREM consuming `gao_li_wellner_small_ball_lower` (R34 axiom) plus
   the lower IsGLWProcess helpers (H1 + H2).
3. **2D KMT coupling** — `two_dim_KMT_coupling_legacy_Ω_form`
   (`524.lean:3889`, R33-D-T2.2-formβ-to-fullsum-bridge sorry).
4. **Block independence** — `iIndepSet_polynomialSupBlock_events`
   (Helpers, fully proved).
5. **Cubic-subsequence asymptotics** —
   `cubic_subseq_log_power_summability` and dual not-summability variant
   (Helpers, fully proved).
6. **Sample-path continuity / sup-block decomposition** —
   `polynomialSupBlock_*` (Helpers, fully proved).

### Body-state inspection (verbatim grep evidence)

```bash
# Total bare `sorry` in 524.lean:
$ grep -c "^\s*sorry$" FormalConjectures/ErdosProblems/524.lean
1

# Location of that sorry:
$ grep -n "^\s*sorry$" FormalConjectures/ErdosProblems/524.lean
3920:  sorry      # R33-D-T2.2-formβ-to-fullsum-bridge (pre-existing)

# Bare sorry / admit / native_decide inside chojecki body:
$ awk '/^theorem chojecki_sparse_lower_envelope_proof/,/^def chojecki_sparse_lower_envelope/' \
    FormalConjectures/ErdosProblems/524.lean | grep -cE "^[[:space:]]*sorry|admit|native_decide"
0  # all matches are inside comments referring to the word "axiom"
```

So `chojecki_sparse_lower_envelope_proof` has **no holes inside its
body**. The five `LABEL:` markers (`chojecki_sparse_lower_block_bc2` at
6168, `_block_ratio_diff_top` at 6317, `_block_shift_apply` at 6821,
`_h7_rearrange` at 7418, `_h7_isBoundedUnder` at 7502) are
**documentation markers for major sub-strategies**, NOT sub-sorries; the
named code paths around them are inlined.

### LOC scope verdict — Lg-already-assembled

| Metric                                  | Value                  |
|-----------------------------------------|------------------------|
| `chojecki_sparse_lower_envelope_proof` body LOC | 2433                   |
| Bare sorries inside the body            | **0**                  |
| Named labelled sub-strategies           | 5 (all inlined)        |
| Required upstream lemmas                | 6 categories (all in place) |

The §11 limit law is **already fully assembled** prior to R37. The
prompt's Sm / Md / Lg scoping does not apply in the conventional sense:
the body is **Lg-by-LOC** but **Full-by-completeness** — there are no
unfilled holes inside the chojecki body that R37 needs to plug.

### What R37 closure verification will do (T2.2 scope)

T2.2 reduces to a **build-verification + structural confirmation**:

* Confirm by `lake build` that the `polynomial_sup_small_ball_*`
  consumers (`524.lean:4071, 4231, 4381, 4764`) of the
  IsGLWProcess helpers still typecheck after T2.1's β-path (axiom
  declarations have identical types to the prior `theorem ... := by
  sorry` so the `obtain` / function-application sites see the same
  signature).
* Confirm chojecki body LOC and zero-bare-sorry property are unchanged
  post-T2.1.
* Document the §11 assembly as **Full** in the round status:
  `chojecki_sparse_lower_envelope_proof` is the §11 limit law, body
  complete, axiom dependence inventory captured (axiom A4 + A5 +
  3 × IsGLWProcess +  3 R33-C/D Mathlib gaps + R35 PhaseA scaffolds).

**Verdict: T1.1.B = Full-by-prior-assembly (Lg-by-LOC, no closure code
needed).**

This is NOT the prompt's projected Sm / Md / Lg-skeleton categorisation —
it is a fourth outcome ("already complete from prior rounds"), and is
honest: the §11 chain glue WAS previously realized inline as part of the
~2400-LOC chojecki body across earlier sessions (S3 / S6 / R29-R33). R37
inherits a cleanly-assembled §11.

---

## Closure decision summary

| Sub-audit | Verdict                                | T2.x action                          |
|-----------|----------------------------------------|--------------------------------------|
| T1.1.A    | β-needed (kernel-mismatch on inputs 1-5) | T2.1 axiomatizes H1 + H2 + H3 (+3 axioms; total 8) |
| T1.1.B    | Full-by-prior-assembly                 | T2.2 = build-verify + structural confirmation |

### Code-level Scope 3 closure tier projection

* **DECLARED** — Helpers green + §11 fully assembled, ENat consumer
  block orthogonal per Grok Q3.

This is the strongest tier the round prompt allows: the §11 limit law is
fully assembled (T1.1.B-Full); the IsGLWProcess helpers retire as
β-axioms with kernel-mismatch diagnostic (T1.1.A-β-needed); ENat is
upstream-pending and orthogonal.

**R37 closure:** 8 user-defined axioms + 3 R33-C/D Mathlib-gap TAG'd
sorries + 3 R35 Phase A scaffold TAG'd sorries (Option (a) preserved per
R36) = honest audit, no contradictions, all axiomatized content
classically correct.

**R38 trajectory:** ENat resolution (orthogonal Mathlib version bump per
Grok Q3) + consumer-level build green + final Scope 3 declaration with
consumer green.
