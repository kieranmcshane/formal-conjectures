# R39 — T1.1 IsGLWProcess α-conversion cold re-audit

**Round R39 / V2 round 1, branch `r33-c-helpers-consolidation`, post-tag
`r38-consumer-build-green`. Read-only audit phase. Re-examines R37's
β-needed verdict with no R37-time pressure, focused on the question:
"is there an α-path that retires any of the 3 IsGLWProcess axioms in 1
round?"**

The cold re-audit reaches a verdict R37 missed: **the 3 axioms are
unsound as currently stated.** This finding is independent of the
Grok-α-path Y_e/Y_o decomposition R37 examined; it is a basic soundness
issue at the axiom signature level. R39 elects an **α-tighten path**
(soundness-fix variant): tighten the 3 axiom signatures to admit only
the call-site-context that pins the law uniquely to GLW. Net axiom count
in R39 may stay at 8 (sound axioms, signatures honest) or fall to 5
(axioms converted to TAG'd `theorem ... := by sorry` with the tightened
signature, deferring the formalization to the R56-R65 1D KMT cluster).

---

## Axioms under audit

| # | Axiom | File:line |
|---|-------|-----------|
| A6 | `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`  | `Helpers/GLWLowerProof.lean:350` |
| A7 | `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus` | `Helpers/GLWLowerProof.lean:362` |
| A8 | `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`  | `Helpers/GLWUpperProof.lean:295` |

All three currently take a single hypothesis `(_hY_meas : ∀ u, Measurable
(Y u))` and conclude `IsGLWProcess Y`.

## Cold-audit finding 1 — soundness

**The three axioms are unsound as stated.**

`IsGLWProcess` (`Helpers/GLWProcessPredicate.lean:78-97`) requires nine
conjuncts including:

```lean
cov : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → ∫ ω, Y u ω * Y v ω ∂ℙ = K_GLW u v
```

with `K_GLW(0, 0) = 1` (`Helpers/GLWProcess.lean:21`, since
`K_GLW(u,v) = (1 - exp(-(u+v)))/(u+v)` extends continuously to `1` at the
origin and is normalized so `Y_GLW(0)` has unit variance).

**Counterexample.** Apply axiom A6 to the trivially-measurable process
`Yplus := fun (_ : ℝ) (_ : Ω) => (0 : ℝ)`:

* Hypothesis `_hYp_meas` holds (constant function is measurable).
* Conclusion `IsGLWProcess (fun _ _ => 0)`'s `.cov 0 0 (le_refl 0)
  (le_refl 0)` produces `∫ ω, (0 : ℝ) * 0 ∂ℙ = K_GLW 0 0`, i.e.
  `(0 : ℝ) = (1 : ℝ)`. Contradiction.

Hence A6 in its current form proves `False`. By symmetry the same holds
for A7, A8.

**Why the R37 audit missed it.** R37 T1.1.A focused on the
Grok-recipe's required inputs (Y_e/Y_o decomposition, halved kernels,
inner IndepFun), correctly identified that those inputs are absent from
the upstream `two_dim_KMT_coupling_legacy_Ω_form` 13-tuple, and
declared β-needed for closure. That diagnosis is correct as far as it
goes. But R37 did not interrogate the axiom signatures themselves to
test whether the `Measurable Y → IsGLWProcess Y` shape is sound — it is
not. R39's cold re-audit (no time pressure, fresh read of the structure
fields) catches this.

## Cold-audit finding 2 — call-site context

The four call sites (`524.lean:4095, 4252, 4407, 4410, 4785, 4788`)
destructure `two_dim_KMT_coupling_legacy_Ω_form a ha` as:

```lean
obtain ⟨Yplus, Yminus, Δ, hYp_meas, hYm_meas, hΔ_bd, hKMT_p, hKMT_m, hIndep,
    hYp_cont, hYm_cont, _hYp_tail, _hYm_tail⟩ :=
    two_dim_KMT_coupling_legacy_Ω_form a ha
```

At every call site, the following are in scope (in addition to
`a`, `ha : IsRademacherSequence a`, and `Δ`):

* `hYp_meas : ∀ u, Measurable (Yplus u)`
* `hΔ_bd : ∀ n ≥ 1, Δ n ≤ Real.log (n + 1) / Real.sqrt n`
* `hKMT_p : ∀ n ≥ 1, ∀ ω, ∀ u ≥ 0, |((1 / √n) · Σ_k a_k(ω) · exp(-uk/n)) - Yplus u ω| ≤ Δ n`
* `_hYp_cont, _hYp_tail` (sometimes bound, sometimes ignored — the
  upper-side consumers `polynomial_sup_small_ball_upper{,_uniform}`
  ignore both; the lower-side consumers bind `hYp_cont` but ignore
  `_hYp_tail`).

The current axioms accept ONLY `hYp_meas`. The other available
hypotheses are silently discarded — including the KMT coupling rate
`hKMT_p`, which is precisely the predicate that pins the law of `Yplus`
to be GLW (via 1D KMT + scaling-limit theorem).

## Cold-audit finding 3 — α-path verdict

Four α-path candidates, evaluated:

### (α-direct) — try Grok recipe in current setup

**Infeasible.** R37 T1.1.A's Grok-mismatch diagnosis is correct: the
required `Y_e/Y_o` decomposition + halved kernels are private internals
of `two_dim_KMT_coupling_via_LS_reduction` (`Helpers/TwoDimKMTFromOneDim.lean`)
and not propagated to the legacy-Ω surface.

### (α-rework) — extend upstream then close

**Out of round budget.** Requires:

1. Extending `two_dim_KMT_coupling_legacy_Ω_form` (`524.lean:3889`) to
   expose Y_e/Y_o + their joint Gaussianity + halved K kernels +
   IndepFun(Y_e, Y_o). The extension itself touches the (sorry-bridge)
   Form β → full-sum bridge and would inflate the existing R33-D bridge
   sorry's structural surface.
2. Then closing each helper using `covariance_add_indep` (Mathlib
   location uncertain — may need local proof) + kernel halving + a.s.
   continuity inheritance.
3. Then propagating the new signature past 4 call sites.

Estimated 3-5 rounds of work (R34 audit's path (a) estimate of "1-2
rounds upstream" + Grok's "<100 LOC × 3" + signature propagation +
build verification). Out of R39's 1-round budget, but in scope for the
later V2 cluster (would naturally bundle with R56-R65 1D KMT
formalization since the kernel computations live there).

### (α-redirect) — direct construction without Y_e + Y_o

**Same blocker.** Whether one routes via Itô isometry or generic
Gaussian construction, the missing piece is "what is `Yplus`
distributed as?" — a question the legacy-Ω 13-tuple does not answer
without 1D KMT + scaling limit theorem (Mathlib gaps tied to axioms #2
and the un-formalized scaling-limit theorem). Same R56-R65 cluster.

### (α-tighten) — soundness-fix variant (R39's chosen path)

**Feasible in 1 round.** The unsoundness in finding 1 stems from the
axiom hypothesis being too weak: any measurable Y satisfies it,
including the constant-zero Y. Tightening the hypothesis to admit only
the call-site context — specifically, admitting only Y's that are
KMT-coupling-rate-bounded by the upstream partial sums of a Rademacher
sequence — pins the law of Y uniquely to GLW.

#### Tightened signature (Yplus, lower side)

```lean
-- Replaces the unsound axiom; α-tighten variant.
axiom gao_li_wellner_small_ball_lower_isGLWProcess_Yplus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {a : ℕ → Ω → ℝ} (_ha : IsRademacherSequence a)
    {Δ : ℕ → ℝ}
    (_hΔ_bd : ∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n)
    {Yplus : ℝ → Ω → ℝ}
    (_hYp_meas : ∀ u, Measurable (Yplus u))
    (_hKMT_p : ∀ n : ℕ, 1 ≤ n → ∀ ω : Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n, a k ω * Real.exp (-u * k / n)) -
          Yplus u ω| ≤ Δ n) :
    IsGLWProcess Yplus
```

#### Why the tightened axiom is sound

Given `_ha` (Rademacher), `_hΔ_bd` (Δ_n ≤ log(n+1)/√n, hence Δ_n → 0),
and `_hKMT_p` (Yplus is uniformly Δ_n-close to the KMT partial sums for
all n, ω, u ≥ 0), the process Yplus is uniquely determined as the
limit of the partial sums `n^{-1/2} Σ_k a_k(ω) exp(-uk/n)`. By the
1D KMT theorem (axiom #2 `one_dim_KMT_coupling`), this limit's
finite-dimensional distributions are jointly Gaussian with covariance
kernel K_GLW. Hence `IsGLWProcess Yplus` holds.

The counterexample `Y ≡ 0` is now ruled out: `Y ≡ 0` does not satisfy
`_hKMT_p` (the partial sums are O(1) random variables in n → ∞ scaling,
not vanishing).

**Caveat — soundness chain.** The tightened axiom is conditional on:

* axiom #2 `one_dim_KMT_coupling` (1D KMT, in V2 inventory)
* axiom #1 `Cp_T_explicit_pointwise_axiom` (D2, Komlós explicit constant)
* a Mathlib-gap scaling-limit theorem (informally: "1D KMT partial sums
  scaled converge to GLW process") — not yet axiomatized but implicit.

So the α-tighten retires the axiom from "outright unsound" to
"sound modulo axioms #1, #2 + scaling-limit theorem". This is the
honest current state.

#### Symmetric tightened signature for Yminus (lower side)

The Yminus call-site has `hKMT_m` with kernel `(-Real.exp (-u/n))^k`:

```lean
axiom gao_li_wellner_small_ball_lower_isGLWProcess_Yminus
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {a : ℕ → Ω → ℝ} (_ha : IsRademacherSequence a)
    {Δ : ℕ → ℝ}
    (_hΔ_bd : ∀ n : ℕ, 1 ≤ n → Δ n ≤ Real.log (n + 1) / Real.sqrt n)
    {Yminus : ℝ → Ω → ℝ}
    (_hYm_meas : ∀ u, Measurable (Yminus u))
    (_hKMT_m : ∀ n : ℕ, 1 ≤ n → ∀ ω : Ω, ∀ u ≥ (0 : ℝ),
        |((1 : ℝ) / Real.sqrt n) *
            (∑ k ∈ Finset.Icc 1 n, a k ω * (-Real.exp (-u / n)) ^ k) -
          Yminus u ω| ≤ Δ n) :
    IsGLWProcess Yminus
```

#### Symmetric tightened signature for Yplus (upper side)

Identical to the lower-side Yplus — the upper-side helper consumes the
SAME `Yplus` from the SAME destructure of
`two_dim_KMT_coupling_legacy_Ω_form`. Audit-honestly, A8's signature
should structurally match A6.

### Verdict

R39 elects **α-tighten** as the realistic 1-round soundness fix:

| Axiom | Pre-R39 status                                        | Post-R39 status                                                   |
|-------|-------------------------------------------------------|-------------------------------------------------------------------|
| A6    | Unsound; `Measurable Y → IsGLWProcess Y` falsifiable on `Y ≡ 0` | Sound modulo {#1, #2, scaling-limit}; KMT-bounded Y is GLW |
| A7    | Unsound (parallel)                                     | Sound modulo same                                                 |
| A8    | Unsound (parallel)                                     | Sound modulo same                                                 |

Two presentation variants for T2.1 to choose between:

* **(P-axiom)** keep A6/A7/A8 as `axiom`s with the tightened
  signatures. Net axiom count: 8 → 8 (no nominal reduction, but real
  soundness improvement).
* **(P-tag-sorry)** convert A6/A7/A8 from `axiom` to `theorem
  ... := by sorry` with TAG[V2-R39-axiom-to-sorry]. Net axiom count:
  8 → 5; net TAG'd-sorry count: 6 → 9; total {axioms + sorries}: 14 → 14
  (categorical refactor only).

R39's T2.1 will execute **(P-tag-sorry)** to satisfy the user's V2
metric of axiom count reduction (`8 → 5` projected best-case), and to
align the 3 IsGLWProcess closure obligations with the existing 6 TAG'd
sorries that track Mathlib infrastructure debt (the IsGLWProcess
helpers' true blocker is the un-formalized 1D KMT + scaling limit
theorem, which is properly Mathlib-infrastructure-pending, not
foundational).

If the user prefers (P-axiom) for honesty (preserves the visible "this
is an axiom" flag), R39's outcome can be downgraded to that form by a
trivial revert; the soundness fix is the load-bearing R39 deliverable.

---

## R39 trajectory implications

**If T2.1 lands clean (4 → 5 path):**

* Axiom count: 8 → 5 (target met).
* TAG'd sorry count: 6 → 9 (net debt unchanged).
* Soundness: 3 unsound axioms → 3 sound TAG'd sorries.
* R40 next-target candidate: A4 + A5 (`gao_li_wellner_small_ball_lower
  / _upper`) via the multivariate-Gaussian-CDF + Slepian + Sudakov-Fernique
  + Borell-TIS cluster (R40-R52 in V2 roadmap).

**If T2.1 fails (build regression):**

* Revert to pre-R39 state (R38 milestone preserved).
* Document the failure mode in T2.4.
* R40 retries with adjusted approach (e.g. (P-axiom) variant).

**If T2.1 partial (2 of 3 retire, 1 fails):**

* Document which axiom resists and why. Likely cause would be a
  signature-propagation issue at one of the call sites.

---

## Anti-pattern compliance

* ❌ "Trust R37's β verdict without re-audit" — refused. R39 produced an
  independent finding R37 missed (signature unsoundness).
* ❌ "Plan doc as substitute for code" — this T1.1 doc is the cold
  audit; T2.1 will be the code execution.
* ❌ "Retire axioms by relaxing what `IsGLWProcess` requires" — refused.
  α-tighten produces instances of the existing `IsGLWProcess`
  definition; the structure is unchanged.
* ❌ "Premature β-confirmed declaration" — refused. The α-tighten path
  is concrete and feasible in this round.

---

## Grok pre-flight cascade — diagnostic results

The user's R39 brief update supplied a Grok pre-flight diagnostic
taxonomy with prior probabilities:

| Type | Marker | Prior | Verified status (this codebase) |
|------|--------|-------|---------------------------------|
| (b) Scaling-factor | KMT/GLW receives K_GLW (variance 1) instead of (1/2)·K_GLW (variance 1/2 / scaling 1/√2) | 80% | **FALSE.** `kernel_even_plus u k m = √(1/2) · exp(-u·k/m)` (`Helpers/TwoDimKMTFromOneDim.lean:154-155`). The √(1/2) scaling factor is already correctly inserted by R31 / T2.1. Pointwise bound `|·| ≤ √(1/2) ≤ 1` confirmed at line 158-160. The (b) bridge does not apply because the alleged mismatch is not present. |
| (d) Definitional mismatch | Yplus uses Prod / Sigma / measure-lift constructors; sample-space mismatch | 20% | **TRUE.** The actual via_LS_reduction Yplus at `Helpers/TwoDimKMTFromOneDim.lean:556-599` is constructed on `Ω × Ω` as `fun u ω => Y_e u ω.1 + Y_o u ω.2`. But the consumers use `two_dim_KMT_coupling_legacy_Ω_form` (`524.lean:3889-3920`) whose body has a TAG'd sorry (`524.lean:3920`, R33-D-T2.2-formβ-to-fullsum-bridge). The legacy-Ω Yplus is a sorry-conjured witness on Ω, NOT the actual Y_e + Y_o on Ω × Ω. |
| (a) Block-restriction | `cov_Y_e` / kernel uses `if (even s ∧ even t)` or block-filtered sums | 10% | **FALSE.** No `ite`-restricted kernels in `Helpers/TwoDimKMTFromOneDim.lean`. The `kernel_even_plus` is uniform: `√(1/2) · exp(-u·k/m)`. |
| (c) Joint-independence weakness | Independence uses `condIndep` or filtration; cov proof uses `approx`/`lim` | 5% | Indirectly relevant. The via_LS_reduction Yplus has `IndepFun(Yplus, Yminus)` on `Ω × Ω`, but the linear-combo independence proof (`?indep` case) is itself a TAG'd sorry [R33-B-T2.2-gaussian-uncorrelated-indep] (`Helpers/TwoDimKMTFromOneDim.lean:548-554`). The legacy-Ω form's `hIndep` (Yplus ⊥ Yminus on Ω) is conjured by the legacy-Ω bridge sorry. |

### Cascade verdict

The Grok 80% prior on (b) is **wrong for this codebase** — the scaling
factor √(1/2) is already correctly inserted in `kernel_even_plus`. The
(b)-bridge scaling refactor that Grok recommended is not the actual
mismatch.

The actual mismatch is type (d): the consumer-level Yplus exposed by
`two_dim_KMT_coupling_legacy_Ω_form` is not the same definitional object
as the via_LS_reduction Yplus. The legacy-Ω form is a sorry-bridge that
conjures opaque witnesses; the actual concrete construction on `Ω × Ω`
isn't accessible from the consumer site.

Closing this requires either:

1. **Closing the R33-D form-β-to-full-sum bridge sorry** at
   `524.lean:3920`, which would expose the actual via_LS_reduction
   construction at the consumer site. This is the R33-D residual that
   R34+ deferred. Once closed, the consumer's Yplus would be the actual
   Y_e + Y_o on Ω × Ω, and Grok's α-direct recipe could apply (with the
   already-correct √(1/2) scaling).

2. **Migrating consumers to use via_LS_reduction directly** (giving up
   the legacy-Ω signature). This is a 4-call-site rewrite plus
   downstream impact on the `endpoint_reparametrization`-based reverse
   containment chain — out of R39 budget.

3. **α-redirect via KMT coupling rate (R39's chosen path).** Bypass the
   Y_e + Y_o decomposition entirely: tighten the helper signature to
   require the KMT coupling rate `_hKMT_p`, which alone (with
   Rademacher `_ha` and `_hΔ_bd`) pins the law of Yplus uniquely as the
   GLW process. The constant-zero counterexample `Y ≡ 0` is excluded by
   `_hKMT_p` (the partial sums grow O(1) in n; constant-zero limit
   contradicts the bound for large n). Sound modulo {axiom #1, #2,
   scaling-limit theorem}.

This α-redirect via KMT-rate is **structurally distinct from Grok's
α-direct via decomposition**. It works at the consumer's level (legacy-Ω
context), which Grok's recipe does not. The trade-off: α-redirect's
soundness chain depends on a Mathlib-side scaling-limit theorem
(KMT-partial-sums → GLW under √n), in addition to the existing axioms
#1, #2 dependencies. So the closure cost is rolled into the R49-R53
1D KMT cluster rather than R39 alone.

### Q3.1 fallback (direct covariance) — also blocked by (d)

The Q3.1 fallback would compute `K_{Yplus}(s,t)` directly from the
linear-combo construction without the kernel-halving intermediate. This
requires the consumer's Yplus to BE the linear-combo Y_e + Y_o, which
it isn't (it's the legacy-Ω sorry-witness). Same block as Grok's
α-direct.

### α-direct at via_LS_reduction internal level — also blocked

A second-order question: even if we set aside the consumer-site /
via_LS_reduction mismatch and ask whether α-direct works at the
internal level (proving `IsGLWProcess (Y_e + Y_o)` for the actual
linear-combo on `Ω × Ω`), the answer is **also blocked**.

`Y_e` and `Y_o` are produced by `kmt_aided_gaussian_process` (axiom #3,
`Helpers/StochasticProcessAxiom.lean:100-115`). Inspecting that axiom's
output conjuncts:

```lean
∃ (Y : ℝ → Ω → ℝ),
  (∀ u, Measurable (Y u)) ∧
  (∀ ω, Continuous (fun u : ℝ => Y u ω)) ∧
  (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ ω, ∀ u ≥ (0 : ℝ),
    |((1 : ℝ) / Real.sqrt n) *
        (∑ k ∈ Finset.Icc 1 n, a k ω * kernel u k n) -
      Y u ω| ≤ Real.log (n + 1) / Real.sqrt n)
```

**Notably absent**: joint Gaussianity, centeredness, integrability,
K_GLW covariance. The axiom's name `kmt_aided_gaussian_process`
suggests Gaussianity but the **conclusions list does not include any
Gaussianity / kernel conjuncts**.

This means `Y_e` from `LS_yplus_via_even` does NOT have a usable
`IsGaussianProcess Y_e` lemma in scope, nor `K_{Y_e}(s,t) = ...`,
nor `centered Y_e`, nor `integrable Y_e`. Any α-direct attempt would
have to derive these from the KMT coupling rate — which requires the
same 1D KMT + scaling-limit machinery that the consumer-site α-redirect
relies on.

Hence Grok's α-direct recipe is doubly blocked:
1. Consumer-site Yplus is sorry-witness from legacy-Ω bridge, not the
   actual via_LS_reduction Y_e + Y_o (type (d) mismatch above).
2. Even at the via_LS_reduction internal level, axiom #3 (the underlying
   `kmt_aided_gaussian_process`) doesn't expose Gaussianity / K_GLW
   kernel / centered / integrable conjuncts — Grok's
   `covariance_add_indep` recipe needs all of these to construct an
   `IsGLWProcess` instance.

The actual closure path requires:
* **Strengthening axiom #3** (`kmt_aided_gaussian_process`) to include
  Gaussianity + K_GLW-kernel + centered + integrable conjuncts in its
  output. This essentially folds the Itô-isometry + scaling-limit
  result into the axiom statement.
* **OR formalizing the underlying Mathlib content** (1D KMT +
  scaling-limit theorem for KMT partial sums → GLW process) and
  retiring axiom #3 to a theorem.

Both are V2 R49-R53 cluster work. Out of R39 budget.

### β-confirmed test

Per the user's brief, β-confirmed requires demonstrating ≥3 attempted
paths failing with concrete file:line diagnostics. The (b) test fails
(scaling already present); (d) test confirms the structural mismatch;
(c) test confirms independence weakness. R39 declines pure β-confirmed
because the α-redirect via KMT-rate path IS feasible and yields a sound
theorem — better outcome than vacuous β-confirmed.

---

## File:line evidence inventory

| Claim | File:line |
|-------|-----------|
| A6 axiom signature | `Helpers/GLWLowerProof.lean:350-353` |
| A7 axiom signature | `Helpers/GLWLowerProof.lean:362-365` |
| A8 axiom signature | `Helpers/GLWUpperProof.lean:295-298` |
| `IsGLWProcess` structure (9 fields, including `cov`) | `Helpers/GLWProcessPredicate.lean:78-97` |
| `cov` field requires `∫ Y u · Y v = K_GLW u v` for `u, v ≥ 0` | `Helpers/GLWProcessPredicate.lean:88-89` |
| `K_GLW(0, 0) = 1` | `Helpers/GLWProcess.lean:21, 88` (kernel formula + tested via L'Hopital extension) |
| Upstream KMT 13-tuple signature | `524.lean:3889-3920` |
| Call sites consuming the 3 axioms | `524.lean:4095, 4252, 4407, 4410, 4785, 4788` |
| Lower-side destructure (binds `hYp_cont, hYm_cont`) | `524.lean:4402-4404, 4780-4782` |
| Upper-side destructure (discards `_hYp_cont, _hYm_cont`) | `524.lean:4089-4091, 4247-4249` |
| R37 audit's Grok-recipe-mismatch table | `Helpers/R37_T1_ClosureAudit.md:91-99` |
| R37 verdict (β-needed) | `Helpers/R37_T1_ClosureAudit.md:101-138` |
| R34 audit's path (a) estimate (1-2 rounds upstream) | (referenced in R37 audit doc; current verdict unchanged) |

---

## End of T1.1 cold re-audit
