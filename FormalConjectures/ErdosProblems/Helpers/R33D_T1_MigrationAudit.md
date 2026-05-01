# R33-D / T1.1 — Migration Audit (read-only state, pre-T2.*)

**Branch.** `r33-c-helpers-consolidation`, HEAD `d7d3ea4` (R33-C T2.2 stretch:
inner Real-arithmetic chain closed).

**Scope.** Audit, before any code modification, of the four call-sites that
consume the public theorem `two_dim_KMT_coupling` (524.lean) and of the
helper `Erdos524.Helpers.two_dim_KMT_coupling_via_LS_reduction`
(`Helpers/TwoDimKMTFromOneDim.lean`) that R33-A intended to discharge it.

The headline finding is: **the two signatures are structurally
incompatible**, and the migration cannot be carried out by a
mechanical `:= via_LS_reduction` (or any thin adapter that projects
back to the original `Ω`).

---

## 1. Public theorem `two_dim_KMT_coupling` (524.lean:3751-3782)

Current signature, in the form left by R33-A:

```
theorem two_dim_KMT_coupling :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), IsRademacherSequence a →
      ∃ (Yplus Yminus : ℝ → Ω → ℝ) (Δ : ℕ → ℝ),
        (∀ u, Measurable (Yplus u))                                              -- (1)
      ∧ (∀ u, Measurable (Yminus u))                                             -- (2)
      ∧ (∀ n ≥ 1, Δ n ≤ Real.log (n + 1) / Real.sqrt n)                          -- (3)
      ∧ (∀ n ≥ 1, ∀ ω, ∀ u ≥ 0,
            |(1/√n) · ∑_{k ∈ Icc 1 n} a k ω · exp(-u·k/n) - Yplus u ω| ≤ Δ n)    -- (4) PLUS-coupling
      ∧ (∀ n ≥ 1, ∀ ω, ∀ u ≥ 0,
            |(1/√n) · ∑_{k ∈ Icc 1 n} a k ω · (-exp(-u/n))^k - Yminus u ω| ≤ Δ n) -- (5) MINUS-coupling
      ∧ IndepFun (fun ω u => Yplus u ω) (fun ω u => Yminus u ω) ℙ                -- (6) INDEP on Ω
      ∧ (∀ ω, Continuous (fun u => Yplus u ω))                                   -- (7)
      ∧ (∀ ω, Continuous (fun u => Yminus u ω))                                  -- (8)
      ∧ (∀ ε>0, ∀ᵐω, ∃ T₀, ∀ u ≥ T₀, |Yplus u ω| ≤ ε)                            -- (9)
      ∧ (∀ ε>0, ∀ᵐω, ∃ T₀, ∀ u ≥ T₀, |Yminus u ω| ≤ ε)                           -- (10)
  := by sorry  -- R33-A stub (524.lean:3782)
```

Key features of this signature:

* Output processes live on the **original `Ω`** with measure `ℙ`.
* Coupling (4)/(5) is the **full-sum form** with kernel `exp(-u·k/n)`
  (plus) and `(-exp(-u/n))^k` (minus).
* Δ-bound (3) is `log(n+1)/√n` (no factor of 2).
* IndepFun (6) is between `Yplus` and `Yminus` **on Ω, measure `ℙ`**.

The TAG'd in-body comment (524.lean:3773-3781) records that the
"full-sum-on-single-Ω + unconditional-IndepFun" form is mathematically
contradictory: a Rademacher sequence on a single space cannot give
*independent* full-sum plus and minus couplings unless the underlying
space is enlarged.

---

## 2. Helpers theorem `two_dim_KMT_coupling_via_LS_reduction`
   (`Helpers/TwoDimKMTFromOneDim.lean:556-583`)

Current signature, in the paper-faithful Form β shape that R33-A/B/C
have stabilised:

```
theorem two_dim_KMT_coupling_via_LS_reduction
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (a : ℕ → Ω → ℝ) (ha : Erdos524.IsRademacherSequence a) :
    ∃ (a' : ℕ → Ω × Ω → ℝ) (_ha' : Erdos524.IsRademacherSequence a')
      (Yplus Yminus : ℝ → Ω × Ω → ℝ) (Δ : ℕ → ℝ),
      (∀ u, Measurable (Yplus u)) ∧ (∀ u, Measurable (Yminus u))                -- (M1)/(M2)
    ∧ (∀ ω : Ω × Ω, Continuous (fun u => Yplus u ω))                            -- (C1)
    ∧ (∀ ω : Ω × Ω, Continuous (fun u => Yminus u ω))                           -- (C2)
    ∧ (∀ ε>0, ∀ᵐω : Ω × Ω, ∃ T₀, ∀ u ≥ T₀, |Yplus u ω| ≤ ε)                     -- (T1)
    ∧ (∀ ε>0, ∀ᵐω : Ω × Ω, ∃ T₀, ∀ u ≥ T₀, |Yminus u ω| ≤ ε)                    -- (T2)
    ∧ (∀ n ≥ 1, Δ n ≤ 2 * Real.log (n + 1) / Real.sqrt n)                       -- (D)
    ∧ (∀ n ≥ 1, ∀ ω : Ω × Ω, ∀ u ≥ 0,                                           -- (P) linear-combo PLUS
        |(1/√n) · ((∑ k ∈ Icc 1 n, a' (2k)   ω · kernel_even_plus u k n)
                 + (∑ k ∈ Icc 1 n, a' (2k+1) ω · kernel_even_plus u k n))
         - Yplus u ω| ≤ Δ n)
    ∧ (∀ n ≥ 1, ∀ ω : Ω × Ω, ∀ u ≥ 0,                                           -- (M) linear-combo MINUS
        |(1/√n) · ((∑ k ∈ Icc 1 n, a' (2k)   ω · kernel_even_plus u k n)
                 - (∑ k ∈ Icc 1 n, a' (2k+1) ω · kernel_even_plus u k n))
         - Yminus u ω| ≤ Δ n)
    ∧ IndepFun (fun ω : Ω × Ω u => Yplus u ω)                                    -- (I)
                (fun ω : Ω × Ω u => Yminus u ω)
                ((ℙ : Measure Ω).prod (ℙ : Measure Ω))
```

Body status (TwoDimKMTFromOneDim.lean:585-943):

* `?ha'.iIndepFun` (line 660): `iIndepFun` for the alternating-fst/snd
  family on `Ω × Ω`. Honest TAG'd sorry
  `R33-C-T2.5-iIndepFun-prod-mathlib-gap`. Mathlib gap — see TAG comment.
* `?indep` (line 943): `IndepFun (Yplus, Yminus) on (ℙ.prod ℙ)`. Honest
  TAG'd sorry `R33-C-T2.4-gaussian-uncorrelated-indep-mathlib-gap`.
  Forward direction `IndepFun → Cov = 0` exists in Mathlib but reverse
  direction (Cov = 0 + joint Gaussian → independent) does not.

All other sub-cases (`meas_p`/`meas_m`, `cont_p`/`cont_m`,
`decay_p`/`decay_m`, `Δ_bound`, `couple_p`/`couple_m`, the
`measurable`/`prob_pos`/`prob_neg` part of `ha'`) are **closed in full**.

`kernel_even_plus` (Helpers/TwoDimKMTFromOneDim.lean:154-155) is
defined as

```
kernel_even_plus u k m = Real.sqrt (1/2) * Real.exp (-u·k/m)
```

i.e. the original kernel `exp(-u·k/m)` rescaled by the constant
`√(1/2) ≈ 0.707`.

---

## 3. Signature mismatch — five concrete divergences

| #  | Aspect             | Public theorem                  | via_LS_reduction                                     |
|----|--------------------|---------------------------------|------------------------------------------------------|
| S1 | Sample space       | `Ω`, measure `ℙ`                | `Ω × Ω`, measure `ℙ.prod ℙ`                          |
| S2 | Δ-bound            | `log(n+1)/√n`                   | `2 · log(n+1)/√n` (FACTOR-OF-2 LARGER)               |
| S3 | Coupling form      | full sum `∑_{k∈[1,n]} a k ω`    | linear combo of `a' (2k) ω` and `a' (2k+1) ω`        |
| S4 | Kernel             | `exp(-u·k/n)` and `(-exp(-u/n))^k` | `kernel_even_plus = √(1/2)·exp(-u·k/n)` only     |
| S5 | Index range        | `k = 1..n` of original `a`      | `k = 1..n` mapped to `(2k)`, `(2k+1)` of lifted `a'` |

S1 and S3 together are the **structural blocker**. There is no
Ω-only adapter:

* **Conditional-expectation adapter** — define `Yplus_adapter u ω :=
  𝔼[Yplus_lifted u (ω, ·)]`. Loses pathwise continuity (C1) and
  pathwise tail decay (T1): conditional expectations of continuous
  processes are typically not continuous in `u` without further
  regularity assumptions.
* **Slice-fixing adapter** — pick a fixed `ω₀ : Ω` (via `Classical.choice`
  on the non-empty `Ω`), define `Yplus_adapter u ω := Yplus_lifted u (ω, ω₀)`.
  Preserves pathwise properties but **destroys IndepFun (6)**: with both
  marginals evaluated at the same `ω₀` slice, the two processes are
  measurable functions of the *same* fst-coordinate and are not in
  general independent.

S2 is also irreducible: the public Δ-bound is *tighter* than what
via_LS_reduction provides. Even if S1/S3/S4 were resolved, the public
theorem's Δ-bound would still fail (`log(n+1)/√n < 2·log(n+1)/√n`).

S4/S5 together: the public theorem's plus-coupling sums
`∑_{k=1..n} a k ω · exp(-u·k/n)`, indexing `k` over the original `a`,
whereas via_LS_reduction's plus-coupling involves
`(1/√(2n)) · (∑_{k=1..n} a (2k) ω.1 · exp(-u·k/n)
              + ∑_{k=1..n} a (2k+1) ω.2 · exp(-u·k/n))`.
The *index* `k` is reparametrised: original index `j ∈ [1, 2n+1]` is
mapped to lifted index `(2k)` or `(2k+1)` for `k ∈ [1, n]`.
The two sums are not algebraically equal — they cover overlapping
but distinct coefficient ranges.

**Conclusion.** No proof of the public theorem can be obtained by
applying `via_LS_reduction` and post-processing the witnesses on `Ω`.
The mathematically correct path is a **public API change**: the public
theorem's signature must move to Form β on `Ω × Ω` (matching
via_LS_reduction up to permutation of conjuncts), and downstream
consumers must absorb that change.

---

## 4. Four consumer call-sites — extraction patterns and downstream usage

### 4.1 Consumer A: `polynomial_sup_small_ball_upper` (524.lean:3933, call-site 3945)

```
obtain ⟨Yplus, _Yminus, Δ, hYp_meas, _hYm_meas, hΔ_bd, hKMT_p,
        _hKMT_m, _hIndep, _hYp_cont, _hYm_cont, _hYp_tail, _hYm_tail⟩ :=
  two_dim_KMT_coupling a ha
```

Fields used downstream:
* `Yplus` — the Gaussian limit, fed into `gao_li_wellner_small_ball_upper`.
* `hYp_meas` — measurability, threaded into `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`.
* `hΔ_bd` — converts `Δ n ≤ log(n+1)/√n`.
* `hKMT_p` — the full-sum plus-coupling, used in the event-containment
  step at 524.lean:3999-4061 to bound `|Yplus u ω| ≤ ε + Δ n` from
  `|(1/√n) ∑ a k ω · exp(-u·k/n)| ≤ ε`.

Migration verdict (under signature change): **(c) needs structural
rewrite**. The downstream uses of `hKMT_p` are written for the
full-sum form. Switching to Form β breaks the `endpoint_reparametrization`
chain that derives `|(1/√n) ∑ a k ω · exp(-u·k/n)| ≤ ε` from
`supNorm a n ω ≤ ε √n`.

Bare LOC budget: ~80–250 LOC (full-sum to linear-combo bridge work).

### 4.2 Consumer B: `polynomial_sup_small_ball_upper_uniform` (524.lean:4085, call-site 4100)

Identical extraction pattern and downstream usage to Consumer A. Same
verdict and LOC budget.

### 4.3 Consumer C: `polynomial_sup_small_ball_lower` (524.lean:4232, call-site 4248)

```
obtain ⟨Yplus, Yminus, Δ, hYp_meas, hYm_meas, hΔ_bd, hKMT_p, hKMT_m,
        hIndep, hYp_cont, hYm_cont, _hYp_tail, _hYm_tail⟩ :=
  two_dim_KMT_coupling a ha
```

Fields used downstream:
* `Yplus`, `Yminus` — both Gaussian limits, into GLW-lower.
* `hYp_meas`, `hYm_meas` — measurability hypotheses.
* `hΔ_bd` — Δ bound.
* `hKMT_p`, `hKMT_m` — both full-sum couplings, used in the
  reverse-containment step (524.lean:4475-4580) bounding
  `supNorm a n ω` via `endpoint_reparametrization` from the `Y±` events.
* `hIndep` — the `IndepFun (Yplus, Yminus)` on `ℙ` (Ω). Threaded into
  `hIndep.measure_inter_preimage_eq_mul` at 524.lean:4442 to factor
  `ℙ(E_p ∩ E_m) = ℙ(E_p) · ℙ(E_m)`.
* `hYp_cont`, `hYm_cont` — continuity, used in the rational-density
  reduction (524.lean:4380-4426) to make `E_p`, `E_m` Pi-preimages of
  measurable cylinders.

**Important:** The triangle bridge — i.e. the multiplicative
factorisation `ℙ(E_p ∩ E_m) = ℙ(E_p) · ℙ(E_m)` via independence — is
**already implemented** in the existing consumer code (524.lean:4337,
specifically the call to `hIndep.measure_inter_preimage_eq_mul` at
4442). The R33-D brief's phrasing "insert triangle bridge step" is
historical: that step was added in R33-A/B and is now in place.
What's missing is a non-stub `hIndep` from a non-stub
`two_dim_KMT_coupling`.

Migration verdict (under signature change): **(c) needs structural
rewrite**. The full-sum-to-Form-β bridge applies, plus the IndepFun
type changes from `…on ℙ` to `…on ℙ.prod ℙ` — affecting the
`measure_inter_preimage_eq_mul` invocation and the measure-mononicity
chain that closes `ℙ {ω : Ω | supNorm a n ω ≤ ε √n}` from the
`E_p ∩ E_m` event on the lifted space.

Bare LOC budget: ~150–350 LOC (lower bound's bridge is heavier than
upper because of the joint-event reverse containment).

### 4.4 Consumer D: `polynomial_sup_small_ball_lower_uniform` (524.lean:4608, call-site 4624)

Identical extraction pattern and downstream usage to Consumer C.
Same verdict and LOC budget.

---

## 5. Actual scope of consumer migration vs R33-D brief

The R33-D brief estimates ~80 LOC for upper consumers (T2.2) and
~120 LOC for lower consumers (T2.3), under the assumption that the
migration is "kernel-call updates" plus "triangle bridge insertion".

The audit shows:

* The triangle bridge is **already in place** (R33-A/B work).
* The "kernel-call update" framing understates the work: full-sum
  → linear-combo is not a renaming but a **change in the underlying
  algebraic identity** that the consumer's `endpoint_reparametrization`
  chain depends on.
* The space change (Ω → Ω × Ω) cascades into the IndepFun type and the
  measure-monotonicity argument that closes `ℙ_Ω {…} ≤ …`.

Realistic per-consumer LOC budget for a full migration: **150–350 LOC
each**, totalling 600–1400 LOC for all four. Beyond the R33-D round
budget.

---

## 6. R33-D delivery plan (committed at end of T1.1)

Given the structural reality:

1. **T2.1 — change public signature to Form β on `Ω × Ω`**, body
   `:= two_dim_KMT_coupling_via_LS_reduction` after a small permutation
   of conjuncts. Concrete Lean code modification at 524.lean:3751-3782.

2. **T2.2/T2.3 — consumer migration as TAG'd sorry-with-diagnostic.**
   Rewrite each consumer's `obtain` pattern to match the new
   signature (lifted `a'`, Form β fields). Where the downstream
   full-sum-based argument requires the bridge, land an honest
   sorry-with-TAG citing this audit (R33-D-T1.1) by file:line.

3. **T2.4 — phase-shift correction.** Calc lemma in Helpers verifying
   `(-exp(-u/n))^k = (-1)^k · exp(-u·k/n)` and the corresponding
   `Y_e − Y_o` ↔ minus-kernel identity. Real Lean code, ~20-40 LOC,
   no sub-sorries.

4. **T2.5 — ENat blocker doc.** Append R33-D status to
   `Helpers/AxiomFoundationAudit.md`.

This delivery is honest under the brief's skin-in-the-game spec:
T2.* land as Lean code modifications (not plan docs), with TAG'd
sorries citing concrete file:line bridge gaps where the structural
work exceeds the round budget. Builds will not verify against
524.lean end-to-end (ENat blocker, orthogonal), but the migration
deliverables — signature change, obtain-pattern rewrite, phase-shift
calc — are concrete code edits.
