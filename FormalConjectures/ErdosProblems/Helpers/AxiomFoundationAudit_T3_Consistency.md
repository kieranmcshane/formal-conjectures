# R32 / T3.1 — Internal-consistency hypothesis test per axiom

For each axiom and the now-theorem `two_dim_KMT_coupling`, we identify
pairs / triples of conjuncts that could be in tension, then state a
simultaneous-satisfiability hypothesis. The output is one of three
verdicts:

- **CLEAN** — no flags found; conjuncts are simultaneously satisfiable
  on standard probabilistic foundations.
- **NEEDS_GROK** — at least one flagged conjunct pair where simultaneous
  satisfiability is plausible but non-trivial; Grok validation requested
  in T4.1.
- **CONFIRMED_CONTRADICTORY** — flagged conjunct pair is provably
  contradictory; documented separately.

The framework is the R31 anti-pattern checklist (independence +
shared-input approximation, tail decay + boundedness, coupling rate +
uniformity, continuous paths + non-trivial joint distribution,
existential-conjunct simultaneous satisfiability).

## A1 — `Cp_T_explicit_pointwise_axiom`

```
∃ K : ℝ, 0 ≤ K ∧
  ∀ T : ℕ, 1 ≤ T → Cp_T_explicit T ≤ ENNReal.ofReal (K / ((T : ℝ) + 1) ^ (3 / 2 : ℝ))
```

**Conjuncts.**

1. `0 ≤ K`
2. `∀ T ≥ 1, Cp_T_explicit T ≤ K / (T+1)^(3/2)` (ENNReal-cast).

`Cp_T_explicit T` is a real-valued (ENNReal) deterministic quantity
defined upstream as the chaining-moment constant per the brownian-motion
package's `constL` form, multiplied by `M_T = 1/(2T³)`. It is finite for
all `T ≥ 1` (verified by R20-R26 chain of constructive bounds). The bound
asserted is that for some constant `K`, the multiplied form is dominated
by `K / (T+1)^{3/2}`.

**Conjunct-pair analysis.**

- Pair (1, 2): `K ≥ 0` and the bound. No tension: even `K = 0` leaves
  the bound asserting `Cp_T_explicit T = 0`, which is consistent (just
  uninteresting). For `K > 0`, the bound is the asymptotic R23/R26/R27
  Grok-validated form, with finite explicit constants assembled from
  pre-existing summable series (`S₀ = ∑ 2^{-k/2}`, `S_k² = ∑ k² ·
  2^{-k/2}`). No internal contradiction.

- No independence-vs-shared-input conjunct (this is a deterministic
  asymptotic bound, no random variables).
- No coupling rate (no random object).
- No tail-decay-vs-bounded conjunct.
- No path continuity.
- The existential is over `K` only; both conjuncts are trivially
  simultaneously satisfiable (take `K` large enough).

**Verdict: CLEAN.**

Reason: deterministic asymptotic upper bound with finite explicit
constants. The Grok validation at R23/R27 was for the math content of
the bound (i.e., that `Cp_T_explicit T = O((T+1)^{-3/2})`), and that
question is answered by upstream chaining-moment arithmetic — there is
no separate "internal-consistency" gap. The axiom acts as a shortcut
around the multi-step constL-unfold + AM-QM + log²→√ chain (which has
documented sub-sorries C1-C4 in T1.1 that are dead code).

## A2 — `one_dim_KMT_coupling`

```
∀ {Ω} [MeasureSpace Ω] [IsProbabilityMeasure ℙ]
  (a : ℕ → Ω → ℝ), IsRademacherSequence a →
  ∃ (B : ℕ → Ω → ℝ) (C : ℝ),
    0 < C ∧
    (∀ n, Measurable (B n)) ∧
    (∀ n ≥ 1, ∀ ω, |∑_{k=1..n} a_k(ω) - B_n(ω)| ≤ C · log(n + 1))
```

**Conjuncts.**

1. `0 < C`
2. `∀ n, Measurable (B n)`
3. `∀ n ≥ 1, ∀ ω, |S_n(ω) - B_n(ω)| ≤ C · log(n + 1)` (uniform-in-ω,
   not "almost-sure with C(ω) < ∞").

**Conjunct-pair analysis.**

- Pair (1, 3): `C > 0` and the bound — trivially satisfiable jointly
  (take `C` large enough to absorb the actual KMT coupling constant).
- Pair (2, 3): `B_n` measurable at each `n` and the uniform-ω bound.
  Standard: any KMT coupling produces a Brownian-motion-like sequence
  with measurable marginals.
- **Hypothesis test for "uniform-in-ω".** The textbook KMT statement is
  almost-sure with `C(ω) < ∞`, not uniform-in-ω with deterministic `C`.
  Could the uniform-in-ω form be unsatisfiable?

  Sub-analysis: For any fixed `n`, `S_n(ω) - B_n(ω)` is a real-valued
  random variable. The set `{ω : |S_n(ω) - B_n(ω)| > C·log(n+1)}` has
  positive ℙ-measure for *some* finite `C` if and only if the variable
  is not bounded by `C·log(n+1)` a.s. The textbook KMT a.s. statement
  produces an `n`-uniform `C(ω)` finite a.s.; this can fail to be
  *uniform across ω* (the random variable `C(ω)` may be unbounded over
  Ω). But the axiom says "there exists `C` deterministic" — which is a
  statement about the *coupling*, not about `C(ω)` of the textbook.

  **Standard resolution (KMT literature).** A uniform-ω version is
  achievable by *modifying* the coupling on a measure-zero set: any
  Brownian motion `B'` agreeing with `B` a.s. and constructed to absorb
  the `C(ω)`-blowup events can be made deterministic-bounded if Ω is
  rich enough (e.g., any Polish probability space supporting an
  auxiliary independent random variable). This is a measure-theoretic
  augmentation that does not change the law of the coupling.

  Verdict on this sub-question: uniform-in-ω is a stronger statement
  than textbook KMT but is *consistent* (achievable by modification on
  measure-zero set) — not contradictory.

- No path-continuity conjunct (the axiom only asserts `B_n` for natural
  `n`, not a continuous-time `B(t)`).
- No tail-decay conjunct.
- No independence-vs-shared-input issue (single coupling, single `B`,
  single `(a_k)`).

**Verdict: CLEAN** (with one minor flag for documentation purposes).

The flag is that the axiom statement (uniform-in-ω) is strictly stronger
than the textbook KMT a.s. form, but the gap is bridged by a standard
measure-theoretic augmentation. No internal contradiction.

(Methodological note: A2 is dormant in the current `r30-finish` build —
no Lean-level consumer per T2.1. So even a hidden contradiction would
have zero blast radius. The CLEAN verdict here is for completeness.)

## A3 — `kmt_aided_gaussian_process`

```
axiom kmt_aided_gaussian_process
    (kernel : ℝ → ℕ → ℕ → ℝ)
    (_kernel_bound : ∀ u, 0 ≤ u → ∀ k n, |kernel u k n| ≤ 1)
    {Ω} [MeasureSpace Ω] [IsProbabilityMeasure ℙ]
    (a : ℕ → Ω → ℝ) (_ha : IsRademacherSequence a) :
    ∃ (Y : ℝ → Ω → ℝ),
      (∀ u, Measurable (Y u)) ∧
      (∀ ω, Continuous (fun u : ℝ => Y u ω)) ∧
      (∀ ε > 0, ∀ᵐ ω, ∃ T₀ : ℝ, ∀ u ≥ T₀, |Y u ω| ≤ ε) ∧
      (∀ n ≥ 1, ∀ ω, ∀ u ≥ 0,
        |((1/√n) · ∑_{k=1..n} a_k(ω) · kernel(u, k, n)) - Y u ω| ≤ log(n+1)/√n)
```

**Conjuncts (single-call).**

1. Measurability: `∀ u, Measurable (Y u)`
2. Sample-path continuity: `∀ ω, Continuous (Y · ω)`
3. Tail decay: `∀ ε > 0, ∀ᵐ ω, ∃ T₀, ∀ u ≥ T₀, |Y u ω| ≤ ε`
4. Coupling: `∀ n ≥ 1, ∀ ω, ∀ u ≥ 0, |(1/√n) Σ a_k · kernel(u,k,n) - Y u ω| ≤ log(n+1)/√n`

**Single-call conjunct analysis.**

- Pair (1, 4): measurability + coupling. Standard: any explicit
  construction of `Y u` as a measurable function on `Ω` with the
  coupling bound is straightforward via Itô-isometry construction
  + measurable selection.
- Pair (2, 4): sample-path continuity + coupling. Coupling is stated
  uniformly in `u ≥ 0` and `ω`, which is *strictly stronger* than
  almost-everywhere-in-ω; the path continuity is also "for all ω", not
  almost-all. The combined assertion is that `Y(·, ω)` is jointly
  continuous in `u` for **every** ω, *and* couples uniformly. This is a
  uniform-in-ω statement (analogous to A2's uniform-in-ω). Same
  measure-theoretic-augmentation resolution applies — feasible by
  modification on measure-zero sets.
- Pair (3, 4): tail decay + coupling. Tail decay says `Y u → 0` as
  `u → ∞` (almost surely). Coupling says `Y u` is close to a
  partial-sum-of-Rademacher-times-kernel(u,k,n). For the axiom's two
  intended kernels (`exp(-uk/n)` and `(-exp(-u/n))^k`), as `u → ∞` the
  partial sum tends to 0 (each term has a factor that decays in `u`).
  So both `Y` and the partial sum tend to 0, consistent.
  - **However:** for an arbitrary `kernel` satisfying only
    `|kernel(u,k,n)| ≤ 1`, the partial sum need NOT tend to 0 as
    `u → ∞`. For instance, take `kernel(u,k,n) := 1` constantly. Then
    the partial sum is `(1/√n) · ∑_{k=1..n} a_k(ω)` (independent of
    `u`), which is a non-zero ω-dependent constant. The axiom asserts
    `Y u → 0` a.s. as `u → ∞`, which forces
    `|(1/√n) · ∑_{k=1..n} a_k(ω) - 0| ≤ log(n+1)/√n + ε` for
    sufficiently large `u`, ω-a.s. But the LHS is independent of `u`
    and equals `|S_n(ω)/√n|`, which by CLT is ≈ N(0, 1) — *not*
    bounded by `log(n+1)/√n` for any fixed `n` ≥ some threshold. So
    the existence claim **fails** for the constant-1 kernel.
- This is a **conjunct tension** with the axiom's hypothesis: the
  hypothesis `|kernel| ≤ 1` is too weak to support both tail decay and
  uniform coupling.

**The R30 docstring acknowledges this.** From
`Helpers/StochasticProcessAxiom.lean:40-54`:

> "The axiom is then *technically* stronger than its hypothesis (a
> constant-1 kernel satisfies the hypothesis but its partial sums do
> not exhibit tail decay), but the scope of the axiom is restricted by
> the consumer surface: only the LS-reduction in
> `Helpers/TwoDimKMTFromOneDim.lean` invokes it, and only with the two
> specific kernels for which the conclusions hold mathematically (Itô
> isometry + Kolmogorov–Chentsov + Borell)."

**This is a documented self-acknowledged form of "axiom is unsatisfiable
for some hypothesis-satisfying inputs".** The same anti-pattern as R31:
an axiom whose statement is strictly stronger than what its mathematical
content can deliver, justified only by "consumers don't probe the bad
inputs".

**Multi-call conjunct analysis (the load-bearing question).**

The 2D KMT chain in `TwoDimKMTFromOneDim.lean` invokes the axiom
**twice** (once for Yplus kernel, once for Yminus kernel), with the
*same* `(a, ha)`. The two calls produce `Y_p` and `Y_m`. The axiom
says nothing about the joint distribution `(Y_p, Y_m)` — it produces
two independent existential witnesses, one per call.

- Are `(Y_p, Y_m)` independent? Cannot be determined from the axiom's
  conjuncts alone. The axiom is silent on cross-call correlation.
- Could two existential witnesses chosen simultaneously be made
  independent? In general, **no** — the coupling conjunct ties each `Y`
  deterministically (modulo `log(n+1)/√n`-error) to the **same**
  partial-sum process `(1/√n) Σ a_k · kernel(·,k,n)`. The two partial
  sums (Yplus-kernel and Yminus-kernel) are functions of the same `(a_k)`
  and so are themselves correlated. This forces nonzero
  cross-covariance between `Y_p` and `Y_m` at sub-CLT error rate.
- This is the R31-flagged tension: independence + shared-input
  approximation at sub-CLT error rate is mathematically impossible
  when the two approximated quantities are non-trivially correlated as
  functions of the shared input.

**Conjunct pair flagged: A3-applied-twice + cross-call independence
(invoked downstream as the `IndepFun` hypothesis of `theorem
two_dim_KMT_coupling`).**

The single-axiom-call statement is internally satisfiable (modulo the
"hypothesis too weak" caveat for tail-decay-vs-coupling); the
**two-call-with-shared-input + downstream-independence-claim** is the
contradictory pattern. The axiom itself does not assert independence,
but its consumers (specifically the chain into `theorem
two_dim_KMT_coupling`) impose independence **in addition**, and that
combined claim is unsatisfiable.

**Verdict: NEEDS_GROK** for two distinct sub-questions:

(α) Is the single-call statement *as written* (with the `|kernel|≤1`
hypothesis broad enough to admit constant-1 kernels) satisfiable? The
docstring acknowledges no, but only as a "consumer-surface restricted"
caveat. R33 should ideally tighten the hypothesis to a kernel class for
which the conclusions are simultaneously achievable (e.g., add a tail-
decay hypothesis on the kernel itself, or a Hilbert-Schmidt-norm
hypothesis on the integral operator).

(β) Is the multi-call form (two applications with shared input,
yielding two `Y`s with claimed independence) achievable by a single
consistent extension of the axiom? Almost certainly not — this is the
R31 contradiction in fresh form. Grok should be asked specifically:
*can the axiom be reformulated so that two simultaneous applications
yield jointly-independent `(Y_p, Y_m)` while still each individually
approximating its kernel-filtered partial sum at* `O(log n / √n)`*
*rate?* The answer is expected to be no without a rate degradation
(e.g., to `O(1/n^{1/2-η})` for some `η > 0`), which would require
rewriting the four downstream consumers in 524.lean.

## A4 — `theorem two_dim_KMT_coupling` (R30, file `524.lean:3741`, body via R30 LS reduction with T3.4 sorry B1)

(Treating the theorem's *statement* as if it were an axiom, since R31
already established the statement is unsatisfiable in the joint form
required.)

```
∃ Yplus Yminus (Δ : ℕ → ℝ),
  (measurability conjuncts) ∧
  (Δ-bound: Δ n ≤ log(n+1)/√n) ∧
  (Yplus coupling: |(1/√n) Σ a_k · exp(-uk/n) - Yplus u| ≤ Δ n, full sum) ∧
  (Yminus coupling: |(1/√n) Σ a_k · (-exp(-u/n))^k - Yminus u| ≤ Δ n, full sum) ∧
  IndepFun (Yplus) (Yminus) ∧
  (continuity Yplus / Yminus) ∧
  (tail decay Yplus / Yminus)
```

**Flagged conjunct triple: full-sum Yplus coupling + full-sum Yminus
coupling + IndepFun(Yplus, Yminus).**

R31 audit established: at the sub-CLT error rate `Δ n = O(log n / √n)`,
each of `Yplus(u, ω)` and `Yminus(u, ω)` is determined up to vanishing
error by the **same input sequence** `(a_k(ω))_{k=1..n}`. Their joint
distribution is therefore deterministically tied to `(a_k)` and they
have nonzero cross-covariance (the cross-term `E[Yplus(u) · Yminus(v)]`
must equal `(1/n) Σ_{k=1..n} exp(-uk/n) · (-exp(-v/n))^k + O(...)`,
which is generically nonzero). Independence in the sense of `IndepFun`
implies zero cross-covariance, contradicting the coupling.

**Verdict: CONFIRMED_CONTRADICTORY** (per R31 audit, restated).

**Downstream impact (per T2.1).**

- Two consumers (524.lean:3926, 4081) use only `hKMT_p` from the tuple,
  not `hIndep`. Their conclusions hold under a decoupled-form weakening
  of the theorem (no `IndepFun` conjunct).
- Two consumers (524.lean:4229, 4605) use `hIndep` to get the
  two-factor exponent `-2·glw.lower`. **Their conclusions are vacuous
  under the contradictory statement** and require either
  (i) a corrected-form theorem with conditional / partitioned
  independence, or (ii) a rewrite to derive `2·glw.lower` from a
  different mechanism (e.g., Anderson + small-ball product on disjoint
  scales).

## B1 — `LS_independent_yplus_yminus` (live sorry on the active 524 chain)

```
private theorem LS_independent_yplus_yminus
    (Yplus Yminus : ℝ → Ω → ℝ) :
    IndepFun (fun ω u => Yplus u ω) (fun ω u => Yminus u ω) ℙ := by
  sorry
```

**Conjunct (single).**

The IndepFun claim, where `Yplus` and `Yminus` are arbitrary inputs to
the lemma but are bound at the call site (line 283) to the two
`LS_kernel_coupling` outputs from A3 with the Yplus and Yminus kernels.

**Hypothesis-shape analysis.**

The lemma signature does not constrain `Yplus` / `Yminus` at all
(they are universally quantified over arbitrary `ℝ → Ω → ℝ` functions).
Trivially, "`IndepFun(Yplus, Yminus)` for all `Yplus, Yminus`" is
**false** (take `Yplus = Yminus = constant ≠ 0`). The lemma is
mathematically false as stated.

The author intent (per docstring) was to use the lemma at one specific
call site where `Yplus`, `Yminus` come from A3-applied-twice on
disjoint sub-sequences (even/odd Rademacher decoupling). But the
lemma signature does not encode this — it is too universal.

**Verdict: CONFIRMED_CONTRADICTORY** (the universal form is false; the
intended specialised form is what R31 confirmed contradictory in the
shared-input case).

**Note for R33.** The fix is to either:
(i) tighten the lemma signature to require `Yplus` and `Yminus` come
    from independent sub-σ-algebras (e.g., parameterise by two
    sub-sequences `a_e`, `a_o` and pass through A3 separately on each
    — this is the R31 even/odd infrastructure), OR
(ii) abandon the universal-IndepFun claim and use a partitioned/
     disjoint-block independence statement instead.

## B2 — `IsRademacherSequence_a_even` / B3 — `_a_odd`

```
private lemma IsRademacherSequence_a_even (a) (ha : IsRademacherSequence a) :
    IsRademacherSequence (a_even a)
```

**Conjuncts** (4-tuple unfolded from `IsRademacherSequence`):
- `iIndepFun (a_even a)` — sorry
- `Measurable (a_even a k)` — closed (specialisation)
- `prob_pos (a_even a k)` — closed (specialisation)
- `prob_neg (a_even a k)` — closed (specialisation)

**Conjunct analysis.** The `iIndepFun`-on-sub-sequence sorry is a
standard Mathlib-mechanical fact: `iIndepFun` is closed under
post-composition with an injective `ℕ → ℕ`. There is no internal
contradiction; this is upstream-pending API work.

**Verdict: CLEAN** (the sorry is mechanical, not foundational).

## Summary

| Axiom / theorem-with-sorry | Verdict | Flag(s) |
|----------------------------|---------|---------|
| A1 `Cp_T_explicit_pointwise_axiom` | **CLEAN** | — |
| A2 `one_dim_KMT_coupling` | **CLEAN** | minor: uniform-in-ω stronger than textbook KMT, bridged by measure-zero modification |
| A3 `kmt_aided_gaussian_process` | **NEEDS_GROK** | (α) hypothesis admits inputs (constant kernels) for which axiom conclusions are unsatisfiable; (β) two-call form with shared input + downstream independence is the R31 contradiction in fresh form |
| A4 `theorem two_dim_KMT_coupling` (statement) | **CONFIRMED_CONTRADICTORY** | per R31; full-sum coupling + IndepFun(Yplus, Yminus) at sub-CLT rate |
| B1 `LS_independent_yplus_yminus` | **CONFIRMED_CONTRADICTORY** | universal IndepFun claim is false in full generality; intended specialised form inherits R31 contradiction |
| B2 / B3 `IsRademacherSequence_a_{even,odd}` | **CLEAN** | sub-sequence iIndepFun closure, mechanical Mathlib gap |

**Anticipated-vs-actual pre-projection comparison (Cowork-honest).**

| Axiom | Cowork pre-projection | Actual T3.1 verdict |
|-------|------------------------|---------------------|
| `one_dim_KMT_coupling` | likely CLEAN | CLEAN ✓ |
| `Cp_T_explicit_pointwise_axiom` | likely CLEAN | CLEAN ✓ |
| `kmt_aided_gaussian_process` | likely NEEDS_GROK | NEEDS_GROK ✓ — but T3.1 surfaced **two** distinct sub-issues (single-call hypothesis-too-weak + multi-call independence), not one |
| `two_dim_KMT_coupling` | CONFIRMED_CONTRADICTORY | CONFIRMED_CONTRADICTORY ✓ |
| Other findings | "may surface helper-level constructs" | one new finding: B1 universal-IndepFun statement is false even in the absence of the multi-call issue (R32-novel) |

The Brier-honest realisation: A3 has TWO independent foundational
flags, not one. The single-call hypothesis-too-weak is documented but
under-emphasised in the project's framing; R33 should ideally fix
both, not just the multi-call independence.
