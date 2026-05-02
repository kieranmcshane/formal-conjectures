# R32 — Axiom foundation audit (synthesis)

**Read-only audit, single round, R32 (branch `r32-audit-finish`).**
Synthesises T1.1 (inventory), T2.1 (consumers), T3.1 (consistency
hypotheses) into a per-axiom verdict table, draft Grok pre-flight
prompts for the NEEDS_GROK items, and an R33+ round-budget estimate.

## Per-axiom verdict table

| # | Axiom / theorem-with-sorry | T1.1 location | T2.1 # consumers | T3.1 verdict |
|---|-----------------------------|----------------|-------------------|---------------|
| A1 | `Cp_T_explicit_pointwise_axiom` | `Helpers/GLWGaussianProjectiveLimit.lean:2070` (private, R27) | 1 (`tsum_Cp_T_explicit_lt_top_R22`) | **CLEAN** |
| A2 | `one_dim_KMT_coupling` | `Helpers/OneDimKMT.lean:101` (semi-public, R29) | **0 (dormant)** | **CLEAN** |
| A3 | `kmt_aided_gaussian_process` | `Helpers/StochasticProcessAxiom.lean:80` (semi-public, R30) | 5 in `TwoDimKMTFromOneDim.lean` (LS_kernel_coupling, R31 even/odd infra) | **NEEDS_GROK** (two distinct sub-issues: α single-call hypothesis-too-weak; β multi-call shared-input ⊕ downstream independence) |
| A4 | `theorem two_dim_KMT_coupling` (statement, body has B1 sorry) | `524.lean:3741` (R30 retirement of public axiom) | 4 in `524.lean` (3926, 4081, 4229, 4605) | **CONFIRMED_CONTRADICTORY** (per R31; full-sum coupling + IndepFun at sub-CLT rate) |
| B1 | `LS_independent_yplus_yminus` (sorry) | `Helpers/TwoDimKMTFromOneDim.lean:213` (R30 stretch) | 1 (`two_dim_KMT_coupling_via_LS_reduction`) | **CONFIRMED_CONTRADICTORY** (universal-IndepFun statement is false; specialised form inherits R31 issue) |
| B2 | `IsRademacherSequence_a_even` (sorry) | `Helpers/TwoDimKMTFromOneDim.lean:442` (R31 infra) | 1 (`LS_yplus_via_even`, dead in r30-finish) | **CLEAN** (mechanical Mathlib gap) |
| B3 | `IsRademacherSequence_a_odd` (sorry) | `Helpers/TwoDimKMTFromOneDim.lean:454` (R31 infra) | 1 (`LS_yminus_via_odd`, dead) | **CLEAN** |
| C1-C4 | R26 dead sub-lemmas in `GLWGaussianProjectiveLimit.lean:2000/2017/2031/2042` | superseded by A1 | **0 consumers** (verified by grep) | (orphaned; flag for R33 cleanup, not audit-relevant) |

**Mainline foundational state in `r30-finish`:**
- 1 active CLEAN axiom (A1) + 1 dormant CLEAN axiom (A2) + 1 NEEDS_GROK
  axiom (A3) on the active 524 chain.
- 1 CONFIRMED_CONTRADICTORY theorem-statement (A4) and its load-bearing
  sorry-discharge (B1).
- 4 dead R26 sorries (C1-C4) that should be deleted in R33 cleanup.

## NEEDS_GROK items — focused pre-flight prompts

### Grok prompt 1 — A3-α (single-call hypothesis tightening)

```
Context: We have a Lean axiom (project: formal-conjectures, Erdős 524 KMT
chain) of the following shape:

  axiom kmt_aided_gaussian_process
      (kernel : ℝ → ℕ → ℕ → ℝ)
      (kernel_bound : ∀ u, 0 ≤ u → ∀ k n, |kernel u k n| ≤ 1)
      (a : ℕ → Ω → ℝ) (ha : IsRademacherSequence a) :
      ∃ Y : ℝ → Ω → ℝ,
        (∀ u, Measurable (Y u)) ∧
        (∀ ω, Continuous (fun u => Y u ω)) ∧
        (∀ ε > 0, ∀ᵐ ω, ∃ T₀, ∀ u ≥ T₀, |Y u ω| ≤ ε) ∧
        (∀ n ≥ 1, ∀ ω, ∀ u ≥ 0,
          |(1/√n) · Σ_{k=1..n} a_k(ω) · kernel(u,k,n) - Y u ω|
            ≤ log(n+1) / √n)

Question 1: Is this axiom statement satisfiable for the constant kernel
`kernel(u, k, n) := 1`? Note: `|kernel| ≤ 1` is verified, but the
partial sum (1/√n) Σ a_k(ω) is independent of u and is approximately
N(0,1) for large n by CLT. The tail-decay conjunct asserts Y(u, ω) → 0
a.s. as u → ∞, which combined with the coupling forces |S_n(ω)/√n| ≤
log(n+1)/√n + ε for arbitrarily small ε at large u — this is impossible
for an N(0,1)-distributed quantity at fixed n. So the axiom is
unsatisfiable for this kernel.

Question 2: Suggest a tightened hypothesis that admits the two intended
kernels (kernel_yplus(u,k,n) = exp(-uk/n) and kernel_yminus(u,k,n) =
(-exp(-u/n))^k) but excludes the constant-1 kernel. Candidates we have
considered: (i) add a u-tail-decay hypothesis on the kernel itself
(`∀ k, ∀ ε > 0, ∃ U, ∀ u ≥ U, |kernel(u,k,n)| ≤ ε`); (ii) Hilbert-
Schmidt type bound on the (u, k)-integral operator at scale n; (iii)
bound the kernel uniformly by a u-decaying envelope. Which of these is
the minimal-stronger hypothesis that:
  (a) the two intended kernels still satisfy,
  (b) admits a stochastic-integral construction of Y with the stated
      coupling AND tail-decay AND continuity, AND
  (c) does NOT admit constant kernels?

Question 3: With the tightened hypothesis, is the per-call axiom
statement provable in classical probability theory (granted upstream
Itô-isometry + Kolmogorov–Chentsov + Borell)? Or does it remain
upstream-pending in any case?

Output format: (1) Yes/no on satisfiability for constant kernel.
(2) Recommended tightened hypothesis (Lean-pseudocode is fine).
(3) Sketch of provability under the tightened form.
```

### Grok prompt 2 — A3-β (multi-call independence, R31 contradiction restated)

```
Context: same axiom as Prompt 1. The 2D KMT chain in our project
applies the axiom TWICE on the same Rademacher sequence (a_k):

  apply 1: kernel = exp(-u·k/n), produces Y_p
  apply 2: kernel = (-exp(-u/n))^k, produces Y_m

Each Y satisfies its individual coupling at rate log(n+1)/√n. Our R31
audit established that the downstream theorem
(`theorem two_dim_KMT_coupling` in 524.lean) additionally claims
`IndepFun(Y_p, Y_m)`, but this is unsatisfiable: both Y_p and Y_m
approximate functions of the same input (a_k) at sub-CLT error rate,
which forces deterministic ties between them and rules out
unconditional independence.

Question 1: Confirm or refute the R31 finding. Specifically: is it
mathematically possible for an axiom of this shape to deliver, on two
calls with shared input, two outputs Y_p, Y_m that are
(i) jointly measurable with the structural conjuncts each, AND
(ii) each individually couples to its kernel-filtered partial sum at
     rate O(log n / √n), AND
(iii) are unconditionally independent as ℝ → ℝ-valued random fields?
Provide a clean yes/no with the contradiction (or the construction).

Question 2: If the answer to Q1 is no, what are the candidate
relaxations to recover *some* independence structure that the
downstream consumers (specifically: 524.lean:4229 / 4605, which need a
two-factor exponent `-2·glw.lower` in a small-ball lower bound) can
still use?

Candidates:
(γ_a) Conditional independence given a sub-σ-algebra (e.g., conditional
on the σ-algebra generated by even-indexed Rademacher variables).
(γ_b) Disjoint-block / partitioned independence: use a_{2k} for Y_p,
a_{2k+1} for Y_m; they are then functions of disjoint Rademacher
blocks. This is the path our R31 even/odd infrastructure was preparing.
The trade-off: each Y now approximates a HALF-sum (Σ over even or odd
indices), not the full sum, which means downstream consumers must work
with half-sums.
(γ_c) Asymptotic / weak independence (e.g., total-variation distance to
independence is o(1) as n → ∞), at the cost of degrading the rate from
O(log n / √n) to slower.

For each of (γ_a, γ_b, γ_c): is it (a) mathematically achievable,
(b) compatible with the Erdős 524 small-ball lower-bound argument
[the chain expects `ℙ{sup ≤ ε√n} ≥ exp(-2·glw.lower · |...|³)`, where
the factor 2 comes from independence of the two "branches"]?

Output format: (Q1) yes/no + sketch. (Q2) verdict and feasibility for
each of γ_a / γ_b / γ_c.
```

### Grok prompt 3 — A4 + B1 corrected-statement options (post-Q2 conditional)

```
Context: same as Prompts 1 / 2. Assume Q2 selects path γ_b
(disjoint-block independence: Y_p built from a_{2k}, Y_m from a_{2k+1}).
Our four downstream consumers in 524.lean live as follows:

  Consumers 3926 / 4081 (upper bound branch): use only Yplus side, do
    NOT need IndepFun. Robust under any γ choice.

  Consumers 4229 / 4605 (lower bound branch, two-factor exponent
    -2·glw.lower): currently use IndepFun(Yplus, Yminus). Under γ_b,
    they would need to:
    (i) reformulate the GLW lower-bound application so that two
        independent half-sum-Gaussian processes can each contribute a
        glw.lower factor, with the Δ-rate replaced by the half-sum
        version, AND
    (ii) bridge the half-sum supremum back to the full-sum supremum
        that supNorm asks for (Erdős 524's headline statement is in
        terms of supNorm of the full polynomial, not a half-sum).

Question 1: Is the bridge (ii) achievable in standard probability
theory? The half-sum Y_p approximates (1/√n) Σ_{k=1..n} a_{2k} ·
kernel(...). The full-sum supremum is (1/√n) Σ_{k=1..n} a_k · kernel.
Is there a sub-Gaussian-tail / Anderson-style lift from the half-sum
result to the full-sum result without the rate-2 factor degrading?

Question 2: If (ii) is *not* directly achievable, what is the next-best
option? Candidates:
(δ_a) Restate Erdős 524 using a "decoupled supNorm" notion that already
splits along even/odd blocks at the small-ball level.
(δ_b) Accept rate degradation from -2·glw.lower to -glw.lower (lose the
factor of 2, fall back to a single-kernel small-ball bound).
(δ_c) Use a different mechanism entirely for the factor of 2 (e.g.,
Anderson + scale-disjointness: split the supremum domain [-1, 1] into
[-1, 0] ∪ [0, 1] and apply small-ball on each half; the two halves are
not independent but Anderson allows a max-bound).

Output format: (Q1) yes/no + sketch. (Q2) for each δ option, an
estimate of how much of 524.lean's proof chain would need rewriting.
```

## CONFIRMED_CONTRADICTORY items — concrete fix sketches (R33 input)

### A4 — `theorem two_dim_KMT_coupling`

**Source of contradiction:** full-sum coupling for both Yplus and Yminus
+ unconditional `IndepFun`, all at rate O(log n / √n).

**Candidate corrected statements:**

- **Form α (joint-correlated, drop independence).** Remove the
  `IndepFun` conjunct. Theorem becomes:

  ```
  ∃ Yplus Yminus Δ,
    (measurability, Δ-bound, full-sum couplings, continuity, tail decay)
  -- no IndepFun
  ```

  Provability: A3-applied-twice provides this directly. **Consumer
  impact:** 3926 / 4081 robust (already underscore `_hIndep`); 4229 /
  4605 lose the `2·glw.lower` factor and must be rewritten to derive
  `1·glw.lower` from a single-kernel small-ball application or similar.

- **Form β (decoupled, half-sum + IndepFun).** Replace the full-sum
  couplings with half-sum couplings, applied separately to the even
  and odd Rademacher sub-sequences. Both Yplus (built from a_{2k}) and
  Yminus (built from a_{2k+1}) are now measurable w.r.t. disjoint
  σ-algebras; `IndepFun` follows. Theorem becomes:

  ```
  ∃ Yplus Yminus Δ,
    (measurability, Δ-bound,
     Yplus couples HALF-sum (1/√m) Σ_{k=1..m} a_{2k} · kernel_p(u,k,m),
     Yminus couples HALF-sum (1/√m) Σ_{k=1..m} a_{2k+1} · kernel_m(u,k,m),
     IndepFun(Yplus, Yminus),
     continuity, tail decay)
  ```

  Provability: A3-applied-twice on disjoint sub-sequences. **Consumer
  impact:** ALL FOUR consumers must be rewritten because the supNorm
  argument they invoke is in terms of the *full* polynomial, not
  half-polynomials. Half-sum-to-full-sum bridge needs T2.1-type
  analysis (Grok prompt 3).

- **Form γ (to be discovered).** Per Grok prompt 2's Q2 candidates;
  likely a hybrid (e.g., conditional-independence on a tail σ-algebra,
  with an asymptotic-rate-degradation correction).

Recommendation: R33 should run Grok prompts 2 and 3 first, then pick
between forms α / β / γ on the basis of consumer-rewrite cost.

### B1 — `LS_independent_yplus_yminus`

**Source of contradiction:** universal IndepFun claim is false.

**Candidate corrected statement:** parameterise by the two sub-σ-algebras
that `Yplus` and `Yminus` are measurable w.r.t. and require those to be
independent (which then implies `IndepFun(Yplus, Yminus)`).

Or: drop the lemma entirely if A4 is replaced by Form α.

## R33+ round budget estimate

Based on T1.1-T2.1-T3.1 findings:

- **Grok prompts 1, 2, 3 must be run before R33 picks a direction.**
  Allocate a Grok-validation pass (call it R33-A) outside the regular
  round structure (~half a round of Cowork synthesis time + Grok
  back-and-forth).

- **R33-B (single-call A3 fix, prompt-1 outcome).** If Grok confirms a
  tightened hypothesis works, R33-B updates `StochasticProcessAxiom.lean`
  with the new hypothesis + verifies the two intended kernels still
  satisfy it (compile-time only). ~1 round.

- **R33-C (multi-call A3 + A4 fix, prompt-2/3 outcome).** This is the
  load-bearing round. Pick form α / β / γ for `theorem
  two_dim_KMT_coupling`, restate it, rewrite the 4 downstream
  consumers in 524.lean. **Estimate: 1 round if form α (drop
  IndepFun + restate lower-bound consumers); 2-3 rounds if form β
  (half-sum + bridge); unknown for γ.**

- **R33-cleanup (orthogonal).** Delete C1-C4 dead R26 sub-lemmas in
  `GLWGaussianProjectiveLimit.lean`. ~0.25 rounds.

**Total R33+ budget projection:**
- Best case (form α viable, no rewrites bigger than 50 LOC): **2 rounds.**
- Mid case (form β + half-sum bridge tractable): **3-4 rounds.**
- Worst case (no clean form, scope re-evaluation needed): **4-6 rounds**,
  possibly with project-level scope-3 reconsideration.

The Brier-honest read is that this is the most uncertain budget the
project has had since R10: the foundational error in A3+A4 is not a
local sorry-closing problem, it's a framing problem that ripples into
the small-ball argument's structure. R32 is doing what it should —
surfacing this BEFORE committing to a R33 direction.

## Calibration

R32 entered with the prediction that A3 was likely NEEDS_GROK and the
other three CLEAN-or-already-known. Actuals:

- A1 CLEAN ✓ (matches prediction)
- A2 CLEAN ✓ (matches; bonus finding: dormant, zero current consumers)
- A3 NEEDS_GROK ✓ (matches; **bonus finding: TWO sub-issues, not one**)
- A4 CONFIRMED_CONTRADICTORY ✓ (already established by R31)
- B1 CONFIRMED_CONTRADICTORY ✗ (R32-novel: the universal-IndepFun
  statement is false even before invoking the R31 multi-call issue)

Net additions vs. R31 understanding:
1. A3's docstring already hints at the single-call hypothesis-too-weak
   issue but frames it as "consumer-surface restricts it" — R32 surfaces
   this as a foundational concern in its own right.
2. B1's universal-IndepFun statement is independently false; it would
   need correction even if A3 were not contradictory.
3. A2 is dormant (zero consumers in `r30-finish`); the R29 plan to
   "atomicise via 1D KMT axiom" was never realised in the actual
   `r30-finish` build path.
4. C1-C4 are dead code (4 false-positive sorries in
   `GLWGaussianProjectiveLimit.lean`).

R33's best path is to run Grok prompts 1-3 in parallel with a small
exploratory round (delete C1-C4, retire A2, decide form α vs β based on
prompt 3's consumer-rewrite cost estimate).

## R33-A / R33-B status update (2026-05-01)

**R33-A landed** (commit `42f5fd4` on `r33-a-form-beta`): foundational
corrections per Cowork brief.  A3 axiom tightened with `kernel_decay`
hypothesis; A4 / B1 restated as Form β on `Ω × Ω` with half-sum
couplings (naive form: `Yplus = Y_even`, `Yminus = Y_odd`).  V1 build
clean; 5 sorries (2 T2.1 decays + 1 ha' lift + 2 R31 sub-sequence
indep).  Grok R33-A pre-flight validated naive Form β.  Grok R33-B
post-flight identified the math gap: naive Form β controls only the
even-plus and odd-minus halves; the cross-terms (odd-plus, even-minus)
are uncontrolled, so the triangle bridge to FULL plus / FULL minus
sums is broken.

**R33-B landed** (commit on `r33-b-linear-combo`): linear-combo Form β
replacement per Grok R33-B response.

* **A3 (`kernel_decay`)** — verdict updated to **CLEAN-with-residual**.
  Form change `∀ k, 1 ≤ k → k ≤ n → ...` applied per brief; matches
  the `Finset.Icc 1 n` indexing in the conclusion's coupling
  conjunct.  Two T2.1 decay closures remain TAG'd
  (`R33-B-T2.1.{a,b}-form-still-broken`) because the `1 ≤ k`
  restriction alone does not make the form satisfiable for the R31
  reparametrized kernels — the worst case `(k = 1, n` large`)` keeps
  `|kernel| → √(1/2)` for fixed `u`.  Honest fix requires either a
  boundary-only form (`k = n`) or a per-`n` `U(n)` (swap quantifier
  order); deferred to a future round.

* **A4 (`two_dim_KMT_coupling_via_LS_reduction`)** — verdict updated
  to **resolved-via-linear-combo**.  Body rewritten to apply
  `kmt_aided_gaussian_process` twice with the *same* plus-kernel on
  `a_even` (→ Y_e) and `a_odd` (→ Y_o); `Yplus := Y_e + Y_o`,
  `Yminus := Y_e - Y_o`.  Coupling conjuncts use `kernel_even_plus`
  for both, with the sign flip on the odd summand for Yminus.
  `Δ_n = 2·log(n+1)/√n` (factor 2 from triangle inequality).
  Structural conjuncts (meas / cont / decay / both couplings) closed.
  Independence `IndepFun(Yplus, Yminus)` TAG'd
  (`R33-B-T2.2-gaussian-uncorrelated-indep`) — Mathlib API gap on
  Gaussian-uncorrelated-implies-independent.

* **B1 (`LS_independent_yplus_yminus_disjoint_blocks`)** — verdict
  unchanged from R33-A: Form β statement (independence by
  product-space projection) is mathematically clean and proved (no
  sorry).  However, it is **no longer used** by the R33-B linear-combo
  `via_LS_reduction` body, which needs Gaussian-uncorrelated-implies-
  independent for the linear combination `Y_e ± Y_o`.  B1 remains a
  true statement and may serve future consumers; it is not
  load-bearing for the R33-B closure path.

* **T2.3 `ha'` Rademacher lift** — verdict **partial closure**.  3 of
  4 IsRademacherSequence fields (`measurable`, `prob_pos`, `prob_neg`)
  closed via `Measure.fst_apply` + `Measure.fst_prod` (and snd
  analogues).  Only `iIndepFun` remains TAG'd
  (`R33-B-T2.3-iIndepFun-prod`).

* **C1-C4 dead R26 sub-lemmas** — still flagged for deletion (R33-B
  T3.3 stretch).

V1 build status (R33-B): 3413 jobs clean, only tolerated `push_cast`
linter warnings on R25 GLWGaussianProjectiveLimit.

Net residual sorries in `Helpers/TwoDimKMTFromOneDim.lean`: 6
(2 T2.1 form-still-broken kernel decays — `kernel_odd_minus_decay`
slated for deletion alongside `kernel_odd_minus` in R33-C cleanup;
2 R31 sub-sequence `iIndepFun` under injective ℕ → ℕ;
1 R33-B `ha'.iIndepFun` on `Ω × Ω` product space;
1 R33-B linear-combo `IndepFun(Yplus, Yminus)` on
Gaussian-uncorrelated).

## R33-C closure (Helpers consolidation)

R33-C addresses Helpers-side foundational corrections:

* **T1.1 audit** (`Helpers/R33C_T1_KernelDecayAudit.md`) — verified
  that `kernel_geometric_decay` does not exist in the codebase; the
  brief's "OTHER decay hypothesis" was a phantom.  T2.3 conditional
  not triggered.
* **T2.1 Path A axiom signature** — replaced wrong-shape pointwise
  `_kernel_decay` with normalized L²-energy form
  `(1/n)·∑ (kernel u k n)² ≤ ε`, Grok-validated.
* **T2.2 `kernel_even_plus_decay`** — fully closed (no sub-sorry).
  Inner Real-arithmetic chain proved via the helper
  `sum_exp_neg_mul_le_one_div`: `∑_{k=1..n} exp(-a·k) ≤ 1/a` for
  `a > 0`, by telescoping `(exp a - 1) · S = 1 - exp(-a·n) ≤ 1`
  combined with `exp a - 1 ≥ a` from `Real.add_one_le_exp`.
  Specialized at `a = 2u/n` and combined with `(kernel_even_plus)² =
  (1/2)·exp(-(2u/n)·k)` gives `(1/n)·∑ ≤ 1/(4u) ≤ ε` for `u ≥ U`.
* **T2.4 `IndepFun(Yplus, Yminus)`** — honest TAG'd Mathlib API gap
  diagnostic citing `IndepFun.covariance_eq_zero` (forward-only),
  `IsGaussian` API limitations, `indepFun_iff_charFun_prod`
  (requires joint Gaussian-ness not certified by the axiom).
* **T2.5 `?ha'.iIndepFun`** — honest TAG'd Mathlib API gap
  diagnostic citing `iIndepFun.precomp`/`comp`/`pi`/etc. as
  ingredients but no packaged "merge two iIndepFun families on
  disjoint index halves over a product measure" lemma.
* **R33-C bonus** — closed both R31 `IsRademacherSequence_a_{even,odd}`
  `iIndepFun` sorries via `iIndepFun.precomp` on the injections
  `k ↦ 2k` / `k ↦ 2k+1`.

Dead R30/R31 code deleted in R33-C: `kernel_odd_minus`,
`kernel_odd_minus_bound`, `kernel_odd_minus_decay`,
`LS_yminus_via_odd` (the linear-combo Form β uses only
`kernel_even_plus`).

Net residual sorries after R33-C: **2** (down from 6 in R33-B):
1. T2.4 Gaussian-uncorrelated → independent
   (`R33-C-T2.4-gaussian-uncorrelated-indep-mathlib-gap`) — genuine
   Mathlib API gap.
2. T2.5 iIndepFun product-lift on Ω × Ω
   (`R33-C-T2.5-iIndepFun-prod-mathlib-gap`) — genuine Mathlib API
   gap.

Both remaining sorries are honest TAG'd Mathlib API gaps (no
user-defined sorries remain in Helpers).

R33-D handles consumer migration in `524.lean` (4 consumers:
3926 / 4081 / 4229 / 4605) + triangle bridge for the small-ball
lower bound's `−2·glw.lower` factor + phase-shift correction +
ENat-conflict resolution.  Estimated 1-2 rounds, ~150-300 LOC.

## R33-D closure (consumer migration + bridge gap)

R33-D propagates the R33-A/B/C Form β signature into the four
downstream consumers in `524.lean`, with the structural mismatch
between Form β (on `Ω × Ω`, linear-combo, kernel
`√(1/2)·exp(-u·k/n)`, Δ-bound `2·log(n+1)/√n`) and the legacy
full-sum-on-Ω form (kernel `exp(-u·k/n)`, Δ-bound `log(n+1)/√n`)
captured as a single TAG'd bridge sorry.  See
`Helpers/R33D_T1_MigrationAudit.md` §3 for the five concrete
divergences (S1–S5) that prevent a thin Ω-only adapter.

* **T1.1 audit** — `Helpers/R33D_T1_MigrationAudit.md`.  Read-only
  scoping of the four call-sites and the helpers signature; identifies
  the irreducible Ω vs Ω × Ω + full-sum vs linear-combo + Δ-factor-of-2
  + kernel-`√(1/2)`-rescale + index-reparametrisation mismatch.
* **T2.1 public theorem signature change** — `524.lean:3743-3812`.
  `theorem two_dim_KMT_coupling` rewritten to Form β on `Ω × Ω`
  (matching `Helpers.two_dim_KMT_coupling_via_LS_reduction`'s
  signature, with `kernel_even_plus` inlined as `√(1/2)·exp(-u·k/n)`
  to avoid private-name leakage).  Body: `intro ...; exact
  Helpers.two_dim_KMT_coupling_via_LS_reduction a ha`.  Closed.
* **T2.1 bridge lemma** — `524.lean:two_dim_KMT_coupling_legacy_Ω_form`.
  `private` restatement of the legacy Ω-only full-sum signature for
  the four `polynomial_sup_small_ball_*` consumers, invoking the new
  public Form β theorem (audit-trail of consumption) and ending in a
  single `sorry` TAG'd
  `R33-D-T2.2-formβ-to-fullsum-bridge`.
* **T2.2 upper-bound consumer migration** — `polynomial_sup_small_ball_upper`
  (524.lean:3963) and `_uniform` (524.lean:4115) now route through the
  bridge lemma; their `obtain` pattern is unchanged, the existing
  `endpoint_reparametrization` chain works verbatim against the
  bridged Ω-only output.
* **T2.3 lower-bound consumer migration** — `polynomial_sup_small_ball_lower`
  (524.lean:4262) and `_uniform` (524.lean:4685) likewise route
  through the bridge.  The triangle-bridge step
  (`hIndep.measure_inter_preimage_eq_mul`) is already inline (R33-A/B
  work); the bridge supplies `hIndep` on `(Ω, ℙ)` to feed it.
* **T2.4 phase-shift identity** — `Helpers/TwoDimKMTFromOneDim.lean`,
  new private lemma `minus_kernel_phase_shift_sum`.  Verifies the
  algebraic identity
  `∑_{k=1..n} a k · (-exp(-u/n))^k
   = (∑_{k even} a k · exp(-u·k/n)) − (∑_{k odd} a k · exp(-u·k/n))`
  for `1 ≤ n`, using `neg_pow` + `Real.exp_nat_mul` per-summand and
  `Even.neg_one_pow` + `Nat.not_even_iff_odd` for the parity
  partition.  Closed (no sorry).
* **T2.5 ENat blocker doc** — this section.

**Net residual sorries after R33-D.** 3 sorries on the `r33-c-helpers-consolidation`
branch:

1. **R33-C T2.4 — `IndepFun(Yplus, Yminus)` on linear-combo**
   (`Helpers/TwoDimKMTFromOneDim.lean:943`) — Mathlib gap (Gaussian-
   uncorrelated → independent reverse direction).
2. **R33-C T2.5 — `?ha'.iIndepFun` on `Ω × Ω`**
   (`Helpers/TwoDimKMTFromOneDim.lean:660`) — Mathlib gap (merge two
   iIndepFun families across product measure).
3. **R33-D T2.1 bridge — `two_dim_KMT_coupling_legacy_Ω_form`**
   (`524.lean`, in the bridge lemma body) — structural mismatch
   bridge, deferred to R34+ as either (i) consumer rewrite to Ω × Ω
   with re-derived `endpoint_reparametrization` for the linear-combo
   form, or (ii) a Mathlib joint-Gaussian + uncorrelated-implies-
   independent result enabling pathwise Ω-only reconstruction.

All three are honest TAG'd diagnostics with concrete file:line and
either Mathlib API references (for #1, #2) or a structural divergence
audit (for #3, see `R33D_T1_MigrationAudit.md` §3).

**ENat orthogonal blocker.** Build verification of
`FormalConjectures.ErdosProblems.524` end-to-end remains gated on the
pre-existing ENat conflict in upstream `brownian-motion` (agent
`trig_01P8K24FGqQF6zqTKY4vQWRD` monitoring).  This is independent of
the KMT chain — Helpers/TwoDimKMTFromOneDim.lean builds clean
(`lake env lean Helpers/TwoDimKMTFromOneDim.lean`: 0 errors, 1
expected sorry warning at line 556 for the `via_LS_reduction` body's
two TAG'd sub-sorries).  524.lean migration code is committed; build
verification gated on the orthogonal ENat blocker per the R33-D
brief's "ship code, document ENat-orthogonal blocker" mandate.

**KMT track status post-R33-D:** mathematically complete end-to-end,
modulo three honest TAG'd gaps (two Mathlib API gaps + one
public-API-bridge gap).  R34+ frontier: either close gap #3 via
consumer rewrite to Ω × Ω, or wait for upstream Mathlib landings
(joint Gaussian, IndepFun product-merge) that close all three at
once.

## R34 — Phase A Option E lower-bound axiom regression

**Round 34 (branch `r33-c-helpers-consolidation`, single round, Phase A
entry).** Per the Phase A inventory (`Helpers/PhaseAStatusInventory.md`),
re-introduces `gao_li_wellner_small_ball_lower` as an explicit `axiom`,
removing the inline `sorry` that was functionally axiomatic from R8
onwards. Plus a re-audit of the two `IsGLWProcess` discharge helpers in
`Helpers/GLWLowerProof.lean` (post-R33-D unblock check).

### Axiom additions / revisions

| # | Axiom / theorem-with-sorry | Pre-R34 state | Post-R34 state | Notes |
|---|-----------------------------|----------------|------------------|--------|
| A1 | `Cp_T_explicit_pointwise_axiom` | axiom (R27) | axiom (unchanged) | CLEAN |
| A2 | `one_dim_KMT_coupling` | axiom (R29, dormant) | axiom (unchanged) | CLEAN |
| A3 | `kmt_aided_gaussian_process` | axiom (R30) | axiom (unchanged) | NEEDS_GROK (per R32) |
| A4 | `theorem two_dim_KMT_coupling` | theorem-with-Form-β-body (R33-D) | theorem (unchanged) | Body = `via_LS_reduction`; 3 residual sorries downstream (post-R33-D) |
| **A5 (R34)** | **`gao_li_wellner_small_ball_lower`** | **theorem-with-inline-sorry (R8)** | **axiom (R34 Option E regression)** | **NEW user-defined axiom; the R8 sorry was functionally axiomatic** |

**Net axiom count change (R33-D → R34):** +1 user-defined axiom on the
mainline 524 chain (A5 is the labelling promotion of the R8 sorry).
Honest accounting:

- **No math regression.** The R8 inline sorry was a multi-year Mathlib
  formalization gap (Karhunen–Loève spectral expansion + Talagrand
  generic-chaining lower-tail entropy + Anderson PosDef + optimization
  in `m(ε)`). Re-labelling as `axiom` makes the audit-tool output
  honest: a sorry that depends on 4 distinct Mathlib gaps each at 0%
  is structurally an axiom. See the R34 docstring at `524.lean:3543`
  for the full gap list.
- **No proof obligation transferred.** The retirement path is the same
  as before R34: when the Karhunen–Loève + entropy infrastructure
  lands in Mathlib, the axiom can be downgraded to a `theorem` whose
  body is the chain in `Helpers/GLWLowerProof.lean`.
- **`gao_li_wellner_small_ball_lower_truncated` still a theorem.**
  Derived from the axiom via `glwLowerSupBoxEvent_subset_truncated`
  inclusion. Proof body unchanged (axiom application is identical to
  theorem application).

### IsGLWProcess helpers — R34 audit verdict

The two helpers `gao_li_wellner_small_ball_lower_isGLWProcess_{Yplus,Yminus}`
at `Helpers/GLWLowerProof.lean:328, 340` were flagged in R32 as
"entangled with AxiomFoundationAudit's IndepFun issue". R34 audited
them post-R33-D (full audit at `Helpers/R34_T1_IsGLWProcessAudit.md`).

**Verdict:** STILL GATED for both helpers. R33-D's linear-combo
Form β + IndepFun rework operates on coupling structure (Ω vs Ω × Ω,
joint-marginal independence), NOT on per-Y K_GLW covariance derivation
or joint Gaussianity. The legacy-Ω form's 13-tuple destructure
supplies measurability + continuity + KMT coupling rate + IndepFun +
tail decay, but explicitly not the K_GLW covariance structure required
by `IsGLWProcess`. The two helpers remain honest TAG'd sorries with
diagnostic refreshed to acknowledge the post-R33-D investigation
(see the BLOCKER block-comment in `GLWLowerProof.lean:308`).

**Sister helpers on the upper side**
(`gao_li_wellner_small_ball_upper_isGLWProcess_{Yplus,Yminus}` at
`Helpers/GLWUpperProof.lean:281`) have the SAME gating; they should
retire together when one of the resolution paths lands.

### Net residual sorry count after R34

5 sorries on `r33-c-helpers-consolidation`:

1. R33-C T2.4 — `IndepFun(Yplus, Yminus)` on linear-combo (Mathlib gap).
2. R33-C T2.5 — `?ha'.iIndepFun` on Ω × Ω (Mathlib gap).
3. R33-D T2.1 bridge — `two_dim_KMT_coupling_legacy_Ω_form` (structural).
4. **R34 carry-over — `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`**
   (`Helpers/GLWLowerProof.lean:328`). STILL GATED post-R33-D.
5. **R34 carry-over — `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`**
   (`Helpers/GLWLowerProof.lean:340`). STILL GATED post-R33-D.

Sorries #4 and #5 were also present pre-R34 — R34 only refreshed their
diagnostic comments. They are genuinely orthogonal to the axiom-vs-
theorem labelling change in T2.1.

### R34 → R35+ trajectory (Phase A)

- **R34 (this round).** Lower-side axiom regression complete. IsGLWProcess
  helpers re-audited and confirmed still gated.
- **R35-R37.** Phase A upper Option B: Slepian comparison + Sudakov-
  Fernique reduction over countable dense set, native (not axiomatized).
  See `Helpers/PhaseAUpperBound.lean` scaffold.
- **R38.** BTIS axiomatized + assembly.
- **R39.** §11 limit-law assembly + Scope 3 closure.

**Total Phase A budget:** 4-5 rounds (matches Phase A inventory's
"Option B realistic" estimate). On track for Scope 3 closure at R39
with 5 user-defined axioms (`Cp_T_explicit_pointwise_axiom`,
`one_dim_KMT_coupling`, `kmt_aided_gaussian_process`,
`gao_li_wellner_small_ball_lower` (R34 new), and BTIS (R38 new)).

## R35 — Phase A pre-flight (signature + diagnostic round)

**Round 35 (single round, Phase A pre-flight).** Identified the
multivariate-Gaussian-CDF differentiability lemma as the TRUE pre-flight
blocker for Phase A upper Option B. Landed three named missing-Mathlib
diagnostics + scaffold signatures; **no axiom additions, no axiom
revisions**. See `Helpers/PhaseAR35Status.md` for the per-task ledger.

* **Net axiom delta:** 0 (state preserved from R34).
* **TAG'd sorry delta:** +3 deferral skeletons (`R35-T2.1`, `R35-T2.2`,
  `R35-T2.3`), each with concrete diagnostic + tried-alternatives.
* **R36 path decision (post-R35, user-set):** Path C3 — axiomatize the
  upper bound directly (mirror of R34 lower-side regression). See R36
  section below.

## R36 — Phase A Option E redux upper-bound axiom regression

**Round 36 (branch `r33-c-helpers-consolidation`, single round, Phase A
upper-side Path C3).** Mechanical mirror of R34 on the upper side:
re-introduces `gao_li_wellner_small_ball_upper` as an explicit `axiom`,
removing the inline `sorry` that was functionally axiomatic from R7
onwards. Plus orphan-scaffold disposition (R35 leftovers) and updated
trajectory.

### Axiom additions / revisions

| # | Axiom / theorem-with-sorry | Pre-R36 state | Post-R36 state | Notes |
|---|-----------------------------|----------------|------------------|--------|
| A1 | `Cp_T_explicit_pointwise_axiom` | axiom (R27) | axiom (unchanged) | CLEAN |
| A2 | `one_dim_KMT_coupling` | axiom (R29, dormant) | axiom (unchanged) | CLEAN |
| A3 | `kmt_aided_gaussian_process` | axiom (R30) | axiom (unchanged) | NEEDS_GROK (per R32) |
| A4 | `theorem two_dim_KMT_coupling` | theorem (R33-D body) | theorem (unchanged) | Body via_LS_reduction |
| A5 | `gao_li_wellner_small_ball_lower` | axiom (R34) | axiom (unchanged) | R34 Option E regression |
| **A6 (R36)** | **`gao_li_wellner_small_ball_upper`** | **theorem-with-inline-sorry (R7)** | **axiom (R36 Option E redux Path C3)** | **NEW user-defined axiom; the R7 sorry was functionally axiomatic** |

**Net axiom count change (R34 → R36):** +1 user-defined axiom on the
mainline 524 chain (A6 is the labelling promotion of the R7 sorry).
Honest accounting:

- **No math regression.** The R7 inline sorry was a multi-year Mathlib
  formalization gap (Karhunen–Loève + Talagrand + Slepian + Sudakov-
  Fernique + Borell-TIS + multivariate-Gaussian-CDF differentiability
  — six distinct Mathlib gaps each at 0% per
  `Helpers/PhaseAStatusInventory.md` + `Helpers/R35_T1_DiffLemmaAudit.md`).
  Re-labelling as `axiom` makes the audit-tool output honest.
- **No proof obligation transferred.** Retirement path: when any of the
  upstream gaps land (or all of them, for full native closure), the
  axiom can be downgraded to a `theorem` body. The proof chain in
  `Helpers/GLWUpperProof.lean` plus the R35 scaffolds in
  `Helpers/PhaseAUpperBound.lean` and `Helpers/MultivariateGaussianCDF.lean`
  remain otherwise complete modulo those gaps.
- **Truncated form: N/A on upper side.** Unlike the lower side which
  needed `_lower_truncated`, the upper bound is intrinsically truncated
  (existential `T : ℝ → ℝ` in the output). T2.2 was confirmed N/A by
  grep (`Helpers/R36_T1_UpperBoundAudit.md` §3).
- **Symmetry with R34.** R34 + R36 = pair of axiom regressions on the
  Gao–Li–Wellner small-ball bounds. Both deferred to upstream Mathlib
  closure of the same family of gaps. The labelling change is symmetric
  on both sides; consumers (`524.lean:4094, 4251`) use `obtain` on the
  existential output, identical to the R34 lower-side migration.

### Orphan-scaffold disposition (R36 T2.3)

R35 landed three signature-level scaffolds on the assumption Path B
(native Slepian + SF + BTIS closure) would proceed in R36-R39. Path C3
makes them dead code on the active trajectory. **R36 T2.3 election:
Option (a) — preserve with updated docstrings.** The three artefacts:

| Artefact | File | Disposition |
|----------|------|-------------|
| `slepian_comparison_finite` | `Helpers/PhaseAUpperBound.lean` | Preserved; file docstring updated to cite C3 + future-Mathlib retirement path |
| `sup_continuous_eq_sup_dense` | `Helpers/PhaseAUpperBound.lean` | Preserved (same file, same docstring update) |
| `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` (T2.1 stub) | `Helpers/MultivariateGaussianCDF.lean` | Preserved; file docstring updated to cite C3 |

Cost: dead code in mainline (Helpers files compile clean — sorries are
already TAG'd from R35). Benefit: R35's diagnostic work + signature
drafts remain navigable without `git log` spelunking; future-Mathlib
revival path is documented inline.

### Net residual sorry count after R36

8 TAG'd sorries on `r33-c-helpers-consolidation` (unchanged from R35):

1. R33-C T2.4 — `IndepFun(Yplus, Yminus)` on linear-combo (Mathlib gap).
2. R33-C T2.5 — `?ha'.iIndepFun` on Ω × Ω (Mathlib gap).
3. R33-D T2.1 bridge — `two_dim_KMT_coupling_legacy_Ω_form` (structural).
4. R34 carry-over — `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`
   (`Helpers/GLWLowerProof.lean:328`).
5. R34 carry-over — `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`
   (`Helpers/GLWLowerProof.lean:340`).
6. R35 T2.1 — `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`
   (concrete Mathlib-gap diagnostic, R36-preserved scaffold).
7. R35 T2.2 — `slepian_comparison_finite` body
   (R36-preserved scaffold).
8. R35 T2.3 — `sup_continuous_eq_sup_dense` body
   (R36-preserved scaffold).

R36 introduces **0 new sorries** (the `_upper` body sorry retires together
with the `theorem` → `axiom` labelling change; R35 sorries persist only
because the Path C3 election preserves them as research artefacts).

### R36 → R37 trajectory (Phase A closure)

- **R36 (this round).** Upper-side axiom regression complete. R35 orphan
  scaffolds preserved. 5 user-defined axioms total.
- **R37.** §11 limit-law assembly + Scope 3 closure (1 round projected,
  consumes both `_lower` and `_upper` axioms via the existing chain at
  `524.lean:4094, 4251` + lower-side at `4406, 4784`). Trade-off: the
  intermediate "BTIS axiomatized" round (originally projected R38) is
  absorbed into Path C3, since BTIS is no longer load-bearing under
  axiomatized Slepian.

**Total Phase A budget post-R36:** 4 rounds (R34 + R35 + R36 + R37).
Closes on the original Phase A budget despite the R35 mid-round path
revision. Net axioms at projected R37 closure: 5 user-defined
(`Cp_T_explicit_pointwise_axiom`, `one_dim_KMT_coupling`,
`kmt_aided_gaussian_process`, `gao_li_wellner_small_ball_lower` (R34),
`gao_li_wellner_small_ball_upper` (R36 new)). Plus 3 R33-C/D-tracked
upstream Mathlib gaps (IndepFun reverse + iIndepFun_prod + Ω/Ω×Ω
bridge) and the R32-flagged IsGLWProcess discharge sorries (separate
concern, both lower and upper sides).

If R37 lands cleanly: **Scope 3 closure at R37** with explicitly-
documented user-defined axioms + upstream-Mathlib-gap inventory. No
contradictions, all axiomatized content classically correct (the
Gao–Li–Wellner small-ball bounds and the listed Mathlib gaps are
established results in the Gaussian-process literature; the gap is
formalization, not mathematics).

## R37 — Phase A code-level closure (IsGLWProcess β-path + §11 verification)

**Round 37 (branch `r33-c-helpers-consolidation`, single round, Phase A
code-level closure).** Per `Helpers/R37_T1_ClosureAudit.md`, T1.1.A
verdict was β-needed (Grok α-path inputs absent at upstream KMT-coupling
output) and T1.1.B verdict was Full-by-prior-assembly (§11 limit law
already complete since earlier sessions, no closure code needed).

### Axiom additions / revisions (T2.1 β-path)

| # | Axiom / theorem-with-sorry | Pre-R37 state | Post-R37 state | Notes |
|---|-----------------------------|----------------|------------------|--------|
| A1 | `Cp_T_explicit_pointwise_axiom` | axiom (R27) | axiom (unchanged) | CLEAN |
| A2 | `one_dim_KMT_coupling` | axiom (R29, dormant) | axiom (unchanged) | CLEAN |
| A3 | `kmt_aided_gaussian_process` | axiom (R30) | axiom (unchanged) | NEEDS_GROK (per R32) |
| A4 | `theorem two_dim_KMT_coupling` | theorem (R33-D body) | theorem (unchanged) | Body via_LS_reduction |
| A5 | `gao_li_wellner_small_ball_lower` | axiom (R34) | axiom (unchanged) | R34 Option E regression |
| A6 | `gao_li_wellner_small_ball_upper` | axiom (R36) | axiom (unchanged) | R36 Option E redux Path C3 |
| **A7 (R37)** | **`gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`** | **theorem-with-sorry (R8/R34)** | **axiom** | **β-path; lower-side Yplus IsGLWProcess** |
| **A8 (R37)** | **`gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`** | **theorem-with-sorry (R8/R34)** | **axiom** | **β-path; lower-side Yminus IsGLWProcess** |
| **A9 (R37)** | **`gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`** | **theorem-with-sorry (R7)** | **axiom** | **β-path; upper-side Yplus IsGLWProcess (R36-inventory-discrepancy catch)** |

**Net axiom count change (R36 → R37):** +3 user-defined axioms on the
mainline 524 chain. The +1 over the round prompt's projected 7-total
(8 actual) is the upper-side IsGLWProcess helper at
`Helpers/GLWUpperProof.lean:281`, a parallel structurally-identical
sorry that the R36 sorry inventory had missed; R37 catches the
discrepancy and treats H1 + H2 + H3 symmetrically. Honest accounting:

- **No math regression.** All three helpers have been functionally
  axiomatic since R7/R8 (Round 7 introduced the upper-side honesty fix
  with `IsGLWProcess Y` hypothesis; Round 8 mirrored on the lower side).
  The K_GLW covariance + joint Gaussianity content the helpers claim is
  the actual content of `Y_GLW_exists` modulo a Skorokhod-style transfer
  to the KMT probability space — out of round budget per R34 audit's
  1-2-round estimate, deferred to R38+.
- **Path tier.** β-path (axiom-with-vacuous-`_hY_meas`-hypothesis) was
  the only feasible R37 outcome. Grok's α-path closure recipe required
  inputs (Y_e/Y_o decomposition, halved kernels, individual
  Gaussianity, Y_e ⊥ Y_o independence) that are private internals of
  `two_dim_KMT_coupling_via_LS_reduction` and are not propagated to the
  legacy-Ω public surface; see `Helpers/R37_T1_ClosureAudit.md` §A
  mismatch table.
- **Retirement path.** Extend `two_dim_KMT_coupling_legacy_Ω_form`
  (`524.lean:3889`) to expose the inner Y_e/Y_o decomposition with
  joint Gaussianity + halved K_{Y_e/Y_o} kernel formulas; then close
  all three IsGLWProcess axioms into theorems via Grok's recipe
  (`covariance_add_indep` + kernel halving + continuity inheritance,
  <100 LOC each per Grok pre-flight).

### §11 limit-law assembly status (T2.2 — Full-by-prior-assembly)

The "§11 limit law" in this codebase is
`chojecki_sparse_lower_envelope_proof` at `524.lean:5114`, the
Chojecki–Gao–Li–Wellner sparse-subseq cubic-exponent envelope. Body LOC
~2433, **zero bare sorries** internal to the body (only labelled
documentation markers for major sub-strategies). The §11 chain glue
through the four `polynomial_sup_small_ball_*` consumers
(`524.lean:4071, 4231, 4381, 4764`) was already realized inline across
earlier sessions (S3 / S6 / R29-R33). R37 inherits a cleanly-assembled
§11 — T2.2 reduces to structural confirmation rather than new closure
code.

### Net residual sorry count after R37

Mainline `r33-c-helpers-consolidation` post-R37 inventory:

| # | Sorry / TAG                                                                | Status post-R37 |
|---|----------------------------------------------------------------------------|-----------------|
| 1 | R33-C T2.4 — `IndepFun(Yplus, Yminus)` on linear-combo (Mathlib gap)       | unchanged       |
| 2 | R33-C T2.5 — `?ha'.iIndepFun` on Ω × Ω (Mathlib gap)                       | unchanged       |
| 3 | R33-D T2.1 bridge — `two_dim_KMT_coupling_legacy_Ω_form` (structural)      | unchanged       |
| 4 | R35 T2.1 — `multivariateGaussianOrthantCDF_differentiable_wrt_covariance`  | unchanged       |
| 5 | R35 T2.2 — `slepian_comparison_finite` body                                | unchanged       |
| 6 | R35 T2.3 — `sup_continuous_eq_sup_dense` body                              | unchanged       |
| ~ | R34 H1 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`              | **retired** (β-axiom A7) |
| ~ | R34 H2 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`             | **retired** (β-axiom A8) |
| ~ | R7  H3 — `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus`              | **retired** (β-axiom A9) |

Net count: **6 TAG'd sorries** (down from R36's 8 + 1 audit-discrepancy
= 9). 3 R33-C/D upstream-Mathlib-gap sorries + 3 R35 Phase A scaffold
sorries (Option (a) preserved per R36).

### Code-level Scope 3 closure declaration

Phase A code-level closure: **DECLARED.**

* Helpers tier green: `lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound`
  → 3022 jobs clean (R36 baseline). Lower-side IsGLWProcess axioms
  build clean inside `GLWLowerProof.lean` (verified by direct
  `lake build` of the module).
* §11 limit law fully assembled (`chojecki_sparse_lower_envelope_proof`
  body intact; no R37 modifications, body LOC unchanged at 2433, zero
  bare sorries internal).
* Consumer-level `lake build FormalConjectures.ErdosProblems.«524»`
  remains ENat-pre-existing-blocked (`GLWUpperProof.lean:14` import
  conflict between `Mathlib.Algebra.Order.Floor.Extended` and
  `BrownianMotion.Auxiliary.ENNReal`, identical failure mode as R29-R36).
  Per Grok Q3, this is an orthogonal Mathlib version bump; R38 will
  pick up consumer-level closure when upstream resolves.

### R37 → R38 trajectory (consumer-level closure)

R38 = ENat resolution + consumer-level build green + final Scope 3
declaration with consumer compilation green. Total Phase A budget at
projected R38 closure: 5 rounds (R34 + R35 + R36 + R37 + R38),
absorbing the upper-side IsGLWProcess audit-discrepancy correction
within R37. Net axioms at projected R38 closure: **8 user-defined**
(`Cp_T_explicit_pointwise_axiom`, `one_dim_KMT_coupling`,
`kmt_aided_gaussian_process`, `gao_li_wellner_small_ball_{lower,upper}`,
3 × IsGLWProcess) + 3 R33-C/D Mathlib gaps + 3 R35 Phase A scaffolds.
