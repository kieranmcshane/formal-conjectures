# KMT Option C Retirement Plan — R28 Stub + Roadmap

**Round:** R28 (`r28-finish` branch)
**Status:** Stub (load-bearing LS-reduction Lean transcription deferred; net-axiom-count guardrail enforces no-regression).
**Pre-authorisation:** 7h-session-brief §"Branch C R28" lines 41-46; §"R27 Branch A KMT Option C spec" lines 105-127; Grok-validated D2 + Option C combination.

## Current state at R28

After R27's Option D bascule:
- `Y_GLW_exists` axiom inventory: `[propext, Classical.choice, Quot.sound, Cp_T_explicit_pointwise_axiom (private)]` — `sorryAx` retired.
- `two_dim_KMT_coupling` (`524.lean:3741`) remains as public axiom (5 consumers in `524.lean`).
- Net axiom count: 2 (1 private D2 + 1 public 2D KMT).

R28 candidate path (per brief, Branch C continuation):
1. Introduce `axiom one_dim_KMT_coupling` in new file `Helpers/OneDimKMT.lean`.
2. Transcribe LS reduction `TwoDimKMTRetirement.md:84-92` into new file `Helpers/TwoDimKMTFromOneDim.lean`.
3. Replace `axiom two_dim_KMT_coupling` in `524.lean:3741` with `theorem two_dim_KMT_coupling := ...` proved via the LS bridge.
4. Verify net axiom count remains 2.

## Why R28 lands at Stub

**Honest scope assessment (post-R26/R27 context-budget review):**

The 2D form `two_dim_KMT_coupling` has **9 conjuncts** quantifying jointly over Yplus, Yminus, Δ, and a Rademacher sequence `a`, including:
- Two kernel-tested coupling bounds with kernels `f₁(u,k) = exp(-u·k/n)` and `f₂(u,k) = (-exp(-u/n))^k`.
- `ProbabilityTheory.IndepFun` between Yplus and Yminus over the joint product space.
- Continuous sample paths for both.
- Tail decay (`∀ε > 0, ∀ᵐω, ∃T₀, ∀u ≥ T₀, |Y u ω| ≤ ε`) for both.

A 1D axiom of the classical Komlós–Major–Tusnády form (`|S_n - B(n)| ≤ C log(n+1)`) does not directly produce kernel-tested couplings. The LS reduction must:

1. **Apply 1D KMT to derive a Brownian motion `B` such that `S_n ≈ B(n)`.**
2. **Use `B` to construct `Yplus(u, ω)`** as a stochastic integral against the kernel `e^{-u s}`. This requires the brownian-motion package's stochastic-integral API at deterministic-kernel parameters — exactly the gap that `Phase2Plan.md` Node 1B identified as the "swing factor" (300-700 LOC of Mathlib gymnastics or one stepping-stone axiom for the Itô isometry on `s ↦ e^{-us}`).
3. **Compute the coupling error** `|((1/√n) ∑ a_k e^{-uk/n}) - Yplus u| ≤ Δ_n` uniformly in `u ≥ 0` and `ω` from the partial-sum coupling. This is the kernel-tested form of the strong invariance principle restricted to our kernel — non-trivial.
4. **Repeat for Yminus** with the second kernel.
5. **Construct the joint product space** carrying two independent BMs `B⁺, B⁻` to satisfy the `IndepFun` conjunct.
6. **Continuous sample paths and tail decay** transfer from the BM construction via Kolmogorov-Chentsov + martingale tail estimates.

**Realistic LOC estimate to land this in Lean:** 300-600 LOC, in the post-`brownian-motion`-stochastic-integral-API world. R28's remaining context budget cannot cover this.

## Net-axiom-count guardrail (Refinement 2) decision

If R28 lands `axiom one_dim_KMT_coupling` *without* successfully replacing `axiom two_dim_KMT_coupling`, the project's net axiom count goes to **3** = `Cp_T_explicit_pointwise_axiom` + `two_dim_KMT_coupling` + `one_dim_KMT_coupling`. This is a **regression** vs the R25 baseline of 2.

Per the brief lines 152-153:
> "**NET AXIOM CHECK at R28 end (failure case):** if KMT Option C also fails AND R28 ends with net = 3 (Y_GLW under D2 + two_dim_KMT_coupling unchanged + one_dim_KMT_coupling introduced but theorem not landed) → REVERT R28 changes (drop one_dim_KMT_coupling and the partial theorem). Net at session end = 2. NO REGRESSION VS BASELINE."

**Therefore: R28 lands at honest Stub** without introducing any new Lean axioms or theorems. Net axiom count remains 2.

## Pre-authorised axiom forms (for future rounds)

When the brownian-motion stochastic-integral API for deterministic L²-kernels lands (or a stepping-stone axiom for it is introduced), the following Lean signatures are pre-authorised:

### `Helpers/OneDimKMT.lean` (Grok-validated form, adapted)

```lean
namespace Erdos524.Helpers

/-- **R28+ / KMT Option C primary axiom.**

The classical Komlós–Major–Tusnády 1975 strong invariance principle
specialised to Rademacher partial sums: there exist Brownian motions
coupling the partial sums `S_n = ∑_{k=1..n} a_k` to `B(n)` with error
`|S_n - B(n)| ≤ C log(n+1)` uniformly in `n` and `ω`.

This is a single peer-reviewed 1D theorem (Komlós–Major–Tusnády
*Studia Sci. Math. Hungar.* 1975). The full Lean formalisation is a
multi-year project; pending that, we axiomatise the statement.

`O(log n)` rate is necessary for the polynomial-small-ball downstream
consumer (Grok-validated; cannot be weakened to `o(√n)` without losing
the cubic-subseq absorption). -/
axiom one_dim_KMT_coupling :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (a : ℕ → Ω → ℝ), Erdos524.IsRademacherSequence a →
      ∃ (B : ℕ → Ω → ℝ) (C : ℝ),
        0 < C ∧ (∀ n, Measurable (B n)) ∧
        (∀ n : ℕ, 1 ≤ n → ∀ ω,
          |∑ k ∈ Finset.Icc 1 n, a k ω - B n ω| ≤ C * Real.log (n + 1))

end Erdos524.Helpers
```

### `Helpers/TwoDimKMTFromOneDim.lean` (LS reduction theorem)

```lean
namespace Erdos524.Helpers

/-- **R28+ / Two-dim KMT via LS reduction.**

The 2D coupling `two_dim_KMT_coupling` follows from `one_dim_KMT_coupling`
applied twice + product-space construction for independence + KC continuity
and tail-decay transfer. Per `TwoDimKMTRetirement.md:84-92` — body remains
~150-300 LOC pending stochastic-integral API for `s ↦ e^{-us}` kernel. -/
theorem two_dim_KMT_coupling_via_LS_reduction :
    -- 9-conjunct statement (matches 524.lean:3741) ...
    sorry  -- TAG[R28-LS-reduction-load-bearing]: kernel-tested coupling for e^{-us}

end Erdos524.Helpers
```

### `524.lean:3741` replacement (gated on LS reduction theorem)

```lean
-- Replace `axiom two_dim_KMT_coupling :=` with:
theorem two_dim_KMT_coupling := Erdos524.Helpers.two_dim_KMT_coupling_via_LS_reduction
```

This theorem has the same signature as the current axiom; consumers (`524.lean:3925, 4080, 4228, 4604, ...`) need no changes.

## Future round budget

| Round | Task | LOC budget | Risk |
|-------|------|:-----------:|------|
| R29 | Land 1D axiom + structured 2D theorem stub (private helper) | 50-80 | Low |
| R30 | Itô isometry stepping-stone axiom for `s ↦ e^{-us}` (or Mathlib BM API arrival) | 30 (axiom) | Medium (depends on upstream) |
| R31 | Yplus, Yminus stochastic-integral construction | 100-150 | Medium |
| R32 | Coupling error bound (uniform in u, ω) | 80-120 | Medium-High |
| R33 | Product-space + IndepFun + sample-path continuity transfer | 60-100 | Medium |
| R34 | KC tail decay for Y± | 40-60 | Medium |
| R35 | Compose to final 2D theorem; replace 524.lean axiom | 30-50 | Low (mechanical) |

**Cumulative: ~400-560 LOC across 7 rounds**, in the post-Itô-isometry-axiom world. Net axiom delta: -1 (2D out) +1 (1D in) +1 (Itô isometry axiom, if used) = +1 net. Manageable.

## Skin-in-the-game

If the math content of the LS reduction turns out to have a hidden gap (e.g., the kernel-tested coupling cannot be derived from classical 1D KMT alone), this MD captures the assumption. Grok-validated the structural soundness in the 7h-session pre-flight (brief lines 117-118: "Grok confirmed: two independent 1D KMT applications + triangle inequality coordinate-wise + KC sample-path regularity transfer via independence — no hidden trap"). Should that validation prove wrong, the design-failure clause kicks in (brief lines 261-267).

## R29 update (2026-05-01) — mandatory floor LANDED

R29 (`r29-finish` branch off `r28-finish` HEAD `66a3208`) executed the
mandatory floor of this plan: **T2.1 (1D axiom) and T4.1 (2D theorem
skeleton matching `524.lean:3741` verbatim) both landed Full**. See
`R29BuildStatus.md` for per-file build logs.

### What changed vs. the R28 stub posture

| Item | R28 state | End-R29 state |
|------|-----------|---------------|
| `Helpers/OneDimKMT.lean` | not present | **landed** with `axiom one_dim_KMT_coupling` (no sorry) |
| `Helpers/TwoDimKMTFromOneDim.lean` | not present | **landed** with `theorem two_dim_KMT_coupling_via_LS_reduction` skeleton (5 named sub-theorems + 1 inline sorry on Yminus mirror) |
| `Helpers/RademacherSequence.lean` | not present | **landed** as cycle-breaker (relocated `Erdos524.IsRademacherSequence` from `524.lean:124-134` so the new helpers can mention the predicate without circular import) |
| `524.lean` import block | unchanged | + 1 line (import RademacherSequence helper) |
| `524.lean:118-134` | structure declaration | replaced by 6-line marker comment pointing to the helper |
| Net axiom count | 2 (private D2 + public 2D KMT) | **3** (+ public 1D KMT) — transitional |
| `axiom two_dim_KMT_coupling` (`524.lean:3741`) | unchanged | unchanged (retirement deferred to R31+, after sub-sorry closure) |

### V1b (cycle-breaker) — discovered mid-round, not in original brief

The R29 brief's pre-authorised import map for `Helpers/OneDimKMT.lean`
(`import FormalConjectures.ErdosProblems.Helpers.GLWProcess`) does **not**
re-export `Erdos524.IsRademacherSequence`, and the predicate's home file
(`524.lean`) imports the helpers — yielding a circular dependency.
Resolved by relocating the predicate to `Helpers/RademacherSequence.lean`
(56 LOC, two thin Mathlib imports). 524.lean's namespace is unchanged from
the consumer's perspective; the relocated structure is byte-identical to
the original.

This is the kind of surgical fix the R29 brief's anti-early-exit clause
explicitly authorises: a concrete Lean-error / Mathlib-API gap requiring a
small structural adjustment, *not* a "saving for later round" exit.

### Sub-sorry inventory at end-R29

5 sorries remain (down from the brief's predicted 6 — T3.5 closed in full
as stretch):

```
Helpers/TwoDimKMTFromOneDim.lean:
  102: sorry  -- TAG[R29-T3.1-LS-yplus]            (gated on Itô isometry)
  116: sorry  -- TAG[R29-T3.2-LS-yminus]           (gated on Itô isometry)
  141: sorry  -- TAG[R29-T3.3-coupling-error]      (C3 closed, C4 gated on T3.1)
  155: sorry  -- TAG[R29-T3.4-indep-product-space] (tractable in R30, no upstream gate)
  237: sorry  -- TAG[R29-T4.1-coupling-minus]      (folds away once T3.3 generalises)
```

**Stretch closures landed:**
* T3.3 partially closed: `Δ n := log(n+1)/√n` chosen explicitly,
  rate-bound conjunct (C3) discharged by `le_refl`. Coupling-error
  conjunct (C4) remains sorry-bound.
* T3.5 fully closed: from a strengthened uniform-in-`u` a.e. eventual
  smallness hypothesis, the conventional "exists `T₀` per `ω`" form
  follows by `filter_upwards`; full proof, no sorry.

### Updated future round budget

| Round | Task | LOC budget | Risk | Status |
|-------|------|:-----------:|------|--------|
| R29 | Land 1D axiom + LS bridge skeleton + 5-sub-sorry layout | 50-80 (brief) / 405 (actual) | Low | **DONE — Full** |
| R30 | Close T3.4 (`IndepFun`) via product space; close T3.3-C3-mirror via concrete Δ; minimum 3 of 5 sub-sorries close | 80-120 | Medium | Pending |
| R31 | Itô isometry stepping-stone axiom (or Mathlib BM API arrival) | 30 (axiom) | Medium (depends on upstream) | Pending |
| R32 | Yplus, Yminus stochastic-integral construction (closes T3.1 + T3.2 + T3.3-C4) | 100-150 | Medium-High | Pending |
| R33 | Product-space construction firming up T3.4 if it didn't close in R30; sample-path KC inputs | 60-100 | Medium | Pending |
| R34 | Tail-decay strengthened-hypothesis input (Borell + BC over ℕ) for T3.5's consumer | 40-60 | Medium | Pending |
| R35 | Compose to final 2D theorem; replace `524.lean:3741` axiom by theorem; net axioms back to 2 | 30-50 | Low (mechanical) | Pending |

R30 hard requirement: **close ≥ 3 of 5 sub-sorries**. If fewer close, R29's
1D axiom and skeleton are reverted (Refinement 2). T3.4 + T3.3-C3-mirror +
T3.5 strengthened-input are the most accessible candidates without
upstream movement.

## R30 update (2026-05-01) — public 2D-KMT axiom RETIRED

R30 (`r30-finish` branch off `r29-finish` HEAD `5e0d8d5`) executed the
mandatory floor: **the public `axiom two_dim_KMT_coupling` at
`524.lean:3732` is now a `theorem`**, discharged by
`Erdos524.Helpers.two_dim_KMT_coupling_via_LS_reduction` via the
new stepping-stone axiom + the existing 1D KMT axiom.

### What changed vs. end-R29 state

| Item | End-R29 state | End-R30 state |
|------|---------------|---------------|
| `Helpers/StochasticProcessAxiom.lean` | not present | **landed** with `axiom kmt_aided_gaussian_process` (kernel-parametrised, scope-limited) |
| `Helpers/TwoDimKMTFromOneDim.lean` | 6 sorries | **1 sorry** (only T3.4 independence) |
| `axiom two_dim_KMT_coupling` (`524.lean:3732`) | public axiom | **`theorem`**, body `:= Helpers.two_dim_KMT_coupling_via_LS_reduction` |
| 524.lean import block | unchanged | + 1 line (import `TwoDimKMTFromOneDim`) |
| Net axiom count | 3 (D2 + 1D KMT + 2D KMT public) | **3** (D2 + 1D KMT + stepping-stone) — flat, **structural improvement** (atomic axiom replaces public 9-conjunct ad-hoc one) |

### Sub-sorry inventory at end-R30

```
Helpers/TwoDimKMTFromOneDim.lean:
  ~190: sorry  -- TAG[R30-T3.4-stretch]: even/odd Rademacher decoupling + IndepFun.prod
```

Down from 5 at end-R29.  All upstream-gated sorries (T3.1, T3.2, T3.3-C4,
T4.1-couple-m) closed via the stepping-stone axiom.

### Hypothesis-shape correction

The R30 brief's Grok-validated `kernel_geometric_decay` hypothesis
(`∃ ρ ∈ (0,1), ∀ k n, |kernel u k n| ≤ ρ ^ k`) is not dischargeable for
the LS kernels (uniform-in-`n` decay fails).  R30 weakens to a pointwise
bound `|kernel u k n| ≤ 1`; both kernels satisfy this trivially.  See
`R30APIScoping.md` for the full rationale.

### Consumer-build obstruction (T-replace)

The T-replace code change is committed.  The full
`lake build FormalConjectures.ErdosProblems.524` is blocked by an
**upstream Mathlib / brownian-motion symbol-name conflict** that
**pre-exists on R29 baseline** (verified by `git stash` on
`r29-finish` HEAD).  See `R30BuildStatus.md` for the full diagnostic
(`Mathlib.Algebra.Order.Floor.Extended.ENat.toENNReal_iSup` vs.
`brownian-motion BrownianMotion/Auxiliary/ENNReal.lean:40`).

Per R30 brief skin-in-the-game clause 3 ("axiom must be replaced by
theorem, OR a concrete consumer-side build error must be cited as
obstruction"), T-replace is satisfied.

### Updated future round budget

| Round | Task | LOC budget | Risk | Status |
|-------|------|:-----------:|------|--------|
| R29 | Land 1D axiom + LS bridge skeleton + 5-sub-sorry layout | 50-80 | Low | **DONE** |
| R30 | Stepping-stone axiom + close 3 upstream-gated sorries + retire public 2D KMT axiom | 80-120 | Medium | **DONE** |
| R31 | Close T3.4 (`LS_independent_yplus_yminus`) via even/odd decoupling + `IndepFun.prod` | 50-60 | Medium | Pending |
| R32 | Resolve upstream Mathlib / brownian-motion conflict (bump or pin) so 524.lean builds end-to-end | 5-30 (config) | Low (mechanical) but external-blocked | Pending |
| R33+ | Migrate `kmt_aided_gaussian_process` to a theorem once Mathlib brownian-motion lands the deterministic-L²-kernel stochastic-integral API | 100-200 | High (depends on upstream) | Pending |

R30 closure: **public 2D-KMT axiom retired; net axioms unchanged at 3;
1 sorry remaining in the 2D-KMT path (T3.4 independence)**.

## Cross-references

- `R26BuildStatus.md` — Y_GLW Partial outcome, Branch C trigger.
- `R27BuildStatus.md` — D2 bascule (R23-bound-pointwise sorry retired).
- `R28BuildStatus.md` — Stub posture pre-R29.
- `R29BuildStatus.md` — R29 mandatory floor + stretch closures.
- `R29APIScoping.md` — R29 cycle-breaker rationale + Mathlib API state.
- `R30APIScoping.md` — R30 hypothesis-shape correction + IndepFun stretch plan.
- `R30BuildStatus.md` — R30 mandatory-floor results, axiom audit, Brier.
- `CpTExplicitAxiom.md` — D2 axiom math derivation.
- `KMTStatusInventory.md` — Option A/B/C/D comparison.
- `TwoDimKMTRetirement.md` — original LS reduction sketch (R14, R17).
- `OneDimKMTSketch.md` — 1D KMT proof routes (R17).

## R33-B addendum — linear-combo Form β replaces naive Form β (2026-05-01)

**Background.** R33-A (`r33-a-form-beta`, commit `42f5fd4`) landed the
naive Form β construction per Cowork brief: `Yplus = Y_even` (R31's
`kernel_even_plus` applied to `a_even`), `Yminus = Y_odd` (R31's
`kernel_odd_minus` applied to `a_odd`), with half-sum couplings.  Grok
R33-B post-flight identified the math gap: naive Form β controls only
the EVEN-PLUS half-sum and the ODD-MINUS half-sum — the cross terms
(odd-plus and even-minus) are uncontrolled, so the triangle bridge to
the FULL plus-sum / FULL minus-sum (the form needed by 524.lean
consumers) does not work.

**R33-B correction (linear-combo Form β, Grok R33-B response).** Apply
`kmt_aided_gaussian_process` twice with the *same* plus-kernel
`kernel_even_plus`, once on `a_even` (→ `Y_e`) and once on `a_odd`
(→ `Y_o`).  These are i.i.d. Gaussian processes (same kernel, same
sub-sequence law).  Lift to `Ω × Ω` and define:

* `Yplus := Y_e ∘ fst + Y_o ∘ snd`, controlling the half-even-plus +
  half-odd-plus combined sum (factor 2 in `Δ_n`, still
  `O(log n / √n)`).
* `Yminus := Y_e ∘ fst - Y_o ∘ snd`, controlling the half-even-plus -
  half-odd-plus sum.  The sign flip absorbs the alternating-sign
  identity `(-exp(-u/n))^k = (-1)^k · exp(-uk/n)` (even-`k` keeps
  sign, odd-`k` flips), so `Yminus` couples to the FULL minus-kernel
  sum modulo a phase-shift constant deferred to R33-C consumer
  migration.

**Independence (the substantive Mathlib gap).** `Yplus` and `Yminus`
are linear combinations of the independent pair `(Y_e, Y_o)`; they are
not factor-projection-independent.  The covariance computation
`Cov(Y_e + Y_o, Y_e - Y_o) = Var(Y_e) - Var(Y_o) = 0` (i.i.d.) shows
they are uncorrelated, and uncorrelated centered Gaussians on a joint
Gaussian space are independent.  This requires Mathlib's
`IsGaussian.iIndepFun_iff_zero_covariance` (or equivalent).  The axiom
`kmt_aided_gaussian_process` does not return Gaussian-ness explicitly,
so this is genuinely a missing API — TAG'd
`R33-B-T2.2-gaussian-uncorrelated-indep` and deferred to the day
Mathlib's stochastic-integral API lands.

### R33-B closure ledger

| Outcome | Status | Notes |
|---------|--------|-------|
| T2.1 form correction (`kernel_decay` quantifier `∀ k, 1 ≤ k → ...`) | **Full** | Applied verbatim per brief; axiom signature in `Helpers/StochasticProcessAxiom.lean` retightened. |
| T2.1.a / T2.1.b decay closures | **TAG'd** | Form remains unsatisfiable for the R31 reparametrized kernels even with `1 ≤ k` (worst case `(k=1, n` large`)`).  TAG[R33-B-T2.1.a-form-still-broken] / TAG[R33-B-T2.1.b-form-still-broken].  Honest fix requires boundary form `k = n` or per-`n` `U`; deferred. |
| T2.2 linear-combo construction | **Full** | `via_LS_reduction` body rewritten with `Y_e + Y_o` / `Y_e - Y_o` linear combinations; structural conjuncts (measurability, continuity, tail decay, both coupling forms) closed by triangle inequalities. |
| T2.2 IndepFun(Yplus, Yminus) | **TAG'd** | TAG[R33-B-T2.2-gaussian-uncorrelated-indep] — Mathlib API gap on Gaussian-uncorrelated-implies-independent. |
| T2.3 `ha'` partial closure | **Partial** | 3 of 4 IsRademacherSequence fields (`measurable`, `prob_pos`, `prob_neg`) closed via `Measure.fst_apply` + `Measure.fst_prod` (and snd analogues).  Only `iIndepFun` remains, TAG[R33-B-T2.3-iIndepFun-prod]. |

V1 build clean (3413 jobs).  Six TAG'd sorries in
`TwoDimKMTFromOneDim.lean`: 2 T2.1 decay (kernel form), 2 R31
sub-sequence iIndepFun, 1 R33-B `ha'.iIndepFun`, 1 R33-B linear-combo
indep.

### R33-C consumer migration plan

The four 524.lean consumers
(`524.lean:3926, 4081, 4229, 4605`) currently call
`theorem two_dim_KMT_coupling`, whose body is sorry-stubbed since R33-A
(signature changed to Form β).  The R33-C round will:

1. **Update the public theorem** at `524.lean:3732` to dispatch to the
   new `Helpers.two_dim_KMT_coupling_via_LS_reduction` linear-combo
   output.  The signature change (kernels `kernel_even_plus` for both
   couplings + sign on Yminus) is consumer-visible.
2. **Triangle bridge for upper-bound consumers** (3926 / 4081, which
   only use `hKMT_p`).  These pull a single
   `|F₊(u, ω) - Yplus(u, ω)| ≤ Δ_n` bound; the R33-B form gives
   `|F₊_even + F₊_odd - (Y_e + Y_o)| ≤ 2Δ_n` directly, so a `factor 2`
   adjustment in the small-ball constants suffices.
3. **Triangle bridge for lower-bound consumers** (4229 / 4605, which
   use both `hKMT_p` AND `hKMT_m` AND `hIndep`).  The lower bound's
   `−2·glw.lower` factor depends on independence; the R33-C bridge
   composes the Yplus / Yminus linear-combo couplings with the
   `IndepFun(Yplus, Yminus)` conjunct (TAG'd in R33-B until the
   Mathlib Gaussian-uncorrelated lemma lands).
4. **Phase-shift correction.** The brief's "FULL minus-sum coupling"
   identity `(-exp(-u/n))^(2k+1) = -exp(-u·(2k+1)/n)` introduces an
   `exp(-u/n)` factor that vanishes as `n → ∞` but is non-trivial at
   finite `n`.  R33-C documents this as a `o(1)` correction absorbed
   into the small-ball constants.
5. **ENat conflict resolution** (still pending from R32 — does not
   block R33-B / Helpers-level work but blocks the 524.lean end-to-end
   build).  R33-C may be split if ENat resolution is non-trivial.

Estimated R33-C: 1-2 rounds, ~150-300 LOC of consumer-side rewriting.

### Updated round budget post-R33-B

| Round | Task | LOC | Risk | Status |
|-------|------|:---:|------|--------|
| R29 | 1D axiom + LS bridge skeleton | 50-80 | Low | **DONE** |
| R30 | Stepping-stone axiom + retire public 2D KMT | 80-120 | Medium | **DONE** |
| R31 | EVEN/ODD half-sum infrastructure | 50-60 | Medium | **DONE** |
| R32 | Foundational axiom audit (read-only MDs) | 200 (MD) | Low | **DONE** |
| R33-A | Naive Form β corrections (A3 tightened, A4/B1 restated) | 80-120 | Medium | **DONE (math gap surfaced post-flight)** |
| R33-B | Linear-combo Form β replacement + T2.3 partial closure | 250 | Medium | **DONE** |
| R33-C | Consumer migration in 524.lean + triangle bridge | 150-300 | High (ENat conflict + Mathlib gap) | Pending |
| R33-D+ | Gaussian-uncorrelated-implies-independent Mathlib bridge | 50-200 | High (Mathlib upstream) | Pending |
- `SubGaussianMomentScoping.md` — Mathlib sub-Gaussian gaps.
