# Phase A Inventory (Slepian + GLW lower bound)

**Out-of-band, read-only.** Goal: produce a calibrated baseline for
the *Phase A* frontier — both the upper-bound scaffold
(`PhaseAUpperBound.lean`) and the GLW lower-bound theorem
(`gao_li_wellner_small_ball_lower` in `524.lean`) — analogous to
`KMTStatusInventory.md`. Pass conducted 2026-05-01 against current
`r33-a-form-beta` HEAD (post-R33-A; `mathlib @ 25ce63313608`,
`brownian-motion @ 91267abd71bd`, `kolmogorov_extension4 @ 2c2b44e55251`).

## 1. Existing artifacts inventory

### 1a. Project `.lean` references

| File | Line | Kind | Status |
|---|---|---|---|
| `Helpers/PhaseAUpperBound.lean` | 73 | `theorem gaussian_density_sign_comparison : True` | **Stub** (`trivial`; R17 T3.2) |
| `Helpers/PhaseAUpperBound.lean` | 114 | `theorem slepian_comparison_GLW : True` | **Stub** (Gap A1; R16 O9) |
| `Helpers/PhaseAUpperBound.lean` | 138 | `theorem sudakov_fernique_GLW : True` | **Stub** (Gap A2; R16 O10) |
| `Helpers/PhaseAUpperBound.lean` | 164 | `theorem borell_tis_GLW : True` | **Stub** (Gap A3; R16 O11) |
| `Helpers/PhaseAUpperBound.lean` | 176 | `theorem phase_a_upper_bound : True` | **Stub** (assembly) |
| `524.lean` | 3504 | `theorem gao_li_wellner_small_ball_upper` | **theorem with inline sorry** (Phase A upper consumer; outside this audit but symmetric) |
| `524.lean` | 3578 | `theorem gao_li_wellner_small_ball_lower` | **theorem with inline sorry at 3614** (was R6-R7 axiom, R8 promoted) |
| `524.lean` | 3626 | `theorem gao_li_wellner_small_ball_lower_truncated` | proved from full-window via inclusion |
| `524.lean` | 3891, 4231, 4234, 4607, 4610 | call sites of GLW-lower | consumers |
| `524.lean` | 4213 | `theorem polynomial_sup_small_ball_lower` | consumer (two-factor `-2·glw.lower`) |
| `524.lean` | 4589 | `theorem polynomial_sup_small_ball_lower_uniform` | consumer (uniform-in-coeffs lift) |
| `Helpers/GLWLowerProof.lean` | 90, 183, 220, 245, 264 | `glwLowerCubicFactor`, `glwLowerEpsZero`, `glwLowerSupBoxEvent`, … | **Full** auxiliary algebra (positive, monotonicity, event-inclusion) |
| `Helpers/GLWLowerProof.lean` | 324, 336 | `gao_li_wellner_small_ball_lower_isGLWProcess_{Yplus,Yminus}` | **theorem with sorry** (helpers; KMT-side `IsGLWProcess` discharge) |

### 1b. Sorry-and-axiom tally on the Phase A active path

| Object | File:line | Severity |
|---|---|---|
| GLW-lower main bound | `524.lean:3614` | **load-bearing** (Karhunen–Loève + Talagrand entropy / Anderson + KL spectral) |
| `IsGLWProcess Yplus` discharge | `GLWLowerProof.lean:328` | downstream (KMT-coupling-side) |
| `IsGLWProcess Yminus` discharge | `GLWLowerProof.lean:340` | downstream (KMT-coupling-side) |
| Phase A upper scaffold | `PhaseAUpperBound.lean` | 5 `True := trivial` stubs (no sorry, vacuous) |

**Total:** 3 sorries on the Phase A active path; 5 vacuous `True`-stubs
on the upper-bound scaffold. **No `axiom` keyword on Phase A**: the
`gao_li_wellner_small_ball_lower` *axiom* of R6-R7 was promoted to a
theorem with inline sorry in R8.

### 1c. Upstream packages — comparison-theorem availability

| Location | Hit | Verdict |
|---|---|---|
| `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Fernique.lean` | `IsGaussian.exists_integrable_exp_sq` | **Fernique's theorem** (`exp(c · ‖·‖²)` integrable) — **Full** |
| `.lake/packages/mathlib/Mathlib/Probability/**` for `slepian / sudakov / borell / gauss.*comparison / covariance.*comparison / logSobolev / herbst` | **0 hits** | None of Slepian, Sudakov–Fernique, Borell–TIS, log-Sobolev present |
| `.lake/packages/brownian-motion/**` for same set | **0 hits** | Library is KC-continuity / stoch-integral / Komlós-L¹ focused; no Slepian-class comparison |

**Verdict on Mathlib comparison-theorem availability: 0%.** The
classical "Slepian → Sudakov–Fernique → Borell–TIS" pipeline that drives
sharp Gaussian-sup small-ball upper bounds is entirely absent at the
current toolchain pin.

## 2. Document inventory

* `Helpers/PhaseADiagnostic.md` — **177 lines, R14 originator with R16
  status table.** Enumerates four blockers: A1 (Slepian), A2
  (Sudakov–Fernique), A3 (Borell–TIS), A4 (quantitative
  Kolmogorov–Chentsov). Each is mapped to a specific Mathlib gap and
  workaround sketch. R16 update narrows A1 to "differentiability of the
  multivariate-Gaussian distribution function w.r.t. the covariance"
  (~30-50 LOC PR), A2 to "sup over interval = sup over countable dense
  subset a.s." (~20 LOC PR), A3 to "probabilistic log-Sobolev for
  standard Gaussian" (dedicated PR). Recommended bypass: accept
  Borell–TIS as a deferred axiom analogous to `two_dim_KMT_coupling`.

* `Helpers/PhaseAUpperBound.lean` — **182 lines, R14 scaffold + R16/R17
  doc upgrades.** Five theorems with `True := trivial` bodies, each
  carrying a ≥30-line proof outline in its docstring. Mirrors the
  classical pipeline: density sign-comparison → Slepian → SF → BTIS →
  assembly. Imports `GLWKernel` and `YGLWConstruction`. **No advance
  since R17.**

* `Helpers/Phase2Plan.md` — **~250 lines.** Describes the Phase 2
  endgame architecture (Nodes 1A → 1B → 2 → 4 → 6) which converges on
  replacing `gao_li_wellner_small_ball_{upper,lower}`. Crucially: the
  *lower* bound is described as needing `relevant_blocks_combined_lower`
  proved in the GLW context (Anderson + KL spectral estimates restricted
  to the relevant-frequency band). This is the mathematical content of
  the `524.lean:3614` sorry.

* `Helpers/R{18,19,20,21,22,23}ReadinessDiagnostic.md` — Each round
  carries a "Phase A: Slepian comparison" / "Phase A: Sudakov-Fernique"
  blocker entry (priority B). Status unchanged from R18 onward
  ("Slepian comparison theorem is not in Mathlib"). Phase A has been
  **deferred for 6 consecutive rounds** in favour of KMT (R30–R32)
  and the foundation audit (R32).

## 3. Mathlib comparison-theorem state

* **Mathlib:** there is NO Slepian inequality, NO Sudakov–Fernique, NO
  Borell–TIS, NO probabilistic log-Sobolev. Confirmed by full grep
  across `Mathlib/Probability/`. The closest infrastructure is:
  - `Mathlib.Probability.Distributions.Gaussian.Fernique` — Fernique's
    theorem (sub-Gaussian-tail for the *norm* of a Gaussian vector).
    Provides exponential-moment bounds on `‖X‖` but **not** on
    `sup_t X_t` of a Gaussian *process*.
  - `Mathlib.Probability.Distributions.Gaussian.{Basic,CharFun,Real}`
    — `IsGaussian` predicate, char-fun bridge.
  - `Mathlib.Probability.SubGaussian` — log-MGF + Chernoff (used for
    Rademacher/Bernstein bounds; orthogonal to Slepian).
* **brownian-motion:** stochastic-integral, Kolmogorov–Chentsov,
  covering-number / chaining (`Continuity/CoveringNumber.lean`)
  infrastructure exists; **no Slepian-class comparison**, no Borell
  concentration. The chaining infrastructure could in principle support
  a Talagrand-style generic-chaining LOWER bound, but no end-user lemma
  is exposed.
* **kolmogorov_extension4:** projective-limit / Kolmogorov-extension
  machinery; does not address Phase A.

**Verdict: NO. Mathlib has 0% of the Phase A upper-bound pipeline,
and 0% of the explicit-eigenvalue Karhunen–Loève + Talagrand-entropy
machinery needed to discharge the `gao_li_wellner_small_ball_lower`
sorry honestly.** The nearest available primitive is
`Mathlib.Probability.Distributions.Gaussian.Fernique` for the
*norm*, not the supremum.

## 4. Existing Phase A Lean files

* `Helpers/PhaseAUpperBound.lean` — **182 lines.** Five
  `True := trivial` stubs, each with ≥30-line proof outline:
  `gaussian_density_sign_comparison`, `slepian_comparison_GLW`,
  `sudakov_fernique_GLW`, `borell_tis_GLW`, `phase_a_upper_bound`.
  Imports `GLWKernel`, `YGLWConstruction`. **No real content** —
  pure scaffolding.

* `Helpers/GLWLowerProof.lean` — **342 lines.** This is the *lower-bound*
  side. Contains:
  - **Full** auxiliary algebra (~270 LOC): `glwLowerCubicFactor` and its
    monotonicity, `glwLowerEpsZero`, `glwLowerSupBoxEvent`, event-inclusion
    lemmas, dominated-`Y' → Y` lift.
  - **Two sorries** (lines 328, 340) on the
    `gao_li_wellner_small_ball_lower_isGLWProcess_{Yplus,Yminus}`
    discharge helpers — these depend on the KMT-coupling / Phase A
    foundation and are entangled with the AxiomFoundationAudit work.
  - The actual GLW-lower main bound lives in `524.lean:3578-3614`, not
    here; `GLWLowerProof.lean` provides the auxiliary surface that
    consumers use to *invoke* the bound.

* `Helpers/GLWLowerProof.lean` is the *only* lower-bound-side helper;
  the entire LOC-cost of the active sorry is currently absent —
  `524.lean:3614` is a single `sorry` with a 25-line BLOCKER-TRIED-NEEDS
  comment block but no actual proof skeleton.

## 5. `524.lean` Phase A consumers

| Caller | Line(s) | Object | What it extracts |
|---|---|---|---|
| `gao_li_wellner_small_ball_lower_truncated` | 3626-3650 | `gao_li_wellner_small_ball_lower` | Truncates full-half-line bound to `Icc 0 T` (free pass via `glwLowerSupBoxEvent_subset_truncated`) |
| `polynomial_sup_small_ball_lower` | 4213-4587 | `gao_li_wellner_small_ball_lower` × 2 | Two calls (Yplus, Yminus); product gives `-2·glw.lower` exponent. Calls require `IsGLWProcess Yplus/Yminus` (the two GLW-lower-side sorry helpers). **Currently entangled with AxiomFoundationAudit's `IndepFun` issue.** |
| `polynomial_sup_small_ball_lower_uniform` | 4589-4640+ | `gao_li_wellner_small_ball_lower` × 2 | Uniform-in-coefficients version; identical extraction pattern. |

**Three direct consumers in `524.lean`.** All depend on the lower-side
sorry (`524.lean:3614`) for the cubic-exponent estimate, plus the
`IsGLWProcess` discharge sorries (`GLWLowerProof.lean:328, 340`) for
adapting the bound to KMT-coupling marginals. The two
`polynomial_sup_small_ball_lower*` consumers are also flagged in
`AxiomFoundationAudit_T2_Consumers.md:96` as the load-bearing call sites
that depend on `IndepFun(Yplus, Yminus)` — meaning Phase A's lower side
**inherits** the form-α/β/γ choice from the KMT axiom audit.

## 6. Honest gap-and-effort estimate

### 6a. Mathlib gaps (in order of structural depth)

1. **Probabilistic log-Sobolev** (Borell–TIS upstream): **0%**.
   Dedicated PR; ~400 LOC by `PhaseADiagnostic.md`'s estimate.
2. **Slepian's lemma + multivariate-Gaussian-CDF differentiation**:
   **0%**. ~200 LOC (or ~50 LOC if the differentiation lemma lands as
   a separate Mathlib PR first).
3. **Sudakov–Fernique + countable-dense-set reduction**: **0%** (depends
   on Slepian). ~150 LOC; the dense-set lemma alone is ~20 LOC.
4. **Karhunen–Loève expansion of `K_GLW`** (lower-bound side):
   **multi-year project** per `524.lean:3606`. Mercer-style
   eigenfunction series + explicit eigenvalue decay `λ_k ~ k^{-2}` for
   the GLW kernel. No partial Mathlib infrastructure.
5. **Talagrand generic-chaining LOWER bound**: **0%** (Mathlib has
   covering-numbers in `brownian-motion/Continuity/CoveringNumber.lean`
   but no Talagrand entropy lemmas).
6. **Quantitative Kolmogorov–Chentsov** (Hölder-norm moment bound):
   *partial* via `brownian-motion`'s `kolmogorov_chentsov_continuity`,
   but the quantitative form is missing. ~50 LOC PR.

### 6b. LOC estimate

| Track | LOC | Notes |
|---|---|---|
| Phase A *upper* (Slepian + SF + BTIS, full) | **~750-1000** | A1 (≈200) + A2 (≈150) + A3 (≈400) + assembly + endpoint reparametrisation. Each step is independently a multi-PR upstream effort. |
| Phase A *upper* (axiomatised BTIS, native A1+A2) | ~300-450 | Bypass option from `PhaseADiagnostic.md` Option 2: accept Borell–TIS as a deferred axiom analogous to `two_dim_KMT_coupling`. Saves the largest of the three pieces. |
| Phase A *upper* (axiomatised whole, log-slack on consumers) | ~150 | Option 3: accept logarithmic slack, axiomatise A1+A2+A3 jointly. **Project-scope cost:** §11 limit law in `524.lean` becomes off by `O(log n)`, requiring statement revision. |
| GLW *lower* main bound (`524.lean:3614`) honest | **multi-year** | Karhunen–Loève + Talagrand chaining. |
| GLW *lower* main bound, axiomatised (Option C-style) | **~30-80** | Re-state as `axiom gao_li_wellner_small_ball_lower_axiom` (re-introducing the R6-R7 axiom posture) and prove the truncated form + the two `IsGLWProcess` helpers from it. **Strictly a regression** vs the R8 theorem-with-sorry posture, but the sorry is functionally an axiom anyway. |
| GLW lower `IsGLWProcess` helpers (`GLWLowerProof.lean:328, 340`) | ~50-150 each | Entangled with AxiomFoundationAudit form-α/β/γ outcome; cannot be tackled before R33-B/C settles the KMT axiom posture. |

### 6c. Round-count calibration

Rate assumption: ~200-400 LOC nets / round at ~50% Brier on mandatory
floors → ~100-200 effective LOC / round. Novel-formalization overhead
(cross-cutting Mathlib API gaps) typically adds ~30-40% rework.

| Option | LOC | Rounds (realistic) | Notes |
|---|---|---|---|
| **A — Full upstream-quality Phase A upper** | 750-1000 | **8-15** | All three Mathlib gaps (A1, A2, A3) closed in our project namespace, then `phase_a_upper_bound` assembled. Rate-limiting: A3 (log-Sobolev). |
| **B — Phase A upper with axiomatised Borell–TIS** | 300-450 | **3-5** | Native A1+A2 (Slepian + SF over a countable dense set), `borell_tis_GLW` remains an axiom. Most pragmatic path. |
| **C — Phase A upper, log-slack via triple-axiom** | 100-150 | **1-2** | Axiomatise all three; revise `524.lean §11` to absorb logarithmic slack. **Cheapest in LOC, but introduces 3 new axioms and forces a §11 statement change.** |
| **D — Phase A *lower* honest (KL + Talagrand)** | 1500+ | **15-30+** | Multi-year-by-`524.lean`'s own admission. Not feasible at our pace. |
| **E — Phase A *lower* axiom regression** | 30-80 | **1** | Re-introduce R6-R7 axiom posture for `gao_li_wellner_small_ball_lower`. Removes the line-3614 sorry but leaves an audit-visible axiom. **Strictly a labelling change.** |
| **F — Defer Phase A entirely; tackle other unblocked piece** | 0 | 0 | Pursue the AxiomFoundationAudit R33-B/C track (KMT form-α/β/γ rewrite) and the C1-C4 cleanup; revisit Phase A only after KMT settles. |

### 6d. Pre-flight risks for R34+ (Phase A start round)

1. **Three axiom-class gaps with no incremental progress.** Unlike KMT
   (where the sub-axiom factoring at R33 yielded a 50-150 LOC bridge),
   Slepian / SF / BTIS have no analogous "easy-bridge" reduction — each
   is its own Mathlib PR.
2. **Lower-side sorry is mathematically deep.** Karhunen–Loève for
   `K_GLW` is genuinely a multi-year upstream project; no shortcut path
   has surfaced in 6 rounds of diagnostics.
3. **Entanglement with AxiomFoundationAudit.** The lower-side
   `IsGLWProcess` helpers (`GLWLowerProof.lean:328, 340`) cannot be
   tackled before R33-B/C settles the KMT form-α/β/γ choice. **Phase A
   lower work is gated on KMT closure**, not vice versa.
4. **Cache-burn risk.** Phase A is lab-style work with high per-round
   diagnostic noise — the same 4 blockers have been re-diagnosed
   verbatim in R18-R23 readiness docs without LOC progress. Doing this
   *again* without committing to one of options B / C / E / F will
   produce another no-net-LOC round.

## 7. Recommendation

**R34+ should NOT pursue Phase A as the primary frontier. Pursue
KMT closure (R33-B/C continuation) + dead-code cleanup instead.**

Reasoning:

* **KMT closure is the closer frontier.** Per
  `AxiomFoundationAudit.md`, R33-A has produced the form α/β/γ analysis;
  R33-B (single-call A3 fix, ~1 round) and R33-C (form choice + 4-consumer
  rewrite, 1-3 rounds) are concrete, scoped, and not gated on
  multi-year-Mathlib work.

* **Phase A is gated on KMT.** The two `IsGLWProcess` discharge sorries
  in `GLWLowerProof.lean:328, 340` are downstream of the KMT-coupling
  output structure. Settling form α/β/γ for KMT *changes the statement*
  these helpers must discharge. Doing Phase A first would invalidate
  any work here.

* **C1-C4 dead-code cleanup is unblocked, ~0.25 rounds.** Per
  `AxiomFoundationAudit.md`'s R33-cleanup item, four dead R26 sub-lemmas
  in `GLWGaussianProjectiveLimit.lean` can be deleted; this is a free LOC
  decrease.

* **If Phase A must be touched in R34+, prefer Option B or E:**
  - Option B (axiomatised Borell–TIS, native Slepian + SF) — 3-5 rounds
    for a genuine Phase A upper closure with one residual axiom.
  - Option E (lower-side axiom regression) — 1 round, removes the
    `524.lean:3614` sorry by re-introducing the R6-R7 axiom posture.
    **This is a labelling-only change** (the sorry is functionally
    an axiom in scope-3 terms), but improves audit-tool output.

* **Honest projection to "Scope 3 closure" if Phase A starts at R34:**
  - Best case (Option B + KMT form α resolution): R34 (cleanup +
    Option E) + R35 (KMT form α) + R36-R38 (Phase A upper Option B) +
    R39 (assembly) ≈ **6 rounds**, with one residual axiom (BTIS) and
    one residual axiom (lower-side via Option E).
  - Mid case (Option B + KMT form β): R34-R36 KMT + R37-R41 Phase A
    Option B + R42 assembly ≈ **9 rounds**, two residual axioms.
  - Worst case (no clean form, full honest Phase A): **~25+ rounds**,
    Karhunen–Loève + Talagrand-chaining is a multi-year project that
    blows our budget.

**Net recommended R34 frontier ordering (in priority):**

1. **R34** — C1-C4 dead-code cleanup (0.25 rounds) + KMT form α/β/γ
   selection per R33-A Grok prompts (0.75 rounds).
2. **R35-R36** — KMT form chosen, rewrite consumers in `524.lean`
   (1-3 rounds depending on form).
3. **R37** — Phase A *lower* Option E (axiom regression) to clear the
   `524.lean:3614` sorry; close the two `IsGLWProcess` helpers now that
   KMT form is settled.
4. **R38+** — Phase A *upper* via Option B (axiomatised BTIS, native
   Slepian + SF). 3-5 rounds.
5. **R43+** — Final assembly + §11 limit law + scope-3 closure.

The Brier-honest read is that Phase A is the second-deepest Mathlib gap
in this project (after KMT), and unlike KMT it does **not** have an
"Option C" sub-axiom factoring that gets us to closure cheaply. Either
we accept axioms (Options B/C/E) or we wait for upstream Mathlib.

## Cross-references

- `Helpers/PhaseADiagnostic.md` — R14-R16 Mathlib gap analysis.
- `Helpers/PhaseAUpperBound.lean` — R14 scaffold (5 stubs).
- `Helpers/GLWLowerProof.lean` — Lower-bound auxiliary algebra and
  `IsGLWProcess` discharge helpers (2 sorries).
- `Helpers/Phase2Plan.md` — Phase 2 endgame architecture (Nodes 1A-6).
- `Helpers/AxiomFoundationAudit.md` (R32) — KMT form-α/β/γ analysis;
  Phase A lower side is downstream of this.
- `Helpers/KMTStatusInventory.md` — sibling inventory; this file mirrors
  its structure.
- `524.lean:3578-3614` — `gao_li_wellner_small_ball_lower` theorem +
  inline sorry (the active Phase A lower-bound gap).
- `524.lean:4213, 4589` — `polynomial_sup_small_ball_lower{,_uniform}`
  consumers.
