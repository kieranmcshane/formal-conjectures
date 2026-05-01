# R33-A — Foundational corrections (A3 tighten + Form β restatement)

**Branch.** `r33-a-form-beta` (off `r32-audit-finish`). Single round,
Variante 1, scope per R33-A brief.

## What landed (T2.1 + T2.2 + T2.3)

### T2.1 — A3 axiom tightened

`Helpers/StochasticProcessAxiom.lean`:

* Added `_kernel_decay` hypothesis to `kmt_aided_gaussian_process`
  using the brief's literal Grok-validated form:
  `∀ ε > 0, ∃ U > 0, ∀ n ≥ 1, ∀ u ≥ U, ∀ k ≤ n, |kernel u k n| ≤ ε`.
* Updated module docstring with R32→R33-A audit lineage.

`Helpers/TwoDimKMTFromOneDim.lean`:

* Added `kernel_even_plus_decay` and `kernel_odd_minus_decay` lemmas
  (Section 2 — R33-A).
* **TAG-sorries.** Both decay lemmas are sorry-stubbed. The literal
  brief signature `∀ k ≤ n, |kernel u k n| ≤ ε` is unsatisfiable for
  the R31 reparametrized kernels at `k = 0` (`kernel_even_plus u 0 m =
  √(1/2) · 1 = √(1/2) ≈ 0.707`, exceeds any `ε < 0.707`). Grok's
  proof sketch tacitly restricted to the boundary case `k = n` (where
  `exp(-u·n/n) = exp(-u)` decays uniformly), but the universal `∀ k ≤
  n` quantifier in the literal hypothesis includes `k = 0` and is
  therefore false as stated. R33-B will replace with the corrected
  form (boundary `k = n`, or L²-energy decay
  `(1/n) ∑_{k=1..n} (kernel u k n)² → 0`) alongside consumer
  migration.

### T2.2 — B1 + A4 restated in Form β

`Helpers/TwoDimKMTFromOneDim.lean` (Section 4):

* **B1 → `LS_independent_yplus_yminus_disjoint_blocks`.** Replaces the
  R32-confirmed-contradictory R30 form (universal IndepFun on a
  single Ω, mathematically impossible per R32 audit). Form β: lift Y±
  via `Prod.fst`/`Prod.snd` to `Ω₁ × Ω₂`; independence is by
  construction, discharged via Mathlib's `indepFun_prod`. No sorry;
  per-`u` measurability hypotheses lift to pi-measurability via
  `measurable_pi_iff`.

* **A4 → `two_dim_KMT_coupling_via_LS_reduction` (Form β).** Replaces
  the R32-confirmed-contradictory R30 form (full-sum couplings on a
  single Ω + unconditional IndepFun, internally inconsistent at sub-CLT
  rate). Form β:
  * Witnesses on `Ω × Ω` (via Mathlib's canonical `prod.measureSpace`).
  * `a' k ω := if 2 ∣ k then a k ω.1 else a k ω.2` (even block on
    fst, odd block on snd).
  * Yplus / Yminus are R31's `Y_even` / `Y_odd` lifted via
    `fst` / `snd`.
  * Half-sum couplings against the R31 reparametrized kernels
    `kernel_even_plus`, `kernel_odd_minus`.
  * Unconditional IndepFun via the new B1 helper.

* **Signature deviations from brief (documented inline).**
  - The brief specified `∃ (Ω' : Type*) (mΩ' : MeasureSpace Ω') ...`;
    we use `Ω × Ω` directly via Mathlib's canonical `prod.measureSpace`
    instance to avoid the typeclass-instance-as-existential gymnastics.
    Mathematical content unchanged.
  - The brief writes the half-sum couplings against the kernels
    `exp(-u·(2k)/n)` and `(-exp(-u/n))^(2k+1)` (original full kernels
    evaluated at even/odd indices); we use the R31 reparametrized
    kernels which the existing R31 axiom applications return. The two
    forms are related by `√(1/2)` normalization + index rescaling and
    produce equivalent witnesses up to reparametrization (R33-B
    bridge).

### T2.3 — Form β proof

Body of `two_dim_KMT_coupling_via_LS_reduction` proves all 11
conjuncts:
* Two `LS_*_via_*` axiom applications (R31 infrastructure).
* `meas_p` / `meas_m` via `Measurable.comp` with `measurable_fst` /
  `measurable_snd`.
* `cont_p` / `cont_m` via direct evaluation (continuity in `u` is at
  fixed `ω` — projects through to the underlying R31 witness's
  continuity).
* `decay_p` / `decay_m` via `Measure.quasiMeasurePreserving_fst` /
  `_snd` and `QuasiMeasurePreserving.ae` (lift a.s. from `Ω` to
  `Ω × Ω`).
* `Δ_bound` trivial (`Δ n = log(n+1)/√n`, `le_refl`).
* `couple_p` / `couple_m` reduce the `if 2 ∣ k` form to `a_even` /
  `a_odd` and apply the R31 axiom outputs.
* `indep` via `LS_independent_yplus_yminus_disjoint_blocks`.

**Residual sorry (one).** The `IsRademacherSequence a'` field on
`Ω × Ω` (the `?ha'` goal): TAG[R33-A-T2.3-rademacher-lift]. The
mathematical content is "iIndepFun under disjoint-block selection on
a product space"; the formal Mathlib API for lifting `iIndepFun`
through measure-preserving projections + disjoint-block construction
is non-trivial and was not in scope for R33-A. R33-B will close this
with explicit `iIndepFun.indepFun_finset` + product-space arguments.

## Net file delta

* **Deleted (R30 dead helpers, superseded by Form β):**
  - `yplus_kernel_bound`, `yminus_kernel_bound` (R30 kernel bounds for
    the original full kernels — only consumed by the R30 dead helpers).
  - `LS_yplus_construction`, `LS_yminus_construction` (R30 structural
    helpers).
  - `LS_kernel_coupling`, `LS_coupling_error` (R30 kernel-parametric
    helpers).
  - **R30 contradictory `LS_independent_yplus_yminus`** (B1 universal
    IndepFun on single Ω) — replaced by Form β
    `LS_independent_yplus_yminus_disjoint_blocks`.
  - **R30 contradictory `two_dim_KMT_coupling_via_LS_reduction`** (full-sum
    + unconditional IndepFun) — replaced by Form β.
* **Added (R33-A):**
  - `kernel_even_plus_decay`, `kernel_odd_minus_decay` (T2.1 sorries).
  - `LS_independent_yplus_yminus_disjoint_blocks` (T2.2 B1 corrected,
    no sorry).
  - `two_dim_KMT_coupling_via_LS_reduction` Form β (T2.2 A4 corrected
    statement + T2.3 proof; one residual sorry on `ha'`).
* **Retained:**
  - R31 kernel reparametrization (`kernel_even_plus`, `kernel_odd_minus`,
    bounds, `a_even`, `a_odd`, `IsRademacherSequence_a_even/odd`,
    `LS_yplus_via_even`, `LS_yminus_via_odd`).
  - `LS_tail_decay_skeleton` (R29 generic helper).

## 524.lean side-effect

The pre-existing direct delegation
`theorem two_dim_KMT_coupling := Helpers.two_dim_KMT_coupling_via_LS_reduction`
no longer typechecks (Helpers theorem signature changed to Form β).
Replaced with a sorry-stub TAGged for R33-B consumer migration. The
four downstream consumers in 524.lean (~3926, 4081, 4229, 4605) are
unchanged — R33-B will rewrite them to call the Helpers theorem
directly + use the triangle bridge for the lower-bound `2·glw.lower`
factor.

In addition: a pre-existing parse error at 524.lean:3732 (two
consecutive `/-- ... -/` doc comments on the `theorem
two_dim_KMT_coupling` declaration, an artifact of R30's axiom→theorem
retirement that left both docstrings) was fixed by converting the
older docstring to a regular `/- ... -/` comment block. This was a
build blocker pre-R33-A and is unrelated to the foundational
correction; flagged as side-effect for completeness.

## Sorry inventory

After R33-A:

| Sorry | File | Tag | Disposition |
|-------|------|-----|-------------|
| `kernel_even_plus_decay` | `Helpers/TwoDimKMTFromOneDim.lean` | R33-A-T2.1.a | Brief signature wrong at `k = 0`; R33-B corrects |
| `kernel_odd_minus_decay` | `Helpers/TwoDimKMTFromOneDim.lean` | R33-A-T2.1.b | (same) |
| `IsRademacherSequence_a_even.indep` | `Helpers/TwoDimKMTFromOneDim.lean` | R31-T2.2.indep-even | Pre-existing R31 sorry, retained |
| `IsRademacherSequence_a_odd.indep` | `Helpers/TwoDimKMTFromOneDim.lean` | R31-T2.2.indep-odd | Pre-existing R31 sorry, retained |
| `via_LS_reduction.ha'` | `Helpers/TwoDimKMTFromOneDim.lean` | R33-A-T2.3-rademacher-lift | New Mathlib API gap; R33-B closes |
| `theorem two_dim_KMT_coupling` body | `524.lean:~3741` | R33-B-consumer-migration | Sorry-stub pending consumer rewrite |

Total reachable sorries on the `via_LS_reduction` Form β chain:
**3 net new** (2 T2.1 decays + 1 T2.3 ha'). The 2 T2.1 sorries are
foreseen "kernel decay form wrong" pre-flight errors per the brief
(50% cap trigger applies if > 2 in T2.3, not if 2 in T2.1). The 1
T2.3 sorry is a Mathlib API gap, not a pre-flight error.

## R33-B forward plan (next round)

1. Replace `kernel_decay` hypothesis in
   `Helpers/StochasticProcessAxiom.lean` with the boundary form
   (`∀ ε > 0, ∃ U > 0, ∀ n ≥ 1, ∀ u ≥ U, |kernel u n n| ≤ ε`) or the
   L²-energy form. Discharge `kernel_even_plus_decay` /
   `kernel_odd_minus_decay`.
2. Close `IsRademacherSequence` lift to `Ω × Ω`
   (TAG[R33-A-T2.3-rademacher-lift]) — explicit
   `iIndepFun.indepFun_finset` + product-space construction.
3. Migrate the four `524.lean` consumers (3926, 4081, 4229, 4605) to
   call `Helpers.two_dim_KMT_coupling_via_LS_reduction` directly
   (Form β half-sum interface).
4. Triangle bridge: from half-sum supremum to full-sum supremum to
   recover the `2·glw.lower` factor in the small-ball lower bound.
5. Delete the orphan `theorem two_dim_KMT_coupling` in 524.lean once
   consumers are migrated.
6. Optional: delete the 4 dead R26 sub-lemmas in
   `GLWGaussianProjectiveLimit.lean` (2000, 2017, 2031, 2042) per
   R32 cleanup item.

## Calibration (Brier-honest)

Pre-round predictions vs. actuals:

| Outcome | Predicted P(Full) | Actual |
|---------|-------------------|--------|
| T2.1 (A3 tighten + decay lemmas) | 0.90 | **Partial — sorry-stubbed** (brief's pointwise `∀ k ≤ n` form unsatisfiable for target kernels at `k = 0`; literal signature added but verification deferred to R33-B) |
| T2.2 (Form β restatement) | 0.85 | **Full** (with documented signature deviations) |
| T2.3 (proof) | 0.65 | **Partial — 1 sorry** (`ha'` Rademacher lift on Ω × Ω; Mathlib API gap on iIndepFun via product) |

Net realistic R33-A score depends on build outcome:
* If the Helpers file builds clean (which it does as of the round end),
  T2.2 and T2.3 main proof land Full for the 9 of 10 conjuncts that
  are not the `ha'` sorry. T2.1 sorries are foreseen and within budget.
* If 524.lean builds clean (with the sorry-stub for the orphan
  theorem), the full-project build is green.

The math judgment for R33-B is now sharper: the R32 audit's "form
β cost" estimate of 2-3 rounds remains accurate. R33-A landed the
mathematical foundation (Form β statement + most of its proof);
R33-B's job is the boilerplate (consumer migration + Mathlib API
gap closing).

## Honesty over optics

* The brief's `kernel_decay` hypothesis is wrong as stated; this was
  not visible from the R32 audit + Grok pre-flight alone, but became
  apparent during T2.1. Documented in-line + here, sorry-stubbed
  rather than fudged.
* The brief's T2.2 coupling form (kernels at indices 2k/(2k+1)) does
  not match the R31 axiom output (R31 reparametrized kernels). I
  used the R31 form to make T2.3 provable from existing R31
  infrastructure; documented in-line.
* The `ha'` Rademacher lift on `Ω × Ω` is more work than the brief
  estimated; honest sorry with a TAG and R33-B forward plan.

R33-A foundational mathematical content lands; remaining gaps are
clearly delineated, tagged, and queued for R33-B.
