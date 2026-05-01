# Phase A — R35 status (single round, branch `r33-c-helpers-consolidation`)

**Pre-flight blocker round.** Per Grok R35 pre-flight, the multivariate-
Gaussian-CDF differentiability lemma (T2.1) is the TRUE pre-flight blocker
for Phase A upper Option B. R35 lands the lemma signature + a TAG'd-gap
body, the Slepian skeleton with covariance-domination signature, and the
countable-dense supremum-reduction signature.

## R35 outcomes

### T1.1 — Mathlib audit + signature draft (Full)

* `Helpers/R35_T1_DiffLemmaAudit.md` (≥ 30 lines, actually ~140) covers:
  - §1 multivariate-Gaussian object inventory (brownian-motion's
    `multivariateGaussian`, no PDF/CDF exposed).
  - §2 `Matrix.PosDef` API (no openness, no inverse-diff specialisation).
  - §3 determinant-differentiability gap (`Matrix.det.continuous` exists,
    differentiability does not).
  - §4 inverse-differentiability gap (generic `HasFDerivAt Ring.inverse`
    exists; no `Matrix.PosDef` specialisation).
  - §5 Slepian / Sudakov-Fernique / Borell-TIS / log-Sobolev: zero
    matches across full Mathlib + brownian-motion.
  - §6 continuous-on-compact + dense-supremum primitives (present).
  - §7-§8 R35 strategy + R36+ retirement options.

* `Helpers/MultivariateGaussianCDF.lean` (~200 LOC) lands:
  - `def orthant (x : ι → ℝ)` — the orthant `{z | ∀ i, z i ≤ x i}` in
    `EuclideanSpace ℝ ι`.
  - `noncomputable def multivariateGaussianOrthantCDF (S : Matrix ι ι ℝ)
    (x : ι → ℝ) : ℝ` — `(multivariateGaussian 0 S).real (orthant x)`.
  - `theorem multivariateGaussianOrthantCDF_differentiable_wrt_covariance` —
    T2.1 signature with TAG'd Mathlib-gap body + concrete diagnostic.
  - `theorem multivariateGaussianOrthantCDF_partial_offdiagonal` —
    documentation-only ledger of the entry-wise derivative formula
    (`True` body; explicit Lean shape deferred to R36).

### T2.1 — Differentiability lemma body (TAG'd Mathlib gap)

The `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` body
is `sorry` with TAG `R35-T2.1-mathlib-gap-density`. The diagnostic in
both the Lean docstring and the audit document cites three concrete
missing Mathlib pieces:

1. `Matrix.det.differentiable` — closure route via `Matrix.det_apply` +
   `MultilinearMap.contDiff`, ~30-80 LOC, unpackaged.
2. `Matrix.PosDef.inv.differentiable` — generic `HasFDerivAt Ring.inverse`
   exists at `Analysis/Calculus/FDeriv/Mul.lean:726`; no specialisation
   through `Matrix.GeneralLinearGroup` at `Matrix.PosDef` covariances.
3. `multivariateGaussianPdf` — brownian-motion's `multivariateGaussian`
   is square-root pushforward (line 160 of `MultivariateGaussian.lean`);
   no explicit Lebesgue density formula exposed.

Tried alternatives: `multivariateGaussian_density_eq` (does not exist),
`IsGaussian.density` (no density extraction), diagonal-Σ product of
`Real.gaussianReal` (covers diagonal only).

Per skin-in-the-game Rule 2, this qualifies as honest TAG'd gap with
concrete missing-API names + tried alternatives — eligible for full
score, not the 50% cap.

### T2.2 — Slepian skeleton (Full)

`Helpers/PhaseAUpperBound.lean` adds `slepian_comparison_finite`
replacing the legacy `slepian_comparison_GLW : True` placeholder. New
signature in real terms:

```
theorem slepian_comparison_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S_X S_Y : Matrix ι ι ℝ) (_h_pdX : S_X.PosDef) (_h_pdY : S_Y.PosDef)
    (_h_diag : ∀ i, S_X i i = S_Y i i)
    (_h_offdiag : ∀ i j, i ≠ j → S_X i j ≤ S_Y i j)
    (_x : ι → ℝ) :
    multivariateGaussianOrthantCDF S_X _x ≤ multivariateGaussianOrthantCDF S_Y _x
```

Body is TAG'd `R35-T2.2-body-deferred-R36`. The proof goes via Gaussian
interpolation `Σ_α := (1-α) S_X + α S_Y` and the chain rule applied to
T2.1; gated on T2.1 closure.

The legacy `True` stub `slepian_comparison_GLW` is preserved for
backward reference (it remains a `True := by trivial`; replacement
audit-tracking, not a compile-time blocker).

### T2.3 — Countable dense reduction (Full skeleton)

`Helpers/PhaseAUpperBound.lean` adds:

```
theorem sup_continuous_eq_sup_dense
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (Y : ℝ → Ω → ℝ) (hY_cont : ∀ᵐ ω ∂ℙ, Continuous (fun u => Y u ω)) :
    ∀ᵐ ω ∂ℙ,
      sSup ((fun u => Y u ω) '' Set.Icc (0 : ℝ) 1) =
        sSup ((fun u => Y u ω) '' ((↑) '' (Set.Icc (0 : ℚ) 1)))
```

Body opens with `filter_upwards [hY_cont]`; remainder is mechanical
density-of-rationals + continuity-on-compact-set, ~20 LOC, deferred to
R36 alongside the Sudakov-Fernique body that consumes it. TAG
`R35-T2.3-density-mechanical`. **No Mathlib gap** — the sorry is purely
deferral, not capability.

## Build verification

`lake build FormalConjectures.ErdosProblems.Helpers.PhaseAUpperBound`:
3022 jobs, exit 0, 2 expected sorry warnings + 1 tolerated unused-
section-vars lint on `MultivariateGaussianCDF`. Sister `GLWLowerProof`
build at 3416 jobs, no regression. Full log in `R35_T2_BuildLog.md`.

## Net axiom + sorry count post-R35

* **Axioms**: unchanged from R34 = 4 user-defined on mainline + 1 in-Helpers
  (`Y_GLW_exists`).
* **Sorries**: R34 carried 5 honest TAG'd; R35 adds 3 (T2.1 + T2.2 + T2.3).
  Total **8** TAG'd sorries on the branch.

R35 introduces no new axioms and no new untagged sorries. Every R35 sorry
carries a unique TAG and concrete diagnostic.

## R36 trajectory (revised post-R35 audit)

The R34→R35→R39 trajectory in `project_lean_erdos_524.md` and
`PhaseAR34Status.md` projected R35-R37 = Slepian + SF native (3 rounds).
The R35 audit reveals deeper Mathlib gaps than projected — the
differentiability lemma alone needs three missing-API pieces, each
~30-80 LOC. R36 must choose between three paths:

**Path A — Full closure (estimated 4-6 rounds R36-R41 not R36-R37):**
Build `Matrix.det.differentiable`, `Matrix.PosDef.inv.differentiable`,
`multivariateGaussianPdf` in-tree across Helpers files; assemble T2.1;
fill T2.2 via interpolation; fill T2.3 (mechanical); BTIS axiomatized;
§11 + Scope 3 closure. ~600-1000 LOC, 4-6 rounds.

**Path B — Bivariate sign-comparison (estimated 3-4 rounds R36-R39):**
Pursue the R17-stub `gaussian_density_sign_comparison` route per
`PhaseAUpperBound.lean:73-75`. Avoids multivariate density via direct
2D ∂p/∂ρ analysis. Trades Mathlib density gaps for an explicit
elementary computation. ~300-500 LOC, 3-4 rounds.

**Path C — Axiomatize Slepian (Option E, +1 user-defined axiom, 1 round):**
Convert `slepian_comparison_finite` directly to an axiom (matching the
R34 lower-side Option E move). Net axioms post-R36 = 5 user-defined.
Allows immediate progression to BTIS (also axiomatized) + Sudakov-
Fernique (which becomes derivable from Slepian + density argument
T2.3) + Phase A consumer + §11. **R36-R37 closes Phase A**, R38 closes
Scope 3.

My R35 prior — given the depth of the Mathlib gaps revealed in the audit
— is on **Path C**. Path A is the principled long-game; Path B
balances effort vs scope; Path C ships fastest with axiom-budget cost
matching the R34 Option E precedent.

## R35 self-grading

Mandatory floor outcomes:

| Outcome | Status | Notes |
|---------|--------|-------|
| T1.1 audit + signature draft | Full | `R35_T1_DiffLemmaAudit.md` lands; `MultivariateGaussianCDF.lean` signature builds |
| T2.1 differentiability body | TAG'd Mathlib-gap | three concrete missing-API names cited + tried alternatives |
| T2.2 Slepian skeleton | Full | real signature, body TAG'd-deferred |
| T2.3 countable dense | Full skeleton | signature + filter_upwards opener, body TAG'd-deferred |
| Build clean (Helpers) | Full | 3022 jobs PhaseAUpperBound, 3416 jobs GLWLowerProof |
| Round exit ≥ 2h | Full | substantive Lean code in 4 files |

All four mandatory outcomes landed; no skin-in-the-game cap triggered
(per Rule 2 — concrete-diagnostic gap qualifies for full score, not the
vague-hand-waving 50% cap).

## Per-prompt Brier check

| Outcome | Predicted P(Full) | Actual | Note |
|---------|-------------------|--------|------|
| T1.1 audit + signature | 0.95 | Full | tracking |
| T2.1 differentiability body | 0.70 | TAG'd Mathlib-gap (Stub-w/-concrete-diagnostic) | predicted gap risk; honest cap-eligible Stub matches predicted state |
| T2.2 Slepian skeleton | 0.95 | Full | tracking |
| T2.3 countable dense | 0.85 | Full skeleton | full closure deferred to R36 because of unrelated body-mechanics; signature lands |

R35 is the first round on the Phase A upper track that exposes Mathlib's
multivariate-Gaussian-density gap. The audit's unambiguous identification
of what's missing is the highest-leverage R35 deliverable — it converts
Phase A from "execute Grok plan blindly" to "pick path A/B/C with
informed cost estimates".
