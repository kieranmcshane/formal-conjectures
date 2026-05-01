# R31 build status — KMT Option C consumer audit + math infrastructure

**Round**: R31 (Cowork, single round, V1)
**Branch**: `r30-finish`
**Scope**: T1.1 (consumer audit) + T2.1 (kernel defs + bound lemmas)
+ T2.2 (two axiom applications). Stretch tasks T3.1 / T4.1 / T5.1
deferred — see "Stretch deferral" below.

## Summary

| Task | Status | Output | Notes |
|------|--------|--------|-------|
| T1.1 | **Full** | `Helpers/R31APIScoping.md` | 4/4 consumers audited; verdict NO on decoupled-form drop-in compatibility |
| T2.1 | **Full** | `kernel_even_plus`, `kernel_odd_minus` + their `_bound` lemmas | Compile clean; no sorries |
| T2.2 | **Full** | `LS_yplus_via_even`, `LS_yminus_via_odd` (axiom applications) | Compile clean; the only sub-sorries are the brief-authorized `IsRademacherSequence_a_{even,odd}` `indep` fields |
| T3.1 | **Deferred** | — | Existing `LS_independent_yplus_yminus` sorry encodes the impossible content (FULL-sum + IndepFun); cannot be closed honestly without first revising surrounding statement (T4.1), which audit gates |
| T4.1 | **Deferred** | — | Helper signature change would break consumer-side build at 4 call-sites; out of R31 scope |
| T5.1 | **Deferred** | — | Gated on T4.1 + audit (per brief); audit fails the gate |

## Build verification

### `Helpers/TwoDimKMTFromOneDim.lean` (R31-modified)

Command: `lake env lean FormalConjectures/ErdosProblems/Helpers/TwoDimKMTFromOneDim.lean`

Result:

```
warning: declaration uses 'sorry'   (line 207, pre-existing R30 LS_independent_yplus_yminus)
warning: declaration uses 'sorry'   (line 436, R31 IsRademacherSequence_a_even, TAG[R31-T2.2.indep-even])
warning: declaration uses 'sorry'   (line 448, R31 IsRademacherSequence_a_odd,  TAG[R31-T2.2.indep-odd])
```

No errors. The two new R31 sub-sorries are explicitly tagged and
brief-authorized as the "standard sub-sequence preserves i.i.d." sub-
step within the T2.2 helpers (`IsRademacherSequence_a_even` /
`IsRademacherSequence_a_odd`). Both are isolated to the `indep` field
of `IsRademacherSequence`; the `measurable / prob_pos / prob_neg`
fields are closed inline by `ha`-specialization at indices `2*k` and
`2*k+1` respectively.

**T2.1.a / T2.1.b (kernel bounds): both Full, no sorry.** The proofs
chain `Real.sqrt (1/2) ≤ 1` (via `Real.sqrt_one`) with
`Real.exp_le_one_iff` applied to a non-positive exponent
(handling the `m = 0` corner case via `Nat.eq_zero_or_pos m`).

**T2.2 (axiom applications): both Full, no sorry.** The axiom hypothesis
`|kernel u k n| ≤ 1` is satisfied by `kernel_{even_plus,odd_minus}_bound`,
and the Rademacher-property hypothesis is supplied by the
`IsRademacherSequence_a_{even,odd}` helpers (which are themselves Full
modulo the documented sub-sequence-independence sub-sorries).

### `524.lean` (consumer file, R31 untouched)

Command: `lake env lean FormalConjectures/ErdosProblems/524.lean`

Result: `error: unexpected token '/--'; expected 'lemma'` at
524.lean:3732:62 — **pre-existing ENat orthogonal blocker** documented
in `R30BuildStatus.md` (lines 73–98) as a Mathlib / brownian-motion
import-order conflict. **R31 did not modify 524.lean** (`git status`
shows only `Helpers/TwoDimKMTFromOneDim.lean` modified +
`Helpers/R31APIScoping.md` and `Helpers/R31BuildStatus.md` untracked).
The blocker is orthogonal to R31's mandatory floor and was named in
the R31 brief as a documented gating condition for the (deferred) T5.1
stretch.

## Stretch deferral rationale

### T3.1 — close `LS_independent_yplus_yminus` (R30 sorry)

The existing R30 sorry at `TwoDimKMTFromOneDim.lean:213` reads:

```lean
private theorem LS_independent_yplus_yminus
    (Yplus Yminus : ℝ → Ω → ℝ) :
    ProbabilityTheory.IndepFun
      (fun ω : Ω => fun u : ℝ => Yplus u ω)
      (fun ω : Ω => fun u : ℝ => Yminus u ω) ℙ := by
  sorry  -- TAG[R30-T3.4-stretch]
```

In the **enclosing** signature of `two_dim_KMT_coupling_via_LS_reduction`,
`Yplus` and `Yminus` are the FULL-sum-approximating Gaussians (the
axiom-application outputs from `LS_kernel_coupling` applied to the
`exp(-uk/n)` and `(-exp(-u/n))^k` kernels respectively). Their joint
law has cross-covariance `Var(Y_even) − Var(Y_odd) ≠ 0` in general
(R31 brief, Grok pre-flight), so the assertion `IndepFun ...` is
**mathematically false**. Closing the sorry honestly therefore requires
revising the enclosing statement to the decoupled form (T4.1) or to a
joint-correlated form (R32 design choice α). T4.1 is itself audit-
gated and deferred.

### T4.1 — revise `two_dim_KMT_coupling_via_LS_reduction` to decoupled form

Audit-gated (brief): "**Gated on consumer audit (T1.1) verifying the
revised form is consumer-compatible.**" The audit fails the gate
(`R31APIScoping.md`: 4/4 consumers incompatible). Revising the helper
signature without simultaneously rewriting the 4 consumers in
`524.lean` would change the type-checked contract relied on by lines
3925, 4081, 4229, 4605 of `524.lean` — i.e., would either compile-error
the consumers or change their meaning silently. Out of scope for R31's
single-round budget.

### T5.1 — revise public `theorem two_dim_KMT_coupling` in `524.lean:3741`

Gated on T4.1; T4.1 deferred. Additionally pre-blocked by the ENat
build error (which prevents *any* edit-and-build cycle on `524.lean`).

## Net axiom-budget impact

R31's T2.1 + T2.2 introduce **no new axioms**. They reuse the existing
`kmt_aided_gaussian_process` stepping-stone axiom (added in R30) twice,
once per even/odd sub-sequence. The only `sorry`-bearing private
declarations introduced by R31 are:

* `IsRademacherSequence_a_even.indep` — TAG[R31-T2.2.indep-even]
* `IsRademacherSequence_a_odd.indep`  — TAG[R31-T2.2.indep-odd]

Both will discharge to a one-liner once the standard
`ProbabilityTheory.iIndepFun.comp` / sub-family-selection lemma is
imported. No public theorem of `524.lean` consumes these helpers; they
are R32 infrastructure.

## Brier-honest calibration debrief

| Outcome | R31 prediction | R31 actual |
|---------|----------------|------------|
| T1.1 Full | 0.95 | Full |
| T2.1 Full | 0.85 | Full |
| T2.2 Full | 0.85 | Full |
| Joint mandatory floor | 0.69 | Full |
| T3.1 stretch | 0.65 cond | Deferred (audit gate) |
| T4.1 stretch | 0.70 cond | Deferred (audit gate) |
| T5.1 stretch | 0.30 cond | Deferred (audit gate + ENat) |

The 0.10–0.15 audit-incompatibility tail event in the R31 brief
materialised. Mandatory floor lands as predicted; the substantive math
result is the **identification of the original public-axiom-shape's
internal contradiction** (FULL-sum + unconditional IndepFun is
impossible) and the **landing of the EVEN/ODD half-sum Gaussian
infrastructure** (T2.1 + T2.2) that R32 will compose into a
mathematically-honest replacement. R30's nominal retirement →
R31's substantive correction trajectory holds.

— end of R31 build status —
