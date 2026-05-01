# Phase A — R34 status (single round, branch `r33-c-helpers-consolidation`)

**Phase A entry round.** Per the Phase A inventory at
`Helpers/PhaseAStatusInventory.md`, R34 starts the Phase A track with
the cheap, mathematically clear Option E move (lower-side axiom
regression) plus a re-audit of two R32-flagged `IsGLWProcess`
discharge helpers. R35-R39 will tackle Phase A upper Option B (Slepian
+ Sudakov-Fernique native, BTIS axiomatized) and §11 limit-law
assembly + Scope 3 closure.

## R34 outcomes

### Lower-side axiom regression complete

`gao_li_wellner_small_ball_lower` at `524.lean:3578` is now an explicit
`axiom`:

- **Pre-R34:** `theorem gao_li_wellner_small_ball_lower ... := by ... sorry`
  (R8 promotion of the original R6-R7 axiom; the `sorry` was
  functionally axiomatic — depended on multiple 0%-Mathlib gaps).
- **Post-R34:** `axiom gao_li_wellner_small_ball_lower : <same statement>`
  (no body). Docstring updated to document the R6 → R8 → R34 history,
  the multi-year Mathlib formalization gaps (Karhunen–Loève spectral
  expansion, Talagrand generic-chaining entropy, Anderson PosDef,
  Slepian / Sudakov–Fernique, BTIS), and the retirement path.

The corollary `gao_li_wellner_small_ball_lower_truncated` at
`524.lean:3622` is unchanged structurally — it applies the source via
`obtain` on the existential, syntactically identical for theorem and
axiom. Its docstring carries an R34 note.

**Net axiom count change (R33-D → R34):** +1 user-defined axiom
(labelling promotion of an inline sorry, not a mathematical regression).
Mainline 524 chain user-defined axioms after R34:

1. `Cp_T_explicit_pointwise_axiom` (R27)
2. `one_dim_KMT_coupling` (R29, dormant in mainline)
3. `kmt_aided_gaussian_process` (R30)
4. **`gao_li_wellner_small_ball_lower`** (R34 new, Phase A Option E)

Plus the in-Helpers stepping-stone axiom `Y_GLW_exists` (in
`Helpers/GLWProcess.lean`).

### IsGLWProcess helpers re-audited — STILL GATED

The two helpers
`gao_li_wellner_small_ball_lower_isGLWProcess_{Yplus,Yminus}` at
`Helpers/GLWLowerProof.lean:347, 362` (post-R34 line numbers) were
re-audited per the R34 prompt's hypothesis that R33-D's linear-combo
Form β + IndepFun rework might unblock them. Verdict:

**Both helpers STILL GATED** post-R33-D. Full audit at
`Helpers/R34_T1_IsGLWProcessAudit.md`. The R33-D contribution operated
on coupling structure (Ω vs Ω × Ω, IndepFun packaging across product
measure), not on per-Y K_GLW covariance derivation or joint
Gaussianity. The legacy-Ω form's 13-tuple destructure post-R33-D
supplies measurability + continuity + KMT coupling rate + IndepFun +
tail decay — but explicitly NOT the K_GLW covariance structure that
`IsGLWProcess` requires.

R34 deliverables on these helpers:
- Sorry bodies preserved (still genuinely gated, not closable in R34's
  budget).
- BLOCKER block-comment expanded with R34 status acknowledging the
  R33-D investigation and its non-unblocking nature.
- Docstrings updated with "**R34 audit verdict: still gated.**"
  pointer to the audit document.

Sister helpers on the upper side
(`gao_li_wellner_small_ball_upper_isGLWProcess_{Yplus,Yminus}` at
`Helpers/GLWUpperProof.lean:281`) carry IDENTICAL gating; they
should retire together when one of the resolution paths lands. Most
practical path: extend `two_dim_KMT_coupling` (or its legacy-Ω form)
to also produce `IsGLWProcess Y±` per marginal, leveraging the
Letwin–Sawhney 2-independent-1D-KMT view (each Y is an Itô integral
against an independent BM, hence Gaussian + K_GLW covariance by
construction). Estimated 1-2 rounds when prioritized; not in R35+ Phase
A budget.

### Build verification (T2.5)

- `lake env lean Helpers/GLWLowerProof.lean`: clean. Two expected
  sorry warnings (R34 carry-overs).
- `lake build FormalConjectures.ErdosProblems.524`: blocked on the
  pre-existing ENat conflict in `BrownianMotion.Auxiliary.ENNReal`
  vs `Mathlib.Algebra.Order.Floor.Extended`'s `ENat.toENNReal_iSup`.
  TAG `R34-T2.5-ENat-pre-existing`. This is the orthogonal blocker
  per agent `trig_01P8K24FGqQF6zqTKY4vQWRD` monitoring; independent of
  R34 work. Full log at `Helpers/R34_T2_5_BuildLog.md`.

## R35-R39 Phase A upper Option B scope

Per the Phase A inventory, R35+ executes the upper-bound side native
where feasible (Slepian + Sudakov-Fernique) and axiomatizes BTIS.

### R35 — Slepian comparison signature + lemma (estimated 1 round)

- Define `slepian_comparison_GLW : ...` in
  `Helpers/PhaseAUpperBound.lean`. Statement: for two centered
  Gaussian fields with `cov₁ ≤ cov₂` pointwise + variance-matched,
  the small-ball probability of `field 2` is at most that of
  `field 1` (the standard Slepian inequality, specialized to GLW
  configurations).
- Prove using Mathlib's existing comparison-of-Gaussian-vectors
  infrastructure (if available) or axiomatize as a documented Mathlib
  gap pending upstream landing of Slepian's lemma.
- **Pre-flight Grok prompt** (T3.2 stretch): draft a query asking
  Grok which formulation of Slepian's lemma is most amenable to a
  Mathlib formalization sketch (covariance-matrix monotonicity vs
  field-pointwise, finite vs. infinite-dim, measurability-of-sup
  hypothesis).

### R36-R37 — Sudakov-Fernique reduction over countable dense set (~2 rounds)

- Reduce the GLW small-ball upper bound from `sup_{u ∈ [0,T]}` to
  `sup_{u ∈ Q ∩ [0,T]}` for `Q` countable dense, using sample-path
  continuity (already in `IsGLWProcess`).
- Apply Sudakov-Fernique to bound the supremum over the countable set
  by an entropy integral. This is the native step that, combined with
  Slepian, drives the cubic exponent in `|log ε|^3`.
- Two rounds budget: SF reduction structural, then SF entropy bound.

### R38 — BTIS axiomatized + assembly (~1 round)

- Add `axiom BTIS_concentration_GLW : ...` to the Helpers chain
  (Borell-TIS Gaussian concentration around the median of the
  supremum). 0% Mathlib per Phase A inventory.
- Assemble the upper-bound proof from Slepian + SF + BTIS into a
  closed `theorem gao_li_wellner_small_ball_upper` body, retiring its
  R7 inline sorry (analogous to R34's lower-side regression but in
  the *forward* direction — closing rather than re-axiomatizing).

### R39 — §11 limit-law assembly + Scope 3 closure (~1 round)

- Lift the small-ball upper + lower bounds (now both at user-defined
  axiom or theorem-with-axiom-content level) through the §11 random-
  polynomial small-ball law via Borel-Cantelli + block independence
  (already in `Helpers/CentralBinomLower.lean` etc.).
- Verify the public-API consumers in 524.lean (`polynomial_sup_*`,
  `chojecki_sparse_lower_envelope_proof`) all type-check end-to-end
  modulo ENat blocker.
- Declare Scope 3 closure with 5 user-defined axioms documented as
  upstream-pending: `Cp_T_explicit_pointwise_axiom`,
  `one_dim_KMT_coupling`, `kmt_aided_gaussian_process`,
  `gao_li_wellner_small_ball_lower`, `BTIS_concentration_GLW`.
  Plus the 3 R33 TAG'd Mathlib/bridge gaps.

## Calibration

R34 was the cheap Phase A entry — landed in 1 round per the prompt's
estimate (joint mandatory floor `~0.45`, realistic score 250-380 pts).
The R34 work was almost entirely mechanical (axiom rename + comment
refresh + audit doc) with the only uncertain task being T2.3
(IsGLWProcess helpers closure attempt; verdict came back STILL GATED
which is honest documented gating per the round prompt's calibration
framing).

R35-R39 carries the actual Phase A mathematical work. Native Slepian
+ SF is the load-bearing structural piece; BTIS axiomatization is the
honest acknowledgment of a 0% Mathlib gap.

**Phase A total budget:** 4-5 rounds (R34-R39 = 6 if all stretch
hits), matching the Phase A inventory's "Option B realistic" estimate.
