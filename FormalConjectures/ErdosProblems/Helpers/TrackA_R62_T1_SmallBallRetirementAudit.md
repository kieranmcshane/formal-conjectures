# Round 62 — T1 audit (mainline, `r46-track-a-mge-posdef`)

**Date:** 2026-05-03. **Branch:** `r46-track-a-mge-posdef` HEAD `f4011b9`
(post-R61 GLW Path A pragmatic close). **Pin:** `mathlib4 @ 25ce63313608`,
`leanprover/lean4 v4.27.0-rc1`, `brownian-motion @ 91267abd71bd`.
**Audit type:** R62 mandatory T1.0 + T1.1 (per
`feedback_paper_recheck_t10` and `feedback_track_c_round_process` —
Cowork-drafted brief depending on paper-application claims; T1.0
paper-recheck must precede T1.1 grep audit; if any claim cannot be
verified, flag explicitly and propose alternative).

## TL;DR

**The R62 brief's central claim — that the now-Full R61 GLW finite-dim
Lemmas 4.1 + 4.2 retire axioms A4 + A5 in 60–130 LOC of body composition
— is NOT supported by the in-tree state at HEAD `f4011b9`. The chain
mismatch documented in the R50 audit (`Round50_T1_GLWShortcutAudit.md`,
mismatch ledger entry #16) still holds in full force after R59 → R60 →
R61.**

Three pieces of standing evidence (all reconfirmed at this audit):

1. **Axiom signature scope is unchanged.** A4 + A5 (`524.lean:3643` /
   `:3574`) are *Gaussian-process* small-ball asymptotics over the
   continuous index set `u ≥ 0` for an `IsGLWProcess Y`, with cubic-rate
   `|log ε|^3` decay. The R59 → R61 work is on *finite-dimensional
   deterministic* matrix identities for `glwMatrixA m hm : Matrix
   (Fin (m·m)) (Fin (m·m)) ℝ`. There is no in-tree code linking the two.

2. **R59 → R61 finite-dim helpers have zero consumers.** `grep -l` on
   `glwMatrixA | glwMatrixB | hierarchicalGrid | glw_lemma_4_1 |
   glw_lemma_4_2 | glw_det_lower_bound` across `FormalConjectures/`
   returns exactly one file: `Helpers/GLWSmallBallShortcut.lean` itself.
   Nothing consumes the Cauchy-form matrix or its Lemma 4.1 / 4.2
   bounds. The R61 audit's T1.7 (`TrackA_R61_T1_PathAAudit.md:239–240`)
   explicitly stages A4/A5 retirement to "R62" without doing any of the
   bridge work.

3. **The α/β/γ/δ/ε bridge is still 0% in Mathlib + 0% in-tree.** The
   chain components R50 identified (discretization + Anderson +
   tail-handling + optimization + IsGLWProcess covariance extraction)
   remain absent at this pin. Grep for `Anderson | anderson_inequality
   | anderson_ball` in `Mathlib/` returns zero hits at
   `mathlib4 @ 25ce63313608`; in-tree Anderson references in
   `Helpers/GLWUpperProof.lean:135–163` are placeholder *factor*
   definitions (`glwUpperAndersonFactor c m ε := exp(-c·m·ε²)`), not
   the multivariate inequality itself; Anderson-as-axiom appears in
   `Helpers/GLWBoxProbInstance.lean:43` as a V1 *field*, also not a
   proof.

This audit is **mismatch ledger entry #18**, same family as #16 (R50)
and #14: a Cowork-drafted brief presupposing finite-dim deterministic
identity = bridge to continuous-process asymptotic, with Grok strategic
review validating only the deterministic half (Probe 3 + Bonus 3
"60–130 LOC" estimate) without flagging the bridge gap.

Per `feedback_paper_recheck_t10` standing protocol and the R50
precedent (`PhaseV2R50Status.md`), R62 ships **T1.0 + T1.1 audit only**;
**T2.1 + T2.2 SKIPPED**; **T3 + T4 reduced to status doc + audit
commit**. **Net debt change: 0 sorries / 0 axioms = 0 net.** Mainline
ledger 18 → 18; axiom inventory 10 → 10. **Audit-redirect, not closure
round.**

---

## T1.0 — Paper recheck (per `feedback_paper_recheck_t10`)

**Source-of-truth.** The R60 attempt-2 audit
(`TrackA_R60_T1_PerLemma41Audit.md` §T1.6) is the verbatim
arXiv:1001.0200v1 §4 source-of-truth at the project pin. R59→R60 used
this fetch to correct the R59 sigs to paper-faithful form (Cauchy-form
`a_{ij} = 1/(δ_i+δ_j)`, inequalities `per(a) ≤ 1` + `det(a) ≥
(240·e)^{-2m³}`, ratio-based perturbation in Lemma 4.1). R61 closed
`per ≤ 1` Full + Lemma 4.1 perturbation Full and axiomatized
`glw_det_lower_bound`.

**§4 application chain (paper, not yet in-tree).** GLW 2010 §4 applies
Lemmas 4.1 + 4.2 to the Gaussian-process small-ball bound through the
following structural chain (textbook Talagrand / Ledoux / Anderson
machinery):

* (α) **Discretization.** Reduce
  `P(sup_{u ∈ [0,T]} |Y(u)| ≤ ε)` to a finite-grid event
  `P(∀ i ∈ Λ_m, |Y(t_i)| ≤ ε)` via path continuity + uniform
  modulus estimates.
* (β) **Anderson's multivariate inequality.** Lower-bound the
  finite-dim Gaussian small-ball
  `P(|G_Λ|_∞ ≤ ε) ≥ vol(box) · density(0)`-style estimate where
  `G_Λ` is the centered Gaussian on `Λ_m` with covariance `Σ_Λ`. The
  Anderson lower (resp. upper) bound is what links the box-event
  probability to `det(Σ_Λ)^{-1/2}` via the Gaussian density at zero.
* (γ) **Tail handling for the FULL-window lower.** A4 is stated for
  the unbounded half-line `u ≥ 0`; the truncation `T(ε) ~ |log ε|²`
  bridge is baked into the axiom statement (`524.lean:3624–3630`)
  via a Ledoux §1.3 BTIS-tail estimate.
* (δ) **Optimization.** The cubic-rate factor `|log ε|^3` arises from
  optimizing `m(ε) ~ |log ε|`: each grid level adds `m` to the chain,
  with `m³` from the `det(Σ_Λ_m) ≥ (240·e)^{-2m³}` plug-in (Lemma 4.2)
  + KL/Talagrand entropy coverage.
* (ε) **`IsGLWProcess` covariance extraction.** A4/A5 abstract over
  any `Y` satisfying `IsGLWProcess`; the §4 chain consumes the
  covariance-kernel side of this predicate to identify `Σ_Λ` with
  the discretized GLW kernel matrix.

**The R59→R61 work covers the deterministic Lemma-4.1 + Lemma-4.2
*statements* used at step (β) (and the det side at step (δ)), but
none of (α), (β-Anderson-proper), (γ), or (ε) is touched.** The
R59→R61 helpers are ingredients, not the recipe.

**Paper budget for the chain.** GLW 2010 §4 itself runs ~6 pages of
dense classical machinery on top of the Lemmas. Under the
`anderson + KL-expansion + Talagrand-entropy` Mathlib gap profile
laid out in the A4/A5 axiom docstrings (`524.lean:3552–3565`,
`:3632–3641`), the residual blocker is "a multi-year Mathlib
formalization project, not a tactical proof gap" — quoted verbatim
from the project's own axiom-introduction commentary at R34/R36.

**T1.0 verdict:** the brief's premise that "now that R61's GLW
finite-dim work has landed, the bridge to A4/A5 is a 60–130 LOC
mechanical composition" **does not survive paper recheck**. The
brief's "standard Gaussian-density-times-volume estimate" sentence
is hand-waving over multi-year Mathlib gaps (α/β/γ/δ/ε above).

---

## T1.1 — Mathlib + in-tree API verification at pin

### A4 / A5 axiom signatures (verbatim, unchanged since R34/R36)

| # | Axiom | Location | Verbatim shape |
|---|-------|----------|----------------|
| A4 | `gao_li_wellner_small_ball_lower` | `524.lean:3643` | `(glw : GaoLiWellnerConstants) → ∀ {Ω} [MeasureSpace Ω] [IsProbabilityMeasure ℙ] (Y : ℝ → Ω → ℝ), IsGLWProcess Y → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀], exp(-glw.lower · |log ε|^3) ≤ (ℙ {ω | ∀ u ≥ 0, |Y u ω| ≤ ε}).toReal` (full half-line lower) |
| A5 | `gao_li_wellner_small_ball_upper` | `524.lean:3574` | `(glw : GaoLiWellnerConstants) → ∀ {Ω} ..., IsGLWProcess Y → ∃ ε₀ T, 0 < ε₀ ∧ ∀ ε ∈ (0, ε₀], (ℙ {ω | ∀ u ∈ Icc 0 (T ε), |Y u ω| ≤ ε}).toReal ≤ exp(-glw.upper · |log ε|^3)` (truncated upper) |

Both signatures are **continuous-index Gaussian-process small-ball
asymptotics** and abstract over `Y` via `Erdos524.Helpers.IsGLWProcess
Y`. There is no `Matrix`, no `MultivariateGaussian`, no `glwMatrixA` in
sight on either side.

### Caller list — A4 + A5 consumers in mainline

`grep -rn "gao_li_wellner_small_ball_lower\|gao_li_wellner_small_ball_upper"
--include="*.lean" --exclude-dir=.lake .` returned the consumer sites in
`524.lean` (axiom-decl sites + truncated-corollary derivation +
downstream pipeline applications):

| Site | Use |
|------|-----|
| `524.lean:3574` (axiom A5 decl) | declaration |
| `524.lean:3643` (axiom A4 decl) | declaration |
| `524.lean:3675` | `gao_li_wellner_small_ball_lower_truncated` derivation (A4 → truncated form) |
| `524.lean:4107`, `:4265` | A5 application via `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus` discharge |
| `524.lean:4421-4426`, `:4801-4806` | A4 application to `Yplus` and `Yminus` GLW process pair |
| `524.lean:6866-6868` | `εGLW_p`, `εGLW_m` consumption in pipeline (A4 ε₀ extraction comment) |
| `524.lean:7638` | A5 referenced in axiom-inventory comment |

Plus the helper-side usage:

| Site | Use |
|------|-----|
| `Helpers/CauchyDetLowerBound.lean:25` | docstring reference (no-Gaussian / no-KMT alternate path) |

Axiom-to-theorem swap is signature-preserving, so all consumers above
remain compatible *if* a body is supplied. **The constraint is the
existence of an honest body, not consumer compatibility.**

### R59 → R61 in-tree helper consumers — zero outside the defining file

`grep -l "glwMatrixA\|glwMatrixB\|glw_lemma_4_1\|glw_lemma_4_2\|
glw_det_lower_bound\|hierarchicalGrid"` over `FormalConjectures/`
returns exactly one file: `Helpers/GLWSmallBallShortcut.lean`.

Per the R60 file-content header at line 339: *"NOT consumed by any
other file at R60 close."* Per the R61 audit T1.7 (out-of-scope
section): *"A4 / A5 retirement — staged R62."* No bridge code
materialised in R59, R60, or R61.

### Mathlib bridge components at pin `25ce63313608` — reconfirmed 0%

| Bridge component | Mathlib pin status | In-tree status |
|------------------|--------------------|----------------|
| Anderson's multivariate inequality (PSD covariance, lower + upper box-event) | **0%** (grep `Anderson\|anderson_inequality\|anderson_ball` in `Mathlib/` → 0 hits) | placeholder `glwUpperAndersonFactor` in `Helpers/GLWUpperProof.lean:140` (a `noncomputable def` for the *factor*, not the inequality); `anderson_lower` / `anderson_upper_sub` are V1-axiom *fields* in `Helpers/GLWBoxProbInstance.lean:43-44`, axiomatized not proven |
| Karhunen–Loève spectral expansion of `K_GLW` with `λ_k ~ k^{-2}` | 0% (per A4/A5 docstrings `524.lean:3553`, `:3603-3605`) | 0% in-tree |
| Talagrand generic-chaining entropy bounds for Gaussian processes | 0% (per A4/A5 docstrings) | 0% in-tree |
| Slepian / Sudakov–Fernique comparison | 0% (per A4/A5 docstrings; R35 stub-with-signature `slepian_comparison_finite` exists for future-Mathlib retirement) | 0% in-tree |
| Borel-TIS Gaussian concentration | 0% in Mathlib at pin; in-tree `borell_tis` Full closed via Path B' (TD2, MGF + Chernoff bypass) — **NOT directly applicable to A4/A5 small-ball lower** (Borel-TIS is a concentration bound for `sup`-deviation, not a small-ball tightness bound) |
| Discretization-of-sup-over-continuous (path continuity → finite-grid event reduction) | 0% in Mathlib at pin | 0% in-tree |
| `IsGLWProcess` covariance extraction at finite grid | predicate exists at `Helpers/GLWProcessPredicate.lean:78` but no covariance-matrix extraction lemma in-tree at HEAD `f4011b9` |

**T1.1 verdict:** the brief's "Mathlib API audit" task can confirm the
finite-dim ingredients (Cauchy matrix, det lower bound axiom,
permanent ≤ 1, ratio perturbation) but cannot confirm any of the
bridge components. **A 50–80 LOC body for A5 (resp. 30–50 LOC for A4)
that honestly composes the axiom would have to invoke at least one of
{Anderson, KL, Talagrand, discretization}, none of which are
available in any form admitting an honest `theorem`-with-body
swap.**

---

## T1.2 — Chain-mismatch finding (R50 entry #16 reconfirmed; new entry #18)

The R62 brief presupposes the chain:

```
[R61 Lemma 4.1 Full]   [R61 Lemma 4.2 per side Full]   [R61 det side axiom]
                              ↓
                    [R62 50–80 + 30–50 LOC body]
                              ↓
       [Continuous-time IsGLWProcess small-ball bound  exp(-c·|log ε|³)
        on full half-line (lower) / on Icc 0 (T ε) (upper)]
```

The arrow from "R61 finite-dim Lemmas" to "R62 small-ball bound" requires:

* (α) Discretization of `sup_{u ∈ [0,∞)}` (resp. `sup_{u ∈ Icc 0 (T ε)}`)
  to a finite grid event, *with quantitative error control matched to
  the cubic rate*.
* (β) Anderson's multivariate inequality at PosDef covariance, applied
  to bound the finite-grid Gaussian box-event by `det(Σ)^{±1/2}`-style
  factors.
* (γ) For A4 only: Ledoux §1.3 tail-handling on the unbounded
  half-line `u ≥ 0`.
* (δ) Optimization `m(ε) ~ |log ε|`, with the Lemma 4.2 det side
  plug-in giving the `m³` exponent.
* (ε) Identification of the finite-grid covariance `Σ_Λ_m` with
  `glwMatrixA m hm` (or its R-scaled analogue) via `IsGLWProcess`'s
  covariance kernel.

**Each of (α), (β-proper), (γ), (δ), (ε) is, individually, beyond a
single round's LOC budget.** Their composition into A4/A5 is the
multi-year Mathlib formalization project that the A4/A5 axiom
docstrings explicitly call out.

**Why R59-R61 do not soften this finding.** R59 added the deterministic
finite-dim Lemma sigs; R60 corrected them to paper-faithful form; R61
closed `per ≤ 1` Full + Lemma 4.1 perturbation Full + axiomatized
`glw_det_lower_bound`. None of these touched (α), (β), (γ), (δ), or (ε).
The R61 helpers are *strictly more useful than zero* for a future R≫62
retirement attempt that builds the bridge — but they do not, on their
own, close the bridge in 60–130 LOC.

**Mismatch ledger entry #18** (Cowork+Grok shared chain-level
scope-mismatch, recurrence of #16 family — entry #17 was the R59
sig-form drift fully resolved at R60 attempt-2). Pattern: brief's Probe 3 +
Bonus 3 quote (`60–130 LOC`) is conditioned on "*After Cauchy det +
Lemma 4.1 land*", and Probe 3 implicitly assumes "land" includes the
bridge. The bridge has not landed; only the deterministic Lemma
*statements* and one direction of the proof have.

---

## T1.3 — Disposition: T2.1 + T2.2 SKIP

Per `feedback_paper_recheck_t10` standing protocol — *"R59 audit
discipline rule 'if any claim cannot be verified, flag explicitly and
propose alternative'"* — and per the R50 precedent (audit-redirect,
honest deferral over fake retirement, `PhaseV2R50Status.md` line
12-14), R62 ships:

* **T1.0 + T1.1 + T1.2 — Full ✓** (this audit doc).
* **T2.1 (A5 retirement) — SKIPPED.** No honest 50–80 LOC body for
  the bridge α/β/γ/δ/ε exists at this pin.
* **T2.2 (A4 retirement) — SKIPPED.** Same chain-mismatch finding;
  additionally, A4's full-window form requires (γ) Ledoux §1.3 tail
  handling on top of the (α/β/δ/ε) of A5.
* **T3 (build verification) — reduced to confirming HEAD `f4011b9`
  helper-build green** (already done at audit dispatch:
  `lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut`
  → `Build completed successfully (3026 jobs)`).
* **T4 (push) — reduced to single audit-doc commit + BACKGROUND.md
  status section + AXIOM_INVENTORY.md unchanged** (no axiom
  retirement to record).

**Net debt change R61 → R62: 0 sorries / 0 axioms = 0 net.** Mainline
ledger 18 → 18 (unchanged); axiom inventory 10 → 10 (unchanged);
project total 38 → 38 (unchanged). **Audit-redirect, NOT closure
round.** This is the second consecutive Cowork-drafted Track A round
(R50, R62) where the GLW-shortcut → A4/A5 retirement claim has been
audit-rejected; the underlying chain mismatch is structural, not a
brief-quality issue.

---

## T1.4 — Alternative paths (for R63+ planning, not R62 execution)

The brief lists R63 as "Cauchy det identity + grid bound chain,
250–450 LOC" to retire `glw_det_lower_bound` (axiom #6). Per this
audit, R63 (as scoped) **is on the deterministic side and is
unaffected by the R62 finding** — it can proceed as drafted.

The actual bridge problem (α/β/γ/δ/ε) is a separate, much larger
program. Three distinct paths exist for honest A4/A5 retirement:

1. **Mathlib-Anderson path (canonical).** Wait for / contribute
   Anderson's multivariate inequality + KL spectral theory + Talagrand
   entropy to Mathlib upstream. Multi-year horizon per A4/A5 docstring
   admission. The R59-R61 finite-dim deterministic Lemmas are
   *contributing* infrastructure for this path (the Lemma 4.2 det side
   would directly plug into step δ).

2. **In-tree no-Gaussian / no-KMT path (Q1a/b/c).** Mainline already
   contains 5909+ LOC across `CauchyDetLowerBound.lean` (3126),
   `CharFunCrossBlock.lean` (635), `MultivariateSmallBallUpper.lean`
   (621), `SurgicalDensityAtZero.lean` (543), `EsseenSmoothing.lean`
   (817), `GaussianHierCauchyBox.lean` (167) on this alternate
   approach (Fourier smoothing + Berry-Esseen + hierarchical Cauchy)
   targeting A5 retirement. Status of this track at HEAD `f4011b9`
   not re-audited in this round; it does NOT consume the R59-R61
   GLW-Cauchy-form helpers (different matrix construction and
   different bridge philosophy).

3. **Hybrid path (Path A pragmatic, R52 gate authorisation).** Add
   the bridge components as their own quantitative axioms (Anderson
   bound + discretization-error bound + optimization), wire them
   through to A4/A5 honestly, and then attempt to retire the new
   axioms separately. Net effect would be axiom-shape change rather
   than axiom-count reduction; possibly net-neutral.

None of (1), (2), (3) is a single 60–130 LOC round. **R62 audit-
redirect closes the door on the R47-strategic-Grok-pre-flight estimate
that A4 + A5 are jointly closeable in 110-150 LOC via the GLW
deterministic shortcut alone.** The compression-bundle item (iv) per
BACKGROUND.md lines 51-52 is structurally unachievable as scoped.

---

## T1.5 — Anti-patterns avoided in this audit

* Skipping T1.0 paper recheck (would have duplicated R59 / R60-attempt-1
  optimism). Avoided.
* Writing a "minimal-LOC body" by re-axiomatizing the bridge on the
  fly. Would have moved debt from A4/A5 line items to new axiom line
  items, no net reduction. Avoided.
* Exporting closure-tier language to AXIOM_INVENTORY.md / BACKGROUND.md
  for a structurally-broken closure (per `feedback_erdos524_framing`).
  Avoided.
* Fake `theorem` body using `sorry` or `exact gao_li_wellner_small_ball_lower
  glw Y h_glw` (circular). Avoided.

End audit.
