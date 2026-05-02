# Track D round 5 PREP — T1 audit (Q3.1 / Q3.2 / Q3.3 path-feasibility)

**Round**: TD5-prep (Variante 1, single round, audit-only).
**Branch**: `track-d-btis-honest`, worktree `~/Documents/formal-conjectures-track-d`.
**HEAD pre-round**: `c6369bd` (TD4 T2.2).
**Wall-clock**: T+0:15 (worktree+cache) → T+1:30 (audit) → T+1:45 (push).
**Goal**: pre-flight verdict on which Grok Q3 path (Q3.1 / Q3.2 / Q3.3) can supply
sub-lemma 3 (`lipschitz_sup_finite_gaussian`, `BTISHonestProof.lean:269-280`)
without a Mathlib pin bump. NO body work this round.
**Net debt change**: **0 sorries / 0 axioms** (audit-only, no signature added — see T1.3 path verdict).

---

## Claims Verification Table (final)

| # | Claim | Verdict | Citation | Notes |
|---|-------|---------|----------|-------|
| 1 | Worktree at `~/Documents/formal-conjectures-track-d` setup successful | **VERIFIED** | `git worktree list` shows worktree at HEAD `c6369bd` on `track-d-btis-honest` | Created this round via `git worktree add ../formal-conjectures-track-d track-d-btis-honest` |
| 2 | `lake exe cache get` retrieves Mathlib oleans for track-d | **VERIFIED** | `Decompressing 7753 file(s)` / `Unpacked in 6193 ms` — no cold compile needed | Cache-hit path (~30s); no fallback `lake build` triggered |
| 3 | TD3-TD4 work preserved on `track-d-btis-honest` | **VERIFIED** | `git log --oneline -3` shows `c6369bd` → `b9dcad1` → `f5117f4` (TD4 T2.2 / T2.1 / T2.0) | sub-lemma 3 sorry preserved at `BTISHonestProof.lean:280` (`TrackD-LipschitzSup`) |
| 4 | `Mathlib.Probability.Moments.SubGaussian` present at pin | **VERIFIED** | `.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean:704` (`HasSubgaussianMGF.measure_ge_le`); file 934 LOC | Re-confirmed at track-d worktree pin; TD2 Path B′ Chernoff plumbing intact |
| 5 | `Mathlib.Probability.Distributions.Gaussian.Fernique` present at pin | **VERIFIED** | `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Fernique.lean` (259 LOC) | Contains `exists_integrable_exp_sq` (Fernique core), `memLp_id`, `integral_dual`, `eq_dirac_of_variance_eq_zero`, dual rotation lemmas — but **zero `Lipschitz` references** (grep confirmed) and no Borell-TIS / Lipschitz-functional concentration |
| 6 | Borell-TIS / CIS direct Gaussian tail tools at pin | **BLOCKED** | `grep -rn "borell\|cirelson\|tsirel\|ibragimov\|sudakov\|cis_inequality"` in `.lake/packages/mathlib/Mathlib/` returns: 0 hits for Borell, 0 hits for Ibragimov, 0 hits for Sudakov, 0 hits for `cis_inequality`; 13 hits for "Tsirelson" all in `Mathlib/Algebra/Star/CHSH.lean` (CHSH/quantum, NOT the CIS Gaussian concentration inequality) | **CRITICAL**: Mathlib at pin has NO Borell-TIS or CIS direct primitive. Grok Q3.1 hinge unsupported |
| 7 | TD2 Path B′ SubGaussian + Chernoff infrastructure used by `borell_tis` Full close | **VERIFIED** | `BTISHonestProof.lean:326-358` (`borell_tis` Full body): builds `HasSubgaussianMGF` via `lipschitz_sup_finite_gaussian X hgauss …` (sub-lemma 3, sorry'd), then applies `hSG.measure_ge_le hr.le` (`SubGaussian.lean:704`), then bridges set + coercion | Path B′ closure of BTIS is structurally locked at file level — only sub-lemma 3 sorry blocks |
| 8 | Sub-lemma 3 signature in `Helpers/BTISHonestProof.lean:280` (TD3) | **VERIFIED** | `BTISHonestProof.lean:269-280` `theorem lipschitz_sup_finite_gaussian` with hyps `(X : T → Ω → ℝ) (_hgauss : IsCenteredGaussianProcess X) (sigma2 : ℝ) (_hσ_pos : 0 < sigma2) (_hσ_var : ∀ t, Var[X t; ℙ] ≤ sigma2) (_hM_int : Integrable (fun ω => ⨆ t, X t ω) ℙ)` ⇒ `HasSubgaussianMGF (centered sup) sigma2.toNNReal ℙ` | Required form: `HasSubgaussianMGF` for the **centered sup** of a Fintype-indexed centered Gaussian process, parameter `sigma2.toNNReal`. Adapter sketch (TD3 docstring lines 245-267) estimates 360 LOC, **conditional on availability of SLT `lipschitz_cgf_bound`** — which was a deleted orphan (TD3 T2.2). |
| 9 | Q3.3 GLW determinant strengthening per R50 audit | **BLOCKED** | Mainline `Helpers/Round50_T1_GLWShortcutAudit.md` row #8 (Q3.3 strengthening): "**UNVERIFIED — exploratory**", note: "Stretch goal explicitly contingent on Lemmas 4.1+4.2 having a strengthened form that gives small-ball directly … Not scoped tightly enough to attempt." R50 §"Alternative path proposal" line 266: "**T2.4 Q3.3 strengthening attempt** is **SKIPPED** — exploratory". Also row #6 (Lemma 4.1 spec): "**UNVERIFIED — defer with alternative path**" because "Brief cites Gao-Li-Wellner 2010 §4 Lemma 4.1 (paper not in repo); …without paper access, cannot write a precise Lean signature." | R50 explicitly skipped Q3.3. Re-attempt blocked by same paper-access gap (GLW 2010 §4 Lemma 4.1+4.2 not in repo). Mainline `GLWSmallBallShortcut.lean` confirms: only TAG'd `glw_lemma_4_1_deferred_paper` + `glw_lemma_4_2_deferred_paper` Stubs landed, no strengthened form |
| 10 | mainline + track-c branches preserved | **VERIFIED** | mainline `~/Documents/formal-conjectures` HEAD `9ba0c27` on `r46-track-a-mge-posdef` (R54 close, matches memory); track-c `~/Documents/formal-conjectures-track-c` HEAD `7af23b8` on `track-c-1dkmt` (matches memory); no commits this round on either parallel branch | TD5-prep branch isolation confirmed |

**Summary**: 8/10 VERIFIED, 2/10 BLOCKED (rows #6 + #9 — the two key Grok Q3 hinges).

---

## §A. T1.1 — Q3.1 Borell-TIS direct verification

### A.1 Grok Q3.1 claim

> "Mathlib's SubGaussian + Fernique (already used in TD2 Path B') plus the existing
> Gaussian tail tools let you derive the required specialization with ~300-500 LOC;
> no pin bump required."

### A.2 Mathlib at pin — Gaussian concentration inventory

`.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/` (4 files, 1342 LOC total):

| File | LOC | Contents (relevant to BTIS) |
|------|-----|------------------------------|
| `Basic.lean` | 259 | `IsGaussian` typeclass, basic measure-theoretic predicates |
| `CharFun.lean` | 200 | Characteristic function of Gaussian measures |
| `Fernique.lean` | 259 | Fernique theorem core: `exists_integrable_exp_sq`, `memLp_id`, `integral_dual`, `eq_dirac_of_variance_eq_zero`, rotation lemmas, dual characterizations. **NO `Lipschitz` mentions, NO Borell-TIS, NO sup-of-Gaussian tail.** |
| `Real.lean` | 624 | 1D Gaussian density / measure / distribution |

`.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean` (934 LOC):

* `HasSubgaussianMGF` typeclass + composition lemmas.
* `HasSubgaussianMGF.measure_ge_le` (line 704) — Chernoff bound for sub-Gaussian
  random variables (TD2 Path B′ uses this).
* `HasSubgaussianMGF.measure_ge_le_exp_add` (line 323), variants.
* **NO** `Lipschitz`-functional-of-Gaussian sub-Gaussian-MGF lemma.
* **NO** Gaussian-Log-Sobolev / Bakry-Émery / Herbst-style derivation.

### A.3 Borell-TIS / CIS / Cirelson-Ibragimov-Sudakov — global Mathlib grep

```
grep -rn "borell\|cirelson\|tsirel\|ibragimov\|sudakov\|cis_inequality" \
   .lake/packages/mathlib/Mathlib/ 2>/dev/null
```

* **0 hits** for `borell` / `Borell`.
* **0 hits** for `ibragimov` / `Ibragimov`.
* **0 hits** for `sudakov` / `Sudakov`.
* **0 hits** for `cis_inequality`.
* **13 hits** for `tsirel` / `Tsirelson` — **all in `Mathlib/Algebra/Star/CHSH.lean`**
  (Tsirelson's CHSH bound for quantum mechanics, structurally unrelated to the
  Cirelson-Ibragimov-Sudakov Gaussian concentration inequality).

**Verdict**: Mathlib at pin contains **zero direct Borell-TIS / CIS primitives**.
The closest available primitive is the SubGaussian framework + Chernoff bound
(which is what TD2 Path B′ already uses, *given* sub-lemma 3 as a black box).

### A.4 Sup-of-Gaussian / Lipschitz-functional-of-Gaussian — Mathlib grep

```
grep -rn "Lipschitz.*Gaussian\|Gaussian.*Lipschitz\|sup.*Gauss\|Gauss.*sup\|
          gaussian_concentration\|GaussianConcentration\|concentration.*gaussian" \
   .lake/packages/mathlib/Mathlib/
```

* **0 hits** in `Mathlib/Probability/`.
* False positives in `Mathlib/RingTheory/PowerSeries/GaussNorm.lean` and
  `Mathlib/RingTheory/Polynomial/GaussNorm.lean` (Gauss norm in ring theory,
  unrelated to probability).

**Verdict**: Mathlib at pin has **no Lipschitz-functional-of-Gaussian concentration
primitive** at any level (neither the conclusion `LipschitzWith K f → HasSubgaussianMGF (f - 𝔼[f]) (K² · sigma2)`
nor any intermediate primitive like Gaussian Log-Sobolev or Herbst's lemma in the
required form).

### A.5 Sub-lemma 3 derivation chain — TD3 docstring inventory

`BTISHonestProof.lean:242-267` gives the documented adapter sketch (post-M1 path):

| Step | Description | LOC est. | Mathlib status |
|------|-------------|----------|----------------|
| 1 | Strengthen `IsCenteredGaussianProcess` to carry `HasGaussianLaw` on finite-dim marginals | 100 | requires harmonization with `BrownianMotion.Gaussian.IsGaussianProcess` |
| 2 | Build covariance matrix `Σ : Matrix T T ℝ`, prove `PosSemidef Σ` | 40 | `Matrix.PosSemidef` available, `Matrix.posSemidef_iff_eq_transpose_mul_self` available |
| 3 | `A := Σ.sqrt`; push `stdGaussianE T` to joint law via `Measure.map A` | 80 | `Matrix.PosSemidef.sqrt` available |
| 4 | Sup-of-coords is 1-Lipschitz in `EuclideanSpace ℝ T` | 20 | `LipschitzWith` API available |
| 5 | Compose: centred sup is `‖A‖`-Lipschitz of std Gaussian; **apply SLT `lipschitz_cgf_bound`** to get CGF inequality | 50 | **BLOCKED** — `lipschitz_cgf_bound` was the deleted sub-lemma 1 (TD3 T2.2 deletion of orphans), depends on Gaussian Log-Sobolev which is not in Mathlib at pin |
| 6 | Package CGF + integrability → `HasSubgaussianMGF` | 40 | structure constructor available |
| 7 | Identify `‖A‖² = ‖Σ‖_op = sigma2` | 30 | `Matrix.PosSemidef.sqrt_norm_sq` available |
| **Total** | — | **360 LOC** | **gated by step 5** |

The 360 LOC estimate **assumes step 5's `lipschitz_cgf_bound` is available**.
That primitive was the deleted sub-lemma 1 (`gaussian_log_sobolev_real`) +
sub-lemma 2 (`herbst_subgaussian_real`) chain, which TD3 T2.2 removed as orphans
because the Gaussian Log-Sobolev derivation from scratch was sized at 1500-2500
LOC (TD2 Path B finding) — out of scope for Track D's budget.

### A.6 Q3.1 verdict

**Q3.1 = BLOCKED.** Grok's "300-500 LOC using SubGaussian + Fernique + Gaussian
tail tools" is **drastically optimistic** vs. the on-the-ground state:

1. SubGaussian framework (Mathlib): present, but only provides Chernoff *given*
   `HasSubgaussianMGF`. Producing `HasSubgaussianMGF` for the centered sup of a
   Gaussian process is exactly sub-lemma 3 itself — SubGaussian framework does
   not bypass it.
2. Fernique theorem (Mathlib `Fernique.lean`): present, gives exp-sq integrability
   of Gaussian, **but no Lipschitz-functional concentration**. Fernique alone
   yields `Integrable (fun ω => exp (c * ‖ω‖²))` for Gaussian `μ`, which is
   weaker than the sub-Gaussian-MGF tail bound for the centered sup.
3. "Gaussian tail tools" — **zero direct primitives at pin**. No Borell-TIS,
   no CIS, no Lipschitz-functional-of-Gaussian concentration, no Gaussian
   Log-Sobolev, no Herbst's lemma in usable form.

To produce the sub-lemma 3 `HasSubgaussianMGF` conclusion **from scratch** at pin
without the deleted SLT chain, the realistic LOC is **600-1500+** — comparable
to the TD2 Path B "from-scratch" estimate that was already ruled out as out of
single-round scope. The honest derivation routes are:

* **Route (i) — SLT via Gaussian Log-Sobolev**: re-introduce sub-lemmas 1+2,
  derive Bakry-Émery / OU-semigroup Log-Sobolev for Gaussian, run Herbst, then
  the 360 LOC adapter. Total: ~1500-2500 LOC. Out of scope.
* **Route (ii) — direct CGF estimation via Hermite expansion / Wick's theorem**:
  derive sub-Gaussian MGF for centered sup of Gaussian process by moment-by-moment
  Hermite-expansion bounds. Combinatorially involved, no Mathlib infrastructure.
  Estimated 800-1500 LOC. Out of scope.
* **Route (iii) — Maurey-Pisier interpolation**: interpolate via Schatten norms
  + Khintchine-like bound. Indirect; likely 600-1000 LOC. Out of scope.

Net: **all three honest derivation routes for Q3.1 fall outside the Track D
single-round budget at pin without a Mathlib pin bump that introduces Borell-TIS
or Gaussian Log-Sobolev as a primitive.**

---

## §B. T1.2 — Q3.2 (TD2 Path B′ generalization) verification

### B.1 Grok Q3.2 claim (paraphrased)

The TD2 Path B′ pattern (`HasSubgaussianMGF` + `measure_ge_le` Chernoff)
generalizes to Lipschitz functionals of Gaussian processes, providing a direct
route to sub-lemma 3.

### B.2 What Path B′ actually establishes

`BTISHonestProof.lean:326-358` — the `borell_tis` Full body — uses
`lipschitz_sup_finite_gaussian` (sub-lemma 3) to produce
`HasSubgaussianMGF (centered sup) sigma2.toNNReal ℙ`, then applies
`HasSubgaussianMGF.measure_ge_le` from `SubGaussian.lean:704`.

The "Path B′ generalization for Lipschitz functionals" is:

```
∀ Lipschitz f : E → ℝ, ∀ Gaussian μ : Measure E,
    HasSubgaussianMGF (f - μ[f]) (LipConst f)² · sigma2² ν
```

This is **exactly the Lipschitz-functional-of-Gaussian concentration result**.
Specializing `f := sup` recovers sub-lemma 3. The "generalization" is therefore
**not a bypass** — it is the same problem renamed at a higher level of abstraction.

### B.3 Q3.2 verdict

**Q3.2 = BLOCKED (= Q3.1 in disguise).** The TD2 Path B′ pattern only "lifts to
Lipschitz functionals" if a Lipschitz-functional-of-Gaussian sub-Gaussian-MGF
lemma exists at pin. Per §A.4, **no such primitive exists in Mathlib at pin**,
and producing it from scratch is the same 600-1500+ LOC effort as Q3.1.

---

## §C. T1.2 — Q3.3 (GLW determinant strengthening) verification

### C.1 R50 audit re-read summary

Mainline `Helpers/Round50_T1_GLWShortcutAudit.md` (22.4 KB, 332 lines):

* **Row #6** (Lemma 4.1 spec): **UNVERIFIED — defer with alternative path**.
  Brief cites GLW 2010 §4 Lemma 4.1 paper not in repo; without paper access,
  cannot write a precise Lean signature.
* **Row #8** (Q3.3 strengthening): **UNVERIFIED — exploratory**. Note: "Stretch
  goal explicitly contingent on Lemmas 4.1+4.2 having a strengthened form that
  gives small-ball directly (skipping the discretization+Anderson chain). Not
  scoped tightly enough to attempt."
* **§"Alternative path proposal"** (line 266): "**T2.4 Q3.3 strengthening
  attempt** is **SKIPPED** — exploratory".
* **Chain-mismatch finding** (§"Chain-mismatch finding", lines 75-117): the
  audit identified a structural gap between finite-dim determinant identities
  (Lemmas 4.1+4.2) and the small-ball probability via continuous Brownian sup —
  the chain α/β/γ/δ/ε bridges this gap, but each link requires its own
  derivation; bypassing sub-lemma 3 by going through determinant identities
  directly does not eliminate the chain, only relocates it.

Mainline `Helpers/GLWSmallBallShortcut.lean` (262 LOC):

* `glw_det_route_lower_bound` (line 58) — Stub.
* `glw_det_route_upper_bound` (line 78) — Stub.
* `gao_li_wellner_small_ball_lower_via_det_route` (line 96) — Stub, "Closes A4
  axiom via Lemma 4.1 + GLW kernel construction" — depends on Lemma 4.1.
* `gao_li_wellner_small_ball_upper_via_det_route` (line 113) — Stub, dual.
* `glw_lemma_4_1_deferred_paper` (line 226) — TAG'd Stub, body deferred to paper.
* `glw_lemma_4_2_deferred_paper` (line 256) — TAG'd Stub, body deferred to paper.

### C.2 Q3.3 dependency on Q1c

`MEMORY.md` `project_lean_erdos_524.md` mentions: "Axioms #6 + #7 + #8 retirement
target R55-R59 post-gate" and "R55 candidates: …(2) Q1c full close attempt".
If Q1c (mainline track) closes Lemmas 4.1+4.2 with paper-derived formulations,
Q3.3 might unblock as side-effect. But this is **mainline R55+ work, gated by
mainline scheduling**, not actionable from track-d in TD5.

### C.3 Q3.3 verdict

**Q3.3 = BLOCKED at TD5 horizon.** Re-attempting Q3.3 from track-d would
reproduce R50's blocker: GLW 2010 paper is not in repo, Lemmas 4.1+4.2 cannot
be specified without paper access. Even if mainline Q1c closes Lemmas 4.1+4.2
in R55-R59, the Q3.3 "strengthening" claim (small-ball directly, bypassing
discretization+Anderson chain) was R50-flagged as exploratory and not scoped
tightly enough — the chain-mismatch finding shows this is a structural gap,
not a notational one.

---

## §D. Path decision (T1.3 prep)

### D.1 Three-path verdict matrix

| Path | Verdict | Blocker | Honest LOC est. (from-scratch) |
|------|---------|---------|--------------------------------|
| Q3.1 Borell-TIS direct | **BLOCKED** | No Borell-TIS / CIS / Lipschitz-functional-Gaussian primitive at pin; SLT chain deleted (TD3 T2.2 orphans) | 600-1500+ |
| Q3.2 TD2 Path B′ generalization | **BLOCKED** | = Q3.1 in disguise; same Lipschitz-functional-Gaussian primitive needed | 600-1500+ |
| Q3.3 GLW determinant strengthening | **BLOCKED** | GLW 2010 paper not in repo (R50 blocker preserved); R50 explicitly SKIPPED Q3.3 attempt | not specifiable without paper |

### D.2 TD5 main-round implication

**TD5 main = pin bump coordination only path.**

Per `feedback_v2_cluster_filesystem_discipline` memory: pin bumps + `lake update`
+ `.lake/packages/` checkouts mutate shared project state across all branches;
require user-confirmed exclusive FS window. TD4 Path A (pin bump) was killed by
exactly this FS-collision constraint (`c6369bd` post-mortem).

**TD5 precondition**: user-coordinated exclusive FS window on
`~/Documents/formal-conjectures/.lake/packages/` for the duration of the bump
+ rebuild + verification cycle. Estimated wall-clock: 2-4 h (cold rebuild
~30-60 min × at least one verification pass).

**Candidate target pins** (which Mathlib version introduces Borell-TIS):

* The `.lake/packages/mathlib/` pin in this worktree is the project pin (not
  the latest Mathlib). A targeted upstream survey is needed to identify the
  Mathlib commit/PR that introduces a Borell-TIS / Lipschitz-functional-Gaussian
  primitive in `Mathlib.Probability.Moments.SubGaussian` or
  `Mathlib.Probability.Distributions.Gaussian.*`.
* This survey is itself a TD5 sub-task (T1 in TD5 main), best done from a
  fresh worktree once the FS window is granted.

### D.3 No signature TAG'd Stub this round

Per the round-spec T1.3 conditional: "If Q3.1 PARTIAL or BLOCKED → … 0 sorries,
audit-only deliverable."

All three paths are BLOCKED ⇒ no signature lockdown this round. No new TAG'd
sorry added to `BTISHonestProof.lean` (or any new file). Net debt: **0 sorries,
0 axioms** on track-d this round.

### D.4 What to recommend for TD5 main scope

1. **First sub-task** (T1, audit): identify the exact Mathlib commit / PR that
   introduces a Borell-TIS-equivalent or Lipschitz-functional-Gaussian
   sub-Gaussian-MGF primitive. Done from a temporary fresh worktree without
   touching project pins; ~1 h.
2. **Second sub-task** (T2, FS-exclusive): with user-confirmed FS window on
   `.lake/packages/`, run `lake update mathlib` to that target pin (or a
   bump-batch including it); rebuild affected files; verify
   `BTISHonestProof.lean` builds; only then re-attempt sub-lemma 3 close.
3. **Fallback** (if no Mathlib commit yet introduces the primitive): defer
   Track D to "post-Mathlib-Borell-TIS-PR" milestone; close track-d-btis-honest
   at TD4 state; document in `TrackDStatus.md` + `BACKGROUND.md`.

---

## §E. Mismatch ledger entry #17 (TD5-prep)

* **Spec claim** (round brief, §"TD5-prep scope" Priority 2): "Grok Q3.1 claim:
  'Mathlib's SubGaussian + Fernique (already used in TD2 Path B') plus the
  existing Gaussian tail tools let you derive the required specialization with
  ~300-500 LOC; no pin bump required.'"
* **Reality at pin**: zero Borell-TIS / CIS / Lipschitz-functional-Gaussian
  primitives in Mathlib. SubGaussian + Fernique are scaffolding, not a
  derivation. Grok's "Gaussian tail tools" claim has no concrete referent in
  Mathlib at pin.
* **Resolution**: Q3.1 BLOCKED, TD5 = pin bump coordination only path.
* **Skin-in-the-game accountability**: third Track D underestimate in a row
  from upstream (Q1 = 150-250 LOC vs. 360 actual; Q3.1 = 300-500 LOC vs.
  600-1500+ actual; both upstream-quoted estimates substantially below
  on-the-ground reality). Future Grok Q-claims must be grep-verified before
  acceptance.

---

## §F. Round-summary banner

* Worktree + cache: **DONE** (~T+0:15).
* T1.1 Q3.1 Borell-TIS direct audit: **DONE** — verdict **BLOCKED**.
* T1.2 Q3.2 + Q3.3 secondary audit: **DONE** — Q3.2 = Q3.1 in disguise (BLOCKED), Q3.3 BLOCKED at TD5 horizon (paper access).
* T1.3 path decision: **TD5 main = pin bump coordination only path**.
* No signature TAG'd Stub added (Q3.1 not VIABLE).
* Net debt change: **0 sorries / 0 axioms** on track-d.
* Mainline + track-c untouched.
