# Round R62 brief — A4 + A5 small-ball retirement (mainline)

**Type**: Closure round, axiom retirement. Direct cascade from R61 GLW Full closures.
**Dispatch surface**: `r46-track-a-mge-posdef` worktree at `~/Documents/formal-conjectures/`, HEAD `f4011b9` (post-R61 GLW Path A pragmatic).
**Scope binding (Q7)**: R62 = retire `gao_li_wellner_small_ball_lower` (A4, `524.lean:3643`) and `gao_li_wellner_small_ball_upper` (A5, `524.lean:3574`) by axiom-to-theorem swap, body proved by chaining the now-Full R61 GLW results. NO new sigs, NO Carter-Pollard work, NO Track D modifications.

---

## Pre-flight context

R61 landed three Full closures that together unlock A4 + A5 retirement :

- `glw_lemma_4_2_paper_specs` first half : `Matrix.permanent (glwMatrixA m hm) ≤ 1` Full
- `glw_lemma_4_2_paper_specs` second half : `Matrix.det (glwMatrixA m hm) ≥ (240 · e)^{-2m³}` (via `glw_det_lower_bound` axiom #6)
- `glw_lemma_4_1_perturbation` : ratio-perturbation bound Full

Per Grok strategic pre-flight Probe 3 + Bonus 3 verdict : the GLW algebraic path retires both small-ball axioms in **60–130 LOC** total (revised down from the original 130–250 LOC estimate). Bonus 3 verbatim :

> "After Cauchy det + Lemma 4.1 land, retiring `gao_li_wellner_small_ball_upper` costs only 60–130 LOC."

Same applies to the matching lower bound, by symmetry.

**Net debt target** : -2 axioms, +0 sorries = **-2 net debt**. Mainline 18 → **16**.

---

## Mandatory floor

### T1.0 — paper recheck (Full, per `feedback_paper_recheck_t10`)
- A4 / A5 statements at `524.lean:3643` / `:3574` are the targets ; do NOT modify their statements (the axiom-to-theorem swap is type-preserving, the *consumers* of A4/A5 must continue to compile).
- Cite arXiv:1001.0200v1 §4 application to the small-ball bound : the multivariate Gaussian small-ball probability `P(‖G‖_∞ ≤ ε)` over a finite hierarchical grid is bounded above and below using `det(Σ)^{-1/2} · (2ε)^n` where `Σ` has Cauchy structure, with the perturbation Lemma 4.1 controlling the discrepancy from the structured form.

### T1.1 — Mathlib API audit (Full)
Document in `Helpers/TrackA_R62_T1_SmallBallRetirementAudit.md` :

- **Verify A4 / A5 axiom signatures** at `524.lean:3643` and `:3574` (read line ranges, capture verbatim).
- **Identify caller sites** : grep mainline for `gao_li_wellner_small_ball_lower` and `gao_li_wellner_small_ball_upper` ; list every consumer file + line. Confirm the axiom-to-theorem swap is consumer-transparent (signature unchanged ; bodies replaced).
- **Verify Mathlib API at pin `25ce63313608`** :
  - `MultivariateGaussian` measure on `EuclideanSpace ℝ (Fin n)` ✓ (already used in `GaussianParametricAnalysis.lean`).
  - `Metric.ball` ✓.
  - Volume-of-ball formula for ℝⁿ : `Real.volume_Ioo`, `MeasureTheory.MeasurePreserving.measure` style.
  - Coercions `(_ : ℝ) ^ n` (Nat exponent) and `(_ : ℝ) ^ (-_ : ℤ)` (Int exponent). Already used in R59-R61.
- **Connect R61 results to the small-ball formulae** :
  - Lower bound : `P(‖G‖_∞ ≤ ε) ≥ (2ε)^{m²} · (2π)^{-m²/2} · det(Σ)^{-1/2}` for the structured Cauchy-grid Gaussian, with `det(Σ) ≥ (240·e)^{-2m³}` from `glw_det_lower_bound` (axiom #6).
  - Upper bound : `P(‖G‖_∞ ≤ ε) ≤ (2ε)^{m²} · (2π)^{-m²/2} · det(Σ - perturbation)^{-1/2}`, where the perturbation is bounded by Lemma 4.1 via the auxiliary matrix `glwMatrixB`.

### T2.1 — A5 retirement (Full)
Replace the axiom with a theorem :

```lean
-- Was (axiom): gao_li_wellner_small_ball_upper at 524.lean:3574
-- Now (theorem):
theorem gao_li_wellner_small_ball_upper [...same signature as axiom...] := by
  -- Apply Lemma 4.1 (R61 Full) to bound the perturbation between
  -- the actual covariance and the structured Cauchy form.
  -- Apply per(A) ≤ 1 (R61 Full) to control the constant.
  -- Derive the small-ball upper bound via the standard
  -- Gaussian-density-times-volume estimate.
  [BODY ~50-80 LOC]
```

Strategy : direct application of `glw_lemma_4_1_perturbation` + `glw_lemma_4_2_paper_specs.1` (per side, Full) to bound `det(Σ_actual)` from above by `det(glwMatrixA) · (1 + ε perturbation term)`, then small-ball upper from Gaussian volume.

Budget : ~50–80 LOC per Bonus 3.

### T2.2 — A4 retirement (Full)
Replace the axiom with a theorem :

```lean
-- Was (axiom): gao_li_wellner_small_ball_lower at 524.lean:3643
-- Now (theorem):
theorem gao_li_wellner_small_ball_lower [...same signature as axiom...] := by
  -- Apply glw_det_lower_bound (axiom #6, R61) directly.
  -- Apply per(A) ≤ 1 (R61 Full) to control the upper-bounding constant.
  -- Derive the small-ball lower bound via the standard Gaussian density estimate.
  [BODY ~30-50 LOC]
```

Strategy : direct application of `glw_det_lower_bound` (axiom #6) for the determinant lower bound, then small-ball lower from Gaussian density.

Budget : ~30–50 LOC.

### T3 — build verification (Full)
- Targeted : `lake build FormalConjectures.ErdosProblems.«524»`. Must be green.
- Targeted helper : `lake build FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut`. Must remain green.
- Counter-check : full project build at the end (it's R62, retirement round, full project sanity). Drift sweep should catch this anyway weekly, but a one-off here confirms.

### T4 — push (Full)
- Single commit on `r46-track-a-mge-posdef` : "R62 GLW small-ball retirement — A4 + A5 Full (-2 axioms)".
- Push to `fork`.
- Update `AXIOM_INVENTORY.md` : remove A4 + A5 entries (or mark RETIRED with R62 commit hash).
- Append R62 status section to `BACKGROUND.md` : 18 → 16 mainline ledger, axiom inventory 10 → 8.

---

## Definitions

- **Full** : axioms become theorems with full bodies (0 sorry inside) ; file compiles ; mainline + helper builds green.
- **Net retirement** : -2 line items in `AXIOM_INVENTORY.md`. Replaces both with theorem provenance pointing to R61 + R62 commits.

---

## Out of scope (explicit binding)

- `glw_det_lower_bound` (axiom #6, R61-introduced) retirement — staged R63 (Cauchy det identity + grid bound chain, 250–450 LOC). NOT this round.
- Any modification to R61 GLW theorem bodies (`glw_lemma_4_2_paper_specs`, `glw_lemma_4_1_perturbation`, `per ≤ 1` body, axiom block).
- Carter-Pollard Track C — separate, TC11+.
- Track D housekeeping — separate brief (TD-drop), can run after R62 lands.

---

## Calibration

- **Total budget** : 80–130 LOC bodies (T2.1 + T2.2). T1.0 + T1.1 + T3 + T4 are zero-LOC verification.
- **Realistic wall-clock** : 1–2 build cycles. The bodies are mechanical compositions ; only friction risk is the Gaussian-density-times-volume estimate if Mathlib's multivariate Gaussian API requires more glue than expected.
- **Risk band** : low. All R61 helpers are Full and Track A has executed against them in the same file.
- **Closure tier** : real. Net debt change R61 → R62 : **-2 axioms = -2 net**. Mainline gate count **18 → 16** (8 axioms + 8 sorries). Project total **38 → 36**.
- **Cross-track FS discipline** : not applicable. Mainline-only round, no `lake update`, no pin bump.

---

## Pre-flight checks (run before commit)

```sh
fc-main
git status
git branch --show-current                                              # r46-track-a-mge-posdef
lakecache
grep -rn "gao_li_wellner_small_ball_lower\|gao_li_wellner_small_ball_upper" \
  --include="*.lean" --exclude-dir=.lake .                             # caller list
lake build FormalConjectures.ErdosProblems.«524» 2>&1 | tail -10       # consumer green
```

---

## Artefact list

- `FormalConjectures/ErdosProblems/«524».lean` — modified (axiom → theorem at lines 3643 + 3574, with bodies).
- `FormalConjectures/ErdosProblems/Helpers/TrackA_R62_T1_SmallBallRetirementAudit.md` — new audit doc.
- `AXIOM_INVENTORY.md` — A4 + A5 marked RETIRED with R62 commit hash.
- `BACKGROUND.md` — appended R62 status section, mainline 18 → 16, axiom inventory 10 → 8.

---

## R63 preview (already drafted in `outputs/R63_Cauchy_Det_Retirement_brief.md`)

After R62 lands, R63 retires `glw_det_lower_bound` (axiom #6) via Cauchy determinant identity. Brief is ready ; dispatchable post-R62. Mainline 16 → 15 (after R63 close), axiom inventory 8 → 7. **Subject to Probe 4 verdict on whether the 3-axiom ship target is honest.**

End brief.
