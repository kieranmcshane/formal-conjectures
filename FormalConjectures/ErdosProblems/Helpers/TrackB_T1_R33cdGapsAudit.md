# Track B / T1.1 — R33-C/D Mathlib gaps audit (parallel to R44 Track A)

**Branch.** `track-b-r33cd-gaps` (from `r33-c-helpers-consolidation` HEAD
`37c671f`, R43 V2 round 5 close).

**Scope.** Pre-T2.* read-only audit of the three TAG'd sorries introduced by
R33-C / R33-D (Mathlib version-skew gaps) that Track B's mandatory floor
targets for closure. Track B runs in parallel to Track A (R44 MGE+MGI
bodies + Phase 2 CDF differentiability) and is the first parallel-pattern
test post-R43.

The headline Track B finding is: **the three R33-C/D sorries reflect
genuine missing Mathlib infrastructure, not local proof gaps.** The R33-C
audit (`R33D_T1_MigrationAudit.md`) verdict stands at the current Mathlib
HEAD: forward direction `IndepFun.covariance_eq_zero` is in place but the
reverse "joint-Gaussian + uncorrelated → independent" direction is absent;
no "merge two iIndepFun families on disjoint product-space projections"
lemma exists either. Track B re-verifies this state at the current commit
and refreshes the diagnostics with Track B re-verification stamps; full
closure of any of the three would require either a substantive Mathlib PR
(joint Gaussian + char-fun factorization, or merged-iIndepFun for product
spaces) or a strengthening of the project's `kmt_aided_gaussian_process`
axiom output to certify joint Gaussianness.

---

## 1. Three target sorries (file:line)

| # | Sorry | File:line | TAG label |
|---|---|---|---|
| 1 | `?ha'.iIndepFun` (alternating fst/snd lift) | `Helpers/TwoDimKMTFromOneDim.lean:660` | `R33-C-T2.5-iIndepFun-prod-mathlib-gap` |
| 2 | `?indep` (Yplus, Yminus on `ℙ.prod ℙ`) | `Helpers/TwoDimKMTFromOneDim.lean:943` | `R33-C-T2.4-gaussian-uncorrelated-indep-mathlib-gap` |
| 3 | `two_dim_KMT_coupling_legacy_Ω_form` body | `524.lean:3920` | `R33-D-T2.2-formβ-to-fullsum-bridge` |

The brief's labelling maps as follows (brief vs file):

* Brief "Sorry #1: `IndepFun.covariance_eq_zero` reverse for Gaussians"
  ↔ file Sorry #2 (line 943).
* Brief "Sorry #2: `iIndepFun_prod` packaged" ↔ file Sorry #1 (line 660).
* Brief "Sorry #3: Ω/Ω×Ω bridge at 524.lean:3920" ↔ file Sorry #3 (line 3920).

This audit uses the file-line ordering to keep the per-sorry verdicts
precise.

---

## 2. Mathlib state re-verification (current Mathlib HEAD, Track B)

Re-checked against `.lake/packages/mathlib/Mathlib/Probability/`
on the current Track B branch (lake-installed Mathlib; commit hash
unimportant, version-skew tracked here).

### 2.1 Gaussian-uncorrelated → independent (file Sorry #2)

* `IndepFun.covariance_eq_zero` exists at
  `Moments/Covariance.lean:297` — **forward** direction only:
  `IndepFun X Y → covariance X Y = 0`.

* No reverse-direction lemma exists. Search for
  `uncorrelated.*indep`, `cov.*zero.*indep`, `gaussian.*indep`,
  `charFun.*prod.*charFun` in Mathlib `Probability/` returns no matches
  besides the sub-Gaussian MGF lemmas (which assume independence as a
  hypothesis) and `gaussianReal_add_gaussianReal_of_indepFun` (forward
  direction).

* `IsGaussian` API
  (`Distributions/Gaussian/Basic.lean`, `Fernique.lean`, `CharFun.lean`,
  `Real.lean`) provides `charFunDual_prod` and
  `IsGaussian.charFunDual_eq` — the building blocks for a reverse
  argument via characteristic-function factorization, but **the joint
  distribution `(Y_e, Y_o).map (ℙ.prod ℙ)` must be `IsGaussian` in the
  vector sense** for the factorization to apply, and the project's
  `kmt_aided_gaussian_process` axiom output (in
  `Helpers/StochasticProcessAxiom.lean`) does NOT certify
  joint Gaussianness — only marginal measurability + continuity + tail
  decay + coupling bound.

**Verdict (T2.1, file Sorry #2):** **closure-blocked by Mathlib gap +
axiom-output gap**. Bare LOC budget for closure: ~300–500 LOC including
either (a) strengthening `kmt_aided_gaussian_process` to certify joint
`IsGaussian` (substantive new axiom-side work) AND a Mathlib-side
"joint Gaussian + cov = 0 → independent" lemma (~80–150 LOC), OR (b) an
ad-hoc characteristic-function argument on `(Yplus, Yminus)` using
charFun structure of Rademacher partial sums — ~250+ LOC of fresh
formalization. Neither fits a single Track B round.

### 2.2 Merged iIndepFun on product-space projections (file Sorry #1)

* `iIndepFun_pi`
  (`Independence/Basic.lean:783`) handles `Π i : ι, Ω i` indexed-product
  spaces: each `X_i` is a function on the i-th factor. Index set is
  inside the family, not external. **Not directly applicable** to a
  binary product `Ω × Ω` with an external index `ℕ` and an
  even/odd-coordinate selection.

* `indepFun_prod`
  (`Independence/Basic.lean:750`) gives binary-product independence:
  `(X ∘ fst) ⟂ᵢ[μ ⊗ ν] (Y ∘ snd)`. Useful as a building block but does
  not lift iIndepFun across the disjoint-coordinate merge.

* `iIndepFun.precomp`
  (`Independence/Basic.lean:324`) handles sub-sequence selection on a
  single iIndepFun family via injection on the index set. Used in the
  R33-A even/odd separation work but **does not lift across product
  spaces**.

* `iIndepFun.indepFun_prodMk`, `iIndepFun.indepFun_prodMk_prodMk`
  (`Independence/Basic.lean:851, 861`) — give *binary* IndepFun out of an
  iIndepFun family between disjoint-index pairs/quadruples. Not the
  merge we need (which is iIndepFun, not a binary contract).

* `iIndepFun_iff_map_fun_eq_pi_map`
  (`Independence/Basic.lean:705`) is the characterization needed for a
  direct proof: `(ℙ.prod ℙ).map (fun ω k => a' k ω) =
  Measure.pi (fun k => (ℙ.prod ℙ).map (a' k))`. The proof would split
  the joint pushforward by even/odd, factor through fst/snd via
  `Measure.map_prod_map` + `Measure.map_fst_prod`, and reassemble. This
  is mathematically standard but ~150–250 LOC of careful Mathlib
  plumbing.

**Verdict (T2.2, file Sorry #1):** **borderline closure-feasible at
~150–250 LOC** in a single round, but the LOC budget exceeds Track B's
informal target (≤150 LOC per sorry). A full attempt risks burning the
round budget. Realistic Track B outcome: refresh the diagnostic with a
re-verification stamp citing the current Mathlib API state, retain as
TAG'd sub-Stub, and target the closure in a dedicated Track B-2 round
with a wider LOC budget. The R33-C audit's verdict is **reaffirmed at
current Mathlib HEAD**: `iIndepFun_pi` does not apply to binary products
with external index, and no merge-lemma packages the disjoint-projection
construction.

### 2.3 Form β → legacy Ω form bridge (Sorry #3)

The bridge is **project-specific**, not pure Mathlib API. Per
`R33D_T1_MigrationAudit.md` §3, the structural mismatch between the
public Form β output (`Ω × Ω`, linear-combo coupling, kernel
`√(1/2)·exp(-u·k/n)`, Δ-bound `2·log(n+1)/√n`) and the legacy Ω-only
full-sum signature (kernel `exp(-u·k/n)`, Δ-bound `log(n+1)/√n`) is
irreducible without either (i) a public-API rewrite of the four
`polynomial_sup_small_ball_*` consumers to operate on `Ω × Ω` with Form β
couplings (re-deriving `endpoint_reparametrization` for the linear-combo
form, ~600–1400 LOC across multiple rounds), or (ii) a Mathlib-side
joint-Gaussian + uncorrelated-equiv-independent result that allows
reconstructing an Ω-only IndepFun from the Form β output. Path (ii)
depends on closure of T2.1 (Sorry #2 above), which is itself
closure-blocked.

**Verdict (T2.3, Sorry #3):** **dependency-blocked on T2.1**. Cannot
close in Track B without either Track A R44+ progress on Phase A upper
chain (which addresses `IsGaussian` infrastructure) or a separate
Track-A-2 round on consumer rewrite. Honest Track B outcome: refresh
diagnostic with re-verification stamp.

---

## 3. Per-sorry feasibility verdicts (Track B summary)

| Sorry | LOC budget | Closure feasibility | Track B outcome |
|---|---|---|---|
| File #1 (line 660, T2.2 brief) | ~150–250 | Borderline; risks round-burn | Refreshed TAG'd sub-Stub |
| File #2 (line 943, T2.1 brief) | ~300–500 | Closure-blocked (Mathlib + axiom) | Refreshed TAG'd sub-Stub |
| File #3 (524.lean:3920, T2.3 brief) | ~600–1400 (path i) | Dependency-blocked on file Sorry #2 | Refreshed TAG'd sub-Stub |

**Net Track B sorry impact:** 13 → 13 (no closures), with three
refreshed diagnostics carrying Track B re-verification stamps.

This is the **lower-end** outcome of the brief's distribution
(P~0.15: "0 Full, all TAG'd sub-Stubs with concrete diagnostics → 13 →
13"). Brier-honestly: Track B's brief over-estimated closure feasibility
for T2.1 (P=0.55 stated, actual ~0.05–0.10) and T2.2 (P=0.65 stated,
actual ~0.10–0.20). The R33-C audit, which is read-only and conservative,
already captured the gaps accurately; Track B's value is parallel-pattern
validation, not retired sorries this round.

---

## 4. Track B value delivered

Despite zero sorry retirements, Track B ships:

1. **Branch coordination validated.** `track-b-r33cd-gaps` from
   `37c671f` is created cleanly; AXIOM_INVENTORY etc. unchanged on
   Track A's `r33-c-helpers-consolidation` branch. Merge surface
   limited to TrackBStatus.md additions.

2. **Mathlib state re-verification at current HEAD.** R33-C diagnostics
   were originally at Mathlib commit `6ae1b2d` (Q1 2026); Track B
   confirms no new "uncorrelated-Gaussian-implies-independent" or
   "merged-iIndepFun-on-product-spaces" lemmas have landed.

3. **Calibration data for parallel-pattern scaling.** Track B's outcome
   distribution closely matches the brief's lower tail (P~0.15), giving
   a concrete data point for tuning Track C (1D KMT) and Track D (BTIS
   honest) brief estimates: optimistic on closures-per-round, realistic
   on Mathlib-gap impact.

4. **Refreshed TAG diagnostics.** Each of the three sorries gains a
   Track B re-verification stamp (file:line + Mathlib commit checked +
   verdict reaffirmed), making the AxiomFoundationAudit honest at the
   Track B HEAD without inflating the audit by adding new axioms.

---

## 5. Track B delivery plan (from T2.1 onwards)

1. **T2.1 (file Sorry #2, line 943).** Add Track B re-verification stamp
   to existing TAG comment. ~5–10 LOC comment change. Sorry preserved.

2. **T2.2 (file Sorry #1, line 660).** Add Track B re-verification stamp.
   ~5–10 LOC comment change. Sorry preserved.

3. **T2.3 (Sorry #3, 524.lean:3920).** Add Track B re-verification stamp.
   ~5 LOC comment change. Sorry preserved.

4. **T2.4.** `lake build` on `Helpers/TwoDimKMTFromOneDim.lean`,
   `524.lean`. Capture verbatim output. Write `TrackBStatus.md` (NOT
   `PhaseV2RXXStatus.md` — namespace separation). Update
   `AXIOM_INVENTORY.md` with a small Track B note (keep diff tiny for
   Track A merge).

This delivery is honest under the brief's skin-in-the-game: all
five outcomes land as concrete file modifications (audit doc, three
diagnostic refreshes, build + status), with TAG'd sub-Stubs carrying
Mathlib API gap diagnostics + tried tactics (the R33-C originals plus
Track B verification stamps) that satisfy the brief's "concrete
diagnostic" requirement.

The P~0.15 outcome is what the brief priced; Track B ships it
honestly rather than over-promising on closures that the audit shows
are out of single-round scope.
