# Track D round 3 — T1.1 semantic verification audit + SLT WebSearch

**Branch:** `track-d-btis-honest` (HEAD `372185f`).
**Pin:** `mathlib4 @ 25ce63313608`, `leanprover/lean4:v4.27.0-rc1`.
**Date:** 2026-05-02.
**Discipline rule:** binding (post-7-misframing pattern, BACKGROUND.md).
**Outcome:** **TWO breaking semantic mismatches detected** in Sub-task B + ONE
secondary blocker. Per binding rule, T2.1 attempts adapter-scaffold path with
preserve-and-document on sub-lemma 3 sorry, citing concrete blockers. T2.2
(sub-lemmas 1+2 deletion) proceeds independently per Sub-task C (orphan
verification confirmed).

---

## Sub-task A — Lean codebase semantic verification

**Target:** `Helpers/BTISHonestProof.lean` on `track-d-btis-honest`.

### A1. Sub-lemma 3 signature (`lipschitz_sup_finite_gaussian`, lines 206–217)

```lean
theorem lipschitz_sup_finite_gaussian
    {Ω T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    [Fintype T] [Nonempty T]
    (X : T → Ω → ℝ)
    (_hgauss : IsCenteredGaussianProcess X)
    (sigma2 : ℝ) (_hσ_pos : 0 < sigma2)
    (_hσ_var : ∀ t, Var[X t; (ℙ : Measure Ω)] ≤ sigma2)
    (_hM_int : Integrable (fun ω => ⨆ t, X t ω) ℙ) :
    HasSubgaussianMGF
      (fun ω => (⨆ s, X s ω) - ∫ ω', (⨆ s, X s ω') ∂ℙ)
      sigma2.toNNReal ℙ := by
  sorry  -- TAG: TrackD-LipschitzSup
```

**Conclusion form**: returns `HasSubgaussianMGF` STRUCTURE (carries MGF-bound + integrability), parameterised by `sigma2.toNNReal` over `(ℙ : Measure Ω)`.

**NOT** a tail-bound conclusion. NOT specialised to `stdGaussianE n` on a Euclidean space. Acts on a user-supplied centered Gaussian process `X : T → Ω → ℝ` over a generic probability space `(Ω, ℙ)`.

### A2. BTIS body chain (lines 260–292)

The single load-bearing call to sub-lemma 3 is line 275:
```lean
have hSG : HasSubgaussianMGF
    (fun ω => (⨆ s, X s ω) - ∫ ω', (⨆ s, X s ω') ∂ℙ)
    sigma2.toNNReal ℙ :=
  lipschitz_sup_finite_gaussian X hgauss sigma2 hσ_pos hσ_var hM_int
```

`borell_tis` then calls `hSG.measure_ge_le hr.le` at line 277 (Mathlib Chernoff at `Probability/Moments/SubGaussian.lean:334`, verified). The remainder (set-rewrite + `Real.coe_toNNReal`) is mechanical. **Sub-lemma 3 is the only blocker between the current chain and a true axiom-free BTIS.**

### A3. Sub-lemmas 1+2 status

* `gaussian_log_sobolev_real` (lines 135–145): genuine TAG'd `sorry` body (`TAG: TrackD-LogSobolev-bottleneck`). Signature uses `gaussianReal 0 1` and standard log-Sobolev-form integrals. Real proof obligation.
* `herbst_subgaussian_real` (lines 163–171): genuine TAG'd `sorry` body (`TAG: TrackD-Herbst`). Signature uses Lipschitz `f` + centered hypothesis on `gaussianReal 0 1`.

Neither is a `True := by trivial` placeholder (cf. R40 lesson). Both are real signatures with real sorries.

### A4. `IsCenteredGaussianProcess` predicate (lines 102–114)

```lean
structure IsCenteredGaussianProcess
    {Ω T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : T → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable (X t)
  integrable : ∀ t, Integrable (X t) ℙ
  centered : ∀ t, ∫ ω, X t ω ∂ℙ = 0
  joint_gaussian : True
```

**The `joint_gaussian` field is `True`** (placeholder). The predicate is currently DEGENERATE on the joint-Gaussian axis — any centered measurable integrable process satisfies it. This was tolerable for round-1 scaffolding; it is **load-bearing for any genuine Gaussian-Lipschitz adapter**, which would need the actual joint-Gaussian content (e.g., to perform a Cholesky factorisation through `stdGaussianE`).

---

## Sub-task B — SLT external repo verification

**Target:** `https://github.com/YuanheZ/lean-stat-learning-theory` @ default branch `main` (HEAD tree sha `4aaea155`).

### B1. License verification — **MISMATCH M1 (BREAKING)**

* **GitHub API**: `repos/YuanheZ/lean-stat-learning-theory` returns `"license": null`.
* **Repo tree**: 77 paths, **no `LICENSE` file present** (verified `truncated: false`).
* **Per-file headers**: each `.lean` file in the SLT tree opens with
  ```
  Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
  ```
  i.e. the file headers ASSERT Apache 2.0 but reference a LICENSE file that DOES NOT EXIST in the repo.

**Mismatch with Grok TD3 Q1 framing**: Grok asserted "SLT repo MIT license + TD2-compatible toolchain". The repo is neither MIT (Apache-2.0 per per-file headers) nor LICENSE-complete (file is missing). The code has an internally inconsistent licensing posture — per-file Apache-2.0 grant without the upstream LICENSE text.

**Operational consequence**: Vendoring SLT code into FormalConjectures (Apache-2.0 with LICENSE file present) creates a license-compliance risk for FormalConjectures itself, because the upstream's license grant is incomplete. Adding SLT as a `require` Lake dependency (no redistribution) is a softer path but still depends on whether the user/maintainers accept the upstream license posture as valid Apache-2.0.

**Disposition**: ESCALATE TO USER. Without a clean license, T2.1 Route (b) is legally blocked; the per-file Apache-2.0 declaration is *probably* the author's intent but is not a substitute for the missing LICENSE file. This is an upstream defect; user (project owner) must call.

### B2. SLT Gaussian-Lipschitz file location and theorem signature

`SLT/GaussianLipConcen.lean` exists (1344 lines, blob sha `8b4eb22572`). Module path matches Grok Q1.

**Headline theorem `gaussian_lipschitz_concentration` (line 1301)**:
```lean
theorem gaussian_lipschitz_concentration {f : 𝔼 → ℝ} {L : ℝ≥0}
    (hn : 0 < n) (hL : 0 < L) (hf : LipschitzWith L f) (t : ℝ) (ht : 0 < t) :
    let μ := stdGaussianE n
    (μ {x | t ≤ |f x - ∫ y, f y ∂μ|}).toReal ≤ 2 * exp (-t^2 / (2 * (L : ℝ)^2)) := by
  ...
```

where `𝔼 := EuclideanSpace ℝ (Fin n)` and `stdGaussianE n` is the standard `n`-dimensional Gaussian on `𝔼`.

**Companion `gaussian_lipschitz_concentration_one_sided` (line 1288)**: same shape, returns `(μ {x | t ≤ f x - ∫ y, f y ∂μ}).toReal ≤ exp (-t^2 / (2 * (L : ℝ)^2))`.

### B3. Theorem-form mismatch — **MISMATCH M2 (SECONDARY)**

Both `gaussian_lipschitz_concentration` flavours return a **direct tail bound** (`(μ {…}).toReal ≤ exp(...)`). They do **NOT** return `HasSubgaussianMGF`.

Sub-lemma 3 (`lipschitz_sup_finite_gaussian`) requires a `HasSubgaussianMGF` STRUCTURE (carrying MGF-bound + integrability). Producing `HasSubgaussianMGF` from a tail bound is generally NOT possible without re-deriving the MGF inequality directly.

**Correct adapter source**: SLT `lipschitz_cgf_bound` (line 1209), which returns `cgf (fun x => f x - ∫ y, f y ∂μ) μ s ≤ s^2 * (L : ℝ)^2 / 2` (the CGF inequality form). Combined with `lipschitz_exp_centered_integrable_E` (line 1229, the integrability lemma), these two together would package into `HasSubgaussianMGF`.

**Mismatch with Grok TD3 Q1 framing**: Grok asserted importing `gaussian_lipschitz_concentration` would suffice. It does NOT — it returns the wrong shape. The actual targets within the same SLT file are `lipschitz_cgf_bound` + `lipschitz_exp_centered_integrable_E`. This is a smaller mismatch than M1 (same file, similar content) but means the adapter is structurally different from what Grok's recipe described.

### B4. Toolchain + Mathlib pin

* SLT `lean-toolchain` = `leanprover/lean4:v4.27.0-rc1` ✅ EXACT match with project pin.
* SLT `lakefile.lean` requires `mathlib` from `https://github.com/leanprover-community/mathlib4.git @ master` (FLOATING).
* SLT `lake-manifest.json` captured `mathlib` rev `d68c4dc09f5e000d3c968adae8def120a0758729`.
* Project pin: `mathlib4 @ 25ce63313608`.

The two mathlib commits **differ**. SLT's master-floating require means SLT does not pin to a fixed commit; lake-manifest captured one historical resolution. Whether SLT builds against the project's `25ce63313608` is **not directly verified** (would require attempting a Lake update). API drift over a ~weeks-window of Mathlib master is a real risk for SLT consumers; production-quality use requires SLT to commit to a fixed pin.

### B5. Specific imports needed (if M1 unblocked)

If user clears M1 (license posture), the imports needed in `BTISHonestProof.lean` would be:
```lean
import SLT.GaussianLipConcen          -- for lipschitz_cgf_bound + lipschitz_exp_centered_integrable_E
import SLT.GaussianMeasure            -- for stdGaussianE definition
```
plus a Lake `require` entry for `lean-stat-learning-theory` git source. This downloads SLT source at build time (no redistribution) and inherits SLT's transitive compilation, including its full ~30,000 LOC dependency graph.

---

## Sub-task C — Sub-lemmas 1+2 orphan verification

**Greps over `FormalConjectures/`**:

```
grep -rn "gaussian_log_sobolev_real" FormalConjectures/
```
Hits:
* `BTISHonestProof.lean:49` — docstring reference (route-(β) chain).
* `BTISHonestProof.lean:135` — the theorem definition itself.
* `BTISHonestProof.lean:157` — docstring reference (Herbst sub-lemma).
* `TrackDStatus.md` (4 lines), `TrackD_round2_T1_PortabilityAudit.md` (2 lines) — documentation only.

```
grep -rn "herbst_subgaussian_real" FormalConjectures/
```
Hits:
* `BTISHonestProof.lean:52` — docstring reference (chain).
* `BTISHonestProof.lean:163` — definition.
* `BTISHonestProof.lean:186` — docstring reference (Lipschitz-sup).
* `TrackDStatus.md` (3 lines), `TrackD_round2_T1_PortabilityAudit.md` (2 lines) — docs.

**Verification**: ZERO consumer call-sites for either sub-lemma 1 or sub-lemma 2 outside `BTISHonestProof.lean`. The TD2 Path B′ closure of `borell_tis` chained directly through sub-lemma 3 (`lipschitz_sup_finite_gaussian`) and bypassed sub-lemmas 1+2 entirely. Q3 verdict CONFIRMED — both are post-Path-B′ orphans.

```
grep -rn "lipschitz_sup_finite_gaussian" FormalConjectures/
```
Hits include `BTISHonestProof.lean:275` (the `borell_tis` body call) — **sub-lemma 3 is consumed**, contrast with sub-lemmas 1+2.

**Disposition**: T2.2 deletion is safe. The TrackDStatus.md and TrackD_round2_T1_PortabilityAudit.md docstring references can stay (they document historical route-(β) plan); the deletion will be reflected in the TD3 status doc addendum.

---

## Sub-task D — Cholesky / canonical embedding compatibility

The genuine adapter (post-M1 unblock) would require embedding `X : T → Ω → ℝ` with `IsCenteredGaussianProcess X` as the image of `stdGaussianE` under a linear map of operator norm `√sigma2`, then pulling SLT's CGF bound on a 1-Lipschitz coordinate-sup back to `(Ω, ℙ)`.

**Mathlib infrastructure available** (verified at pin `25ce63313608`):
* `Mathlib/LinearAlgebra/Matrix/PosDef.lean` — `PosDef` and `PosSemidef` predicates, `posDef_min_eigenvalue_pos` (R46 contribution).
* `Mathlib/Analysis/Matrix/PosDef.lean` — analytic API (operator norm, square root).
* `Mathlib/Probability/Moments/SubGaussian.lean` — `HasSubgaussianMGF` structure (line 142), `measure_ge_le` Chernoff (line 334) ✅ matches sub-lemma 3 conclusion.

**Mathlib infrastructure GAP**: No Cholesky factorisation theorem in Mathlib at this pin (`grep -i cholesky` returns empty in the pinned tree). Workarounds via `PosDef.sqrt` exist but produce a symmetric square root, not lower-triangular Cholesky; for the sup-Lipschitz adapter the symmetric square root is sufficient (the specific factorisation does not matter, only the existence of A with A·Aᵀ = Σ).

**`IsCenteredGaussianProcess` predicate gap**: per A4, the `joint_gaussian : True` field is degenerate. A genuine Cholesky adapter would require strengthening this predicate (or harmonising with `BrownianMotion.Gaussian.IsGaussianProcess`) so that the finite-marginal joint-law is actually a multivariate Gaussian, hence pushable from `stdGaussianE` via the matrix square root.

**Adapter LOC estimate** (post-M1 unblock, with predicate-strengthening): 250–500 LOC, NOT 150–250 as Grok Q1 estimated. The discrepancy is because the predicate-strengthening adds ~100 LOC of joint-Gaussian content, the matrix-square-root push-through adds ~80 LOC of `Measure.map` arithmetic, and the SLT CGF-bound consumption adds ~100 LOC of CGF-to-`HasSubgaussianMGF` packaging. This is the **third Grok TD3 underestimate**; Q1's "~150-250 LOC, P(Full) ≈ 0.70" was optimistic.

---

## Disposition for T2.1, T2.2, T2.3

**T2.1 (sub-lemma 3 closure)**: **ABORT FULL CLOSURE per binding discipline rule.** Two breaking mismatches (M1 license, M2 theorem-form) plus secondary issues (mathlib pin drift, predicate-degeneracy gap). Ship as TAG'd preserve-and-document with concrete diagnostic + adapter scaffold sketch. Updated docstring documents M1-M4 blockers and what would be needed if user clears M1.

**T2.2 (sub-lemmas 1+2 deletion)**: **PROCEED.** Sub-task C confirmed zero consumers. Deletion is mechanical. Net retirement: -2 sorries on branch.

**T2.3 (build verification + status doc)**: **PROCEED.** Document M1-M4 blockers in `TrackDStatus.md` addendum + `AXIOM_INVENTORY.md`. Track D cluster forecast: TD3 retires 2 (was projected 3); cluster needs additional round (TD4) only if user clears M1 OR pivots to from-scratch route.

## Eighth-misframing ledger entry

R40-R48 captured 7 consecutive Cowork-Claude semantic-mismatch failures caught by Local Claude T1.1 audits. **TD3 adds entries 8 and 9**:

* **#8 (M1, license)**: Grok asserted SLT MIT-licensed; reality is no LICENSE file + per-file Apache-2.0 headers referencing the missing LICENSE — internally inconsistent posture. Pattern: external repo metadata claim made without verification.
* **#9 (M2, theorem-form)**: Grok asserted `gaussian_lipschitz_concentration` (tail-bound) was the right import target for sub-lemma 3 (`HasSubgaussianMGF` wrapper). Pattern: matched name on cursory read without reading the actual conclusion shape; correct target is `lipschitz_cgf_bound` in the same file.

Pattern `TD3#8` is novel (license verification was not in prior misframing audit). Pattern `TD3#9` (cursory-read mismatch) recurs from R44/R45/R46/R48.
