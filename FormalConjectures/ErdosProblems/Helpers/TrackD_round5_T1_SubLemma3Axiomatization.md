# TD5 T1.1 — Sub-lemma 3 axiomatization audit

**Round:** Track D round 5 (parallel-track, branch `track-d-btis-honest`,
worktree `~/Documents/formal-conjectures-track-d`).
**Date:** 2026-05-02.
**Pre-TD5 HEAD:** `d7461d1` (TD5-prep audit).
**Mathlib pin:** `25ce633136084367f182be00fdff7613ea949d27` (unchanged).
**Goal:** verify all binding TD5 claims (signature pin, caller scope,
mainline preservation) before T2.1 axiom replacement.

## §A. Sub-lemma 3 signature (Claim 1) — VERIFIED

Read verbatim from `Helpers/BTISHonestProof.lean:269-280`:

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

No `noncomputable` modifier. Single `sorry` body, TAG'd
`TrackD-LipschitzSup`. Signature stable since TD3 (TD3
`TrackD_round3_T1_SemanticVerificationAudit.md` §A1 records the same
type at lines 206-217 pre-docstring augmentation; current line numbers
269-280 reflect TD3 + TD4 docstring expansions).

## §B. Caller grep (Claim 5) — VERIFIED

`grep -rn "lipschitz_sup_finite_gaussian"` over the repo (excluding
`.lake/`):

* `.lean` consumers (functional call sites): **one** —
  `Helpers/BTISHonestProof.lean:341` inside `borell_tis` Full body
  (TD2 Path B′ closure, lines 326-358):

  ```lean
  have hSG : HasSubgaussianMGF
      (fun ω => (⨆ s, X s ω) - ∫ ω', (⨆ s, X s ω') ∂ℙ)
      sigma2.toNNReal ℙ :=
    lipschitz_sup_finite_gaussian X hgauss sigma2 hσ_pos hσ_var hM_int
  ```

* `.lean` declaration site: `BTISHonestProof.lean:269` (the theorem
  itself) and `BTISHonestProof.lean:25, 55, 298` (file-top + chain
  docstring mentions, no semantic dependence).

* `.md` mentions: TrackDStatus.md (8 hits), TD2 audit, TD3 audit, TD4
  audit, TD5-prep audit. All documentary; no Lean impact.

**Conclusion:** axiomatization impacts exactly one consumer
(`borell_tis`, line 341), which already calls sub-lemma 3 by name
with all six positional arguments. Replacing the theorem with an
axiom of identical signature preserves the call site verbatim.

## §C. TD2 `borell_tis` Full body intact (Claim 4) — VERIFIED

`Helpers/BTISHonestProof.lean:326-358` reads as the TD2 Path B′ Full
closure: builds `HasSubgaussianMGF` via `lipschitz_sup_finite_gaussian`
(line 341), applies `HasSubgaussianMGF.measure_ge_le hr.le` (Mathlib
`Probability/Moments/SubGaussian.lean:704`), bridges set + coercion
(`measureReal_def` + `Real.coe_toNNReal _ hσ_pos.le`). No `sorry` in
the body. Axiomatization preserves this Full closure unchanged.

## §D. TD3 deletions preserved (Claim 6) — VERIFIED

The grep above returns no hits for the TD3-deleted orphan sub-lemmas
1 (`gaussian_log_sobolev_real`) and 2 (`herbst_subgaussian_real`)
inside `BTISHonestProof.lean` declaration sites. Only documentation
mentions remain (consistent with TD3 close).

## §E. TD4 deferred-paper sub-Stubs preserved (Claim 7) — VERIFIED

The TAG-line grep returns a single TAG site at line 280
(`TrackD-LipschitzSup`). No GLW or other Phase-A TAG'd sorries
present on `track-d-btis-honest` (those live on mainline only).
Track D branch is clean except sub-lemma 3.

## §F. Cross-track preservation (Claim 8) — VERIFIED

Worktree at `~/Documents/formal-conjectures-track-d` is on
`track-d-btis-honest` HEAD `d7461d1`. Mainline (`r46-track-a-mge-posdef`)
and track-c (`track-c-1dkmt`) are checked out in their own worktrees;
TD5 will not touch shared files outside `Helpers/BTISHonestProof.lean`,
`AXIOM_INVENTORY.md`, `Helpers/TrackDStatus.md`, and this audit doc.

## §G. Worktree + cache (Claim 9) — VERIFIED

* Worktree present, clean (`git status --short` empty before T1.1).
* Lake manifest mtime: 2026-05-02 19:24 (today; cache fresh).
* Mathlib build artefacts present in `.lake/build/lib/Mathlib/...`.
* No `lake exe cache get` needed pre-T2.3 build verification.

## §H. Borell-TIS literature (Claim 10) — VERIFIED

Sub-lemma 3 is the standard Borell-TIS (Borell-Tsirelson-Ibragimov-
Sudakov) inequality for the centered supremum of a Fintype-indexed
centered Gaussian process: the sup `M(ω) := ⨆ t, X t ω` minus its
mean is sub-Gaussian with variance proxy `sigma2 := sup_t Var(X_t)`.

Classical citations:
* Borell, "The Brunn-Minkowski inequality in Gauss space," Invent.
  Math. 30 (1975).
* Tsirelson, Ibragimov, Sudakov, "Norms of Gaussian sample functions,"
  Springer LNM 550 (1976) and earlier 1974 announcement.
* Adler & Taylor, *Random Fields and Geometry*, Springer 2007/2010,
  Theorem 2.1.2.
* Boucheron, Lugosi, Massart, *Concentration Inequalities*, OUP 2013,
  Theorem 5.6 / 5.8.

Mathlib pin status (TD5-prep §A.3 + Grok cross-check 2026-05-02):
zero hits for `borell`, `tsirelson`, `ibragimov`, `sudakov`,
`cis_inequality` across `leanprover-community/mathlib4`. Structural
gap, not a pin-version artefact (Claim 3 — VERIFIED).

## §I. Mismatch ledger (TD5 contribution)

No new misframings caught. T1.1 is a verification round on a
mechanical axiomatization; no Grok recipe was solicited and no math
content is being closed. Cumulative ledger unchanged at 8.

## §J. Status

All 10 Claims Verification Table rows VERIFIED (Claims 1, 5 deferred
to T1.1 in the brief; both confirmed here). Proceeding to T2.1
(axiom replacement).
