# R36 T1.1 — Upper-bound symbol audit (`gao_li_wellner_small_ball_upper`)

**Read-only audit, R36 (branch `r33-c-helpers-consolidation`, single round, Phase A
upper-side regression Path C3).** Mirror of R34 T1.1 audit (`R34_T1_IsGLWProcessAudit.md`)
on the lower side. Locates the upper symbol, captures current state, enumerates
consumers + auxiliary lemmas, and identifies the orphan-scaffold candidates created
by the C3 decision (Option E redux on the upper side, post-R35).

## §1 — Current declaration

* **File / line:** [`524.lean:3504`](../524.lean) — `theorem gao_li_wellner_small_ball_upper`.
* **Status pre-R36:** `theorem` with a single-line `sorry` body at `524.lean:3541`,
  preceded by a multi-paragraph BLOCKER comment block (`524.lean:3515-3540`) listing
  the Karhunen–Loève + Talagrand + V1-Anderson missing infrastructure.
* **Symmetry with lower side:** the lower companion `gao_li_wellner_small_ball_lower`
  was migrated `theorem-with-sorry → axiom` in R34 (`524.lean:3604`); R36 mirrors
  that transformation on the upper side.

## §2 — Exact signature (verbatim, line 3504)

```
theorem gao_li_wellner_small_ball_upper (glw : GaoLiWellnerConstants) :
    ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (Y : ℝ → Ω → ℝ), Erdos524.Helpers.IsGLWProcess Y →
      ∃ (ε₀ : ℝ) (T : ℝ → ℝ), 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          (ℙ {ω | ∀ u ∈ Set.Icc (0 : ℝ) (T ε), |Y u ω| ≤ ε}).toReal ≤
            Real.exp (-glw.upper * |Real.log ε| ^ 3) := by
  intro Ω _mΩ _hℙ Y _h_glw
  refine ⟨1, Erdos524.Helpers.glwUpperT, one_pos, ?_⟩
  intro ε _hε_pos _hε_le_one
  -- BLOCKER: ... (multi-paragraph diagnostic comment) ...
  sorry
```

Distinguishing features from the lower-side axiom:

* **Truncated form baked in.** Statement quantifies over `u ∈ Set.Icc 0 (T ε)` for a
  shape-preserving `T : ℝ → ℝ` (specifically `Erdos524.Helpers.glwUpperT`, a Round 7
  helper). Compare lower-side `axiom` which quantifies over `∀ u ≥ (0 : ℝ)` with
  the truncated-form derivation in a separate theorem `_lower_truncated`.
* **Existential over `T`.** The upper bound binds `T : ℝ → ℝ` existentially in the
  output, where the lower bound only binds `ε₀`. Consumers in `524.lean` `obtain ⟨εGLW, T, hεGLW_pos, hGLW_upper⟩`
  (4-tuple) where lower-side `obtain ⟨εGLW, hεGLW_pos, h_bound⟩` (3-tuple).

## §3 — Truncated companion (T2.2 — N/A on upper side)

```
$ grep -n "gao_li_wellner_small_ball_upper_truncated\|small_ball_upper_truncated" \
       FormalConjectures/ErdosProblems/524.lean \
       FormalConjectures/ErdosProblems/Helpers/*.lean
0 matches.
```

**Confirmed:** **no `_upper_truncated` companion exists.** The truncated form is
*the upper bound itself* (the `T(ε)` truncation is intrinsic to the upper-side
statement, since the proof would discretize `[0, T(ε)]`). The `_lower_truncated`
companion is needed only because the lower axiom is stated on the *full half-line*
`u ≥ 0`. T2.2 is therefore **N/A** on the upper side, cited per V1 protocol.

## §4 — Consumers (grep across `524.lean` + `Helpers/`)

```
$ grep -n "gao_li_wellner_small_ball_upper" 524.lean
   3504: theorem gao_li_wellner_small_ball_upper                  -- definition
   4055: gao_li_wellner_small_ball_upper glw Yplus               -- consumer 1
   4212: gao_li_wellner_small_ball_upper glw Yplus               -- consumer 2
plus three doc-comment references at 49, 3470, 4007, 7580.
```

**Two active call-sites** in `524.lean`:

| # | File:line | Theorem context | Use pattern |
|---|-----------|-----------------|-------------|
| C1 | `524.lean:4055` | `polynomial_sup_small_ball_upper` chain (Yplus branch) | `obtain ⟨εGLW, T, hεGLW_pos, hGLW_upper⟩ := gao_li_wellner_small_ball_upper glw Yplus (Erdos524.Helpers.gao_li_wellner_small_ball_upper_isGLWProcess_Yplus hYp_meas)` |
| C2 | `524.lean:4212` | `chojecki_lemma_15` chain (Yplus branch) | identical destructure pattern, same helper |

Both consumers use `obtain` on the existential output. The statement and helper
signatures are unchanged; the `theorem ↔ axiom` swap is invisible at the call-site
(same as the R34 lower-side migration confirmed empirically in R34 T2.5).

**No `Yminus`-side consumer.** Unlike the lower side which uses both `Yplus` and
`Yminus` (524.lean:4367 / 4370 / 4745 / 4748), the upper-side chain only invokes
the Yplus instance; the `Yminus` analogue is not currently called.

## §5 — Auxiliary lemmas referenced only by the upper chain

```
$ grep -n "gao_li_wellner_small_ball_upper_isGLWProcess" 524.lean Helpers/*.lean
   524.lean:4056, 4213            (consumers C1/C2 hypothesis discharge)
   Helpers/GLWUpperProof.lean:281 (definition: stub-with-sorry, sister of lower-side R34 carry-over)
```

**Sister carry-over sorries** (from R34 audit `Helpers/GLWLowerProof.lean:328, 340`):

* `gao_li_wellner_small_ball_upper_isGLWProcess_Yplus` — sorry, R34 audit notes
  "STILL GATED, retires together with lower-side sister".
* (No `_Yminus` upper sister currently used in 524.lean; presence in
  `GLWUpperProof.lean` not surveyed here — outside R36 scope.)

These are auxiliary lemmas (not orphans) — they discharge the `IsGLWProcess Y`
hypothesis at the C1/C2 call-sites. They remain valid post-R36 axiomatization
(the axiom still consumes an `IsGLWProcess Y` hypothesis), just as the lower-side
sister sorries remained valid post-R34.

## §6 — Orphan candidates from R35 (T2.3 input)

R35 landed three signature-level scaffolds on the assumption that Path B (native
Slepian + Sudakov-Fernique closure) would proceed in R36-R39. The post-R35 user
decision elects **Path C3** (axiomatize the upper bound directly, mirror of R34
lower-side Option E). Under C3 the following R35 artefacts have no immediate
consumer:

| Artefact | File | Status under C3 | Disposition (T2.3) |
|----------|------|------------------|--------------------|
| `slepian_comparison_finite` | `Helpers/PhaseAUpperBound.lean` | Skeleton, no consumer | **(a) Preserve with updated docstring** |
| `sup_continuous_eq_sup_dense` | `Helpers/PhaseAUpperBound.lean` | Skeleton, no consumer | **(a) Preserve with updated docstring** |
| `multivariateGaussianOrthantCDF_differentiable_wrt_covariance` (T2.1 stub) | `Helpers/MultivariateGaussianCDF.lean` | Signature + concrete-diagnostic body | **(a) Preserve with updated docstring** |

**Decision (T2.3, default option (a)):** preserve as research artefacts. Update
each enclosing-file docstring to note the C3 election and that the scaffold is
preserved for the (hypothetical) future round when the relevant Mathlib API
matures. Cost: dead code in mainline (Helpers files compile clean). Benefit:
R35's diagnostic work + signature drafts remain navigable from `git log`
without spelunking history.

The legacy `slepian_comparison_GLW : True` placeholder R35 preserved alongside
the new `slepian_comparison_finite` is unaffected (`True := by trivial` carries
no axiom risk).

## §7 — Doc-comment references (cosmetic, non-blocking)

* `524.lean:49` — top-of-file commentary noting upper/lower as `theorem`s; will
  need adjustment to reflect both as `axiom`s post-R36.
* `524.lean:3470` — sub-axiom enumeration list still references upper as item 1
  alongside lower as item 2. List adjustment is cosmetic.
* `524.lean:4007` — proof comment in the consumer chain references "Applying
  `gao_li_wellner_small_ball_upper`"; valid both pre/post-R36 (`apply` works on
  axioms).
* `524.lean:7580` — bottom-of-file recap comment.

R36 will update the line-49 and line-3470 commentaries inline with the axiom
conversion (T2.1).

## §8 — Audit verdict + R36 path readiness

**T2.1 (axiom conversion) is mechanical.** The mirror-of-R34 surgery is:

1. Replace `theorem` → `axiom` at `524.lean:3504`.
2. Strip the `:= by intro ... refine ... sorry` body.
3. Replace the `Round 7 status` paragraph + BLOCKER block-comment with the R36
   audit-honesty paragraph (analogue of the R34 paragraph at `524.lean:3543-3603`).
4. Adjust the doc references at lines 49, 3470, 7580 (cosmetic).

**T2.2 is N/A** (no `_upper_truncated` companion).

**T2.3 default option (a)** is the recommended path: preserve the R35 scaffolds
with updated docstrings citing C3.

**Build verification (T2.5):** the C3 conversion should leave the build state
identical to post-R34 — i.e. blocked on the pre-existing ENat conflict. R36
captures verbatim build output.

**Risk profile:** mechanical mirror of R34; the only round-specific engineering
content is the T2.3 orphan decision. R34 itself is the precedent, so R36 has a
working template.
