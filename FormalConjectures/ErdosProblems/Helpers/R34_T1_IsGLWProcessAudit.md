# R34 — T1.1 IsGLWProcess Helpers Audit (post-R33-D)

**Read-only audit, single round, R34 (branch `r33-c-helpers-consolidation`).**
Documents the post-R33-D status of the two `IsGLWProcess` discharge
helpers at `Helpers/GLWLowerProof.lean:328, 340` and reports a verdict
on whether they are now closable, still gated, or need an adapter.

## Helpers under audit

### Helper 1 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus`

**Location**: `Helpers/GLWLowerProof.lean:324-328`.

**Statement**: takes `{Yplus : ℝ → Ω → ℝ}` and `_hYp_meas : ∀ u, Measurable (Yplus u)`,
returns `IsGLWProcess Yplus` (the predicate from
`Helpers/GLWProcessPredicate.lean`).

**Body**: `sorry` (line 328).

**Block-comment context (lines 308-320)**:
- BLOCKER: deriving `IsGLWProcess` from the KMT-coupling output, which
  asserts measurability + continuity + tail decay + coupling bound but
  NOT the explicit K_GLW covariance.
- TRIED: extraction from `two_dim_KMT_coupling` output (insufficient).
- NEEDS: (a) extend coupling output to assert `IsGLWProcess` directly;
  OR (b) Skorokhod-style transfer from `Y_GLW_exists` to the KMT
  probability space; OR (c) accept as stepping-stone helper analogous
  to `Y_GLW_exists` itself.

### Helper 2 — `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus`

**Location**: `Helpers/GLWLowerProof.lean:336-340`.

**Statement**: parallel to Yplus helper, takes `_hYm_meas : ∀ u, Measurable (Yminus u)`,
returns `IsGLWProcess Yminus`.

**Body**: `sorry` (line 340).

Same gating as Yplus helper. Comment says "same argument as for Yplus".

## Consumer call-sites (post-R33-D)

The two helpers are consumed at four call-sites in `524.lean`:

| Line  | Theorem                                            | Yplus/Yminus source                       |
|-------|----------------------------------------------------|-------------------------------------------|
| 4366  | `polynomial_sup_small_ball_lower`                  | `two_dim_KMT_coupling_legacy_Ω_form a ha` |
| 4369  | `polynomial_sup_small_ball_lower`                  | (same)                                    |
| 4744  | `polynomial_sup_small_ball_lower_uniform`          | `two_dim_KMT_coupling_legacy_Ω_form a ha` |
| 4747  | `polynomial_sup_small_ball_lower_uniform`          | (same)                                    |

The destructuring at all four call-sites:
```
obtain ⟨Yplus, Yminus, Δ, hYp_meas, hYm_meas, hΔ_bd, hKMT_p, hKMT_m, hIndep,
    hYp_cont, hYm_cont, _hYp_tail, _hYm_tail⟩ :=
  two_dim_KMT_coupling_legacy_Ω_form a ha
```
The legacy-Ω form returns the standard 13-tuple shape that pre-existed
the R33 Form β migration. The helpers are then called with only
`hYp_meas / hYm_meas` (the `Measurable` conjunct).

## Post-R33-D status check

The R34 prompt hypothesises that R33-D's "linear-combo Form β + IndepFun
TAG'd-but-correct" might unblock these helpers. Verifying:

**R33-D landed (commit `e58ea93`)**:
1. Public `theorem two_dim_KMT_coupling` body = `via_LS_reduction a ha`,
   with Form β signature (linear-combination conjunct, joint-Gaussianity
   on Ω × Ω product space).
2. 4 consumers migrated to legacy-Ω form via `two_dim_KMT_coupling_legacy_Ω_form`.
3. Bridge theorem `two_dim_KMT_coupling_legacy_Ω_form` itself carries a
   residual sorry (TAG `R33-D-T2.2-formβ-to-fullsum-bridge`) — the
   Ω × Ω → Ω reconstruction from joint-Gaussian + uncorrelated-equiv-
   independent.

**Does R33-D unblock the IsGLWProcess helpers?** **No.** The R33-D work
addressed a different concern: how to expose the coupling output on the
single Ω space (legacy form) given the new product-space Form β. The
mathematical content available at the consumer call-site post-R33-D is:

- `Yplus, Yminus : ℝ → Ω → ℝ`
- Measurability of each marginal
- Continuity of each path
- Coupling rate `|n^{-1/2} Σ a_k · kernel - Y u ω| ≤ Δ n` (for both `+` and `-` branches)
- `IndepFun (Yplus, Yminus)`
- Tail decay (a.s.)

What is STILL absent is **K_GLW covariance** and **joint Gaussianity**
of `Yplus / Yminus` as random elements of `ℝ → ℝ`. Both are required by
`IsGLWProcess` per `Helpers/GLWProcessPredicate.lean:78-97`. The KMT
coupling rate alone does NOT propagate the limit's covariance structure
to a per-call-site assertion: it only says `Y` is the in-probability
limit at sub-CLT rate of the partial sum, which is an EXISTENTIAL
covariance fact, not a structural one.

R33-D's IndepFun work is upstream of the joint-Gaussianity question,
not the per-Y K_GLW covariance question. The `Y_GLW_exists` axiom (in
`Helpers/GLWProcess.lean`) DOES produce a Y with `IsGLWProcess`, but
that Y lives on a different probability space than the KMT space, so
the gap is genuinely an isomorphism / Skorokhod transfer issue.

## Verdict per helper

### `gao_li_wellner_small_ball_lower_isGLWProcess_Yplus` — **Still gated**

Same gating as pre-R33-D, with a refreshed diagnostic acknowledging the
linear-combo Form β work but noting that R33-D operated on coupling
structure (Ω vs Ω × Ω + IndepFun), NOT on joint-Gaussianity / K_GLW
covariance derivation. Resolution paths unchanged:
- (a) Extend `two_dim_KMT_coupling` (or its legacy-Ω form) to assert
  `IsGLWProcess` directly. This requires that the coupling construction
  package the limit's structural facts, which is conceptually simple
  given Letwin–Sawhney's two-independent-1D-KMT view (each Y is an
  Itô integral against an independent BM, hence Gaussian + K_GLW
  covariance by construction). Out of round budget but not deeply
  obstructed.
- (b) Skorokhod transfer of `Y_GLW_exists` Y to the KMT space —
  abstract-measure-isomorphism argument.
- (c) Accept as stepping-stone helper analogous to `Y_GLW_exists`
  itself — currently de-facto status (TAG'd sorry).

### `gao_li_wellner_small_ball_lower_isGLWProcess_Yminus` — **Still gated**

Identical gating, identical resolution paths.

## Adapter possibility (rejected)

One alternative considered: change the helpers' signatures to take
`IsGLWProcess Y` as a direct hypothesis (instead of `Measurable`), then
`exact h_glw` discharges trivially. This relocates the gate to the
consumer call-sites in `524.lean:4366/4369/4744/4747`, where the
caller would have to prove `IsGLWProcess Yplus / Yminus` from the
legacy-Ω destructuring. **Same gating, just moved**. Rejected: no real
progress, and the relocation would force the same sorry into 4
call-sites instead of 2 helpers.

## Comparison with the upper-bound side

The corresponding upper-bound helpers
(`gao_li_wellner_small_ball_upper_isGLWProcess_Yplus / _Yminus` at
`Helpers/GLWUpperProof.lean:281`) carry IDENTICAL TAG'd sorries with
identical gating. Both are consumed by `polynomial_sup_small_ball_upper`
and its uniform variant. The lower-side and upper-side helpers should
be retired together when one of the resolution paths above lands.

## Conclusion

The post-R33-D environment does NOT unblock the IsGLWProcess helpers.
Verdict for both: **Still gated**, with a documented refreshed
diagnostic. T2.3 will leave the sorries in place but update the
in-file comments to reflect the post-R33-D status (R33-D mentioned in
the BLOCKER block as "investigated but not unblocking"), so the audit
trail is complete.

Round budget for actually closing: estimated 1-2 rounds via path (a)
(`two_dim_KMT_coupling` extension to assert `IsGLWProcess` per
marginal), once the Form β output has a stable structure post-R34's
upper-bound axiom regression.

## R34 action

Per the binding floor: T2.3 lands as **"Still gated, comment refreshed"**
with concrete diagnostic citing the R33-D investigation. This is
honest documented gating, not a vague defer. No 50%-cap penalty per
the round prompt's calibration framing.
