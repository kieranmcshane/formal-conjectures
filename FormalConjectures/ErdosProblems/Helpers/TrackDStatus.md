# Track D — Status doc (round 1, branch `track-d-btis-honest`)

**Round**: 1.
**Wall-clock**: < 2.5 h (within hard-stop trigger).
**Goal**: BTIS honest proof formalization scaffold (signature + audit +
portability assessment). NO closure of BTIS proper.

---

## 1. Build verification (verbatim)

* Command: `lake build FormalConjectures.ErdosProblems.Helpers.BTISHonestProof`.
* Result (final iteration, after the two trivial fixes — copyright header
  blank-line conformance and `σ²` → `sigma2` identifier rename, plus adding
  the project-standard
  `set_option linter.style.ams_attribute false`
  + `set_option linter.style.category_attribute false`):

  ```
  warning: brownian-motion: repository '/.../packages/brownian-motion' has local changes
  ✔ [7867/7867] Built FormalConjectures.ErdosProblems.Helpers.BTISHonestProof (49s)
  Build completed successfully (7867 jobs).
  EXIT: 0
  ```

* Only inherited warning (the `brownian-motion local changes` warning is
  pre-existing in the project; unrelated to Track D).

* Build log captured at `/tmp/trackd_build3.log` (last iteration);
  `/tmp/trackd_build.log` and `/tmp/trackd_build2.log` capture the two
  earlier iterations with the syntactic fixes applied incrementally.

## 2. File summary

* `Helpers/BTISHonestProof.lean` — 234 LOC. Within the
  spec's combined T2.1 + T2.2 budget (≈ 80-150 LOC infrastructure +
  30-50 LOC sub-lemmas; slightly over due to detailed docstrings, but
  inside the hard ceiling and substantively justified).
* Five declarations:
  1. `IsCenteredGaussianProcess` (structure, round-1 placeholder
     predicate; TD5 swaps to `BrownianMotion.Gaussian.IsGaussianProcess`
     or `Erdos524.Helpers.IsGLWProcess`).
  2. `gaussian_log_sobolev_real` (theorem, TAG'd
     `TrackD-LogSobolev-bottleneck`).
  3. `herbst_subgaussian_real` (theorem, TAG'd `TrackD-Herbst`).
  4. `lipschitz_sup_finite_gaussian` (theorem, TAG'd
     `TrackD-LipschitzSup`).
  5. `borell_tis` (theorem, TAG'd
     `TrackD-round1-signature-only-BTIS-stub`).
* All four theorems carry TAG'd `sorry` bodies. Sorry count in this file
  = 4 (verified by `grep -c "sorry" BTISHonestProof.lean = 5`, of which
  one is the docstring mention "carry TAG'd `sorry` bodies").

## 3. Net debt change (project-wide, branch `track-d-btis-honest`)

| Metric | Pre-round-1 | Round-1 end | Δ |
| --- | --- | --- | --- |
| User-defined axioms | 5 | 5 | 0 |
| TAG'd sorries | 12 | 16 | +4 |

Total debt items: 17 → 21 (+4). Composition of the four new sorries:
* `TrackD-LogSobolev-bottleneck` (TD2-TD3 closure target);
* `TrackD-Herbst` (TD3-TD4 closure target);
* `TrackD-LipschitzSup` (TD4-TD5 closure target);
* `TrackD-round1-signature-only-BTIS-stub` (TD5 assembly target).

This is the EXPECTED behaviour per Grok Q3+Q4: round-1 is scaffolding,
sorries land NOW so future rounds can retire them with concrete proofs.
The R59 ceiling is not affected by this round (closure scheduled in
TD2-TD5, possibly compressed to TD2-TD3 per Q5 if SLT portable).

## 4. Cluster trajectory projection

### 4.a Conservative case (5-round cluster, no SLT portability)

| Round | Target | Bottleneck | Estimated wall |
| --- | --- | --- | --- |
| TD1 (this) | Signature + audit + portability | — | < 2.5 h ✓ |
| TD2 | Gaussian log-Sobolev (1D) | Bakry-Émery / OU semigroup | 4-6 h |
| TD3 | Gaussian log-Sobolev (multivariate) + multivariate-to-1D bridge | Tensor-product structure | 4-6 h |
| TD4 | Herbst's argument + Lipschitz-sup | Standard once log-Sobolev present | 3-4 h |
| TD5 | BTIS assembly + downstream consumer rewire | Mathlib's `HasSubgaussianMGF.measure_ge_le` | 2-3 h |

Net axiom retirement at cluster end: -1 axiom (`gao_li_wellner_small_ball_upper`
or its consumer-side reformulation, depending on which BTIS-form is wired
into the GLW chain). The Y_GLW_exists / kmt_aided / one_dim_KMT axioms
remain unaffected by Track D — they belong to Tracks A/C.

### 4.b Compressed case (2-3-round cluster, SLT portability holds)

| Round | Target |
| --- | --- |
| TD1 (this) | Signature + audit + portability |
| TD2 | Import-adapt SLT log-Sobolev + Herbst; close Sub-lemmas 1+2 |
| TD3 | Lipschitz-sup + BTIS assembly + downstream rewire |

Wall-clock saving: 5-9 h. Calendar saving: 2-3 rounds. R59 ceiling
buffer impact: positive (frees up rounds for either Track A
non-BTIS sorries or Track B / Track C residuals).

### 4.c Worst case (SLT non-portable, multivariate log-Sobolev hard)

If SLT formalization on a too-distant Mathlib pin AND multivariate
tensor-product log-Sobolev requires a deeper Bakry-Émery / OU semigroup
formalization than budgeted: 6-7-round cluster, possible TD2 bottleneck
escalation. Mitigation: stay within 1D Gaussian log-Sobolev for an
intermediate sub-result, accept a slightly weaker BTIS form (single
marginal direction at a time, then union-bound over the discrete grid
in the GLW consumer). Quantitatively this gives a constant-factor
worse exponent in the GLW-upper consumer but does not break R59.

## 5. External SLT formalization portability assessment

**Repo identity**: per Grok Q1, the `lean-stat-learning-theory` (Yuanhe
et al., Feb 2026) library reportedly contains Gaussian concentration
via the log-Sobolev + Herbst route. Citation chain: Grok pre-flight
verbatim. CAVEAT: not independently verified at TD1 time.

**Verification status (TD1)**:

* I do not have an active network in the present `Bash` environment to
  `git clone` or `WebFetch` the repo. Verification deferred to TD2.
* `WebFetch` IS available as a deferred tool in this CLI environment.
  TD2 should `WebFetch` against the canonical GitHub URL once it is
  identified (suggested first-pass query: `WebSearch
  "lean-stat-learning-theory Gaussian concentration log-Sobolev Yuanhe"`),
  then a focused inspection of:
  - License (Apache-2.0 / MIT compatibility).
  - Mathlib pin (target: ≤ 2 months drift from `25ce6331`).
  - Module structure (whether `LogSobolev` / `GaussianConcentration` are
    standalone modules importable without dragging the entire SLT corpus).

**Round-1 portability call (honest)**:

* Probability of successful import without major adaptation:
  ~ 0.40 (large drift between SLT releases and Mathlib pins is common).
* Probability of partial-import / proof-text adaptation reducing TD2-TD3
  by ≥ 50%: ~ 0.55 (even non-importable SLT code accelerates Lean
  proof-search by serving as a worked example).
* Probability of zero usable transfer: ~ 0.20.

Combined effective expected speedup of cluster: weighted average of
2-round (compressed, P=0.40), 3-round (partial, P=0.40), 5-round
(no transfer, P=0.20) = 2 · 0.40 + 3 · 0.40 + 5 · 0.20 = 3.0 rounds
mean. So expected cluster length ≈ 3 rounds (TD1-TD3) under the union
of cases, with TD4-TD5 capacity reserved as buffer for the 20 % tail.

**Discipline note**: until TD2's verification fires, Track D plans for
the 5-round conservative case as the binding floor and treats any
compression as accelerator-only. No promised timeline that REQUIRES
SLT portability without prior verified import.

## 6. Branch coordination + isolation check

* Branch `track-d-btis-honest` created from `track-b-r33cd-gaps@5596638`
  (parent matches inventory state at R45 close).
* Files added (this round, on this branch only):
  - `FormalConjectures/ErdosProblems/Helpers/BTISHonestProof.lean`
    (234 LOC, 4 TAG'd sorries).
  - `FormalConjectures/ErdosProblems/Helpers/TrackD_T1_BTISAudit.md`
    (audit doc).
  - `FormalConjectures/ErdosProblems/Helpers/TrackDStatus.md` (this
    file).
* Files modified: NONE (no edits to shared Track A / Track B / Track C
  surfaces; no edits to `524.lean` or any non-Track-D helper).
* Branch isolation **verified strict**.

## 7. Round-end Brier-honest scoring (mandatory floor)

| Mandatory-floor item | Predicted P(Full) | Realised | Comment |
| --- | --- | --- | --- |
| T1.1 Mathlib audit + framing | 0.85 | Full | Pin `25ce6331` audited; SLT verification honestly deferred |
| T2.1 Infrastructure + signature | 0.85 | Full | Builds clean after two trivial syntactic fixes (header blank line, `σ²` rename) |
| T2.2 Sub-lemma signatures | 0.85 | Full | All three TAG'd; signatures concrete (1D Gaussian for log-Sobolev, NNReal Lipschitz for Herbst, Fintype for sup) |
| T2.3 Build + status + portability | 0.90 | Full | Clean build at iteration 3; portability assessment landed honestly |

**Joint mandatory floor**: 4/4 = Full. Predicted joint P(Full) ≈ 0.55;
realised Full. Modest favourable surprise — the brownian-motion
`IsGaussianProcess` discovery (T1.1) trimmed a layer of TD5 work and
the syntactic fixes (header blank line, `σ²` rename) were trivial and
single-iteration each.

## 8. Anti-patterns avoided this round

* No closure attempt of BTIS proper (Grok Q3 explicit infrastructure
  scope).
* No edits to Track A / B / C files; branch isolation strict.
* No reliance on Grok's Mathlib state without pin verification (audit
  done in T1.1; Grok Q1 verdict (a)–(e) confirmed against pin).
* No commitment to SLT portability without a verification gate
  (deferred to TD2 with explicit `WebFetch`/`WebSearch` plan).
* No premature multivariate log-Sobolev statement (1D form chosen as
  the round-1 anchor; multivariate generalisation deferred to TD3 if
  the conservative path holds).

## 9. Outstanding diagnostic items for TD2

1. `WebFetch`/`WebSearch` the SLT repo, verify license + Mathlib pin
   compatibility, capture the verdict in `TrackD_T2_SLTVerification.md`
   (or note non-existence honestly).
2. Decide on TD2's specific log-Sobolev target: 1D from-scratch
   (conservative) vs SLT-imported (compressed). Decision rule: if
   verification at (1) returns Apache-2.0/MIT + Mathlib pin within
   2-month drift, route compressed; else route conservative.
3. Stage the `IsCenteredGaussianProcess` → `IsGaussianProcess`
   harmonisation: TD5 will replace the round-1 placeholder structure.
   TD2 may stage the harmonisation early if it is cheap.
4. Confirm whether `gaussian_log_sobolev_real`'s consumer needs the
   normalized form `Ent(f²)` or the entropy-minus-mean variant;
   adjust signature in TD2 if consumer-needs differ from current
   round-1 statement.

## 10. Cluster-spanning calibration note

Track D is the fourth parallel track (post Tracks A/B/C). Math-content
P(Full) bias rule applies: do NOT promote round-1 confidence to
round-2 closure timelines without an independent re-anchor at TD2.
The honest cluster forecast carries a ~20% tail on conservative
5-round duration; do not budget around the optimistic 2-round case.

---

# Round-2 closure (Path B′) — addendum

**Round**: 2.
**Wall-clock**: < 3.0 h (within hard-stop trigger).
**HEAD at commit**: `41ad28b` (`Track D round 2 (T2.1 + T2.2): close
borell_tis body via Chernoff`), parent `bb31686` (portability audit doc),
parent `3b75bde` (round-1 closure).

## Round-2 net debt change (this round)

| Metric | Round-1 end | Round-2 end | Δ |
| --- | --- | --- | --- |
| User-defined axioms | 5 | 5 | 0 |
| TAG'd sorries (file BTISHonestProof.lean) | 4 | 3 | **−1** |

**One sorry retired**: `borell_tis` (was TAG'd
`TrackD-round1-signature-only-BTIS-stub`). Replaced by a Full body that
deduces the BTIS tail bound via:

1. Sub-lemma 3 (`lipschitz_sup_finite_gaussian`) wrapped in
   `HasSubgaussianMGF` (signature lift, body still TAG'd
   `TrackD-LipschitzSup`).
2. Mathlib's Chernoff bound `HasSubgaussianMGF.measure_ge_le`
   (`Probability/Moments/SubGaussian.lean` line 704).
3. Set translation `{ω | r ≤ Y ω} = {ω | M ω ≥ E[M] + r}` via
   `Set.mem_setOf_eq` + `linarith`.
4. Coercion `(sigma2.toNNReal : ℝ) = sigma2` via `Real.coe_toNNReal`.
5. `Measure.real ↔ (· ).toReal` bridge via `measureReal_def` (rfl).

**Remaining 3 sorries** (all upstream of `borell_tis`):

- `gaussian_log_sobolev_real` (TAG `TrackD-LogSobolev-bottleneck`) — TD3
  closure target, ~200-300 LOC if ported from
  `lean-stat-learning-theory`.
- `herbst_subgaussian_real` (TAG `TrackD-Herbst`) — TD4 closure target,
  ~80-150 LOC mechanical Herbst iteration.
- `lipschitz_sup_finite_gaussian` (TAG `TrackD-LipschitzSup`) — TD4
  closure target, ~50-100 LOC after Herbst lands.

## Round-2 cluster forecast (UPDATED 5 → 4 rounds)

| Round | Target | Status |
| --- | --- | --- |
| TD1 (R1) | Signature + audit + first portability assessment | ✓ Full |
| TD2 (this) | Path-decision (Path B′) + close `borell_tis` body | ✓ Full |
| TD3 | Close `gaussian_log_sobolev_real` (port from SLT) | Pending |
| TD4 | Close `herbst_subgaussian_real` + `lipschitz_sup_finite_gaussian` | Pending |
| TD5 (BTIS axiom retirement, target 4) | Wire BTIS into `gao_li_wellner_small_ball_upper`; consumer rewrite | Pending |

Compression mechanism: Path B′ achieves a **structural** closure that does
not require log-Sobolev to land first. The `borell_tis` body is now Full
modulo `lipschitz_sup_finite_gaussian` (sub-lemma 3), and the chain
`Lipschitz-sup ← Herbst ← log-Sobolev` remains as a 2-round bottleneck
(TD3 + TD4). TD5 is the BTIS-axiom retirement at the GLW consumer site.

**Net cluster compression**: 5 → 4 rounds (−1 round); R52 gate evaluation
unaffected since cluster compression is favourable.

## Round-2 portability assessment outcome

`Helpers/TrackD_round2_T1_PortabilityAudit.md` records the verified
findings:

- `lean-stat-learning-theory` (Yuanhe Zhang et al., Feb 2026):
  MIT license (compatible with Apache-2.0); toolchain match
  `leanprover/lean4:v4.27.0-rc1` (exact); Mathlib pin
  `d68c4dc09f5e000d3c968adae8def120a0758729` (vs ours `25ce633136` —
  different but same major series).
- `SLT/GaussianLipConcen.lean` (~1,400 LOC) exports
  `gaussian_lipschitz_concentration` — the direct match for our
  BTIS-style conclusion.
- `SLT/GaussianLSI/` directory contains tensorized log-Sobolev.

**Path A (full lake-level import)**: HIGH RISK due to Mathlib pin diamond
with `brownian-motion` / `kolmogorov_extension4`; demoted to "future
optional" rather than "round 2".

**Path B (manual port, TD3+)**: viable. 200-400 LOC across 2-3 rounds.
The SLT proofs remain a strong reference point regardless of import
strategy.

**Cross-track**: `GaussianParametricAnalysis.lean` exists on R46 mainline
(commit `53ac58a`) but NOT on `track-d-btis-honest`. Cherry-pick deferred;
not blocking round-2 closure.

## Round-2 build verification

Command: `lake build FormalConjectures.ErdosProblems.Helpers.BTISHonestProof`

Output (verbatim, after the `borell_tis` body fix iteration):

```
warning: brownian-motion: repository '...' has local changes
✔ [7867/7867] Built FormalConjectures.ErdosProblems.Helpers.BTISHonestProof (16s)
Build completed successfully (7867 jobs).
```

Captured at `/tmp/trackd_round2_build.log`. The `brownian-motion` warning
is pre-existing (not introduced by Track D).

## Round-2 Brier-honest scoring (binding)

| Mandatory-floor item | Predicted P(Full) | Realised | Comment |
| --- | --- | --- | --- |
| T1.1 Re-grep + WebSearch + cross-track | 0.85 | Full | KL-divergence found (irrelevant to round-2 path); SLT MIT + `v4.27.0-rc1` confirmed; cross-track GPA not on this branch |
| T2.1 Path decision + first commit | 0.55 | Full | Path B′ chosen; build clean after one fix iteration (Set.mem_setOf_eq unfold, NNReal coercion, μ.real bridge) |
| T2.2 Path completion (docstring update) | 0.55 | Full | File-top docstring updated; build re-verified clean |
| T2.3 Build + status + cluster forecast | 0.95 | Full (this addendum) | Build log captured; cluster forecast updated 5 → 4 rounds |

**Joint mandatory floor**: 4/4 = Full. Predicted joint P(Full) ≈ 0.45;
realised Full. Modest favourable surprise from the SLT portability check
(MIT + exact toolchain match) plus a structural-closure path (Path B′)
that did not require pin migration.

## Round-2 anti-patterns avoided

* No closure attempt of log-Sobolev or Herbst under round budget (would
  have eaten the 3.5h hard-stop with no robust outcome).
* No full lake-level SLT import (would have triggered Mathlib pin
  diamond, breaking project build for unrelated tracks).
* No cherry-pick of `GaussianParametricAnalysis` from R46 mainline
  without explicit user dispatch (deferred; avoids accidental cross-track
  contamination).
* No promotion of strong-portability evidence to a round-2 commitment
  beyond what the SLT-API-aligned closure path actually delivers.
* No edits to mainline files; branch isolation strict on commits
  `bb31686` and `41ad28b` (only `BTISHonestProof.lean` and the two new
  `TrackD_round2_*.md` files touched).

## Round-2 outstanding diagnostic items for TD3

1. Decide TD3 closure approach for `gaussian_log_sobolev_real`:
   (a) port from SLT `GaussianLSI/` directory; (b) from-scratch via
   Bakry-Émery (high cost) or direct Stein's identity (medium cost,
   may interact with Mathlib's `KullbackLeibler`).
2. Whether to cherry-pick `GaussianParametricAnalysis.lean` from R46
   commit `53ac58a` for use in TD4's Lipschitz-sup body — deferred
   pending the TD3 path choice (some Lipschitz-sup approaches don't
   need the parametric DCT machinery).
3. Whether to harmonise `IsCenteredGaussianProcess` with
   `BrownianMotion.Gaussian.IsGaussianProcess` at TD3 (early bridge)
   or wait until TD5 (cluster end). Decision rule: if the SLT port
   uses the brownian-motion predicate natively, harmonise at TD3;
   else defer to TD5.
