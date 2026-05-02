# Track D — round 2 T1.1 Portability audit (binding)

**Branch**: `track-d-btis-honest` (HEAD `3b75bde` pre-round-2).
**Round**: 2.
**Wall-clock at write**: ≈ T+0:35.
**Goal**: WebSearch + Mathlib re-grep + cross-track check → concrete portability verdict
to drive T2.1 path decision.

---

## 1. Pinned Mathlib re-audit (vs round 1, on rev `25ce633136`)

Running `grep -l` from `.lake/packages/mathlib/Mathlib`:

| Pattern | Hits in pin | Verdict |
| --- | --- | --- |
| `log_sobolev`, `logSobolev` | 0 | absent |
| `herbst` | 0 | absent |
| `Bakry`, `BakryEmery` | 0 | absent |
| `OrnsteinUhlenbeck` | 0 | absent |
| `Hermite` (polynomials) | 0 file matches | absent |
| `Concentration` (file name) | 0 | absent |
| `HasSubgaussianMGF` | `Probability/Moments/SubGaussian.lean` | **present** |
| `Fernique` | `Probability/Distributions/Fernique.lean` + Gaussian sub-file | **present** |
| `KullbackLeibler` (KL divergence) | `InformationTheory/KullbackLeibler/Basic.lean` + `KLFun.lean` | **present** (new finding vs round 1) |
| `HasGaussianLaw` | 0 in Mathlib | absent (only `BrownianMotion.Gaussian.IsGaussianProcess` available) |

**Summary.** Round-1 conclusion (no log-Sobolev / no Herbst / no Bakry-Émery /
no OU semigroup / no Hermite) is re-verified. New finding: KL-divergence
infrastructure is present (relevant if any future log-Sobolev proof goes
through the Gibbs-variational form), but not enough by itself to short-circuit
log-Sobolev. The from-scratch Mathlib path remains a 5-round cluster minimum.

## 2. Cross-track `GaussianParametricAnalysis` check

`ls FormalConjectures/ErdosProblems/Helpers/GaussianParametricAnalysis.lean`
returns "No such file or directory" on `track-d-btis-honest` HEAD `3b75bde`.

`git log --all -- ...GaussianParametricAnalysis.lean`:

* commit `53ac58a` "R46-T3.1 (stretch): GaussianParametricAnalysis cross-track
  synergy library" lives on `r46-track-a-mge-posdef` branch (R46 mainline).
* The commit is **not yet merged** into `track-d-btis-honest`.

**Verdict.** Cross-track synergy from R46 mainline is unavailable at round-2
start. Cherry-picking `53ac58a` would be a 1-commit operation, but it pulls
in dependencies that may not yet be present on this branch. **Decision**:
defer cross-track integration to a future round; do NOT block round-2 closure
on the import.

## 3. WebSearch — Yuanhe Zhang's `lean-stat-learning-theory`

WebSearch (May 2026) returns the repository at
<https://github.com/YuanheZ/lean-stat-learning-theory> with the following
verified facts:

| Property | Value | Compatibility |
| --- | --- | --- |
| **License** | MIT | **compatible** with project Apache-2.0 |
| **Lean toolchain** | `leanprover/lean4:v4.27.0-rc1` | **exact match** with our `lean-toolchain` |
| **Mathlib pin** | `d68c4dc09f5e000d3c968adae8def120a0758729` | **differs** from our `25ce633136` (same major series, low API drift expected; lake-level dependency import is HIGH RISK due to potential diamond-pin conflict with `brownian-motion` / `kolmogorov_extension4`) |
| **Scale** | ~30,000 LOC, 500h dev | adaptation-not-import only (full lake import beyond a single round's scope) |

**Module structure (verified via WebFetch on `tree/main/SLT`)**:

* `SLT/GaussianLipConcen.lean` — main consumer; ≈ 1,400-1,500 LOC.
  Exports `gaussian_lipschitz_concentration` (two-sided BTIS-style tail
  for L-Lipschitz functions of standard Gaussian on `EuclideanSpace ℝ (Fin n)`).
* `SLT/GaussianLSI/TensorizedGLSI.lean` — tensorized log-Sobolev (multi-D).
* `SLT/GaussianPoincare/` — Poincaré inequality + Lévy continuity etc.
* `SLT/GaussianSobolevDense/` — density of `Cc∞` in Sobolev (auxiliary).
* `SLT/SubGaussian.lean` — sub-Gaussian wrapper (likely thinner than Mathlib's).

The `GaussianLipConcen.lean` file's import list:
`SLT.GaussianLSI.TensorizedGLSI`, `SLT.LipschitzProperty`,
`SLT.MeasureInfrastructure`, `SLT.GaussianSobolev.LipschitzMollification`.
Transitive footprint: several thousand LOC.

## 4. Path verdict (binding for T2.1)

| Path | Round-2 closure cost | Risk | Net sorry change |
| --- | --- | --- | --- |
| **Path A** — full lake-level SLT import | 1-3 days infrastructure work + Mathlib pin migration | **HIGH**: pin diamond may break project build (regression) | -2 to -3 IF migration succeeds |
| **Path B** — manual port of log-Sobolev + Herbst from SLT | 200-400 LOC over 2-3 rounds | Medium: API translation between Mathlib pins | -1 this round (log-Sobolev only), then -1 in TD3 (Herbst), -1 in TD4 (Lipschitz-sup) |
| **Path B′ (chosen)** — close `borell_tis` body **via** sub-lemma 3 + Mathlib's `HasSubgaussianMGF.measure_ge_le` (Chernoff) | 30-80 LOC | Low | **-1 this round** (BTIS Full, three sub-lemmas remain); cluster compresses 5 → 4 rounds |
| **Path C** — original from-scratch | 250 LOC × 5 rounds | Low | -1/round, full cluster |

**Decision.** **Path B′** (BTIS-via-Chernoff). Rationale:
1. Mandatory floor + 3.5 h hard-stop forbids Path A's pin-migration risk.
2. SLT API-surface match found: `HasSubgaussianMGF.measure_ge_le` (line 704
   of `Probability/Moments/SubGaussian.lean`) is exactly the Chernoff bound
   `μ.real {ω | ε ≤ X ω} ≤ exp(-ε²/(2c))` we need to deduce
   `borell_tis` from `lipschitz_sup_finite_gaussian`.
3. Path B′ is a *structural* closure: the BTIS theorem is reduced to the
   sub-Gaussian-MGF property (sub-lemma 3), which itself reduces to log-Sobolev
   (sub-lemma 1) via Herbst (sub-lemma 2). The reduction is **independent of
   whether SLT is imported or ported manually** — it commits to the chain
   without locking into a specific port strategy. TD3-TD4 retain the option
   to either port from SLT (Path B refinement) or from scratch (Path C).
4. The required `HasSubgaussianMGF` wrapper requires upgrading sub-lemma 3's
   conclusion from a bare `mgf ≤ exp(...)` to the full `HasSubgaussianMGF`
   structure (carrying integrability + the bound). This signature
   refinement is local to `Helpers/BTISHonestProof.lean` and does not
   break any existing import.

**Cluster forecast post-T2.1**:

* TD2 (this round): close `borell_tis` body. **Cluster 5 → 4 rounds**.
* TD3: close `gaussian_log_sobolev_real` (port from SLT, ~200-300 LOC).
* TD4: close `herbst_subgaussian_real` body (mechanical Herbst iteration,
  ~80-150 LOC) AND `lipschitz_sup_finite_gaussian` body (apply Herbst to
  sup as Lipschitz functional, ~50-100 LOC). Both close together because
  Herbst + sub-lemma 3 are bookkeeping once log-Sobolev is in scope.
* TD5: BTIS axiom retirement (consumer rewrite + closure verification).

## 5. T2.2 stretch (path B′ refinement)

If T2.1 closes cleanly with budget remaining, attempt to close
`herbst_subgaussian_real` body **assuming `gaussian_log_sobolev_real` as
hypothesis** (i.e., the standard Herbst iteration):

* Differentiate `t ↦ log mgf Y t` w.r.t. `t`.
* Apply log-Sobolev to `g(x) := exp(t f(x) / 2)`.
* Derive ODE `(d/dt) (cgf Y t / t) ≤ L² t / 2`.
* Integrate `cgf Y t / t ≤ L² t / 2` from 0 to t (Grönwall).

This is ~80-150 LOC of careful Lean. **Time-permitting only**; do not
sacrifice T2.3 build verification or T2.1 robustness for this.

## 6. Sub-checkpointing forecast

| Sub-check | Time | Status target |
| --- | --- | --- |
| T+0:30 | T1.1 grep + WebSearch + audit doc committed | **on track at T+0:35** |
| T+1:30 | T2.1 first commit (BTIS-via-Chernoff) | path locked, ~30 LOC body |
| T+2:30 | T2.2 path completion (Herbst attempt or doc-only) | depends on T2.1 success |
| T+3:00 | T2.3 build clean + status doc | mechanical |
| T+3:30 | hard-stop | push + audio |

## 7. Honest Brier-style status (round-2 T1.1)

| Sub-outcome | Predicted | Realised | Comment |
| --- | --- | --- | --- |
| Mathlib re-grep no surprises | 0.90 | Full (KL is bonus, not blocker) | KL is irrelevant to round-2 path |
| SLT repo identification | 0.85 | Full | URL + license + toolchain confirmed |
| SLT pin matches ours | 0.40 | Partial (toolchain match, Mathlib pin differs) | Lake-import path A demoted to high-risk |
| Cross-track `GaussianParametricAnalysis` accessible | 0.40 | Partial (in R46 mainline, not on this branch) | Cherry-pick deferred, not blocking |
| Path decision is conservative | 0.85 | Full | Path B′ is the only sub-3.5h-risk path |

## 8. Anti-patterns avoided

* No commit on the strength of unverified portability (round-1 deferral was
  honest; round-2 verifies before committing path).
* No premature lake-level SLT import attempt (would break build on Mathlib pin
  diamond).
* No skip of WebSearch/license check (Path B′ depends on knowing SLT exists
  even if we don't import it — round-2 commits to a closure path that lines
  up structurally with SLT's API surface).
* No edits to mainline files (branch isolation strict).
