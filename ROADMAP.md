# Erdős 524 Lean — Round Roadmap

**Last updated** : 2026-05-03 post-R61 + R62 audit-redirect + Probe 5 grounded recalibration.
**Mainline ledger at HEAD `f4011b9`** : 18 gate items (10 axioms + 8 sorries).
**Ship target** : 5-axiom-conditional / 6-axiom-realistic. See `HANDOVER_BRIEF.md` §1.

---

## Immediate dispatch queue

| Round | Surface | Brief | Realistic LOC | Net debt | Mainline ledger after |
|---|---|---|---|---|---|
| **R62 audit-redirect commit** | mainline | `outputs/R62_SmallBall_Retirement_brief.md` (audit doc only) | 0 (no body work) | 0 | 18 → 18 |
| **R63** Cauchy det identity + retire `glw_det_lower_bound` | mainline | `outputs/R63_Cauchy_Det_Retirement_brief.md` | 350-600 | -1 axiom | 18 → 17 |
| **TC12** Carter-Pollard §2 eq (7) + §4 bulk upper bound | track-c | `outputs/TC12_CarterPollard_Eq7_BulkUpper_brief.md` | 500-700 (TC11 overrun-adjusted) | +0 (3 NEW Full theorems) | 18 → 18 (track-c side) |
| **TD-drop housekeeping** | track-d → mainline | `outputs/TD_drop_housekeeping_brief.md` | trivial | -1 axiom (orphan removal) | depends on R63 timing |
| **TC13** Carter-Pollard §4 bulk lower + tail discard + §5 Theorem 2 | track-c | not yet drafted ; depends on TC12 | ~300-400 | +0 (Full closures) | track-c |
| **TC14** envelope + retire `tusnady_base_polynomial` | track-c | not yet drafted ; depends on TC13 | ~200-400 | -1 sorry | -1 mainline |

**Best-case cumulative through TC14 land** : -3 mainline items (R63 + TD-drop + TC14). Mainline 18 → 15. Axiom inventory 10 → 8.

---

## Pre-dispatch audits required (apply Rule 2 BEFORE drafting brief)

| Round candidate | Surface | Audit needed | Predicted GAP risk |
|---|---|---|---|
| **TC15** `hungarian_dyadic_step` body | track-c | YES — does the body need brownian-motion package primitives that are 0% at pin ? | MEDIUM-HIGH (BM-marginal coupling primitive likely absent) |
| **TC16** `sup_error_log_over_sqrt` body | track-c | YES — chain-level Borel-Cantelli ; verify BC-1/BC-2 at pin | LOW |
| **TC17+** `oneDimKMT` main body + retire `one_dim_KMT_coupling` | track-c | YES — Skorokhod-style construction primitive ? | HIGH (the irreducible classical-oracle status of A2 stems from this gap) |

**Disposition under Rule 2** : if TC15 / TC17+ surface GAP annotations during pre-dispatch audit, flag the round as "contributing infrastructure" rather than retirement. A2 (`one_dim_KMT_coupling`) is one of the irreducible 5 axioms in the ship target — TC15-TC17+ do NOT need to retire it for the ship to land.

---

## What CANNOT be retired in the project timeline

Per Probe 5 + R62 audit-redirect + Local Claude's grounded read of the Q1a/b/c track :

1. **A4 + A5 (`gao_li_wellner_small_ball_lower / _upper`)** — bridge to continuous-process small-ball asymptotic requires α/β/γ/δ/ε infrastructure (Anderson + KL + Talagrand + BTIS + IsGLWProcess covariance extraction) OR {multivariate Esseen + multivariate CF integration}. **Both paths are multi-year Mathlib gaps.** The Q1a/b/c track in-tree (5909+ LOC) delegates the gap via `_compat` hypotheses to non-existent producers — confirmed by Local Claude's grounded file read at `Helpers/MultivariateSmallBallUpper.lean` lines 194 (`fourier_smoothing_reduction_quantitative`), 449 (`inblock_cf_integral_bound_quantitative`), 765 (final assembly). Both axioms stay in the ship.

2. **A1 (`Cp_T_explicit_pointwise_axiom`)** — full informal proof is the entire Carter-Pollard 2004 paper (~10 pages). Lean formalisation feasible in principle but represents ~600-1500 LOC of heavy analytical infrastructure. Stays in the ship.

3. **A2 (`one_dim_KMT_coupling`)** — full Tusnády chain (Beta integral + Stirling + Mills + Theorem 1 + Theorem 2 + (5) + dyadic chaining + Borel-Cantelli) + KMT existential coupling. TC11-TC17+ contributing infrastructure but unlikely to retire in the project timeline. Stays in the ship.

4. **A3 (`kmt_aided_gaussian_process`)** — depends on A2. Stays in the ship until A2 retires.

---

## Trajectory math (post-Probe-5 grounded)

| Round | Best-case net | Realistic net |
|---|---|---|
| R62 | 0 (audit-redirect) | 0 |
| R63 | -1 axiom (`glw_det_lower_bound`) | -1 |
| TD-drop | -1 axiom (`lipschitz_sup_finite_gaussian` orphan) | -1 |
| TC12 | +0 (track-c-internal Full +3) | +0 |
| TC13 | +0 (track-c-internal Full +N) | +0 |
| TC14 | -1 sorry (`tusnady_base_polynomial` body retired) | -1 (if TC15+ wires consumer) |
| TC15+ | 0 to -1 (depends on bridge-gap audit verdict) | 0 (likely contributing infra only) |
| **Cumulative best** | **-4 over ~10 rounds** | **-3 over ~10 rounds** |

**Mainline at cumulative best : 18 → 14** (8 axioms + 6 sorries).
**Mainline at cumulative realistic : 18 → 15** (8 axioms + 7 sorries).

Ship-readiness = sorry-free + minimum-axiom commit. **Sorry-free target : ~12-15 more rounds beyond R63 to clear the remaining 6-7 sorries (some via TC chain, some via direct proofs).** Axiom-minimum target : 5-6 axioms (A1 + A2 + A3 + A4 + A5 minimum, possibly + `glw_det_lower_bound` if R63 stalls).

---

## Cross-track dispatch matrix (FS-independence)

R63 (mainline) and TC12 (track-c) and TD-drop (track-d) can run in parallel — different worktrees, different branches, no `lake update`, no pin bump, no shared mutable state. Per `feedback_v2_cluster_filesystem_discipline.md`, the only forbidden parallel pattern is concurrent pin-bump probes ; none of the immediate queue requires pin bump.

---

## How to add a new round to the queue

1. Apply Rule 2 (bridge-gap audit) before drafting the brief.
2. Draft brief in `outputs/R<N>_<topic>_brief.md` or `outputs/TC<N>_<topic>_brief.md`.
3. Add row to "Immediate dispatch queue" table above.
4. If the new round depends on another, document the dependency in the row.
5. Push the brief + ROADMAP.md update to the repo (or share via Zulip / shared doc per your team workflow).

End roadmap.
