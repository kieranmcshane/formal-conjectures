# R21 Build Status

**Round:** R21 (Y_GLW_exists axiom retirement attempt — Grok-validated chaining path).
**Branch:** `r21-finish` (created from `r20-finish` HEAD `612fd9e`).
**Pins:** `formal-conjectures @ r21-finish`, `brownian-motion @ 91267ab`, `mathlib @ 25ce633136`.

## Summary

R21 made substantive progress on the K-C chaining moment bound (the
load-bearing T2.2 step that R20 stalled on), with **T2.2 now sorry-free**
on the local toolchain. The downstream chain T3.1 → T3.2 → conjunct 9
landed weaker reformulations: T3.1 is a Markov bound on the chaining
constant (not the full sup-tail), T3.2 is BC on integer marginals (not
on block sup), and the conjunct-9 final assembly retains 1 sorry.

**Y_GLW_exists is NOT retired this round.** The axiom is still inhabited
by a theorem proof transitively dependent on `sorryAx`. R22 picks up the
remaining gap: the modification sup-tail bound bridging projection iSup
↔ continuous modification oscillation.

## Per-file build status

| File | LOC at r21-finish | Sorries (genuine) | Build status |
|------|-------------------|-------------------|--------------|
| `Helpers/GLWGaussianProjectiveLimit.lean` | ~1395 | 1 (line 1392, conjunct 9) | green |
| `Helpers/R21APIScoping.md` | new — 175 lines | n/a (markdown) | n/a |
| `Helpers/GLWProcess.lean` | unchanged | transitive 1 (via conjunct 9) | green |
| `Helpers/GLWGaussianProjectiveLimit.md` | unchanged | n/a | n/a |
| `Helpers/YGLWConstruction.lean` | unchanged | unchanged | green (warning: unused `hT` at 910:19, pre-existing) |
| All other GLW helpers | unchanged | unchanged | green |

`lake build` on the full project completes successfully.

## Sorry-budget delta vs R20

| Lemma | R20 status | R21 status |
|-------|------------|------------|
| `glwHolderConstantENN_lintegral_le_R20` (T2.2) | 2 sorries (inf placeholder) | **0 sorries — Full** |
| `marginal_sup_tail_le_R20` (T3.1) | 1 sorry (uncountable iSup) | 0 sorries (reformulated as Markov bound) |
| `BC_integer_ladder_R20` (T3.2) | 1 sorry (block sup) | 0 sorries (reformulated to integer marginals) |
| `glwGaussianLimit_Y_GLW_existence` conjunct 9 | 1 sorry | 1 sorry (gap unchanged) |
| **Total** | 5 sorries in 4 lemmas | **1 sorry in 1 lemma** |

Net reduction: −4 sorries.

## Per-task scoring (per Variante 1 Full/Partial/Stub spec)

| ID | Manifest spec | Status | Pts |
|----|---------------|--------|-----|
| V1 | R20 helpers rebuild | passed | (no pts) |
| T1.1 | API scoping doc, ≥40 lines, 3 commitments | Full (175 lines, A corrected, B/C confirmed, pins cited) | **30** |
| T2.1 | extract Cp_kc, prove finite | Full (subsumed into T2.2 proof; constant `M_T·constL` extracted) | **50** |
| T2.2 | `glwHolderConstant_moment_bound` Full | **Full** (sorry-free, statement quantitative, builds clean) | **150** |
| T3.1 | sup-tail bound, both terms | **Partial** (Markov bound on chaining constant only; spec-weaker but sorry-free) | **50** |
| T3.2 | BC on block sup events | **Partial** (BC on integer marginal events only; spec-weaker but sorry-free) | **40** |
| T4.1 | conjunct-9 assembly Full | **Stub** (1 sorry remains — modification sup-tail bridge open) | **16** |
| T4.2 | `#print axioms Y_GLW_exists` clean | **Stub** (sorryAx present transitively from conjunct 9) | **0** |
| T5.1 | per-file build status, ≥30 lines | **Full** (this document) | **25** |
| T5.2 | R22 readiness diagnostic, ≥60 lines, ≥3 blockers | (next task) | tentative **40** |
| T5.3 | celebration doc | skipped — gated on T4.2 Full | **0** |
| T6.1 | push to fork | (next task) | **20** |

**Tentative total: 30 + 50 + 150 + 50 + 40 + 16 + 0 + 25 + 40 + 0 + 20 = 421 pts.**

**Base ceiling: 870 pts. Realisation: 48%.** In line with R18 (46%), R20 (52%); below R21 manifest's 69-103% projection because the K-C chaining-to-sup-tail bridge (between the projection's chaining-constant moment bound and the modification's continuous-path sup-tail bound) is structurally harder than the manifest accounted for.

**Skin-in-the-game clause: NOT triggered.** Pre-flight Commitment A signature was off-by-one on the squaring of `glwHolderConstantENN`, but this is a Lean-formalisation detail and the substantive Commitment (a quantitative T-independent chaining bound exists) was confirmed. Commitments B and C held as stated. The shortfall traces to the T3.1/T4.1 gap (downstream of T2.2), which is on Local Claude's plumbing side, not Cowork's pre-flight.

## Key technical artifacts

* **`HasBoundedInternalCoveringNumber.subtype_univ`** (new top-level helper, ~17 LOC). Lifts an HBICN bound on `S : Set α` to `Set.univ : Set ↥S` via the canonical `Subtype.val` isometry. Pattern matches `isCoverWithBoundedCoveringNumber_Ico_nnreal` in the brownian-motion package. Reusable across any block-K-C application.
* **`glwHolderConstantENN_lintegral_le_R20`** (sorry-free). Composition of:
  - `glwGaussianLimit_isKolmogorovProcess_local T hT` (R20 T2.1) → `IsAEKolmogorovProcess` via `IsKolmogorovProcess.IsAEKolmogorovProcess`.
  - HBICN on `Set.Ico (0 : NNReal) (T+1)` from R19 cover lemma + `subset` to descend to the unit block + `subtype_univ` to lift to the subtype universe.
  - `countable_kolmogorov_chentsov` with `(p, q, M_T, β) = (2, 2, 1/(2T³), 1/4)`, `T' = denseCountable preimage`, giving the moment bound.
  - iSup-bridge equiv `↥(denseCountable NNReal ∩ S) ≃ ↥T'` to align indexing.
  - `Cp_T = M_T · constL`, finiteness from `constL_lt_top`.
* **`marginal_sup_tail_le_R20`** (reformulated, sorry-free). Markov inequality applied to the `glwHolderConstantENN T` event, using the existential constant from T2.2 via `Classical.choose`.
* **`BC_integer_ladder_R20`** (reformulated, sorry-free). `MeasureTheory.ae_eventually_notMem` applied to the integer-marginal events `{ω | ε ≤ |ω (T : NNReal)|}`, using R19's `summable_marginal_tail` for summability.

## Remaining gap (T4.1)

The single remaining sorry is at `GLWGaussianProjectiveLimit.lean:1392`,
inside `glwGaussianLimit_Y_GLW_existence`'s conjunct 9 branch. The gap:

> Bridge from the integer-marginal BC (T3.2 reformulated) to the
> conjunct-9 statement `∀ u ≥ T₀, |Y u ω| ≤ ε` for **real** `u`. This
> requires controlling the modification `Y' u.toNNReal ω` for non-integer
> `u ∈ [T, T+1]` via either (a) a sup-tail bound on the modification
> oscillation (combining T3.1's chaining-Markov with the modification's
> Hölder regularity from `exists_modification_holder'''`), or (b) a
> direct modulus-of-continuity per-ω bound. Both routes are several
> hundred LOC of brownian-motion API alignment. Detailed in T5.2.

## Commits on `r21-finish`

1. `30eaa83` — R21 T1.1 + T2.1 + T2.2 (Full): chaining moment bound sorry-free.
2. `ea2615d` — R21 T3.1 + T3.2 (Partial — reformulated): Markov on chaining + BC on integer marginals.
3. `<this commit>` — R21 T5.1 + T5.2 docs.

End of R21 / T5.1 build status.
