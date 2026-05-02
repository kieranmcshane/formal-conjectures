# R59 — T1 audit (mainline, `r46-track-a-mge-posdef`)

Audit grounding for the GLW infrastructure round R59. This file
records the empirical Mathlib API surface available at the project
pins, the paper recheck of the GLW 2010 §4 grid + `det(A)` formula,
and the existing placeholder locations in
`Helpers/GLWSmallBallShortcut.lean` that R59 augments (NOT retires).

Pins assumed: `mathlib4 @ 25ce63313608`,
`brownian-motion @ 91267abd71bd` (carried through R58).

R59 is **infrastructure, not closure**. Per the active discipline
rule that infra rounds are milestones and not closures (Erdős 524
framing, see `feedback_erdos524_framing`), no Stub retirements are
claimed; +2 sorries land as paper-faithful refinements TAG'd for
R60–R61 bodies.

---

## T1.1 — grep audit (run on `.lake/packages/mathlib`)

| Identifier | Status | Pin location |
|---|---|---|
| `Matrix.permanent` | ✅ present | `Mathlib/LinearAlgebra/Matrix/Permanent.lean:32` |
| `Matrix.permanent_one` | ✅ present | `Mathlib/LinearAlgebra/Matrix/Permanent.lean:45` |
| `Matrix.permanent_diagonal` | ✅ present | `Mathlib/LinearAlgebra/Matrix/Permanent.lean:35` |
| `Matrix.permanent_transpose` | ✅ present | `Mathlib/LinearAlgebra/Matrix/Permanent.lean:73` |
| `Matrix.permanent_smul` | ✅ present | `Mathlib/LinearAlgebra/Matrix/Permanent.lean:90` |
| `Matrix.det_apply` | ✅ present | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:63` |
| `Matrix.det_apply'` (with `ε σ`) | ✅ present | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:67` |
| `Mathlib/.../Matrix/Block.lean` (file) | ✅ present | `Mathlib/LinearAlgebra/Matrix/Block.lean` |
| `Finset.sup'` | ✅ present | `Mathlib/Data/Finset/Lattice/Fold.lean:700` |
| `Finset.univ_nonempty` | ✅ present | `Mathlib/Data/Finset/BooleanAlgebra.lean:52` |
| `cauchyMatrix` / `det_cauchy` / `cauchy_det` | ❌ **0 hits** in `.lake/packages/mathlib` | — |

### Verdict on Cauchy

The post-TC9 Grok strategy probe estimated a "5% chance" that the
Cauchy determinant identity might already be a Mathlib helper. The
empirical grep result is **0% — no `cauchyMatrix`, `det_cauchy`,
or `cauchy_det` hits anywhere under `.lake/packages/mathlib`**. R59
records this finding and stages the consequence for R61: either

- (a) derive the Cauchy identity from scratch (≈30–60 LOC,
  multilinearity of `det` + Vandermonde-like manipulation), or
- (b) axiomatize the identity (treat as 1 axiom = +1 tech debt
  item under the Erdős 524 framing).

R59 itself does NOT consume Cauchy; it lands signatures only.

### Verdict on `Finset.sup'`

Available and exactly fits Grok's broken `Matrix.row A k |>.max'`
intent. R59 introduces a small `Matrix.rowSup` def wrapping
`Finset.univ.sup' Finset.univ_nonempty (A k)` so downstream
proofs (R60+) can rewrite without re-deriving the wrapper.
`Nonempty ι` is required as a typeclass on the row index — folded
into the lemma signatures.

### Verdict on `Matrix.permanent`

`Matrix.permanent` is the Mathlib name and lives in a file already
imported by `GLWSmallBallShortcut.lean` (line 17:
`import Mathlib.LinearAlgebra.Matrix.Permanent`). The R59 sigs
reference `Matrix.permanent` directly.

---

## T1.2 — paper recheck (GLW 2010 §4)

Source: arXiv:1001.0200v1 (Gao–Li–Wellner 2010, "A
finite-dimensional version of Talagrand's small-ball
inequality"), §4.

R59 brief states (carried from a Cowork bonus probe done at brief
composition time):

- Grid dimension: `m * m` flat-encoded over `Fin (m * m)`,
  decomposed as `(p, q)` with `p ∈ {0, …, m−1}` and
  `q ∈ {1, …, m}` via `p = i.val / m`, `q = (i.val % m) + 1`.
- Grid values: `δ_{m·p + q} = 4·m / (m + q)`.
- Lemma 4.2 conclusion: `permanent(A) = 1` and
  `det(A) = 32^m · (240·exp(−3))^m`. The `32^m` form corrects the
  `32·m` form inadvertently encoded in the R50 deferred-paper
  sub-Stub (`Helpers/GLWSmallBallShortcut.lean:259`), which the
  R50 docstring already self-flagged as ambiguous without paper
  access.
- Matrix `A` entries: diagonal entry `A i i = δ_i · δ_i`;
  off-diagonal entry `A i j = exp(−δ_i · δ_j)` for `i ≠ j`.
- Lemma 4.1 (perturbation/comparison): for square matrices
  `A, B` with `B ≤ A` entrywise and `0 ≤ B` entrywise,
  `det(B) ≥ det(A) − (∑ k, (∑ l, B k l) · rowSup(A, k)) · perm(A)`.

### Uncertainty flag

Per the R59 brief, the paper recheck was performed by Cowork
during brief composition, NOT independently re-verified at
dispatch time. WebFetch / external paper retrieval is out of
scope for this round (T1.2 was scoped as "confirm the brief's
form" rather than "re-derive from arXiv"). If R60–R61 surface a
mismatch with the paper while filling bodies, the calibration
should be revisited and the formulas in `glwMatrixA` /
`glw_lemma_4_2_paper_specs` updated (this is signature-only work,
no consumer file consumes them at R59 close).

This uncertainty flag is the analogue of the R50 ambiguity note
("`32 · m` vs `32^m`") with the resolution recorded but not
independently re-derived at R59 dispatch.

---

## T1.3 — placeholder location confirmation

Existing R50 deferred-paper sub-Stubs in
`Helpers/GLWSmallBallShortcut.lean`:

| Sub-Stub | Line | Form |
|---|---|---|
| `glw_lemma_4_1_deferred_paper` | 226 | Generic Jacobi-style: `∃ c, HasDerivAt (fun ε => (K + ε • E).det) c 0` |
| `glw_lemma_4_2_deferred_paper` | 256 | `∃ A : Matrix (Fin (m*m)) (Fin (m*m)) ℝ, A.permanent = 1 ∧ A.det = 32 · m · (240 · exp(−3))^m` |

Per the R50 docstring (lines 167–203 of the file):
*"R51+ should refine signatures and either close Full or replace
with the concrete in-tree consumer construction."*

R59 takes the **augment, not retire** path: the two R50 sub-Stubs
remain as the conservative-shape historical deferral records, and
R59 adds the paper-faithful refinements
(`glw_lemma_4_2_paper_specs`, `glw_lemma_4_1_perturbation`)
alongside `glwMatrixA`, `Matrix.rowSup`, and `hierarchicalGrid`.
Net sorries: +2 (paper-spec sigs are sorried). Net axioms: 0.
Net Stub retirements: 0 (R50 sub-Stubs are NOT retired this
round — that is staged for a future R6x round once the paper-spec
bodies close in R60–R61).

Upstream consumers (`gao_li_wellner_small_ball_lower` /
`_upper` at `524.lean:3643` / `:3574`) are NOT touched at R59
close. The R50 chain-mismatch finding (Mismatch ledger #16) is
unchanged: closing `glw_lemma_4_2_paper_specs` does NOT directly
retire A4 or A5, only the determinant-shortcut math layer. The
Anderson + discretization + tail bridges remain staged for R62+.

---

## R59 calibration (carried for T2/T3 implementation)

- T2 (`hierarchicalGrid` + 2 test lemmas): 25–40 LOC.
- T3 (`glwMatrixA` + `Matrix.rowSup` + 2 sorried theorems):
  50–80 LOC.
- Total budget: 80–120 LOC, all in
  `Helpers/GLWSmallBallShortcut.lean`.
- New imports likely needed: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
  (transitively via current imports — confirm at build),
  `Mathlib.Data.Finset.Lattice.Fold` (for `Finset.sup'`).
- Build verification: `lake build
  FormalConjectures.ErdosProblems.Helpers.GLWSmallBallShortcut`
  must be green at <90s on warm cache.

---

End audit.
