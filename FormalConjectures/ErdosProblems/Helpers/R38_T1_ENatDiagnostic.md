# R38 T1.1 — ENat conflict diagnostic + resolution path

## Verbatim error (from `lake build FormalConjectures.ErdosProblems.Helpers.GLWUpperProof`)

```
✖ [7916/7916] Building FormalConjectures.ErdosProblems.Helpers.GLWUpperProof (13s)
error: FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean:14:0:
  import BrownianMotion.Auxiliary.ENNReal failed,
  environment already contains 'ENat.toENNReal_iSup' from
  Mathlib.Algebra.Order.Floor.Extended
error: Lean exited with code 1
```

## Root cause: not an ENat coercion / instance issue — a duplicate-declaration import collision

Two distinct sources define the **same fully-qualified name** `ENat.toENNReal_iSup`:

1. `.lake/packages/brownian-motion/BrownianMotion/Auxiliary/ENNReal.lean:40`
   (in pinned rev `91267abd71bd32e9ef6c10c9359938f24a3e1f38`):

   ```lean
   @[norm_cast]
   lemma ENat.toENNReal_iSup {ι : Sort*} (f : ι → ℕ∞) :
       ⨆ i, f i = ⨆ i, (f i : ℝ≥0∞) := by
     refine eq_of_forall_ge_iff fun c ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
     · exact iSup_le fun i ↦ le_trans (ENat.toENNReal_le.2 (le_iSup f i)) h
     ...
   ```

2. `.lake/packages/mathlib/Mathlib/Algebra/Order/Floor/Extended.lean:211`
   (in pinned rev `25ce633136084367f182be00fdff7613ea949d27`):

   ```lean
   @[simp] lemma toENNReal_iSup {ι : Sort*} (f : ι → ℕ∞) :
       toENNReal (⨆ i, f i) = ⨆ i, toENNReal (f i) :=
     eq_of_forall_ge_iff fun _ ↦ by simp [← le_floor]
   ```

   (declared inside `namespace ENat`, so fully qualified
   `ENat.toENNReal_iSup`.)

When Lean compiles `GLWUpperProof.lean`, it loads `Mathlib.Algebra.Order.Floor.Extended`
through the standard Mathlib chain (e.g. transitively via
`Mathlib.Probability.Distributions.Gaussian.Basic`), which seeds the
environment with `ENat.toENNReal_iSup`. Then the transitive import of
`BrownianMotion.Auxiliary.ENNReal` (via `GLWGaussianProjectiveLimit.lean`)
attempts to add the same name → conflict → import fails.

## Import chain (consumer-side)

```
524.lean (or GLWUpperProof.lean)
  → Helpers/GLWProcess.lean
    → Helpers/GLWGaussianProjectiveLimit.lean
      → BrownianMotion.Gaussian.…
        → … → BrownianMotion/Auxiliary/ENNReal.lean   (duplicate!)
  → Mathlib.Probability.Distributions.Gaussian.Basic
    → … → Mathlib/Algebra/Order/Floor/Extended.lean   (also defines it)
```

Reproducible: every R29–R37 build log captures the same error
verbatim (`R30BuildStatus.md`, `R34_T2_5_BuildLog.md`,
`R36_T2_BuildLog.md`, `R37_T2_BuildLog.md`).

## Versions in play

- Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
- Mathlib pin: `25ce633136084367f182be00fdff7613ea949d27`
- brownian-motion pin: `91267abd71bd32e9ef6c10c9359938f24a3e1f38`
- kolmogorov_extension4 pin: `2c2b44e5525186fbe23b01e6acc76460db616009`

## Upstream brownian-motion state

`origin/master` HEAD currently is `f139db2 switch to the module system`.
Inspecting the file history of `BrownianMotion/Auxiliary/ENNReal.lean`:

```
f139db2 switch to the module system
4fa8fc0 bump                      ← removes ENat.toENNReal_iSup (file 81→42 lines)
c8d6986 feat: …                   ← still has the lemma
…                                 ← ditto
91267ab bump                      ← OUR PIN (still has the lemma)
```

Confirmation that `4fa8fc0` (`Wed Mar 4 12:05:45 2026 +0100`) is the upstream
commit that retired the duplicate. Diff stats from `git show 4fa8fc0`:

```
 BrownianMotion/Auxiliary/ENNReal.lean | 23 +----------------------
 lake-manifest.json                    | 28 ++++++++++++++--------------
 lakefile.toml                         |  1 +
 lean-toolchain                        |  2 +-
```

`4fa8fc0`'s `lean-toolchain` pins `leanprover/lean4:v4.28.0`, and its
manifest pins Mathlib `55c8532eb21ec9f6d565d51d96b8ca50bd1fbef3`.

## Resolution path candidates

### P1 — upstream-bump (rejected)

Bump `brownian-motion` to `4fa8fc0` in our `lakefile.toml`. Required side
effects:

- Bump `lean-toolchain` from `v4.27.0-rc1` to `v4.28.0`.
- Bump Mathlib from `25ce6331…` to `55c8532e…` (or compatible).
- Bump `kolmogorov_extension4` accordingly.

Cascading risk: every R29–R37 file (8 user-defined axioms, 6 TAG'd
sorries, 5400+ LOC of helpers, 524.lean consumer) was authored against
the v4.27 / Mathlib `25ce6331` API surface. A toolchain + Mathlib bump
would force re-verification of every proof. The 3 R33-C/D Mathlib gaps
TAG'd in R37 may also shift name. Far outside R38's mandate of "land
consumer green WITHOUT regressing helpers".

**Verdict: P1 rejected** — out of budget, high regression risk on
already-locked R37 content.

### P2 — local-patch on the pinned brownian-motion

Mirror `4fa8fc0`'s deletion at our pinned rev. Surgical edit at
`.lake/packages/brownian-motion/BrownianMotion/Auxiliary/ENNReal.lean:40`:
remove the duplicate `ENat.toENNReal_iSup` lemma (and its proof body,
lines 39–59). The Mathlib-provided version satisfies the only consumer
in brownian-motion (`Continuity/CoveringNumber.lean:662`), since the
two lemmas have **identical statements** modulo coercion notation.

Verification of intra-bm consumers of the lemma:

```
$ grep -rn "ENat.toENNReal_iSup" .lake/packages/brownian-motion/BrownianMotion/
.lake/packages/.../BrownianMotion/Continuity/CoveringNumber.lean:662:
    simp_rw [← ENNReal.iSup_mul, ← ENat.toENNReal_coe, ← ENat.toENNReal_iSup, h]
.lake/packages/.../BrownianMotion/Auxiliary/ENNReal.lean:40: lemma ENat.toENNReal_iSup …
```

Single intra-bm caller. Mathlib's lemma resolves the same name (and
the Mathlib version is `@[simp]`, the bm version was `@[norm_cast]` —
attribute difference noted; CoveringNumber's `simp_rw` call uses the
identifier explicitly so attribute set does not matter for that
callsite).

Risk: `.lake/packages/` is a vendored dependency tree and the patch is
**not durable across `lake update`** — any future `lake update` (or
fresh clone) restores the upstream conflict. We mitigate by also
committing a copy of the patch under
`Helpers/R38_T2_BrownianMotionENNRealPatch.diff` so future
contributors can reapply.

**Verdict: P2 selected.** Surgical, mirrors upstream's own fix,
self-contained, reversible. Caveats documented.

### P3 — code-rewrite (rejected)

Restructure our project imports to avoid pulling in
`BrownianMotion.Auxiliary.ENNReal` transitively. Requires splitting or
re-implementing the parts of `BrownianMotion.Gaussian.…` we use, since
its standard import chain leads to `Auxiliary.ENNReal`. `GLWGaussianProjectiveLimit.lean`
(126 KB) is the deepest brownian-motion consumer; rewriting away its
brownian-motion dependency is a major engineering project, not a
single-round fix.

**Verdict: P3 rejected** — out of budget.

### P4 — defer (fallback)

Document the unresolved conflict, ship at R37's DECLARED tier with
ENat as a fourth Mathlib version-skew item. Always available; selected
only if P2 introduces cascading errors we cannot reasonably contain.

**Verdict: P4 reserved as fallback.**

## Selected path: P2

Execute P2 in T2.1: edit `.lake/packages/brownian-motion/BrownianMotion/Auxiliary/ENNReal.lean`
to remove lines 39–59 (the conflicting lemma + its proof), rebuild
brownian-motion, then run `lake build FormalConjectures.ErdosProblems.524`
and capture verbatim output in T2.2.

If brownian-motion fails to rebuild after the patch, or if downstream
consumers (CoveringNumber, etc.) cascade-fail, document the failure
mode concretely, revert the patch, fall back to P4 with the verbatim
post-fallback build log.
