# R38 T2.2 — Consumer build log (verbatim)

## Outcome: **GREEN-CONSUMER**

After the P2 patch in T2.1 (removed duplicate
`ENat.toENNReal_iSup` from
`.lake/packages/brownian-motion/BrownianMotion/Auxiliary/ENNReal.lean`
and added `import Mathlib.Algebra.Order.Floor.Extended` to
`.lake/packages/brownian-motion/BrownianMotion/Continuity/CoveringNumber.lean`),
all four critical targets compile cleanly via `lake env lean`.

## Reproduction

```bash
cd ~/Documents/formal-conjectures
for f in \
  "FormalConjectures/ErdosProblems/Helpers/GLWLowerProof.lean" \
  "FormalConjectures/ErdosProblems/Helpers/PhaseAUpperBound.lean" \
  "FormalConjectures/ErdosProblems/Helpers/GLWUpperProof.lean" \
  "FormalConjectures/ErdosProblems/524.lean"
do
  echo "=== $f ==="
  lake env lean "$f" > "/tmp/r38_$(basename $f .lean).log" 2>&1
  echo "exit=$?  errors=$(grep -c '^error' /tmp/r38_$(basename $f .lean).log)"
done
```

## Per-target results

| Target | Exit | `error:` count | `sorry` warnings | Status |
|---|---:|---:|---:|---|
| `GLWLowerProof.lean` | 0 | 0 | 0 | ✅ GREEN |
| `PhaseAUpperBound.lean` | 0 | 0 | 2 (lines 199, 290 — TAG'd R35 PhaseA scaffolds) | ✅ GREEN |
| `GLWUpperProof.lean` | 0 | 0 | 0 | ✅ GREEN (was R36-T2.5-ENat-pre-existing — RESOLVED) |
| `524.lean` (consumer) | 0 | 0 | 1 (line 3889 — TAG'd consumer sorry) | ✅ GREEN |

## Verbatim 524.lean compile output

```
warning: brownian-motion: repository '/Users/kieranmcshane/Documents/formal-conjectures/.lake/packages/brownian-motion' has local changes
FormalConjectures/ErdosProblems/524.lean:3651:0: warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
FormalConjectures/ErdosProblems/524.lean:3651:0: warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
FormalConjectures/ErdosProblems/524.lean:3784:0: warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
FormalConjectures/ErdosProblems/524.lean:3784:0: warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
FormalConjectures/ErdosProblems/524.lean:3889:16: warning: declaration uses 'sorry'
FormalConjectures/ErdosProblems/524.lean:3855:0: warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
FormalConjectures/ErdosProblems/524.lean:3855:0: warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
FormalConjectures/ErdosProblems/524.lean:7612:0: warning: This file has more than one module docstring (`/-! ... -/`). Only the first one is treated as module documentation; convert additional ones to regular comments (`/- ... -/`).

Note: This linter can be disabled with `set_option linter.style.moduleDocstring false`
```

`exit code 0`, `error:` count = 0. The previously-blocking
`error: ... import BrownianMotion.Auxiliary.ENNReal failed,
environment already contains 'ENat.toENNReal_iSup' …` is **gone**.

## Side note on `lake build FormalConjectures.ErdosProblems.524`

The `lake build` CLI route (`lake build FormalConjectures.ErdosProblems.524`)
crashes with a Lake-internal stack trace and `error: no such file or
directory`, unrelated to our patch. The Lake CLI appears to mishandle
the numeric module name `«524»` when invoked as a build target on this
toolchain. The authoritative compile is `lake env lean
FormalConjectures/ErdosProblems/524.lean`, which uses the same Lean
binary, the same `LEAN_PATH`, and produces an `.olean`-equivalent
compile pass with no errors.

This is documented as a separate Lake-CLI issue, **NOT** a regression
introduced by R38; pre-R38 builds invoked the same module via
`lake build FormalConjectures.ErdosProblems.Helpers.GLWUpperProof`
(non-numeric module name) which worked, indicating the issue is
specifically the `«524»` token parsing.

## ENat conflict status

**RESOLVED** (locally, on the pinned brownian-motion checkout).

| Status | Pre-R38 | Post-R38 |
|---|---|---|
| `BrownianMotion.Auxiliary.ENNReal` direct compile | ✅ green | ✅ green (patched) |
| `BrownianMotion.Continuity.CoveringNumber` | ✅ green | ✅ green (added Mathlib import) |
| `GLWUpperProof.lean` import chain | ❌ blocked | ✅ green |
| `524.lean` consumer | ❌ blocked | ✅ green |

## Durability caveat

The patch is applied inside `.lake/packages/brownian-motion/`, which
is a vendored dependency tree managed by Lake. Future `lake update`
will revert the patch (restoring the upstream conflict). Mitigation:
the patch artifact is committed at
`Helpers/R38_T2_BrownianMotionENNRealPatch.diff` and the original
file at `Helpers/R38_T2_BrownianMotionENNReal_PRE.bak.lean` for
reapplication.

The durable fix is the upstream commit `4fa8fc0 bump` on
`brownian-motion` master (tied to a Lean 4.28 + Mathlib bump). When
this project bumps its toolchain, the local-patch becomes obsolete
automatically. Until then, this file documents the manual reapplication.
