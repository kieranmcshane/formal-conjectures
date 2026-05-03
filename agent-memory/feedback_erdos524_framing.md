---
name: feedback_erdos524_framing
description: For the Lean Erdős 524 project, treat user-defined axioms as technical debt and frame infrastructure rounds (build green, ENat resolution, etc.) as MILESTONES, not closures
type: feedback
originSessionId: b73ef32b-4f50-438a-9eac-5501ce6e2871
---
In the formal-conjectures Erdős 524 project, **build-infrastructure
landings are milestones, not closures**. Even when a round brief
uses words like "Scope 3 closure" or "GREEN-CONSUMER tier", do
**not** declare or imply that Phase A or the project itself is
closed/done/ship-ready when the residual user-defined axiom
inventory is non-zero.

The 8 user-defined axioms currently on the mainline 524 chain
(D2 + 1D KMT + stepping-stone + GLW lower + GLW upper + 3
IsGLWProcess β) are **technical debt** to be retired, not
foundations. R29–R38 was build-infrastructure work; the
mathematical mission (axiom-retirement) is a separate program
that re-enters at R39+.

**Why:** the user explicitly corrected my R38 commit message and
tag (renamed `r38-scope3-green-consumer` → `r38-consumer-build-green`,
reframed commit body) to make this clear. Conflating "build green"
with "project closure" misrepresents the mathematical state and
inflates the perceived completion fraction.

**How to apply:**
- User priority #1 across all rounds is a **sorry-free AND
  axiom-free** Lean formalization of Erdős Problem 524. Treat any
  state with user-defined axioms as still-open with respect to
  this priority.
- When writing commit messages, status docs, ship checklists, or
  closure declarations: prefer "milestone", "build infrastructure
  landed", or "consumer-build-green" framing over "closure",
  "ship-ready", "Phase A closes here", or "tier achieved".
- When tagging: prefer descriptive build-state names
  (`r38-consumer-build-green`) over tier-language names
  (`r38-scope3-green-consumer`).
- When listing axioms in inventories: label them "technical debt
  / retire targets", not "foundations" or "upstream-pending"
  alone.
- When citing visible round counts (e.g., "R29-R38 = 10 rounds"),
  scope the statement to "build-infrastructure work" — do not
  imply the project budget is exhausted; the math-content
  axiom-retirement program is a separate, yet-to-be-bounded
  budget.
- Round briefs may continue to use closure-tier language as a
  scoring framework. That is fine internally; do **not** export
  closure-tier language to user-facing artifacts (commit
  messages, tags, README sections, ship docs) without
  reframing.
