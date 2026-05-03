# Probe / brief discipline — bridge-gap audit before LOC estimation

## Rule (binding)

Before estimating LOC for any axiom-retirement round, write the end-to-end proof sketch from existing in-tree primitives (or imminent-PR Mathlib lemmas) to the axiom's verbatim signature, naming each step. If any step requires multi-paragraph upstream-Mathlib infrastructure (Anderson's multivariate inequality, Karhunen-Loève spectral expansion, Talagrand entropy bounds, Slepian / Sudakov-Fernique comparison, Borel-TIS for Gaussian processes, multivariate Esseen smoothing, Plancherel-on-boxes, multivariate CF integration, KMT coupling at Brownian scale, dyadic-block embeddings, etc.), the round is **contributing infrastructure, not retirement** — flag the bridge-gap blocker and decline to estimate LOC, regardless of how many ingredient theorems just landed.

**Companion ask, in one sentence (Grok formulation)** : *Does the exact downstream consumer statement (here A4/A5) require the full continuous-index process with sup-over-`[0, ∞)`, or only a finite-grid version? Verify the hypothesis match in the axiom docstring verbatim.*

## Operational form for Grok pre-flight probes

Replace the prompt phrasing **"Is the ingredient-theorem now available?"** with :

> *"Write out steps 1…N from in-tree state to the axiom's verbatim signature. Name the Mathlib lemma each step invokes. Flag any step where the named lemma does not exist at the project pin or is multi-paragraph upstream work. Do not estimate LOC unless every step has a named, present (or imminent-PR) Mathlib lemma."*

If a probe response cannot list step-by-step Mathlib invocations all the way to the verbatim axiom shape, **the probe has not actually estimated LOC — it has estimated ingredient-availability and conflated the two.**

## Operational form for Cowork brief T1.0

Brief T1.0 must include an **end-to-end bridge sketch** subsection BEFORE T1.1 Mathlib API audit, when the brief proposes axiom retirement. The sketch enumerates :

1. Verbatim axiom signature (paste from `524.lean` line range).
2. Numbered proof steps from the in-tree primitives the brief expects to consume.
3. For each step, the Mathlib lemma name + line/file at pin OR the in-tree theorem name + line/file at HEAD.
4. Explicit "GAP" annotations on any step where the named lemma does not exist or is multi-paragraph upstream work.

If the sketch contains any GAP annotation, the brief's T2.x LOC estimate is invalid until the gap is reframed (axiomatize the gap, defer the round, switch to contributing-infrastructure framing, or abandon the path).

## Pattern : the "delegation via compat hypothesis" failure mode

A close cousin of the bridge-gap blunder : when an in-tree file appears to be advancing toward a closure but the deep math has been **architecturally relocated into `_compat` / `compat` hypotheses**, the body proofs discharge trivially (`exact compat ε hε`) while the producer of the compat witness does not exist in-tree. Reading the lemma body alone is insufficient ; one must also grep for the compat-witness producer and verify it exists or is in-flight. If the producer is "out of scope" or "user supplies" or absent entirely, the file is **delegating the gap, not closing it.**

Grep recipe :

```bash
grep -rn "_compat\b\|\.compat\b" --include="*.lean" \
  Helpers/<TargetFile>.lean
# If matches found, identify each compat hypothesis, then grep for its producer:
grep -rn "<compat_name> :" --include="*.lean" \
  --exclude-dir=.lake FormalConjectures/
# If zero hits outside the consumer file's hypothesis declaration, the gap is delegated.
```

## Precedents (the rule generalises from these)

- **R50 mismatch ledger entry #16** : Cowork drafted GLW-shortcut → A4/A5 retirement at 110-150 LOC. Track A T1.1 audit found the bridge α/β/γ/δ/ε is 0% in Mathlib + 0% in-tree. Round shipped audit-redirect.
- **R62 mismatch ledger entry #17** : Cowork re-drafted same shortcut at 60-130 LOC after R59-R61 landed deterministic Lemma sigs Full. Track A T1.0+T1.1 audit reconfirmed the same chain mismatch (R59-R61 deliver ingredients, not bridge). Round shipped audit-redirect.
- **Probe 5 (post-R62) Local-vs-Grok divergence** : Grok estimated 700-1300 LOC for Q1a/b/c track A5 retirement based on three TAG'd sorries' surface content. Local Claude grounded read found the sorries are delegated via `_compat` hypotheses to non-existent producers ; the Q1a/b/c track has the same Mathlib gap re-localised to {multivariate Esseen + multivariate CF integration}. Local Claude wins on grounding.

## Application to TC11 → TC14 chain (current dispatch)

The Carter-Pollard chain (TC11 → TC12 → TC13 → TC14) closes `tusnady_base_polynomial`. Apply the rule before TC12 dispatch :

- **`tusnady_base_polynomial` verbatim signature** (paste from current branch HEAD) : per-step polynomial bound `|B - n - Z| ≤ A + C·Z²/n` for `Bin(2n, 1/2)` paired with `N(0, n/2)`. **Per-step, finite-n.** NOT continuous-process. NOT a sup-over-`[0, ∞)` asymptotic.
- **End-to-end sketch** (TC11 → TC14) :
  1. TC9 `binomial_tail_beta_integral` (Full) — Mathlib `intervalIntegral` ✓.
  2. TC10 `stirling_prefactor_bound` (Full) — Mathlib `Nat.descFactorial_le_pow` ✓.
  3. TC11 `carterPollardH_taylor_upper_bound` (Full) — Mathlib `taylor_mean_remainder_lagrange` ✓.
  4. TC12 §2 eq (7) reformulation : Mathlib `intervalIntegral.integral_comp_div` (audit at TC12 T1.1) + TC8 Stirling Robbins ✓.
  5. TC12 §4 bulk upper bound : pointwise Taylor + Gaussian compl_cdf evaluation ✓.
  6. TC13 §4 bulk lower + tail discard : Mills reciprocal-bridge `m(x) = 1/ρ(x)` adapter (TC6/7/8 helpers Full ; reciprocal trivial).
  7. TC13 §5 Theorem 2 two-case : analytic bookkeeping, finite-n.
  8. TC14 envelope + cutpoint approximation : finite-n composition of TC9-TC13.
  9. TC14 `tusnady_base_polynomial` close : direct apply.

**No GAP annotations.** Every step routes through finite-n primitives ; no continuous-process bridge required. The chain is in scope. **TC12 dispatch is safe under the rule.**

## Application to TC15 → TC17+ cascade (NEXT — audit before dispatch)

After TC14 closes `tusnady_base_polynomial`, the cascade is :

- **TC15 `hungarian_dyadic_step` body** : sig tightened TC5 with sub-Gaussian + BM-law marginals. **Audit before dispatch** — does the body require Brownian-motion-marginal construction primitives that are 0% in Mathlib at pin ? Possibly yes (the BM-law constraint may force going through the brownian-motion package's not-yet-merged primitives). **GAP risk : flag.**
- **TC16 `sup_error_log_over_sqrt` body** : chain-level Borel-Cantelli applied to the dyadic chain. Mathlib has BC-1 ; verify BC-2 if needed.
- **TC17 `oneDimKMT` main body** : existential coupling assembly. **GAP risk : if coupling-existence requires Skorohod-style construction, audit Mathlib pin for `MeasureTheory.MeasurePreserving.skorohod_*` analog.**

**Dispatch TC15+ briefs only after the bridge-gap audit per this rule.**

## Promotion + index entry

Add to `~/.claude/projects/-Users-kieranmcshane/memory/MEMORY.md` index :

```markdown
- [feedback_probe_bridge_gap_audit](feedback_probe_bridge_gap_audit.md) — Discipline rule : before LOC estimation for axiom-retirement rounds, write end-to-end proof sketch naming each Mathlib lemma ; if any step is multi-paragraph upstream work, flag bridge-gap blocker and decline to estimate. Catches the R50 / R62 chain-mismatch family.
```
