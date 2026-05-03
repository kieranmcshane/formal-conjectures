# Grok Probe 5 — recalibration after R62 audit-redirect on the GLW-shortcut bridge

**Context.**

I'm formalising Erdős problem 524 in Lean 4 + Mathlib (pin `25ce633136`, August 2024). In an earlier strategic pre-flight (Probes 2 + 3 + 4 + Bonus 3) you and I jointly estimated that the GLW (Gao-Li-Wellner 2010 §4) determinant identity + Lemma 4.1 perturbation, once landed as Lean theorems, would retire two axioms (`gao_li_wellner_small_ball_lower` = A4 and `gao_li_wellner_small_ball_upper` = A5) in approximately 60-130 LOC of consumer rewire. I drafted a Round 62 brief on this premise.

**The R62 brief premise was wrong.** Local Claude T1.0 + T1.1 audit halted Round 62 before any body work, with a structural chain-mismatch finding. The mismatch is the same family caught at R50 (also a GLW-shortcut Cowork-drafted brief audit-redirected). Verbatim summary :

> What R59-R61 actually shipped : finite-dim deterministic facts on `glwMatrixA m hm : Matrix (Fin (m·m)) (Fin (m·m)) ℝ` — `per ≤ 1` Full body, ratio-perturbation Lemma 4.1 Full body, det-side `glw_det_lower_bound` axiom. Zero consumers outside `Helpers/GLWSmallBallShortcut.lean`.
>
> What A4 / A5 actually require (`524.lean:3574` upper, `:3643` lower) : continuous-index Gaussian-process small-ball asymptotics on `Y : ℝ → Ω → ℝ` with `IsGLWProcess Y` predicate, with cubic-rate `|log ε|^3` decay. Verbatim signature shape (lower) : `∀ (glw : GaoLiWellnerConstants) {Ω} [...] (Y : ℝ → Ω → ℝ), IsGLWProcess Y → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀], exp(-glw.lower · |log ε|^3) ≤ (ℙ {ω | ∀ u ≥ 0, |Y u ω| ≤ ε}).toReal`.
>
> The bridge from R61 finite-dim Lemmas to A4/A5 needs :
> - (α) discretization of `sup_{u ∈ [0,∞)}` to a finite grid `{u_1, …, u_m}` with quantitative error control matched to the cubic rate ;
> - (β) Anderson's multivariate inequality at PosDef covariance — confirmed 0 hits on `Anderson | anderson_inequality | anderson_ball` in Mathlib at pin `25ce633136`, also 0% in-tree (only placeholder factor `glwUpperAndersonFactor c m ε := exp(-c·m·ε²)` and a V1-axiom field `anderson_lower` exist) ;
> - (γ) Ledoux §1.3 BTIS-tail handling for A4's full half-line `u ≥ 0` ;
> - (δ) optimization `m(ε) ~ |log ε|` with the Lemma 4.2 det side plug-in giving the `m³` exponent ;
> - (ε) IsGLWProcess covariance extraction at the finite grid.
>
> None of (α), (β-proper), (γ), (δ), (ε) is in Mathlib at pin or in-tree at HEAD `f4011b9`. The brief's "60-130 LOC body" hand-waves a multi-year Mathlib gap that the A4/A5 axiom docstrings themselves explicitly call out as such. **R62 ships audit-redirect only, mismatch ledger entry #17** (recurrence of #16 = R50 same finding).

**Two paths exist for honest A4/A5 retirement (per R62 audit §T1.4) :**

1. **Mathlib-Anderson canonical path.** Wait for or contribute Anderson's multivariate inequality + Karhunen-Loève spectral theory + Talagrand entropy bounds for Gaussian processes to Mathlib upstream. Multi-year horizon per A4/A5 docstring admission. The R59-R61 finite-dim Lemmas are *contributing infrastructure* to this path — not the path itself.

2. **In-tree no-Gaussian / no-KMT alternate (Q1a/b/c).** Mainline already contains 5909+ LOC across 6 helper files at HEAD `f4011b9`, working toward A5 retirement via a completely different machinery (Fourier smoothing + Berry-Esseen + hierarchical Cauchy + density-at-zero infrastructure). This track is **disjoint from the R59-R61 GLW-Cauchy-form helpers** — different matrix construction, different bridge philosophy. The 6 files :
   - `Helpers/CauchyDetLowerBound.lean` — 3126 LOC. Q1a : `det Σ ≥ exp(-c₀·m³)` for m²×m² Cauchy matrix on hierarchical grid.
   - `Helpers/CharFunCrossBlock.lean` — 635 LOC. Q1b : two-scale cosine-product cross-block swap inequality (Lindeberg swap with kernel decay ; replaces KMT/Brownian coupling).
   - `Helpers/MultivariateSmallBallUpper.lean` — 621 LOC. Q1c : multivariate small-ball UPPER on hierarchical grid. **3 named TAG'd sorries at lines 73, 238, 616 = the real in-tree blockers for A5 retirement via this track.**
   - `Helpers/SurgicalDensityAtZero.lean` — 543 LOC. Density-at-zero infrastructure for Q1a/b/c.
   - `Helpers/EsseenSmoothing.lean` — 817 LOC. Berry-Esseen smoothing for Q1c Step 1 (20 internal sorries, mostly untagged scaffolds).
   - `Helpers/GaussianHierCauchyBox.lean` — 167 LOC. `glwBoxProb_anderson_upper_*` chain (uses the V1-axiom Anderson field, not Mathlib).
   The status of this track at HEAD `f4011b9` has not been re-audited in any recent round.

3. **Hybrid axiom-shape path.** Add the bridge components (Anderson bound + discretization-error bound + optimization) as their own quantitative axioms, wire them through to A4/A5 honestly, then attempt to retire the new axioms separately. Net effect : axiom-shape change, not necessarily axiom-count reduction.

4. **Stick-with-axioms path.** Accept A4 + A5 as two of the irreducible axioms in the pragmatic ship.

**Trajectory math, post-R62 audit-redirect.** Your Probe 4 trajectory had R62 = -2 axioms, R63 = -1 axiom (Cauchy det), TD-drop = -1 axiom (Borell-TIS orphan), and TC11 → TC17+ = -3 sorries +0 axioms. Cumulative = -7 items, mainline 19 → 12. With R62 = 0 net (audit-redirect), cumulative becomes -5 items, mainline 19 → **14**, axiom inventory **9** (10 - 1 R63 retirement, A4/A5 stay axiomatized). The 3-axiom ship target you recommended in Probe 4 is no longer achievable from this side.

**The actual question.**

(a) Given that the R59-R61 → A4/A5 bridge requires α/β/γ/δ/ε infrastructure that is 0% in Mathlib + 0% in-tree at HEAD `f4011b9`, and given that the in-tree Q1a/b/c track has 5909+ LOC of alternate machinery already deployed targeting A5 retirement via Fourier smoothing + Berry-Esseen + density-at-zero, **is the Q1a/b/c track realistic for retiring A5 in the project timeline (next 10-15 dispatch rounds)?** Specifically : are the 3 named TAG'd sorries in `MultivariateSmallBallUpper.lean:73, :238, :616` plausibly closeable in single-round increments at 100-300 LOC each, or are they themselves multi-round / multi-year analytic identity gaps in disguise (the file header comment calls them "deep multivariate analytic identities")? If yes-feasible, what's the realistic LOC and round budget? If no, name the structural blocker.

(b) Given the answer to (a), **what is the new realistic minimum-axiom ship target?** Probes 1 + 4 gave 4-axiom and 3-axiom respectively, both conditioned on A4/A5 retirement via the GLW shortcut (now audit-rejected). The honest options appear to be :
- 4 axioms (Cp_T, one_dim_KMT, kmt_aided_gaussian_process, glw_det_lower_bound stays + A4 + A5 retired via Q1a/b/c) = best case.
- 5 axioms (the four above + A4 OR A5 sticky) = mid case.
- 6 axioms (the four above + A4 + A5 both sticky) = realistic-conservative case.

Which is the honest target ?

(c) Should we abandon the GLW-shortcut path for A4/A5 retirement entirely and commit to (1) Q1a/b/c track if your verdict on (a) is favorable, or (2) shipping at higher axiom count with A4 + A5 as oracles if (a) is unfavorable? Or is there a third option (e.g., axiomatize the missing α/β/γ/δ/ε bridge components, wire through to A4/A5, and ship at the same axiom count but with A4/A5 swapped for smaller, more defensible axioms)?

(d) Calibration self-critique : Probes 3 + 4 + Bonus 3 made the same chain-mismatch error as Cowork's brief (conflating finite-dim Lemma availability with full continuous-process bridge). What's the discipline rule that would have caught this BEFORE issuing the "60-130 LOC" estimate? Specifically : which question should I have included in Probe 3 / Probe 4 to force the bridge-gap analysis upfront ? I want to avoid the same family of error in future probes (the next likely candidate is the TC11 → TC14 Carter-Pollard chain → `tusnady_base_polynomial` retirement, which has the same "deterministic Lemma + bridge to consumer" structure).

**Success criterion** : a verdict on (a) yes/no with named sorries assessed individually, an honest N for (b) with the specific axioms that stay sticky in each case, a recommendation on (c) with rationale, and a literal one-sentence discipline rule for (d) that I can paste into a `feedback_*.md` memory note.
