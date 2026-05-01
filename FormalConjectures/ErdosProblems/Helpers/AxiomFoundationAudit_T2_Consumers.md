# R32 / T2.1 — Consumer extraction analysis

For each `axiom` and each live sorry-bearing theorem in T1.1, this document
records the actual call-sites, which conjuncts are extracted, and what
downstream theorem(s) use the extracted data. The "weakening tolerance"
column is a one-line note on whether the consumer's conclusion would still
hold under a weakened axiom statement (decoupled / conditional /
asymptotic-only relaxation).

## A1 — `Cp_T_explicit_pointwise_axiom`

| File:line | Caller | Extraction pattern | Downstream | Weakening tolerance |
|-----------|--------|--------------------|------------|---------------------|
| `Helpers/GLWGaussianProjectiveLimit.lean:2080` | `tsum_Cp_T_explicit_lt_top_R22` (private theorem at 2078) | `obtain ⟨K_axiom, hK_axiom_nn, h_axiom⟩ := Cp_T_explicit_pointwise_axiom` — extracts the constant `K_axiom : ℝ`, its non-negativity, and the pointwise bound for `T ≥ 1` | `tsum_Cp_T_explicit_lt_top_R22` is in turn consumed at line 2184 inside the conjunct-9 (Borel-Cantelli) discharge of `glwGaussianLimit_isAEKolmogorov_witness`-style chain feeding `Y_GLW_exists` | Tolerant: only the *summable* implication is needed downstream; any pointwise bound of the form `Cp_T_explicit T ≤ f(T)` with `∑ f(T) < ∞` would suffice. The `(T+1)^(3/2)` form is convenient but not load-bearing. |

**Single Lean-level consumer.** The axiom's only call site is line 2080.
No leakage of the explicit constant `K_axiom` to other files.

## A2 — `one_dim_KMT_coupling`

| File:line | Caller | Extraction pattern | Downstream | Weakening tolerance |
|-----------|--------|--------------------|------------|---------------------|
| (none) | — | — | — | — |

`grep -rn -E '(apply|exact|refine|obtain|have)[^a-zA-Z_].*one_dim_KMT_coupling'`
project-wide returns **zero matches**. The axiom is referenced only in
documentation comments:

- `Helpers/OneDimKMT.lean:44` — own docstring
- `Helpers/TwoDimKMTFromOneDim.lean:63` — header comment
- `Helpers/TwoDimKMTFromOneDim.lean:237` — explicit note: *"The 1D KMT axiom
  (`one_dim_KMT_coupling`) is **not** directly invoked here — it is
  encapsulated inside the stepping-stone axiom's mathematical content"*

**Audit-relevant fact.** A2 is a *dormant* axiom: declared in R29 with the
intent that the 2D KMT theorem would reduce to it via the LS bridge, but in
the actual R30 implementation the LS bridge is short-circuited by A3
(`kmt_aided_gaussian_process`), which absorbs the 1D-coupling content. Net
effect: A2 contributes zero atomicity benefit to the project's axiom budget
in `r30-finish` and is in practice replaced by the strictly-broader A3.

## A3 — `kmt_aided_gaussian_process`

Lean-level invocations (5 in `Helpers/TwoDimKMTFromOneDim.lean`):

| File:line | Caller | Extraction pattern |
|-----------|--------|--------------------|
| `TwoDimKMTFromOneDim.lean:122-126` | `LS_yplus_construction` (private theorem 115) | `obtain ⟨Y, h_meas, h_cont, h_decay, _⟩ := kmt_aided_gaussian_process (fun u k n => Real.exp (-u * (k:ℝ) / (n:ℝ))) yplus_kernel_bound a ha` — drops the coupling conjunct (5th `_`) |
| `TwoDimKMTFromOneDim.lean:137-141` | `LS_yminus_construction` (private theorem 130) | as above with kernel `(-Real.exp (-u/n))^k` |
| `TwoDimKMTFromOneDim.lean:168-171` | `LS_kernel_coupling` (private theorem 154) | extracts all 5 conjuncts (meas / cont / decay / coupling), kernel-parametric |
| `TwoDimKMTFromOneDim.lean:480-481` | `LS_yplus_via_even` (private theorem 469, R31 infra) | term-mode application; produces a Gaussian witness for the even-indexed half-sum |
| `TwoDimKMTFromOneDim.lean:498-499` | `LS_yminus_via_odd` (private theorem 487, R31 infra) | mirror of above on odd sub-sequence |

**`LS_kernel_coupling`** at `TwoDimKMTFromOneDim.lean:154-171` is the
bottleneck consumer: it extracts the 4 structural conjuncts plus the
coupling conjunct from the axiom, and is itself called twice inside
`two_dim_KMT_coupling_via_LS_reduction` at lines 275 (Yplus) and 279
(Yminus).

The R31 infrastructure (`LS_yplus_via_even`, `LS_yminus_via_odd`) is
consumed by **no current downstream theorem** in `r30-finish`; it is
scaffolding for an R33-planned corrected-form path.

### Downstream chain from A3 to 524.lean's 4 consumers

```
kmt_aided_gaussian_process (axiom)
  └── LS_kernel_coupling (helper, twice)
        └── two_dim_KMT_coupling_via_LS_reduction (theorem)
              └── theorem two_dim_KMT_coupling (524.lean:3741)
                    └── 4 call-sites in 524.lean:
                        - 3926 (upper-bound for Y⁺ small ball, exponent `-glw.upper`)
                        - 4081 (uniform-N₀ refinement of 3926)
                        - 4229 (lower-bound, two-factor exponent `-2·glw.lower` — this is the consumer that uses **`hIndep`**)
                        - 4605 (uniform-N₀ refinement of 4229)
```

### 4 consumers in `524.lean` — extraction patterns

All four use the same 13-tuple `obtain` pattern matching the 10-conjunct
existential of `theorem two_dim_KMT_coupling`:

```
obtain ⟨Yplus, [_]Yminus, Δ, hYp_meas, [_]hYm_meas, hΔ_bd,
        hKMT_p, [_]hKMT_m, [_]hIndep,
        [_]hYp_cont, [_]hYm_cont, [_]hYp_tail, [_]hYm_tail⟩ :=
  two_dim_KMT_coupling a ha
```

(Underscores `[_]` indicate hypotheses bound but unused — varies per call-site.)

| Line | Conjuncts actually used (un-underscored) | Conclusion shape | Weakening tolerance |
|------|-------------------------------------------|-------------------|---------------------|
| 3926 | `Yplus`, `Δ`, `hYp_meas`, `hΔ_bd`, `hKMT_p` | `ℙ {sup ≤ ε√n} ≤ exp(-glw.upper · |log(ε + log(n+1)/√n)|³)` | **Decoupled-form compatible**: only Yplus side is used; `hIndep`, `hYm_*`, `hYp_cont`, `hYp_tail` all underscored. |
| 4081 | same as 3926 | same shape, uniform-N₀ refinement | **Decoupled-form compatible** (same conjunct usage). |
| 4229 | `Yplus`, `Yminus`, `Δ`, `hYp_meas`, `hYm_meas`, `hΔ_bd`, `hKMT_p`, `hKMT_m`, **`hIndep`**, `hYp_cont`, `hYm_cont` | `ℙ {sup ≤ ε√n} ≥ ... · exp(-2·glw.lower · |...|³)` (two-factor; uses product formula via `hIndep`) | **NOT decoupled-form compatible**: `hIndep` is the load-bearing input that gives the `2·glw.lower` factor (this is what R31 audit flagged). |
| 4605 | same as 4229 | uniform-N₀ refinement of 4229 | **NOT decoupled-form compatible** (same `hIndep` dependency). |

**Critical asymmetry.** Two of the four consumers (the upper-bound branch
3926 / 4081) are robust to the R31-flagged contradiction because they do
not invoke `hIndep`. The other two (lower-bound branch 4229 / 4605) are
the ones whose conclusions become vacuous if A3's axiom statement is
internally inconsistent.

This matches the R31 finding: the 2D KMT theorem's *statement*
(full-sum approximation + unconditional independence at rate
`O(log n / √n)`) is contradictory, but two of its four consumers happen to
use only the consistent half (full-sum approximation alone).

## B1 — `LS_independent_yplus_yminus` (live sorry, R30 T3.4)

| File:line | Caller | Extraction pattern | Downstream |
|-----------|--------|--------------------|------------|
| `TwoDimKMTFromOneDim.lean:283` | `two_dim_KMT_coupling_via_LS_reduction` (theorem 252) | `have h_indep := LS_independent_yplus_yminus Yplus Yminus` — discharges the `IndepFun` conjunct of the headline theorem | feeds the 4-consumer chain in 524.lean (transitively, via `theorem two_dim_KMT_coupling`) |

The `Yplus` and `Yminus` arguments come from two separate
`LS_kernel_coupling` calls at lines 275 / 279 — both use A3 with
*different* kernels but the *same* underlying Rademacher sequence
`(a, ha)`. The independence conjunct is the load-bearing claim that the
two axiom-produced witnesses are independent **as functions of the same
Ω**, despite having been constructed from the same input sequence.

### Why B1 is uncloseable in current shape (R31 finding, restated)

The two `LS_kernel_coupling` calls receive the same `(a, ha)`. Each
applied axiom produces a `Y` that satisfies
`|(1/√n) ∑_{k=1..n} a_k · kernel(u, k, n) - Y u| ≤ log(n+1)/√n`
uniformly in n, ω, u. Both `Yplus` and `Yminus` therefore approximate
the **same input sequence** `(a_k)` (filtered through different
deterministic kernels), at sub-CLT error rate. Their values are
deterministically tied to `(a_k)` up to a vanishing error, which forces
nonzero cross-covariance and rules out unconditional `IndepFun`. Hence
the sorry at line 213 cannot be closed in the current axiom shape: the
axiom itself does not provide independent constructions across two
calls.

## B2 / B3 — `IsRademacherSequence_a_{even,odd}` (R31 sorries)

Both have a single Lean-level consumer in the R31 infrastructure:
- `IsRademacherSequence_a_even` → `LS_yplus_via_even` (480, term-mode `IsRademacherSequence_a_even a ha` argument)
- `IsRademacherSequence_a_odd` → `LS_yminus_via_odd` (498)

`LS_yplus_via_even` and `LS_yminus_via_odd` are themselves dead-ends in
`r30-finish` (no consumers). The sorry content is the standard
"`iIndepFun` closed under sub-sequence selection along an injective
`ℕ → ℕ`" lemma — Mathlib-mechanical, not a foundational issue.

## Out-of-scope (Section E of T1.1) — brief note

Sorries in `EsseenSmoothing.lean`, `SurgicalDensityAtZero.lean`,
`MultivariateSmallBallUpper.lean`, `YGLWFromBrownianMotion.lean:3083`
are confirmed not on the active 524.lean discharge chain (verified: none
of these files are imported by 524.lean directly except via the
GLWUpperProof / GLWLowerProof chain, and the 2 sorries each in
GLWUpperProof.lean:285 / GLWLowerProof.lean:328,340 are documented gaps
on the Karhunen–Loève + entropy bound — orthogonal to the axiom
foundations being audited here).

## Summary table

| Axiom / sorry | # Lean consumers | Conjunct-tension risk | Downstream blast radius |
|---------------|------------------|------------------------|--------------------------|
| A1 `Cp_T_explicit_pointwise_axiom` | 1 (line 2080) | low | `tsum_Cp_T_explicit_lt_top_R22` → `Y_GLW_exists` chain |
| A2 `one_dim_KMT_coupling` | 0 (dormant) | n/a | dormant, no current downstream |
| A3 `kmt_aided_gaussian_process` | 5 in `TwoDimKMTFromOneDim.lean` | medium-high (T3.1 will analyze) | 4 in `524.lean` (2 robust, 2 vacuous-if-A3-contradictory) |
| B1 `LS_independent_yplus_yminus` | 1 (line 283) | already CONFIRMED uncloseable per R31 | 4 in `524.lean` (same as A3 chain) |
| B2/B3 (Rademacher sub-sequence) | 1 each, both leading to dead helpers | low (Mathlib-mechanical) | none in `r30-finish` |
