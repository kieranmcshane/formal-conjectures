# Round TC12 brief — Carter-Pollard §2 eq (7) reformulation + §4 bulk upper bound

**Type**: Closure round, Track C / Carter-Pollard chain.
**Dispatch surface**: `track-c-1dkmt` worktree at `~/Documents/formal-conjectures-track-c/`, HEAD `efe78d7` (post-TC11).
**Scope binding (Q7)**: TC12 = (i) close two TC11 placeholders (`bin_tail_beta_integral` body, `bin_tail_h_integral` body) bridging to paper §2 eq (7) form, AND (ii) prove the §4 bulk integral upper bound `∫_0^η e^{N·h(s)} ds ≤ √(2π/N) · Φ̄(ε√N)` using the TC11 Taylor bound. Lower bound (paper §4 with cutoff-η optimization) staged TC12.5/TC13. Tail discard (`∫_η^1`) staged TC13.

---

## T1.0 — paper recheck (verbatim, per `feedback_paper_recheck_t10`)

Carter-Pollard 2004 (arXiv:math/0508606) §2 eq (7) (verbatim, paper page 5) :

> P{X ≥ k} = e^Δ √(N/(2π)) ∫_0^1 e^{Nh(s) - Nε²/2} ds                                  (7)
>
> where Δ = log(1 + N⁻¹) + Λ - (1/2) log(1 - ε²) - Nε⁴γ(ε).

Carter-Pollard 2004 §4 first paragraph (verbatim) — TC11 closed `h(s) ≤ ε²/2 - (s+ε)²/2` for `0 < s < 1`. TC12 uses this :

> The right-hand side of the approximation (9) is actually an upper bound, because the integrand is nonnegative on (1, ∞). That is,
>
> P{X ≥ k} ≤ e^Δ Φ̄(ε√N),
>
> which gives the upper bound for An(ε) stated in the Theorem.

(Paper's eq (9) is the Gaussian-tail integral that emerges after the TC11 Taylor upper bound is applied to the integrand of eq (7).)

---

## Pre-flight context (post-TC11)

TC11 closed Best-distribution :
- `carterPollardH_taylor_upper_bound` Full : `h(ε, s) ≤ ε²/2 - (s+ε)²/2` for `0 ≤ s < 1`, `0 ≤ ε ≤ 1`. ✓
- h-function infrastructure : `H`, `h`, derivatives `h'`, `h''`, `h'''` explicit forms with sign control, `h_concave` Full.
- 18 Full artefacts total. Paper typo flagged + corrected.
- Audit estimate 200 LOC, actual 395 LOC = **98% overrun** (source : iteratedDeriv-via-EventuallyEq chains).

Two TC11 placeholders left for TC12 to close :
- `bin_tail_beta_integral` body : sorry. Bridges TC9 `binomial_tail_beta_integral` to the §4 form (specialise `p = 1/2`, factor out `n!/((k-1)!(n-k)!)`).
- `bin_tail_h_integral` body : `True := by trivial` placeholder. Performs the change-of-variables `t = 1/2 + s/√N`, extracts the Stirling prefactor `√(N/(2π)) · 4^N · exp(Λ)`, lands the eq (7) form.

These two placeholders are **TC12 mandatory floor** before any §4 bulk upper bound work.

---

## Mandatory floor

### T1.1 — Mathlib API audit (Full)
Document in `Helpers/TrackC_round12_T1_Eq7BulkUpperAudit.md` :

- **Verify Mathlib pin `25ce633136`** :
  - `intervalIntegral.integral_smul_real`, `integral_const_mul`, `mul_integral` : standard, used in change-of-variable.
  - `intervalIntegral.integral_comp_div`, `integral_comp_sub_left`, `integral_comp_add_right` : substitution lemmas. Verify exact name + hypothesis shape at pin.
  - `intervalIntegral.integral_mul_continuousOn_le` : monotone integral bound.
  - `Real.sqrt` API + `Real.sqrt_pos`, `Real.sqrt_mul_self`, `Real.sqrt_div`, `Real.sqrt_inv` : standard.
  - `Real.exp_pos`, `Real.exp_mul`, `Real.exp_neg`, `Real.exp_log` : standard.
  - **Stirling factor** : compose `factorial_le_stirling_robbins` (TC8) + `Stirling.le_factorial_stirling` (Mathlib) for both-sided `n!` bounds. Or simpler if only the upper bound is needed.
  - `Real.gauss_pdf` / `Real.normalCDF` / `Real.gauss_cdf_compl` (or whatever Mathlib calls Φ̄) for the Gaussian tail comparison. Verify exact name at pin (probably `Probability.GaussianReal` namespace).
- **Strategy proposal (NOT binding, per TC9-TC10-TC11 lesson)** :
  - **Strategy A (recommended)** : direct change-of-variable via `intervalIntegral.integral_comp_div` with substitution `t = 1/2 + s/√N`. Combine with `bin_tail_beta_integral` from TC9 to land eq (7). Use TC11 `carterPollardH_taylor_upper_bound` to bound the integrand `e^{Nh(s)}` from above by `e^{Nε²/2 - N(s+ε)²/2}`, then evaluate the Gaussian-tail integral. ~250-400 LOC.
  - **Strategy B (fallback)** : if change-of-variable lemma surfaces issues, bypass with manual unfolding of the integral via `MeasureTheory.integral_smul_measure` and direct measure-pushforward.

### T2.1 — close `bin_tail_beta_integral` (Full)
Replace the TC11 placeholder body with the actual proof :

```lean
lemma bin_tail_beta_integral (n k : ℕ) (hkn : k ≤ n) (hk : 1 ≤ k) :
    (1 / 2 ^ n : ℝ) * ((Finset.Ico k (n + 1)).sum
      (fun j => (n.choose j : ℝ))) =
    ((n : ℝ) * ((n - 1).choose (k - 1)) * ∫ x in (0 : ℝ)..(1/2),
      x ^ (k - 1) * (1 - x) ^ (n - k)) := by
  -- Specialise TC9's binomial_tail_beta_integral to p = 1/2.
  have h_tc9 := binomial_tail_beta_integral n k hk hkn
    (p := 1/2) (hp0 := by norm_num) (hp1 := by norm_num)
  -- Multiply both sides by (1/2)^n and rearrange.
  [BODY ~30-50 LOC]
```

Bridge from TC9. ~30-50 LOC.

### T2.2 — close `bin_tail_h_integral` body (Full)
Replace the `True := by trivial` placeholder with the actual eq (7) statement + body :

```lean
lemma bin_tail_h_integral (n : ℕ) (hn : 28 ≤ n) (k : ℕ) (hkn : k ≤ n) (hk : 1 ≤ k)
    (hε_range : let ε := (2 * (k : ℝ) - n - 1) / (n - 1); 0 ≤ ε ∧ ε ≤ 1) :
    let N : ℕ := n - 1
    let ε : ℝ := (2 * (k : ℝ) - n - 1) / N
    let Δ : ℝ := Real.log (1 + (1 / N : ℝ)) + (Λ_term n k)
                  - (1 / 2) * Real.log (1 - ε^2) - N * ε^4 * γ ε
    (1 / 2 ^ n : ℝ) * ((Finset.Ico k (n + 1)).sum (fun j => (n.choose j : ℝ))) =
    Real.exp Δ * Real.sqrt (N / (2 * Real.pi)) *
      ∫ s in (0 : ℝ)..1, Real.exp (N * h ε N s - N * ε^2 / 2) := by
  [BODY ~150-250 LOC]
```

Strategy : (i) start from TC11 `bin_tail_beta_integral` (now Full from T2.1) ; (ii) substitute `t = 1/2 + s/√N` via `intervalIntegral.integral_comp_div` (or analog) ; (iii) extract Stirling prefactor `(n choose ...) · (1/2)^n = √(N/(2π)) · exp(Λ_term)` using TC8 Robbins + `Stirling.le_factorial_stirling` ; (iv) factor `H(K/N)` to get the `-N·ε²/2` shift in the integrand. ~150-250 LOC.

(Note : `Λ_term n k` and `γ ε` are paper-defined functions ; they may need their own short Lean defs in TC11 starter or this round. Audit decides where they live.)

### T2.3 — §4 bulk upper bound on `∫_0^1 e^{N·h(s) - Nε²/2} ds` (Full, **closure target**)
```lean
/-- **Carter-Pollard 2004 §4 bulk upper bound** (paper page 7).
    The integrand is non-positive on (1, ∞), so the upper bound extends naturally :
    `∫_0^1 e^{N(h(s) - ε²/2)} ds ≤ ∫_0^∞ e^{-N(s+ε)²/2} ds = √(2π/N) · Φ̄(ε√N)`. -/
theorem carterPollardH_bulk_upper_bound
    {N ε : ℝ} (hN : (28 : ℝ) ≤ N) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∫ s in (0 : ℝ)..1, Real.exp (N * h ε N s - N * ε^2 / 2) ≤
    Real.sqrt (2 * Real.pi / N) * Real.Gaussian.compl_cdf (ε * Real.sqrt N) := by
  -- Apply TC11 carterPollardH_taylor_upper_bound to the integrand pointwise :
  -- h(s) - ε²/2 ≤ ε²/2 - (s+ε)²/2 - ε²/2 = -(s+ε)²/2
  -- So e^{N(h(s) - ε²/2)} ≤ e^{-N(s+ε)²/2}.
  -- Then bound ∫_0^1 e^{-N(s+ε)²/2} ds by ∫_0^∞ e^{-N(s+ε)²/2} ds (extend integrand),
  -- substitute u = (s+ε)·√N, integrate to √(2π/N) · Φ̄(ε·√N).
  [BODY ~120-200 LOC]
```

Strategy : pointwise Taylor-bound application + Gaussian tail integral evaluation + substitution. The substitution step `u = (s + ε)·√N` is the only mildly non-trivial step ; rest is pure positivity + monotonicity. ~120-200 LOC.

### T3 — build verification (Full)
- Targeted : `lake build FormalConjectures.ErdosProblems.Helpers.CarterPollardHFunction`. Must be green at <90s.
- Counter-check : ensure TC11 Full theorems still build (no regression).

### T4 — push (Full)
- Single commit on `track-c-1dkmt` : "TC12 Carter-Pollard §2 eq (7) + §4 bulk upper — 3 Full closures".
- Push to `fork`.
- Append TC12 section to `Helpers/TrackCStatus.md`.

---

## Definitions

- **Full** : signature present, body fully proved, file compiles, single-target build green.
- **Sub-Stub** : NOT used this round (TC12 = clean Full closures, no sub-stubs).

---

## Out of scope (explicit binding)

- §4 bulk LOWER bound + cutoff-η optimization (`12η² + η = ε_N`) — staged TC13 / TC12.5. Realistic 200-300 LOC.
- §4 tail discard `∫_η^1 e^{Nh(s)} ds = O(N⁻¹)` — staged TC13.
- §3 Mills-bridge inequalities (Lemma 1, ρ/r/Ψ functions) — already DONE in Lean as Mills `_pos` (TC7), `_truncation` (TC6), `_antitone` (TC8). Reciprocal-bridge `m(x) = 1/ρ(x)` adapter staged TC13.
- §5 Theorem 2 derivation + envelope + `tusnady_base_polynomial` close — staged TC14.
- A2 (`one_dim_KMT_coupling`) retirement — staged TC17+.

---

## Calibration

- **Total budget** : 300-500 LOC bodies (T2.1 + T2.2 + T2.3) per Grok Probe 4 mid-band, **adjusted upward to 500-700 LOC realistic** per TC11 overrun history (TC11 audit 200 → actual 395 = 98% overrun; analogous risk on T2.2 Stirling-factor extraction + T2.3 substitution step). Budget +30% to compensate.
- **Realistic wall-clock** : 2-3 build cycles. T2.2 (Stirling factor + change-of-variable) is the main risk. T2.3 (Gaussian tail integral) is mechanical given Mathlib has the basic Gaussian API.
- **Risk band** : medium. Three areas of friction predicted :
  - (a) `intervalIntegral.integral_comp_div` exact API signature at pin — verify in T1.1.
  - (b) Stirling factor casting (Robbins `(1/2)^n` extraction) — typed as ℕ vs ℝ.
  - (c) Gaussian compl_cdf naming — verify exact Mathlib namespace at pin.
- **Closure tier** : real, additive. Net debt change TC11 → TC12 : **+0 sorries** (3 NEW Full theorems / lemmas, no new sub-stubs introduced if all three close cleanly). +3 Full theorems advancing the Carter-Pollard chain.
- **Cross-track FS discipline** : not applicable. Track-c-only round, no `lake update`, no pin bump. R63 (mainline Cauchy det) can run concurrently in mainline worktree.

---

## Pre-flight checks (run before commit)

```sh
fc-c
git status
git branch --show-current                                       # track-c-1dkmt
lakecache
lake build FormalConjectures.ErdosProblems.Helpers.CarterPollardHFunction 2>&1 | tail -10
lake build FormalConjectures.ErdosProblems.Helpers.BinomialTailBeta 2>&1 | tail -10  # TC9-TC10 still green
```

---

## Artefact list

- `FormalConjectures/ErdosProblems/Helpers/CarterPollardHFunction.lean` — modified (close 2 TC11 placeholders + add bulk upper bound theorem, +300-500 LOC additive).
- `FormalConjectures/ErdosProblems/Helpers/TrackC_round12_T1_Eq7BulkUpperAudit.md` — new audit doc.
- `FormalConjectures/ErdosProblems/Helpers/TrackCStatus.md` — TC12 section appended.

---

## Strategy proposal vs binding (TC9-TC10-TC11 lesson)

Brief proposes Strategy A (direct change-of-variable + Taylor bound application). Track C dispatch is free to substitute Strategy B (manual measure-pushforward) if T1.1 audit surfaces `integral_comp_div` API issues at pin. Document choice in audit T1.1 BEFORE writing T2.x — TC10 protocol.

**TC11-overrun calibration adjustment (NEW per TC11 closure)** : audit budgets for iterated-derivative chains should be multiplied by ~2x to match observed Lean cost. T2.2 (Stirling extraction + change-of-variable) is the analogous chain-of-rewrites risk in TC12 ; budget at 2x audit estimate.

End brief.
