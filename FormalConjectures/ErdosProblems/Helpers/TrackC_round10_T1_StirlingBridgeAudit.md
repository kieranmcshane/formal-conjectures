# Track C Round 10 — T1.1 Stirling-prefactor + PMF.binomial-bridge audit

**Round**: TC10 (Carter–Pollard Step 2 + PMF.binomial bridge corollary)
**Surface**: `track-c-1dkmt` worktree, HEAD `1fa1317` (post-TC9)
**Pin**: Mathlib (current Track C lake-manifest)
**Audit author**: Cowork (T1.1)
**Status**: `VERIFIED` for Route A; bridge lemmas all present.

---

## 1. Paper recheck — what does Carter–Pollard 2004 actually need?

**Claim**: Carter–Pollard's KMT-style polynomial small-ball couplings exploit Step-2
prefactor as an **explicit (non-asymptotic) upper bound**, NOT a `~`-asymptotic
equivalence. The downstream argument needs uniform control in `m` for fixed `k`,
because the coupling error must be tied to a polynomial-in-`m` upper bound on
the inverse-Beta normaliser. An `IsEquivalent` would give sharpness but no
absolute upper bound (only "for `m` large enough"), which is unusable when one
wants finite-`m` Bernstein-type bounds.

**Conclusion**: Step 2 = explicit bound is the correct target. Asymptotic
sharpness can be added later, separately, and is NOT required by TC10 scope.

**Sharpness aside**: the bound `m · C(m-1, k-1) ≤ m^k / (k-1)!` is in fact
tight: `m · C(m-1, k-1) = (k-1)!^{-1} · m·(m-1)·…·(m-k+1)`, and as `m → ∞`
this is `(1+o(1)) · m^k / (k-1)!`. So the bound *is* sharp asymptotically,
and gives explicit non-asymptotic control. Best of both worlds — no need for
Route B/C.

---

## 2. Mathlib API surface (verified at current pin)

### 2.1 Choose / descFactorial / factorial bridge (Route A backbone)

| Lemma | Statement | Location |
|---|---|---|
| `Nat.choose_mul_factorial_mul_factorial` | `k ≤ n → choose n k * k! * (n-k)! = n!` | `Mathlib/Data/Nat/Choose/Basic.lean:141` |
| `Nat.factorial_mul_descFactorial` | `k ≤ n → (n-k)! * n.descFactorial k = n!` | `Mathlib/Data/Nat/Factorial/Basic.lean:375` |
| `Nat.descFactorial_le_pow` | `n.descFactorial k ≤ n^k` | `Mathlib/Data/Nat/Factorial/Basic.lean:438` |
| `Nat.add_one_mul_choose_eq` | `(n+1) * choose n k = choose (n+1) (k+1) * (k+1)` | (used in TC9) |
| `Nat.factorial_pos` | `0 < n!` | `Mathlib/Data/Nat/Factorial/Basic.lean` |

All `VERIFIED`.

### 2.2 PMF.binomial bridge (Route bridge corollary)

| Lemma | Statement | Location |
|---|---|---|
| `PMF.binomial` | `(p : ℝ≥0) → (h : p ≤ 1) → (n : ℕ) → PMF (Fin (n+1))` | `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean:29` |
| `PMF.binomial_apply` | `binomial p h n i = ↑(p^i.val * (1-p)^(Fin.last n - i).val * choose n i.val)` | `…/Binomial.lean:42` |
| `PMF.toOuterMeasure_apply_finset` | `(s : Finset α) → p.toOuterMeasure s = ∑ x ∈ s, p x` | `Mathlib/.../Basic.lean:152` |
| `PMF.toOuterMeasure_apply_fintype` | `[Fintype α] → p.toOuterMeasure s = ∑ x, s.indicator p x` | `Mathlib/.../Basic.lean:202` |
| `Fin.last_sub` | `last n - i = Fin.rev i` | `Mathlib/Data/Fin/Basic.lean:467` |
| `Fin.val_rev` | `(Fin.rev i).val = n - i.val` (for `i : Fin (n+1)`) | `Mathlib/Data/Fin/Basic.lean` (vicinity 467) |
| `Finset.coe_filter` | `↑(filter p s) = {x ∈ s | p x}` | `Mathlib/Data/Finset/Filter.lean` (standard) |
| `ENNReal.toReal_sum` | `(∀ i ∈ s, f i ≠ ⊤) → (∑ i ∈ s, f i).toReal = ∑ i ∈ s, (f i).toReal` | `Mathlib/Data/ENNReal/Real.lean` |

All `VERIFIED` for the bridge.

### 2.3 Stirling toolkit (NOT required for TC10 — Route B/C reference only)

| Lemma | Statement | Location |
|---|---|---|
| `Stirling.factorial_isEquivalent_stirling` | `n! ~ √(2πn)·(n/e)^n` | `Mathlib/Analysis/SpecialFunctions/Stirling.lean:235` |
| `Stirling.le_factorial_stirling` | `√(2πn)·(n/e)^n ≤ n!` (lower bound only) | `…/Stirling.lean:266` |
| `Stirling.tendsto_stirlingSeq_sqrt_pi` | `Tendsto stirlingSeq atTop (𝓝 √π)` | `…/Stirling.lean:228` |

Confirmed: **no upper bound on `n!`** in `Stirling.lean`. Route B would need to
derive one from the asymptotic. Skipped — Route A doesn't need it.

---

## 3. Claims Verification Table

Step 2 + bridge requires the following claims to compose. Each is marked
`VERIFIED` (lemma name + line cited), `PARTIAL` (need wrapper), or
`NEEDS-PROOF` (must be proved in TC10).

| # | Claim | Status | Source / TC10 task |
|---|---|---|---|
| 1 | `m · C(m-1, k-1) · (k-1)! = m.descFactorial k` (in ℕ, `1 ≤ k ≤ m`) | `NEEDS-PROOF` | T2.1 internal lemma |
| 2 | `m.descFactorial k ≤ m^k` (in ℕ) | `VERIFIED` | `Nat.descFactorial_le_pow` |
| 3 | `((k-1)! : ℝ) > 0` | `VERIFIED` | `Nat.factorial_pos` + `Nat.cast_pos` |
| 4 | Cast and divide: `(claim 1) ∧ (claim 2) → m · C(m-1, k-1) ≤ m^k / (k-1)!` (in ℝ) | `NEEDS-PROOF` | T2.1 main proof |
| 5 | `Fin.last m - i = Fin.rev i`, so `(Fin.last m - i : ℕ) = m - i.val` | `VERIFIED` | `Fin.last_sub`, `Fin.val_rev` |
| 6 | `↑(Finset.filter (k ≤ ·.val) Finset.univ) = {i : Fin (m+1) \| k ≤ i.val}` (set/finset coercion) | `VERIFIED` | `Finset.coe_filter`, `Finset.mem_univ` |
| 7 | `(PMF.binomial p h m).toOuterMeasure ↑F = ∑ i ∈ F, binomial p h m i` (ENNReal) | `VERIFIED` | `PMF.toOuterMeasure_apply_finset` |
| 8 | `(∑ i ∈ F, binomial p h m i).toReal = ∑ i ∈ F, (binomial_apply ... ).toReal` (NNReal/ENNReal/ℝ) | `PARTIAL` | T2.2 internal — `ENNReal.toReal_sum` + finiteness |
| 9 | `Finset.Ico k (m+1)` ↔ `Finset.filter (k ≤ ·.val) (Finset.univ : Finset (Fin (m+1)))` re-indexing (sum equality) | `NEEDS-PROOF` | T2.2 internal — `Finset.sum_bij` or `Finset.sum_attach`/`Finset.sum_fin_eq_sum_range` |

`NEEDS-PROOF` count: 3 (claims 1, 4, 9). `PARTIAL`: 1 (claim 8 — needs finiteness wrapper).

---

## 4. Strategy proposal — Route A (recommended, NON-binding per TC9 lesson)

### 4.1 T2.1 — Stirling prefactor (explicit bound)

**Target signature** (chosen):
```lean
theorem stirling_prefactor_bound (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hkm : k ≤ m) :
    (m : ℝ) * ((m - 1).choose (k - 1) : ℝ) ≤ (m : ℝ) ^ k / ((k - 1).factorial : ℝ)
```

**Proof sketch**:

1. (Lemma `mul_choose_eq_descFactorial`, ℕ) `m · C(m-1, k-1) · (k-1)! = m.descFactorial k`.
   - From `Nat.choose_mul_factorial_mul_factorial (m-1) (k-1) ≤ (m-1)`:
     `C(m-1, k-1) · (k-1)! · (m-k)! = (m-1)!`
     (uses `(m-1) - (k-1) = m - k`, by `Nat.sub_sub_sub` or `omega`).
   - Multiply both sides by `m`:
     `m · C(m-1, k-1) · (k-1)! · (m-k)! = m · (m-1)! = m!`.
   - Apply `Nat.factorial_mul_descFactorial hkm`: `(m-k)! · m.descFactorial k = m!`.
   - Cancel `(m-k)!` (positive) on both sides: claim.

2. (Main bound, ℝ) Cast claim 1 to ℝ; combine with `Nat.descFactorial_le_pow`:
   `m · C(m-1, k-1) · (k-1)! ≤ m^k`.
   Divide by `(k-1)! > 0` (cast `Nat.factorial_pos`) to land in ℝ:
   `m · C(m-1, k-1) ≤ m^k / (k-1)!`.

**LOC budget**: 50–80. Two helper lemmas (claim 1 internally, claim 4 = main bound).
**Risk**: low. All ingredients are present in Mathlib.

### 4.2 T2.2 — PMF.binomial bridge corollary

**Target signature** (chosen, leveraging TC9 `binomialPolyTail`):
```lean
theorem binomialPolyTail_eq_pmf_tail
    (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (p : ℝ≥0) (h : p ≤ 1) :
    binomialPolyTail m k (p : ℝ) =
      (((PMF.binomial p h m).toOuterMeasure
        {i : Fin (m + 1) | k ≤ (i : ℕ)})).toReal
```

**Note on `p`**: The brief uses `p : ℝ` with `0 ≤ p ≤ 1` and packages
`⟨p, hp⟩ : ℝ≥0`. We use `p : ℝ≥0` directly (cleaner: avoids `Subtype.mk`
beta-reduction friction). Composition with `binomial_tail_beta_integral`
(TC9, takes `p : ℝ`) goes through `(p : ℝ)`. If downstream needs the brief
form, we add a `_real` variant — out of scope here.

**Proof sketch**:

1. **Reduce RHS to a Finset sum**:
   - Define `F : Finset (Fin (m+1)) := Finset.filter (fun i => k ≤ i.val) Finset.univ`.
   - Show `(↑F : Set (Fin (m+1))) = {i | k ≤ i.val}` via `Finset.coe_filter` + `mem_univ`.
   - Apply `PMF.toOuterMeasure_apply_finset` (or `_apply_fintype` + indicator):
     `(binomial p h m).toOuterMeasure ↑F = ∑ i ∈ F, binomial p h m i` (ENNReal).

2. **Reduce ENNReal sum to ℝ sum**:
   - Each `binomial p h m i` is a finite ENNReal (it's `↑r` for `r : ℝ≥0`).
   - Apply `ENNReal.toReal_sum` (with finiteness via `coe_ne_top`).
   - Result: `(∑ i ∈ F, binomial p h m i).toReal = ∑ i ∈ F, (binomial p h m i).toReal`.

3. **Compute each term explicitly**:
   - `binomial p h m i = ↑(p^i.val * (1-p)^(Fin.last m - i).val * choose m i.val)` by `binomial_apply`.
   - `(Fin.last m - i).val = m - i.val` by `Fin.last_sub` + `Fin.val_rev`.
   - Cast NNReal → ℝ via `NNReal.coe_mul`, `NNReal.coe_pow`, `NNReal.coe_sub_of_le`.
   - **Note**: `(1 - p : ℝ≥0)` needs `p ≤ 1` (we have `h`); coerce via
     `NNReal.coe_sub` → `(1 - p : ℝ) = 1 - (p : ℝ)`.
   - Result: `(binomial p h m i).toReal = (p:ℝ)^i.val * (1-(p:ℝ))^(m - i.val) * choose m i.val`.

4. **Re-index sum to match `binomialPolyTail`**:
   - `binomialPolyTail m k (p:ℝ) = ∑ j ∈ Finset.Ico k (m+1), choose m j * (p:ℝ)^j * (1-(p:ℝ))^(m-j)`.
   - Re-index `F = filter (k ≤ ·.val) univ` over `Fin (m+1)` to `Finset.Ico k (m+1)` over `ℕ`:
     bijection `i ↦ i.val` from `F` to `Finset.Ico k (m+1)`. Use
     `Finset.sum_bij` or `Finset.sum_fin_eq_sum_range` (which sums `Fin n.val`-indexed
     functions over an `Finset.range n` post-image).
   - Conclude equality.

**LOC budget**: 100–150. NNReal/ENNReal/ℝ chain has known friction. The
re-indexing step (claim 9) is the riskiest sub-step.

**Risk**: medium. Coercion gymnastics. If first build cycle hits a coercion
wall, fall back to `Finset.sum_attach` + manual `Fin.mk` re-index, or
state the bridge with `Fin (m+1)`-indexed RHS sum and a separate `_eq_Ico`
helper.

### 4.3 Audit conclusion

**Route A is locked**. Routes B and C are not pursued. Total LOC budget
**150–230** (T2.1 ≤ 80, T2.2 ≤ 150). Both pieces append to
`BinomialTailBeta.lean` (currently 312 LOC; final target ≤ ~480 LOC, well
under the 600 LOC threshold from the brief).

**File location**: append to `BinomialTailBeta.lean` (no new `StirlingPrefactor.lean`
needed). Rationale: both Step-2 prefactor and PMF bridge are tightly coupled
to `binomialPolyTail` (TC9 helper); splitting would add an import edge
without compaction benefit.

**Title for the section in `BinomialTailBeta.lean`**:
```
/-! ### Stirling prefactor and PMF.binomial bridge (Carter–Pollard 2004 §3 Step 2) -/
```

---

## 5. Risks and forecasts

| Risk | Probability | Mitigation |
|---|---|---|
| `Finset.coe_filter` unfolding doesn't reach `{i \| k ≤ i.val}` cleanly | low | wrap with `Set.ext` + `Finset.mem_filter` if needed |
| `Fin.val_rev` doesn't simp out `(Fin.last m - i).val` | low | use `Fin.last_sub` + `Fin.val_rev` explicitly, no `simp` reliance |
| NNReal `(1 - p)^k` ↔ ℝ `(1 - (p:ℝ))^k` coercion misalignment | medium | first cycle: try `push_cast`; if stuck, manual `NNReal.coe_sub` |
| Re-indexing `F` (Fin) → `Ico k (m+1)` (ℕ) sum mismatch | medium | use `Finset.sum_bij` with `i ↦ i.val` and explicit inverse `j ↦ ⟨j, h⟩` |
| Build cache invalidation (no — TC9 already green, no Mathlib pin bump) | none | n/a |

**Build-cycle forecast**: 2–3 cycles. T2.1 likely 1 cycle; T2.2 likely 1–2
cycles due to coercion friction. No `lake update`, no pin bump → no
cross-track FS coordination needed.

**Closure tier**: real, additive. TC10 adds 2 Full theorems
(`stirling_prefactor_bound`, `binomialPolyTail_eq_pmf_tail`) plus auxiliary
lemmas. No Stub retirement (Carter–Pollard chain assembly Step 3+ deferred
to TC11+). Project-level sorry count unchanged. Per V1 framing: this is
**infra round, NOT closure**; do not export closure-tier language to
user-facing artifacts.

---

## 6. Out-of-scope (re-assert from brief)

- Step 3+ of Carter–Pollard chain.
- KMT-coupling integration with the bridge.
- GLW small-ball connection (`gao_li_wellner_small_ball_*`, Track A R59+).
- `BACKGROUND.md` updates (Track C status doc only).
- Asymptotic sharpness lemma `stirling_prefactor_isEquivalent` (Route B, deferred).

---

## 7. Uncertainty flags (per Track C feedback memory)

- **Paper recheck (§1)**: I do not have direct access to the Carter–Pollard
  2004 *Annals of Statistics* paper ("Tusnády's inequality revisited"); the
  rationale "explicit bound > asymptotic" is reconstructed from standard
  KMT-coupling practice. If TC11+ assembly reveals the asymptotic form is
  also needed, add `stirling_prefactor_isEquivalent` then.
- **Citation correction**: an earlier draft of this audit (and the TC10
  brief) referenced "Carter–Pollard 1986" — that date is incorrect. The
  paper everyone calls "Carter–Pollard" in the Tusnády/KMT context is
  Carter & Pollard (2004), *Annals of Statistics* 32(6), 2731–2741, DOI
  10.1214/009053604000000733. The rest of `TrackCStatus.md` (TC3+) and the
  `BinomialTailBeta.lean` docstrings consistently use "2004"; this audit
  is now aligned.
- **Bridge target form (§4.2)**: chose `p : ℝ≥0` for cleaner statement.
  Brief allows `p : ℝ` with `Subtype.mk`. If a downstream consumer needs
  the `p : ℝ` form, add a `_real` variant in TC11+.
- **Re-indexing sub-step (§4.2 step 4)**: rated "medium risk" because
  `Finset.sum_bij` + Fin/ℕ coercions historically need 10–20 LOC of
  bookkeeping. If first cycle stalls, alternate path via
  `Finset.sum_fin_eq_sum_range` is documented.

End audit.
