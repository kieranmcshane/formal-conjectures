# R31 — Consumer audit of `two_dim_KMT_coupling` call-sites in `524.lean`

**Round**: R31 (Cowork, single round, V1)
**Task**: T1.1 — Read-only audit of every consumer of the public 2D-KMT
theorem in `FormalConjectures/ErdosProblems/524.lean`, to determine
whether the **decoupled paper-faithful form** (Y⁺ approximates only the
EVEN-indexed half of the plus-kernel sum, Y⁻ approximates only the
ODD-indexed half of the minus-kernel sum, Y⁺ ⫫ Y⁻ unconditionally) is a
**drop-in replacement** for the current full-sum + independence form.

**Verdict (front-loaded for the impatient reader)**: **NO** — the
decoupled form is consumer-incompatible. All four current consumers rely
on the FULL-sum form of the KMT coupling conjuncts (`hKMT_p`, `hKMT_m`)
to convert bounds on `|Y±|` to bounds on the FULL discrete sums
`Z±_full(u, ω) = (1/√n) ∑_{k=1..n} a_k ω · kernel±(u, k, n)`. Two of the
four additionally rely on `IndepFun (fun ω u => Y⁺ u ω) (fun ω u =>
Y⁻ u ω)` to factor `ℙ(Ep ∩ Em) = ℙ(Ep) · ℙ(Em)`. The conjunction
"Y± approximate the FULL sum within `O(log n / √n)` AND Y⁺ ⫫ Y⁻
unconditionally" is **mathematically impossible** (Grok pre-flight,
R31 brief), so the original public-axiom shape that consumers depend on
is contradictory in its content.

R31 therefore lands the mandatory floor (T1.1 + T2.1 + T2.2) and
**defers** the consumer-side rewrite (and the corresponding revision of
the public theorem statement) to R32. T2.1 and T2.2 stand as the
mathematical infrastructure required by that rewrite: they produce the
EVEN-half and ODD-half Gaussian witnesses that R32 will combine into
joint (correlated) `(Y⁺, Y⁻)` pairs that approximate the full sums
without claiming unconditional independence.

## Methodology

For each invocation of `two_dim_KMT_coupling a ha` in `524.lean`, the
audit records:

* **(a) Conjuncts extracted via `obtain`** — which of the 13 destructured
  binders (`Yplus, Yminus, Δ, hYp_meas, hYm_meas, hΔ_bd, hKMT_p,
  hKMT_m, hIndep, hYp_cont, hYm_cont, hYp_tail, hYm_tail`) are kept
  vs. discarded with `_`-prefixes.
* **(b) Downstream usage** — which extracted fields are then *actually
  used* in the proof body (vs. extracted-and-ignored).
* **(c) Decoupled-form compatibility** — whether the usage in (b) is
  preserved under the decoupled form, where `hKMT_p` says only that
  `Yplus u ω` approximates the **EVEN-indexed half** of the FULL
  plus-kernel sum (and similarly for `hKMT_m`), and where `hIndep` is
  unconditional independence of the corresponding half-sum Gaussians.

Read-only; no Lean modifications. Cross-referenced against the actual
proof bodies in `polynomial_sup_small_ball_{upper,lower}{,_uniform}`.

## Per-call-site audit

### Call-site 1 — `polynomial_sup_small_ball_upper` (524.lean:3914)

* `obtain` line: 524.lean:3924–3926.
* Extracted (kept): `Yplus`, `Δ`, `hYp_meas`, `hΔ_bd`, `hKMT_p`.
* Discarded with `_`: `_Yminus`, `_hYm_meas`, `_hKMT_m`, `_hIndep`,
  `_hYp_cont`, `_hYm_cont`, `_hYp_tail`, `_hYm_tail`.
* Downstream usage: `hKMT_p n hn ω u hu` is invoked as
  `|Yplus u ω - (1/√n) ∑_{k=1..n} a k ω · exp(-u·k/n)| ≤ Δ n` (the
  FULL-sum form), then a triangle inequality bound
  `|Yplus u ω| ≤ |Z⁺_full(u, ω)| + Δ n` is derived from a bound on the
  FULL sum (which itself comes from `endpoint_reparametrization` +
  `supNorm a n ω ≤ ε √n`). See the calc block at 524.lean:4154–4172
  (mirror in `_uniform`) for the exact triangle step.
* **Decoupled-form compatibility: NO.** Under the decoupled form,
  `hKMT_p` would say `|Yplus u ω - (1/√(n/2)) ∑_{k=1..n/2} a (2k) ω ·
  kernel_even_plus u k (n/2)| ≤ log(n/2 + 1) / √(n/2)`, i.e. a coupling
  between `Yplus` and the EVEN-indexed half-sum. The triangle bound
  `|Yplus u ω| ≤ |Z⁺_full(u, ω)| + Δ n` would no longer follow because
  `|Z⁺_even_half| ≤ |Z⁺_full|` is a one-sided inequality and is **not**
  what the consumer chains; the actual consumer chains the *opposite*
  direction (`|Z⁺_full| ≤ |Yplus| + Δ`) which would also break.

### Call-site 2 — `polynomial_sup_small_ball_upper_uniform` (524.lean:3994)

* `obtain` line: 524.lean:4079–4081.
* Extracted (kept): identical to call-site 1 (`Yplus`, `Δ`, `hYp_meas`,
  `hΔ_bd`, `hKMT_p`).
* Downstream usage: identical to call-site 1 (the body is a "replay"
  with the `N₀`-quantifier-pulled-out variant).
* **Decoupled-form compatibility: NO** (same analysis as call-site 1).

### Call-site 3 — `polynomial_sup_small_ball_lower` (524.lean:4213)

* `obtain` line: 524.lean:4227–4229.
* Extracted (kept, no `_` prefix): `Yplus`, `Yminus`, `Δ`, `hYp_meas`,
  `hYm_meas`, `hΔ_bd`, `hKMT_p`, `hKMT_m`, `hIndep`, `hYp_cont`,
  `hYm_cont`. Only the two tail-decay binders are dropped
  (`_hYp_tail`, `_hYm_tail`).
* Downstream usage:
  * `hKMT_p` / `hKMT_m` invoked as FULL-sum couplings (524.lean:4469
    and 4503), used in the *reverse-containment* triangle to derive
    `|Z±_full(u, ω)| ≤ |Y±(u, ω)| + Δ n ≤ δ + Δ n = ε` from
    `|Y±(u, ω)| ≤ δ` (the GLW small-ball lower-bound event).
  * `hIndep` invoked as `hIndep.measure_inter_preimage_eq_mul Ap Am
    hAp_meas hAm_meas` (524.lean:4423) to factor `ℙ(Ep ∩ Em) = ℙ(Ep) ·
    ℙ(Em)`, where `Ep` and `Em` are continuity-measurable pullbacks of
    the events `{∀ u ≥ 0, |Y±(u)| ≤ δ}` along `fun ω u => Y±(u, ω)`.
  * `hYp_cont` / `hYm_cont` used (524.lean:4412 / 4416) to reduce the
    uncountable intersection `∀ u ≥ 0, _` to a countable rational one
    (Pi-measurability prerequisite for the independence-factor step).
* **Decoupled-form compatibility: NO**, on **two** independent
  grounds:
  1. The FULL-sum coupling (used in the reverse-containment triangle)
     is the same incompatibility as call-sites 1–2.
  2. The independence factorization step requires `IndepFun (fun ω u =>
     Yplus u ω) (fun ω u => Yminus u ω)` for `Y±` that approximate the
     FULL sums. Under the decoupled form, the WITNESSES `Y±` for
     EVEN/ODD half-sums **are** independent; but a construction where
     the FULL-sum-approximating `Y±` are also independent is
     **mathematically impossible** (Grok pre-flight, R31 brief). So
     even if we lifted the decoupled half-sum Gaussians to full-sum
     approximants by `Y⁺_full := Y_even + Y_odd`,
     `Y⁻_full := Y_even - Y_odd` (the LS construction), independence
     between `Y⁺_full` and `Y⁻_full` would FAIL because `Cov =
     Var(Y_even) - Var(Y_odd) ≠ 0` in general.

### Call-site 4 — `polynomial_sup_small_ball_lower_uniform` (524.lean:4585)

* `obtain` line: 524.lean:4603–4605.
* Extracted: identical to call-site 3.
* Downstream usage: identical to call-site 3 (replay variant).
* **Decoupled-form compatibility: NO** (same two grounds as
  call-site 3).

## Aggregate verdict and impact

| Call-site | Uses FULL-sum `hKMT_*`? | Uses `hIndep`? | Decoupled-form drop-in? |
|-----------|------------------------|----------------|--------------------------|
| 3925 / `..._upper`           | Yes (Yplus side only) | No  | **No** |
| 4081 / `..._upper_uniform`   | Yes (Yplus side only) | No  | **No** |
| 4229 / `..._lower`           | Yes (both sides)      | Yes | **No** (two grounds) |
| 4605 / `..._lower_uniform`   | Yes (both sides)      | Yes | **No** (two grounds) |

**Aggregate**: 4 / 4 call-sites are **incompatible** with the decoupled
paper-faithful form as a drop-in replacement. The current public
`theorem two_dim_KMT_coupling` (524.lean:3741), which composes
full-sum couplings with unconditional `IndepFun (Y⁺, Y⁻)`, is the shape
the consumers were designed against — and Grok pre-flight has confirmed
that **shape** is mathematically impossible to discharge honestly.

## Implications for R31 strategy

The brief's stretch tasks T4.1 (revise `via_LS_reduction` statement to
the decoupled form) and T5.1 (update public `two_dim_KMT_coupling` to
match) are **gated** on consumer-compatibility (per brief §"R31
stretch", T5.1 is "**Gated on consumer audit (T1.1) verifying the
revised form is consumer-compatible.**" — and T4.1 cannot stand
without T5.1 because the public theorem at 524.lean:3741 is
`Helpers.two_dim_KMT_coupling_via_LS_reduction` directly, so any
signature change in the helper propagates to a build break in the
public file).

**The audit fails the gate.** Therefore:

* **T4.1 — DEFERRED.** Revising the helper statement to the decoupled
  form would either (a) break `524.lean`'s build (4 consumers), or
  (b) require simultaneously rewriting all 4 consumers — a scope that
  exceeds R31's single-round budget and was not pre-authorized in the
  brief.
* **T5.1 — DEFERRED.** Same reason as T4.1.
* **T3.1 — DEFERRED.** The existing `LS_independent_yplus_yminus` sorry
  (TwoDimKMTFromOneDim.lean:213) asserts independence of FULL-sum-
  approximating Y⁺/Y⁻, which is the impossible content. It cannot be
  closed honestly without first revising the surrounding statement to
  the decoupled form (T4.1) — and T4.1 is deferred. Closing T3.1 in
  the decoupled-form sense (`IndepFun` of the half-sum Gaussians) is
  mathematical content R32 will need, and the building blocks for
  *that* closure are landed by T2.1 + T2.2 of this round.

The mandatory floor (T1.1 + T2.1 + T2.2) lands as planned. The
substantive math result of R31 is that the EVEN/ODD Gaussian witnesses
are constructed and named (`LS_yplus_via_even`,
`LS_yminus_via_odd`) — these are the two halves R32 will combine into
joint correlated Y⁺/Y⁻ that approximate the full sums, with consumer-
side `IndepFun` use replaced by an explicit covariance / Cauchy–Schwarz
argument.

## R32 recommended trajectory (for the next round's brief)

1. **Document the impossibility honestly** in the public-theorem doc
   comment at 524.lean:3733 (or thereabouts): the original full-sum +
   unconditional-IndepFun form is mathematically over-stated, and the
   `via_LS_reduction` "discharge" is currently a `sorryAx`-bearing
   theorem.
2. **Choose between two corrections** (R32 design choice):
   * **(α) Joint-correlated form.** Revise the public theorem to: Y⁺
     and Y⁻ approximate the FULL sums with KMT rate `O(log n / √n)`,
     and (Y⁺, Y⁻) are jointly Gaussian with explicit cross-covariance
     `Var(Y_even) - Var(Y_odd)`. Drop the `IndepFun` claim. Rewrite
     consumer 3 and 4's product-factorization step using the explicit
     covariance bound (Cauchy–Schwarz-style). Consumers 1 and 2 are
     unaffected (they only use `Y⁺` side, no independence).
   * **(β) Decoupled form (paper-faithful).** Revise the public theorem
     to the EVEN-half / ODD-half decoupled form. Rewrite all 4
     consumers to use Y⁺_full := Y_even + Y_odd (jointly with the
     consumer's existing `endpoint_reparametrization` + supNorm
     identity), accepting that the resulting Y⁺_full / Y⁻_full pair is
     *not* independent — and refactor the small-ball-lower consumers
     to use a covariance-based factorization.
3. The mathematical infrastructure for either path is what T2.1 + T2.2
   land in this round.

R31 ends having (a) detected and named the math gap, (b) produced the
audit document that proves the gap is consumer-load-bearing, and
(c) landed the two half-sum Gaussian witnesses (T2.1 kernels + T2.2
axiom applications) that R32 will compose. Honesty over optics.

— end of R31 T1.1 audit —
