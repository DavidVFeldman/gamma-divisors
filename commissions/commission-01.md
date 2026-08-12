# Commission 1 — gamma-divisors — Tiers 1–3

## Scope

Prove, sorry-free with clean `#print axioms`, the first three targets in
`lean/GammaDivisors/Targets.lean`:

1. `sum_card_divisors_le` (Tier 1, counting identity)
2. `tendsto_average_Zfix` (Tier 2, fixed-window law)
3. `tendsto_two_harmonic_sqrt_sub_harmonic` (Tier 3, harmonic bridge)

Tiers 4–6 are OUT OF SCOPE for this commission. Do not attempt them.
Statements of in-scope targets must not be altered; if a statement is
unprovable as written, report the obstruction instead of changing it.

## Mathlib census (verified against master, August 2026)

- `Nat.Ioc_filter_dvd_card_eq_div : #{x ∈ Ioc 0 n | p ∣ x} = n / p`
  (Mathlib.Data.Nat.Factorization.Basic) — the key primitive for Tier 1.
- `harmonic : ℕ → ℚ` (Mathlib.NumberTheory.Harmonic.Defs).
- `Real.eulerMascheroniConstant`, `Real.tendsto_harmonic_sub_log`,
  `Real.eulerMascheroniSeq`, monotonicity lemmas
  (Mathlib.NumberTheory.Harmonic.EulerMascheroni).
- `Nat.divisors`, `Nat.mem_divisors`, `Nat.filter_dvd_eq_divisors`
  (Mathlib.NumberTheory.Divisors).

## Proof strategies

### Tier 1 — `sum_card_divisors_le`

Double counting. Both sides count pairs `(q, d)` with `1 ≤ q ≤ B`,
`d ∣ q`, `d ≤ a` (note `d ∣ q` with `q ≥ 1` forces `d ≥ 1` and `d ≤ q ≤ B`;
divisors `d ∈ (B, a]` on the right side contribute `B / d = 0`).
Recommended route: rewrite the left side with
`Finset.card_filter`-style indicator sums, swap the order of summation
(`Finset.sum_comm` after reindexing through
`Finset.sum_sigma` or a direct bijection), and finish the inner count with
`Nat.Ioc_filter_dvd_card_eq_div` after transporting `Icc 1 B` to `Ioc 0 B`
(`Nat.Icc_succ_left` / `Finset.Icc 1 B = Finset.Ioc 0 B`).

Named-hole discipline: if decomposition is needed, acceptable holes are
strictly smaller statements, e.g. the single-`d` identity
`∑ q ∈ Icc 1 B, (if d ∣ q then 1 else 0) = B / d`.

### Tier 2 — `tendsto_average_Zfix`

Reduce to Tier 1. With `hab : a ≤ b`:

- `#{d ∈ q.divisors | a < d ∧ d ≤ b} = #{d ∈ q.divisors | d ≤ b} − #{d ∈ q.divisors | d ≤ a}`
  (filter of a filter; the sets nest).
- Hence `∑_{q ≤ B} Zfix a b q = 2·(∑ d ∈ Icc 1 a, B/d) − (∑ d ∈ Icc 1 b, B/d)` (over ℤ).
- For fixed `d`, `(B / d : ℝ) / B → 1/d` (floor-division estimate
  `B/d ≤ B·(1/d) < B/d + 1`; squeeze). Finite sums of limits:
  `(∑ d ∈ Icc 1 m, (B/d : ℝ))/B → (harmonic m : ℝ)`.
- Assemble with `Tendsto.sub`, `Tendsto.const_mul`.

Cast note: `harmonic` is ℚ-valued; the target uses `((harmonic m : ℚ) : ℝ)`
via the coercion in the statement. Keep the identity
`(harmonic m : ℝ) = ∑ d ∈ Icc 1 m, (1 : ℝ)/d` available
(`harmonic` is defined over `range` with `i+1`; reindex once, early).

### Tier 3 — `tendsto_two_harmonic_sqrt_sub_harmonic`

Pure analysis. Write, for `T ≥ 1`,

  2·H_{⌊√T⌋} − H_T
    = 2·(H_{⌊√T⌋} − log ⌊√T⌋) − (H_T − log T) + log(⌊√T⌋² / T).

- `Real.tendsto_harmonic_sub_log` gives the first two limits (γ and γ,
  hence contribution 2γ − γ = γ). Compose with `Nat.sqrt` tendsto atTop
  (`Nat.sqrt` tends to atTop; `Filter.Tendsto.comp`).
- `log(⌊√T⌋² / T) → 0`: from `Nat.sqrt_le'` and `Nat.lt_succ_sqrt'`,
  `⌊√T⌋² ≤ T < (⌊√T⌋+1)²`, so the ratio lies in `((√T/(√T+1))², 1]`;
  squeeze the log.

Watch the `T = 0` and small-`T` cases: all statements are `atTop`, so
restrict via `Filter.eventually_atTop` with `T ≥ 1` before rewriting logs.

## Session protocol

- Fresh Aristotle session; all state in the tarball; this file plus
  `Targets.lean` constitute the round's inputs.
- Census first: `exact?`/`apply?` against Mathlib before writing manual
  proofs; report any name drift from the census above.
- Closure claim only as: compiled + clean `#print axioms` for each of the
  three targets (expected axioms: `propext`, `Classical.choice`, `Quot.sound`).
- Return: full tarball, build log, `#print axioms` output.

## Numerical anchors (sanity, not proof)

- Tier 2 at (a,b) = (5,30), B = 4·10⁵: average 0.57171 vs 2H₅ − H₃₀ = 0.57168.
- Tier 3: 2H_{⌊√T⌋} − H_T at T = 10⁶: 0.57772 vs γ = 0.57722.
