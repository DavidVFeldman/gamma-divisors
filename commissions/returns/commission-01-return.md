# Commission 1 return — gamma-divisors, Tiers 1–3

All three in-scope targets are proved sorry-free with clean `#print axioms`.
No in-scope statement was altered.

## Where the work lives

- `RequestProject/GammaDivisors/Targets.lean` — the proved targets (buildable
  in this project: `lake build RequestProject.GammaDivisors.Targets`).
- `RequestProject/GammaDivisors/Audit.lean` — the `#print axioms` audit.
- `gamma-divisors-extract/` — the commission tarball, unpacked, with
  `lean/GammaDivisors/Targets.lean` replaced by the proved version, an
  `Audit.lean` added, and the toolchain/Mathlib pins fixed (see below).
  The original `gamma-divisors.zip` is left untouched.

## Toolchain / Mathlib fix

The provisional pin `leanprover/lean4:v4.22.0` was replaced by
`leanprover/lean4:v4.28.0`, with Mathlib pinned to `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`). The proofs were developed
and verified against exactly that pair.

## Axiom audit output

```
'GammaDivisors.sum_card_divisors_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'GammaDivisors.tendsto_average_Zfix' depends on axioms: [propext, Classical.choice, Quot.sound]
'GammaDivisors.tendsto_two_harmonic_sqrt_sub_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Census / name drift report

Verified against the pinned Mathlib:

- `Nat.Ioc_filter_dvd_card_eq_div` — present, as stated in the census; used for Tier 1.
- `harmonic`, `Real.eulerMascheroniConstant`, `Real.tendsto_harmonic_sub_log` — present as stated.
- `Nat.divisors`, `Nat.mem_divisors` — present.

Drift / corrections found while working:

- `Nat.Icc_succ_left` was not needed: `Finset.Ioc 0 B = Finset.Icc 1 B` holds by `rfl`.
- `Finset.filter_card_add_filter_neg_card_eq_card` is deprecated; the current name is
  `Finset.card_filter_add_card_filter_not` (used in `card_divisors_split`).
- `Nat.sqrt_le'` and `Nat.lt_succ_sqrt'` are stated with `^ 2`
  (`n.sqrt ^ 2 ≤ n`, `n < n.sqrt.succ ^ 2`), not with an explicit product.
- `div_le_div_iff` is now `div_le_div_iff₀`.

## Proof outline (as executed)

Tier 1: for `1 ≤ q`, `{d ∈ q.divisors | d ≤ a} = {d ∈ Icc 1 a | d ∣ q}`
(`filter_divisors_le`); rewrite the cardinality as an indicator sum over
`Icc 1 a`, swap the order of summation with `Finset.sum_comm`, and evaluate the
inner count with `Nat.Ioc_filter_dvd_card_eq_div` (`sum_indicator_dvd`).

Tier 2: `card_divisors_split` gives
`#{d ≤ a} + #{a < d ≤ b} = #{d ≤ b}` for `a ≤ b`, so `Zfix a b q = 2·#{d ≤ a} − #{d ≤ b}`;
summing and applying Tier 1 twice yields `sum_Zfix`. Then
`(⌊B/d⌋ : ℝ)/B → 1/d` by a squeeze between `1/d − 1/B` and `1/d`
(`tendsto_div_div`), and a finite sum of these limits gives
`tendsto_sum_div`, using `harmonic m = ∑_{d ∈ Icc 1 m} 1/d`.

Tier 3: `2 H_{s} − H_T = 2(H_s − log s) − (H_T − log T) − (log T − 2 log s)`
with `s = ⌊√T⌋`. `Real.tendsto_harmonic_sub_log`, composed with
`Nat.sqrt → ∞`, handles the first two terms (`2γ − γ = γ`). The gap
`log T − 2 log s` is squeezed between `0` (from `s² ≤ T`) and `2/s`
(from `T < (s+1)²` and `log(1 + 1/s) ≤ 1/s`), and `2/s → 0`.

Tiers 4–6 were not attempted, as instructed.
