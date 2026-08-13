# Commission 2 return — gamma-divisors, Tiers 4–6

All five in-scope targets from `gamma-divisors-extract/commissions/roadmap-tiers-4-6.lean`
are proved sorry-free with a clean `#print axioms`. No in-scope statement was
altered: the theorem and definition signatures are character-for-character the
ones in the roadmap file.

## Where the work lives

Buildable in this project (`lake build`, all files are default targets):

- `RequestProject/GammaDivisors/Counting.lean` — divisor/codivisor counting
  infrastructure (reflection identity, splitting of divisor counts by powers).
- `RequestProject/GammaDivisors/Asymptotics.lean` — the master asymptotic for
  truncated divisor sums `∑_{d ≤ B}(⌊B/d⌋ − c d^{j−1})`.
- `RequestProject/GammaDivisors/Tier4.lean` — `Z`, `tendsto_average_Z`.
- `RequestProject/GammaDivisors/Tier5.lean` — `Zhalf_open`, `Zhalf_closed`,
  `tendsto_average_Zhalf_open`, `tendsto_average_Zhalf_closed`.
- `RequestProject/GammaDivisors/Tier6Window.lean` — `tendsto_average_window_difference`.
- `RequestProject/GammaDivisors/Tier6Rate.lean` — `tendsto_rate_gamma_seq`.
- `RequestProject/GammaDivisors/Audit.lean` — the `#print axioms` audit for all
  eight commissioned targets (Commissions 1 and 2).

The same files are mirrored into `gamma-divisors-extract/lean/GammaDivisors/`
(with `RequestProject.GammaDivisors.X` imports rewritten to `GammaDivisors.X`),
and `gamma-divisors-extract/lean/GammaDivisors.lean` imports them all. The
toolchain/Mathlib pins are those fixed in Commission 1:
`leanprover/lean4:v4.28.0` with Mathlib at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

## Axiom audit output

```
'GammaDivisors.tendsto_average_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'GammaDivisors.tendsto_average_Zhalf_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'GammaDivisors.tendsto_average_Zhalf_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'GammaDivisors.tendsto_rate_gamma_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
'GammaDivisors.tendsto_average_window_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Proof outline (as executed)

**Counting layer.** For `q ≥ 1` the divisor/codivisor involution `d ↦ q/d`
gives `#{d ∣ q : d^j < q} + #{d ∣ q : q < d^j …}` splittings; the two basic
facts used throughout are

* `card_divisors_split_pows`: for `i ≤ j`, `#{d ∣ q : d^i < q}` splits as
  `#{d ∣ q : d^j < q} + #{d ∣ q : q ≤ d^j ∧ d^i < q}`, so each tier's signed
  count is `2·Ndiv j q − Ndiv i q` with `Ndiv j q := #{d ∣ q : d^j < q}`;
* `sum_Ndiv`: `∑_{q ≤ B} Ndiv j q = ∑_{d} (⌊B/d⌋ − …)`, obtained by swapping the
  order of summation over the pairs `(d, q)` with `d ∣ q`.

**Asymptotic layer.** The master theorem `tendsto_S` states, for `c ≥ 1`,
`j ≥ 2`, that
`S c j B / B − ((1/j)(log B − log c) + γ − 1/j) → 0`,
where `S c j B = ∑_{d ≤ B}(⌊B/d⌋ − c·d^{j−1})` truncated at the threshold
`c d^j + d ≤ B`. The proof combines `|∑_{d ≤ x} ⌊B/d⌋/B − H_x| = O(x/B)`,
Bernoulli-type bounds for `∑ d^{j−1}`, and `H_m − log m → γ`.

**Tier 4.** `Z q = 2·Ndiv 4 q − Ndiv 2 q`; summing and inserting the master
theorem twice, the `log B` terms cancel and the average tends to `γ`.

**Tier 5.** The same scheme at scale `α = 1/2` with thresholds `2d² < q` and
`2d ≶ q`; the two endpoint conventions differ by the count of `d` with
`2d = q`, whose average is `1/2`. Limits: `3/2 − log 2` (open) and
`1 − log 2` (closed).

**Tier 6, window law.** With `Wdiv i j q := #{d ∣ q : q < d^j ∧ d^i < q}` one has
`Wdiv i j q = Ndiv i q − Ndiv j q − (endpoint count)`, so the signed combination
`Wdiv 2 4 q − 2·Wdiv 4 8 q` sums to `S 1 2 B − 3·S 1 4 B + 2·S 1 8 B` up to
endpoint terms that are `O(√B)`. In the master asymptotic the three
contributions carry weights `1, −3, 2` at `j = 2, 4, 8`, and
`1/2 − 3/4 + 2/8 = 0` while `1 − 3 + 2 = 0`, so both the `log B` terms and the
constant terms (`γ` included) cancel, leaving limit `0`.

**Tier 6, rate theorem.** With `a_m := H_m − log m − γ` one has
`γ − γ_n = 1/n + a_{n²} − 2a_n` (using `H_{n−1} = H_n − 1/n`). Write
`y m := H_m − log m − 1/(2m) + 1/(12m²)` and `c m := y m − γ`; then

```
n²(γ − γ_n) − 2/3 = −1/(12n²) − 2n²·c n + n²·c (n²).
```

The key input is `|c m| ≤ 10/m³` for `m ≥ 2` (`abs_yseq_sub_gamma`), proved by a
monotonicity sandwich: `y m − 10/m³` is monotone and `y m + 10/m³` antitone from
`m = 2` on, and both tend to `γ`, so `Monotone.ge_of_tendsto` /
`Antitone.le_of_tendsto` trap `γ` between them. The step inequality
`|y(m+1) − y(m)| ≤ 10/m³ − 10/(m+1)³` follows from the cubic Taylor bound
`|log(m+1) − log m − (1/m − 1/(2m²) + 1/(3m³))| ≤ 2/m⁴` (from Mathlib's
`Real.abs_log_sub_add_sum_range_le` with `x = −1/m`, `n = 3`) plus an explicit
rational inequality. This yields `|n²(γ − γ_n) − 2/3| ≤ 31/n` for `n ≥ 2`
(`rate_bound`), and the limit follows by squeezing.

## Name drift observed against the pinned Mathlib

- `div_le_div_iff` → `div_le_div_iff₀`.
- `Finset.filter_card_add_filter_neg_card_eq_card` → `Finset.card_filter_add_card_filter_not`.
- `Finset.card_insert_of_not_mem` is no longer the convenient form; `simp` handles
  the insertions used here.
- `Real.abs_log_sub_add_sum_range_le` is present and stated exactly as in the
  census, with `log (1 - x)` (so the useful instance for `log(1 + t)` is `x = −t`).
- `Nat.findGreatest_spec` needs the predicate supplied explicitly (`(P := …)`).
