# Commission 2 — gamma-divisors — Tiers 4–6

Builds on the Commission 1 return (Tiers 1–3 closed, sorry-free, clean
axioms). Toolchain and Mathlib are now pinned: `leanprover/lean4:v4.28.0`,
Mathlib `v4.28.0` (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`),
manifest committed at `lean/lake-manifest.json`. Develop against exactly
that pair.

## Scope and priority

Targets live in `commissions/roadmap-tiers-4-6.lean`, deliberately outside
`lean/` so that CI's sorry audit stays meaningful: only proved material
enters the build. Attempt in this order:

1. **Tier 6a** `tendsto_rate_gamma_seq` — `n²(γ − γₙ) → 2/3`.
2. **Tier 6b** `tendsto_average_window_difference` — the γ-free window
   difference tends to `0`.
3. **Tier 5** `tendsto_average_Zhalf_open`, `tendsto_average_Zhalf_closed`.
4. **Tier 4** `tendsto_average_Z` — the headline theorem.

Tier 4 is the hard target and is expected to consume most of the round; the
ordering front-loads the results that are likely to close, and Tiers 5 and 6b
build machinery Tier 4 reuses. Partial returns are acceptable: report exactly
which targets closed, and leave the rest with `sorry` rather than weakening a
statement. **No in-scope statement may be altered.** If a statement is false
or unprovable as written, stop and report the obstruction with a
counterexample or the precise blocking step.

## Reusable assets from Commission 1

- `sum_card_divisors_le` — the counting identity; the workhorse.
- `tendsto_div_div : (⌊B/d⌋ : ℝ)/B → 1/d` for fixed `d ≠ 0`.
- `tendsto_sum_div`, `harmonic_eq_sum_Icc`, `card_divisors_split`,
  `filter_divisors_le`, `sum_indicator_dvd`, `tendsto_nat_sqrt_atTop`,
  `tendsto_log_sqrt_gap`.

Name-drift corrections already established (do not re-derive):
`Finset.card_filter_add_card_filter_not` (not the deprecated
`filter_card_add_filter_neg_card_eq_card`), `div_le_div_iff₀`,
`Nat.sqrt_le'` / `Nat.lt_succ_sqrt'` stated with `^ 2`,
`Finset.Ioc 0 B = Finset.Icc 1 B` by `rfl`.

## Tier 6a — the rate `n²(γ − γₙ) → 2/3`

Paper reference: Proposition 7.

`γₙ = H_{n−1} + H_n − H_{n²} = 2H_n − 1/n − H_{n²}`. The proof needs the
second-order expansion `H_m = log m + γ + 1/(2m) − 1/(12m²) + O(m⁻⁴)`, which
Commission 1 did **not** need and which may not exist in Mathlib in usable
form. Census first:

- Search for Euler–Maclaurin / Stirling-adjacent expansions of `harmonic`.
  Mathlib has `Real.tendsto_harmonic_sub_log` and bracketing sequences
  (`eulerMascheroniSeq`, `eulerMascheroniSeq'`) but likely nothing to
  second order.
- If no expansion exists, the cheapest self-contained route is
  `H_m − log m − γ = ∑_{k>m} (1/k − log(1 + 1/k)) + (something telescoping)`;
  more practically, define `δ_m = H_m − log m − γ` and prove
  `δ_m = 1/(2m) + O(m⁻²)` from
  `δ_m − δ_{m+1} = log(1 + 1/m) − 1/(m+1)` and summation of the resulting
  series, using `Real.abs_log_sub_add_sum_range_le` or the alternating-series
  machinery for `log(1+x)`.

Report the census result explicitly before committing to a route. If the
required expansion turns out to be a multi-thousand-line project in itself,
say so and return the tier unclosed rather than burning the round on it.

Note the shape of the cancellation, which is the point of the statement:
`2·(1/(2n)) − 1/n = 0` kills the first-order term, and
`2·(−1/(12n²)) − 1/(2n²) = −2/(3n²)` supplies the constant. Any correct route
must reproduce exactly this.

## Tier 6b — the γ-free window difference

Paper reference: Corollary 4. Statement: the average over `q ≤ B` of
`#{d ∣ q : q < d⁴ ∧ d² < q} − 2·#{d ∣ q : q < d⁸ ∧ d⁴ < q}` tends to `0`.

Strategy: prove the threshold law (paper Theorem 2) in the form actually
needed, for the two exponents `c = 1/4` and `c = 1/8`, phrased through
integer powers so no real exponentiation appears:

- `d⁴ < q` encodes `d < q^{1/4}`; `d⁸ < q` encodes `d < q^{1/8}`;
  `d² < q` encodes `d < q^{1/2}`.
- By the divisor–codivisor swap (`Lemma 1` of the paper, i.e.
  `sum_card_divisors_le`'s pair form), `d⁴ < q = de ⟺ d³ < e`, and
  `d⁸ < q ⟺ d⁷ < e`. So
  `∑_{q≤B} #{d ∣ q : d⁴ < q} = ∑_{d ≤ ⌊B^{1/4}⌋} (⌊B/d⌋ − d³) + O(B^{1/4})`,
  and similarly with `d⁷` and `⌊B^{1/8}⌋`.
- Then `∑_{d≤D} d³ = D⁴/4 + O(D³)` (`Finset.sum_range_pow` or direct
  induction; a `Gauss`-style closed form for cubes exists in Mathlib) and
  `D = ⌊B^{1/4}⌋` gives `D⁴ = B + O(B^{3/4})`.
- The `log` terms cancel between the two windows, as do the `γ` terms; what
  remains is the constant, `(1/4)·1 − 2·(1/8)·1 = 0`.

A useful intermediate, worth naming: for fixed `k ≥ 1`,
`(∑_{q≤B} #{d ∣ q : d^{k+1} < q})/B − (1/(k+1))·log B → γ − 1/(k+1)`.
Proving this general-`k` lemma once serves Tiers 6b, 5 and 4.

## Tier 5 — scaled windows at α = 1/2

Paper reference: Theorem 5 with `α = 1/2`, `K = 2`, `K' = 1`.

Both statements share the count `#{d ∣ q : 2d² < q}`; they differ only in
`2d < q` versus `2d ≤ q`. Proof shape:

- `2d² < q = de ⟺ 2d < e`, so
  `∑_{q≤B} #{d ∣ q : 2d² < q} = ∑_{d} (⌊B/d⌋ − 2d)` over `d` with `2d² < B`,
  giving `B·H_D − D² + O(√B)` with `D ≈ √(B/2)`; the `D²` term contributes
  `−B/2`.
- `d ≥ q/2 ⟺ e ≤ 2`, so `#{d ∣ q : 2d < q} = τ(q) − #{e ∣ q : e ≤ 2} − ρ(q)`
  where `ρ(q) = 1` iff `2 ∣ q` (the divisor `d = q/2` exactly). This is where
  the two conventions part: the closed window absorbs `ρ`, the open one does
  not, and `∑_{q≤B} ρ(q) = ⌊B/2⌋ ~ B/2`.
- Dirichlet's asymptotic `∑_{q≤B} τ(q) = B log B + (2γ−1)B + O(√B)` is
  needed. Census Mathlib for it; if absent, derive it by the hyperbola
  method from `sum_card_divisors_le` — the paper's Lemma 3 proof is short and
  translates directly, using `tendsto_two_harmonic_sqrt_sub_harmonic` from
  Commission 1 for the harmonic part.

The pair of theorems is the formal content of the endpoint erratum, so
closing **both** matters more than closing either: their difference must come
out to exactly `1/2`.

## Tier 4 — the headline theorem

Paper reference: Theorem 3, specialized to `F(q) = √q`.

`Z q = #{d ∣ q : d⁴ < q} − #{d ∣ q : q ≤ d⁴ ∧ d² < q}`. As in the paper,
`Z q = 2·#{d ∣ q : d⁴ < q} − #{d ∣ q : d² < q}` exactly (every `d` with
`d⁴ < q` also has `d² < q`, since `q ≥ 1`); prove this pointwise identity
first, as a named lemma — it is the single most important reduction and it
is purely combinatorial.

Then apply the general-`k` threshold lemma from Tier 6b at `k = 3` and
`k = 1`:
```
(1/B)·∑ Z → 2·(1/4·log B + γ − 1/4) − (1/2·log B + γ − 1/2) = γ.
```
The `log B` terms cancel (`2·(1/4) − 1/2 = 0`) and the constants give
`2γ − γ − 1/2 + 1/2 = γ`. Note that the paper's general-`F` proof (with the
counting inverse `R` and the boundary lemma) is **not** needed here: the
`F(q) = √q` case is exactly Remark 4 of the paper, which routes through the
threshold law. Do not formalize the general-`F` argument this round.

## Session protocol

- Fresh session; all state in the tarball; this file plus the repo constitute
  the round's inputs.
- Census before manual work; report all name drift against the corrections
  listed above.
- Closure claim only as: compiled + clean `#print axioms`. Extend
  `lean/GammaDivisors/Audit.lean` with a `#print axioms` line for each newly
  closed target, and update the CI target list in
  `.github/workflows/verify.yml` to match.
- Place **closed** targets in `lean/GammaDivisors/Roadmap.lean` (a new file,
  imported from `lean/GammaDivisors.lean`), and leave any target still open
  in `commissions/roadmap-tiers-4-6.lean` with its `sorry`. Nothing carrying
  a `sorry` may enter `lean/`. Name every open target in the return note.
- Return: full tarball, build log, `#print axioms` output, census/drift
  report, and an explicit per-target status table.

## Numerical anchors (B = 4·10⁵ unless noted)

| target | computed | expected limit |
|---|---|---|
| Tier 4 average of `Z` | 0.57770 | γ = 0.57722 |
| Tier 5 open | 0.80685 | 3/2 − log 2 = 0.80685 |
| Tier 5 closed | 0.30685 | 1 − log 2 = 0.30685 |
| Tier 6b difference | −0.047 (slow, oscillating) | 0 |
| Tier 6a, n = 3000 | 0.66667 | 2/3 |

The Tier 6b anchor converges slowly and changes sign; treat a small nonzero
value at finite `B` as consistent with the limit, not as evidence against it.
