# gamma-divisors

Companion repository for the paper *Divisors in windows and the
Euler–Mascheroni constant* (D. V. Feldman), with a Lean 4 / Mathlib
formalization campaign.

## Results

For 0 < c < 1, the number of divisors of q below q^c averages, over q ≤ B,
to c·log B + (γ − c) + O(B^(−min(c,1−c))). Consequences:

- **Window law** (γ-free): the average number of divisors in (q^a, q^b) is
  (b − a)(log B − 1) + o(1); average counts for two windows stand in the
  ratio of exponent lengths. In particular, a number has on average twice
  as many divisors in (n^(1/4), n^(1/2)) as in (n^(1/8), n^(1/4)).
- **γ as an average discrepancy**: for weakly increasing F with F(q) → ∞
  and q/F(q) → ∞, a number q has on average exactly γ more divisors below
  √F(q) than in [√F(q), F(q)). Endpoint-convention-free.
- **Windows on the scale of q**: for α ∈ (0,1), the discrepancy for the
  window from √(αq) to αq tends to H_⌊1/α⌋ − log(1/α) (right endpoint
  open) or H_⌈1/α⌉−1 − log(1/α) (right endpoint closed); the constants
  differ exactly when 1/α is an integer, and then by α. Mean value over
  α ∈ (0,1): ζ(2) − 1.
- **Rate**: γ_n := Σ_{k<n} 1/k − Σ_{n<k≤n²} 1/k satisfies
  γ − γ_n = (2/3)n^(−2) + O(n^(−4)).

## Layout

- `paper/divisor-windows.tex` — the paper (self-contained; compiles with
  pdflatex, 9 pp.)
- `paper/cover-letter.txt` — submission cover letter draft
- `lean/` — Lake project; `GammaDivisors/Targets.lean` holds the
  Commission 1 targets (Tiers 1–3)
- `commissions/commission-01.md` — work order for Commission 1 (returned, closed)
- `commissions/commission-02.md` — work order for Commission 2 (Tiers 4–6, open)
- `commissions/returns/commission-01-return.md` — Aristotle's return note
- `commissions/roadmap-tiers-4-6.lean` — Tier 4–6 statements, held outside
  the build until proved (only proved material enters `lean/`)
- `.github/workflows/verify.yml` — CI: lake build, sorry audit (excluding
  `.lake/`), axiom audit (sed-parsed; only `propext`, `Classical.choice`,
  `Quot.sound` accepted), audit artifacts uploaded

## Verification policy

A tier counts as closed only when its theorem compiles and shows a clean
`#print axioms`. Aristotle sessions are fresh per round with all state in
the round tarball; tarballs are ground truth.

Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`), with `lake-manifest.json`
committed for reproducibility.

## Tier ladder

| tier | statement | status |
|---|---|---|
| 1 | Counting identity: Σ_{q≤B} #{d ∣ q : d ≤ a} = Σ_{d≤a} ⌊B/d⌋ | **closed** |
| 2 | Fixed-window law: average → 2H_a − H_b | **closed** |
| 3 | Harmonic bridge: 2H_⌊√T⌋ − H_T → γ | **closed** |
| 4 | Main theorem, F(q) = √q: average of Z → γ | open |
| 5 | α = 1/2 scaled windows, both conventions (→ 3/2 − log 2, → 1 − log 2) | open |
| 6 | Rate n²(γ − γ_n) → 2/3; γ-free window difference → 0 | open |

Tiers 1–3 close Commission 1: proved sorry-free, each depending only on
`propext`, `Classical.choice`, `Quot.sound`. Tiers 4–6 remain in
`commissions/roadmap-tiers-4-6.lean`, outside the build.

## Numerical anchors (B = 4·10⁵ unless noted)

| quantity | computed | target |
|---|---|---|
| avg Z, F(q) = √q | 0.57770 | γ = 0.57722 |
| α = 1/2, open window | 0.80685 | 3/2 − log 2 = 0.80685 |
| α = 1/2, closed window | 0.30685 | 1 − log 2 = 0.30685 |
| fixed window (5, 30) | 0.57171 | 2H₅ − H₃₀ = 0.57168 |
| n²(γ − γ_n), n = 3000 | 0.66667 | 2/3 |

## Archive

Zenodo DOI: (to be minted on first release)
