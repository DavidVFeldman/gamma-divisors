/-
Commission 2 targets: Tiers 4-6.

Statements only; bodies to be supplied per commissions/commission-02.md.
This file is deliberately OUTSIDE lean/ so that CI's sorry audit stays
meaningful: only proved material enters the build. The Commission 2 return
places the closed targets in lean/GammaDivisors/Roadmap.lean and leaves any
target still open here. Statements must not be altered.
-/
import Mathlib

open Finset Filter Real Topology

namespace GammaDivisors

/-! ### Tier 4: the main theorem, concrete instance F(q) = √q
    (thresholds q^{1/4} and q^{1/2}, phrased through fourth and second powers) -/

/-- Divisors below the fourth root, minus divisors between the fourth root
and the square root. -/
noncomputable def Z (q : ℕ) : ℤ :=
  (#{d ∈ q.divisors | d ^ 4 < q} : ℤ) - #{d ∈ q.divisors | q ≤ d ^ 4 ∧ d ^ 2 < q}

/-- On average a number has exactly `γ` more divisors below its fourth root
than between its fourth root and its square root. -/
theorem tendsto_average_Z :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Z q : ℝ)) / B)
      atTop (𝓝 eulerMascheroniConstant) := by
  sorry

/-! ### Tier 5: windows on the scale of q at α = 1/2, both endpoint conventions.
    Thresholds √(q/2) and q/2, phrased through 2d² vs q and 2d vs q. -/

/-- Open right endpoint: divisors below `√(q/2)` minus divisors strictly
between `√(q/2)` and `q/2`. -/
noncomputable def Zhalf_open (q : ℕ) : ℤ :=
  (#{d ∈ q.divisors | 2 * d ^ 2 < q} : ℤ) -
    #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d < q}

/-- Closed right endpoint: the window `(√(q/2), q/2]`. -/
noncomputable def Zhalf_closed (q : ℕ) : ℤ :=
  (#{d ∈ q.divisors | 2 * d ^ 2 < q} : ℤ) -
    #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d ≤ q}

/-- Open convention: the average tends to `H₂ − log 2 = 3/2 − log 2`. -/
theorem tendsto_average_Zhalf_open :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Zhalf_open q : ℝ)) / B)
      atTop (𝓝 (3 / 2 - Real.log 2)) := by
  sorry

/-- Closed convention: the average tends to `H₁ − log 2 = 1 − log 2`.
Together with `tendsto_average_Zhalf_open` this verifies that the two
endpoint conventions differ in the limit by exactly `1/2`. -/
theorem tendsto_average_Zhalf_closed :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Zhalf_closed q : ℝ)) / B)
      atTop (𝓝 (1 - Real.log 2)) := by
  sorry

/-! ### Tier 6 (stretch): the rate of the logarithm-free approximation,
    and the γ-free window law -/

/-- `γₙ := H_{n−1} + H_n − H_{n²}` satisfies `n²(γ − γₙ) → 2/3`. -/
theorem tendsto_rate_gamma_seq :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 *
        (eulerMascheroniConstant -
          ((harmonic (n - 1) : ℝ) + (harmonic n : ℝ) - (harmonic (n ^ 2) : ℝ))))
      atTop (𝓝 (2 / 3)) := by
  sorry

/-- γ-free window law, concrete instance: on average, a number has twice as
many divisors in `(q^{1/4}, q^{1/2})` as in `(q^{1/8}, q^{1/4})`; the
difference of the two averages tends to `0`. -/
theorem tendsto_average_window_difference :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B,
        ((#{d ∈ q.divisors | q < d ^ 4 ∧ d ^ 2 < q} : ℝ) -
          2 * #{d ∈ q.divisors | q < d ^ 8 ∧ d ^ 4 < q})) / B)
      atTop (𝓝 0) := by
  sorry

end GammaDivisors
