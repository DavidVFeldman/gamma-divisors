/-
Tier 4 of the gamma-divisors campaign: the main theorem in the concrete instance
`F(q) = √q`.  On average a number has exactly `γ` more divisors below its fourth
root than between its fourth root and its square root.
-/
import Mathlib
import GammaDivisors.Counting
import GammaDivisors.Asymptotics

open Finset Filter Real Topology

namespace GammaDivisors

/-- Divisors below the fourth root, minus divisors between the fourth root
and the square root. -/
noncomputable def Z (q : ℕ) : ℤ :=
  (#{d ∈ q.divisors | d ^ 4 < q} : ℤ) - #{d ∈ q.divisors | q ≤ d ^ 4 ∧ d ^ 2 < q}

lemma Z_eq (q : ℕ) : Z q = 2 * (Ndiv 4 q : ℤ) - (Ndiv 2 q : ℤ) := by
  have h := card_divisors_split_pows q 2 4 (by norm_num)
  simp only [Z, Ndiv]
  omega

lemma sum_Ndiv_eq_S (j B : ℕ) (hj : 1 ≤ j) :
    ∑ q ∈ Icc 1 B, Ndiv j q = S 1 j B := by
  rw [sum_Ndiv j B hj, S]
  simp

lemma sum_Z (B : ℕ) :
    ∑ q ∈ Icc 1 B, (Z q : ℝ) = 2 * (S 1 4 B : ℝ) - (S 1 2 B : ℝ) := by
  have h4 : ∑ q ∈ Icc 1 B, Ndiv 4 q = S 1 4 B := sum_Ndiv_eq_S 4 B (by norm_num)
  have h2 : ∑ q ∈ Icc 1 B, Ndiv 2 q = S 1 2 B := sum_Ndiv_eq_S 2 B (by norm_num)
  calc ∑ q ∈ Icc 1 B, (Z q : ℝ)
      = ∑ q ∈ Icc 1 B, (2 * (Ndiv 4 q : ℝ) - (Ndiv 2 q : ℝ)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have := Z_eq q
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    _ = 2 * (∑ q ∈ Icc 1 B, (Ndiv 4 q : ℝ)) - ∑ q ∈ Icc 1 B, (Ndiv 2 q : ℝ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * (S 1 4 B : ℝ) - (S 1 2 B : ℝ) := by
        rw [← Nat.cast_sum, ← Nat.cast_sum, h4, h2]

/-- **Tier 4.** On average a number has exactly `γ` more divisors below its fourth
root than between its fourth root and its square root. -/
theorem tendsto_average_Z :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Z q : ℝ)) / B)
      atTop (𝓝 eulerMascheroniConstant) := by
  have h4 := tendsto_S 1 4 (by norm_num) (by norm_num)
  have h2 := tendsto_S 1 2 (by norm_num) (by norm_num)
  have hcomb := (h4.const_mul (2 : ℝ)).sub h2
  rw [show (2 : ℝ) * 0 - 0 = 0 by ring] at hcomb
  have hlim : Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Z q : ℝ)) / B
      - eulerMascheroniConstant) atTop (𝓝 0) := by
    refine hcomb.congr fun B => ?_
    rw [sum_Z B]
    simp only [Nat.cast_one, Real.log_one, Nat.cast_ofNat]
    ring
  have := hlim.add (tendsto_const_nhds (x := eulerMascheroniConstant) (f := (atTop : Filter ℕ)))
  simpa using this

end GammaDivisors
