/-
Tier 6 (stretch), γ-free window law: on average a number has twice as many
divisors in `(q^{1/4}, q^{1/2})` as in `(q^{1/8}, q^{1/4})`; the difference of
the two averages tends to `0`.
-/
import Mathlib
import GammaDivisors.Counting
import GammaDivisors.Asymptotics
import GammaDivisors.Tier4

open Finset Filter Real Topology

namespace GammaDivisors

/-- The divisors of `q` strictly inside the window `(q^{1/j}, q^{1/i})`. -/
noncomputable def Wdiv (i j q : ℕ) : ℕ := #{d ∈ q.divisors | q < d ^ j ∧ d ^ i < q}

/-- The (at most one) divisor sitting exactly at the window endpoint `q^{1/j}`. -/
noncomputable def Ewin (i j q : ℕ) : ℕ := #{d ∈ q.divisors | d ^ j = q ∧ d ^ i < q}

lemma card_split_boundary (q i j : ℕ) :
    #{d ∈ q.divisors | q ≤ d ^ j ∧ d ^ i < q} = Wdiv i j q + Ewin i j q := by
  have e1 : {d ∈ q.divisors | q < d ^ j ∧ d ^ i < q}
      = {d ∈ ({d ∈ q.divisors | q ≤ d ^ j ∧ d ^ i < q}) | q < d ^ j} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    constructor
    · intro h
      exact ⟨⟨le_of_lt h.1, h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  have e2 : {d ∈ q.divisors | d ^ j = q ∧ d ^ i < q}
      = {d ∈ ({d ∈ q.divisors | q ≤ d ^ j ∧ d ^ i < q}) | ¬ (q < d ^ j)} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    simp only [not_lt]
    constructor
    · intro h
      exact ⟨⟨le_of_eq h.1.symm, h.2⟩, le_of_eq h.1⟩
    · intro h
      exact ⟨le_antisymm h.2 h.1.1, h.1.2⟩
  rw [Wdiv, Ewin, e1, e2]
  exact (Finset.card_filter_add_card_filter_not
    (s := {d ∈ q.divisors | q ≤ d ^ j ∧ d ^ i < q}) (p := fun d => q < d ^ j)).symm

lemma Wdiv_eq (q i j : ℕ) (hij : i ≤ j) :
    (Wdiv i j q : ℤ) = (Ndiv i q : ℤ) - (Ndiv j q : ℤ) - (Ewin i j q : ℤ) := by
  have h1 := card_divisors_split_pows q i j hij
  have h2 := card_split_boundary q i j
  simp only [Ndiv] at *
  omega

/-- The endpoint divisors are `o(B)`: their total over `q ≤ B` is at most `√B`. -/
lemma sum_Ewin_le (i j B : ℕ) (hj : 2 ≤ j) :
    ∑ q ∈ Icc 1 B, Ewin i j q ≤ Nat.sqrt B := by
  refine le_trans (Finset.sum_le_sum fun q _ => ?_)
    (sum_card_eq_le B (fun d => d ^ j) ?_ ?_)
  · exact Finset.card_le_card (Finset.monotone_filter_right _ (fun d _ h => h.1))
  · intro a b ha hb hab
    exact Nat.pow_left_injective (by omega) hab
  · intro d hd hdB
    have h1 : d * d ≤ d ^ j := by
      have h2 : d ^ 2 ≤ d ^ j := Nat.pow_le_pow_right hd hj
      nlinarith [h2]
    exact Nat.le_sqrt.2 (le_trans h1 hdB)

lemma sum_window_diff (B : ℕ) :
    ∑ q ∈ Icc 1 B, ((Wdiv 2 4 q : ℝ) - 2 * (Wdiv 4 8 q : ℝ))
      = ((S 1 2 B : ℝ) - 3 * (S 1 4 B : ℝ) + 2 * (S 1 8 B : ℝ))
        - (∑ q ∈ Icc 1 B, Ewin 2 4 q : ℕ) + 2 * (∑ q ∈ Icc 1 B, Ewin 4 8 q : ℕ) := by
  have key : ∀ q : ℕ, (Wdiv 2 4 q : ℝ) - 2 * (Wdiv 4 8 q : ℝ)
      = ((Ndiv 2 q : ℝ) - 3 * (Ndiv 4 q : ℝ) + 2 * (Ndiv 8 q : ℝ))
        - (Ewin 2 4 q : ℝ) + 2 * (Ewin 4 8 q : ℝ) := by
    intro q
    have h1 := Wdiv_eq q 2 4 (by norm_num)
    have h2 := Wdiv_eq q 4 8 (by norm_num)
    have h1' : (Wdiv 2 4 q : ℝ) = (Ndiv 2 q : ℝ) - (Ndiv 4 q : ℝ) - (Ewin 2 4 q : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
    have h2' : (Wdiv 4 8 q : ℝ) = (Ndiv 4 q : ℝ) - (Ndiv 8 q : ℝ) - (Ewin 4 8 q : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
    rw [h1', h2']
    ring
  rw [Finset.sum_congr rfl fun q _ => key q]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum,
    sum_Ndiv_eq_S 2 B (by norm_num), sum_Ndiv_eq_S 4 B (by norm_num),
    sum_Ndiv_eq_S 8 B (by norm_num)]

/-- **Tier 6 (γ-free window law).** On average a number has twice as many divisors
in `(q^{1/4}, q^{1/2})` as in `(q^{1/8}, q^{1/4})`. -/
theorem tendsto_average_window_difference :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B,
        ((#{d ∈ q.divisors | q < d ^ 4 ∧ d ^ 2 < q} : ℝ) -
          2 * #{d ∈ q.divisors | q < d ^ 8 ∧ d ^ 4 < q})) / B)
      atTop (𝓝 0) := by
  have h2 := tendsto_S 1 2 (by norm_num) (by norm_num)
  have h4 := tendsto_S 1 4 (by norm_num) (by norm_num)
  have h8 := tendsto_S 1 8 (by norm_num) (by norm_num)
  have hE1 : Tendsto (fun B : ℕ => ((∑ q ∈ Icc 1 B, Ewin 2 4 q : ℕ) : ℝ) / B) atTop (𝓝 0) :=
    tendsto_div_of_le_sqrt _ fun B => sum_Ewin_le 2 4 B (by norm_num)
  have hE2 : Tendsto (fun B : ℕ => ((∑ q ∈ Icc 1 B, Ewin 4 8 q : ℕ) : ℝ) / B) atTop (𝓝 0) :=
    tendsto_div_of_le_sqrt _ fun B => sum_Ewin_le 4 8 B (by norm_num)
  have hcomb := ((h2.sub (h4.const_mul (3 : ℝ))).add (h8.const_mul (2 : ℝ))).sub hE1
  have hcomb2 := hcomb.add (hE2.const_mul (2 : ℝ))
  rw [show (0 : ℝ) - 3 * 0 + 2 * 0 - 0 + 2 * 0 = 0 by ring] at hcomb2
  refine hcomb2.congr fun B => ?_
  have hsum := sum_window_diff B
  simp only [Wdiv] at hsum
  rw [hsum]
  simp only [Nat.cast_one, Real.log_one]
  push_cast
  ring

end GammaDivisors
