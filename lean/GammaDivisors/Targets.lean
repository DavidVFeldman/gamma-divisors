/-
Gamma-Divisors formalization targets.

Companion to "Divisors in windows and the Euler-Mascheroni constant".
Commission 1 scope (Tiers 1-3).

Conventions:
* `q.divisors` is Mathlib's `Nat.divisors` (positive divisors of q, empty for q = 0).
* Averages run over `Finset.Icc 1 B`.
* `harmonic : ℕ → ℚ` and `Real.eulerMascheroniConstant` come from
  Mathlib.NumberTheory.Harmonic.{Defs, EulerMascheroni}.
-/
import Mathlib

open Finset Filter Real Topology

namespace GammaDivisors

/-! ### Auxiliary lemmas -/

/-- The divisors of `q` that are at most `a` are exactly the elements of `[1, a]`
dividing `q`, provided `q ≠ 0`. -/
lemma filter_divisors_le (a q : ℕ) (hq : q ≠ 0) :
    {d ∈ q.divisors | d ≤ a} = {d ∈ Icc 1 a | d ∣ q} := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, -⟩, hda⟩
    exact ⟨⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega), hda⟩, hd⟩
  · rintro ⟨⟨-, hda⟩, hd⟩
    exact ⟨⟨hd, hq⟩, hda⟩

/-- Counting multiples of `d` in `[1, B]`. -/
lemma sum_indicator_dvd (B d : ℕ) :
    ∑ q ∈ Icc 1 B, (if d ∣ q then 1 else 0) = B / d := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter]
  rw [show Finset.Ioc 0 B = Finset.Icc 1 B from rfl]

/-- The real harmonic number as a sum over `Icc 1 m`. -/
lemma harmonic_eq_sum_Icc (m : ℕ) :
    (harmonic m : ℝ) = ∑ d ∈ Icc 1 m, (1 : ℝ) / d := by
  rw [show Finset.Icc 1 m = Finset.Ico 1 (m + 1) by ext x; simp,
    Finset.sum_Ico_eq_sum_range]
  simp [harmonic, one_div, add_comm]

/-! ### Tier 1: the counting identity (divisor-codivisor swap, threshold form) -/

/-- Summing, over `q ≤ B`, the number of divisors of `q` that are at most `a`,
counts for each `d ≤ a` the multiples of `d` up to `B`. -/
theorem sum_card_divisors_le (B a : ℕ) :
    ∑ q ∈ Icc 1 B, #{d ∈ q.divisors | d ≤ a} = ∑ d ∈ Icc 1 a, B / d := by
  have hq : ∀ q ∈ Icc 1 B, #{d ∈ q.divisors | d ≤ a}
      = ∑ d ∈ Icc 1 a, (if d ∣ q then 1 else 0) := by
    intro q hq
    simp only [Finset.mem_Icc] at hq
    rw [filter_divisors_le a q (by omega), Finset.card_filter]
  rw [Finset.sum_congr rfl hq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => sum_indicator_dvd B d

/-! ### Tier 2: fixed windows -/

/-- The window discrepancy for a fixed window: divisors in `[1, a]` counted
positively, divisors in `(a, b]` counted negatively. -/
noncomputable def Zfix (a b q : ℕ) : ℤ :=
  (#{d ∈ q.divisors | d ≤ a} : ℤ) - #{d ∈ q.divisors | a < d ∧ d ≤ b}

/-- Splitting the divisors below `b` at the threshold `a`. -/
lemma card_divisors_split (a b q : ℕ) (hab : a ≤ b) :
    #{d ∈ q.divisors | d ≤ a} + #{d ∈ q.divisors | a < d ∧ d ≤ b}
      = #{d ∈ q.divisors | d ≤ b} := by
  rw [← Finset.card_filter_add_card_filter_not (s := {d ∈ q.divisors | d ≤ b})
    (p := fun d => d ≤ a)]
  congr 1
  · congr 1
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hab⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  · congr 1
    ext d
    simp only [Finset.mem_filter, not_le]
    tauto

/-- The summed window discrepancy in closed form. -/
lemma sum_Zfix (a b B : ℕ) (hab : a ≤ b) :
    ∑ q ∈ Icc 1 B, Zfix a b q
      = 2 * (∑ d ∈ Icc 1 a, ((B / d : ℕ) : ℤ)) - ∑ d ∈ Icc 1 b, ((B / d : ℕ) : ℤ) := by
  have key : ∀ q : ℕ, Zfix a b q
      = 2 * (#{d ∈ q.divisors | d ≤ a} : ℤ) - (#{d ∈ q.divisors | d ≤ b} : ℤ) := by
    intro q
    have := card_divisors_split a b q hab
    unfold Zfix
    omega
  simp only [key, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Nat.cast_sum, ← Nat.cast_sum, sum_card_divisors_le, sum_card_divisors_le]
  push_cast
  ring

/-- For fixed `d ≥ 1`, `(⌊B/d⌋ : ℝ)/B → 1/d`. -/
lemma tendsto_div_div (d : ℕ) (hd : d ≠ 0) :
    Tendsto (fun B : ℕ => ((B / d : ℕ) : ℝ) / B) atTop (𝓝 ((1 : ℝ) / d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hlim : Tendsto (fun B : ℕ => (1 : ℝ) / d - 1 / B) atTop (𝓝 ((1 : ℝ) / d - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with B hB
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have key : (B : ℝ) ≤ ((B / d : ℕ) : ℝ) * d + d := by
      have h : B < B / d * d + d := by
        have h1 := Nat.div_add_mod B d
        have h2 : B % d < d := Nat.mod_lt _ (Nat.pos_of_ne_zero hd)
        nlinarith [h1, h2]
      have h2 : (B : ℝ) < ((B / d * d + d : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h2
      nlinarith
    rw [div_sub_div _ _ hd'.ne' hB'.ne', div_le_div_iff₀ (by positivity) hB']
    nlinarith [key]
  · filter_upwards [eventually_ge_atTop 1] with B hB
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    rw [div_le_div_iff₀ hB' hd']
    have h : B / d * d ≤ B := Nat.div_mul_le_self B d
    calc ((B / d : ℕ) : ℝ) * d = ((B / d * d : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (B : ℝ) := by exact_mod_cast h
      _ = 1 * B := by ring

/-- The averaged Tier-1 count converges to the harmonic number. -/
lemma tendsto_sum_div (m : ℕ) :
    Tendsto (fun B : ℕ => (∑ d ∈ Icc 1 m, ((B / d : ℕ) : ℝ)) / B) atTop
      (𝓝 (harmonic m : ℝ)) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Finset.sum_div]
  refine tendsto_finset_sum _ fun d hd => ?_
  simp only [Finset.mem_Icc] at hd
  exact tendsto_div_div d (by omega)

/-- Fixed-window law: for `a ≤ b`, the average of `Zfix a b` over `q ≤ B`
tends to `2·H_a − H_b` as `B → ∞`. -/
theorem tendsto_average_Zfix (a b : ℕ) (hab : a ≤ b) :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Zfix a b q : ℝ)) / B)
      atTop (𝓝 (2 * (harmonic a : ℝ) - (harmonic b : ℝ))) := by
  have hfun : ∀ B : ℕ, (∑ q ∈ Icc 1 B, (Zfix a b q : ℝ)) / B
      = 2 * ((∑ d ∈ Icc 1 a, ((B / d : ℕ) : ℝ)) / B)
        - (∑ d ∈ Icc 1 b, ((B / d : ℕ) : ℝ)) / B := by
    intro B
    have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_Zfix a b B hab)
    simp only [Int.cast_sum, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast] at h
    rw [h]
    ring
  simp only [hfun]
  exact ((tendsto_sum_div a).const_mul 2).sub (tendsto_sum_div b)

/-! ### Tier 3: the harmonic bridge -/

/-- `Nat.sqrt` tends to infinity. -/
lemma tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨b * b, fun a ha => ?_⟩
  calc b = Nat.sqrt (b * b) := (Nat.sqrt_eq b).symm
    _ ≤ Nat.sqrt a := Nat.sqrt_le_sqrt ha

/-- `log T − 2 log ⌊√T⌋ → 0`. -/
lemma tendsto_log_sqrt_gap :
    Tendsto (fun T : ℕ => Real.log T - 2 * Real.log (Nat.sqrt T)) atTop (𝓝 0) := by
  have hub : Tendsto (fun T : ℕ => (2 : ℝ) / (Nat.sqrt T)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp tendsto_nat_sqrt_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hs : 1 ≤ Nat.sqrt T := Nat.sqrt_pos.mpr hT
    have hs' : (0 : ℝ) < Nat.sqrt T := by exact_mod_cast hs
    have hle : (Nat.sqrt T : ℝ) * Nat.sqrt T ≤ T := by
      have := Nat.sqrt_le' T
      have h2 : ((Nat.sqrt T ^ 2 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast this
      push_cast at h2
      nlinarith [h2]
    have : Real.log ((Nat.sqrt T : ℝ) * Nat.sqrt T) ≤ Real.log T :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_mul hs'.ne' hs'.ne'] at this
    linarith
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hs : 1 ≤ Nat.sqrt T := Nat.sqrt_pos.mpr hT
    have hs' : (0 : ℝ) < Nat.sqrt T := by exact_mod_cast hs
    have hlt : (T : ℝ) ≤ ((Nat.sqrt T : ℝ) + 1) * ((Nat.sqrt T : ℝ) + 1) := by
      have h0 : T < (Nat.sqrt T + 1) * (Nat.sqrt T + 1) := by
        have := Nat.lt_succ_sqrt' T
        nlinarith [this]
      have h2 : (T : ℝ) < (((Nat.sqrt T + 1) * (Nat.sqrt T + 1) : ℕ) : ℝ) := by
        exact_mod_cast h0
      push_cast at h2
      linarith
    have hlog : Real.log T ≤ 2 * Real.log ((Nat.sqrt T : ℝ) + 1) := by
      have := Real.log_le_log (by positivity : (0:ℝ) < T) hlt
      rwa [Real.log_mul (by positivity) (by positivity), ← two_mul] at this
    have hstep : Real.log ((Nat.sqrt T : ℝ) + 1) - Real.log (Nat.sqrt T)
        ≤ 1 / (Nat.sqrt T : ℝ) := by
      have h1 : Real.log ((Nat.sqrt T : ℝ) + 1) - Real.log (Nat.sqrt T)
          = Real.log (((Nat.sqrt T : ℝ) + 1) / (Nat.sqrt T)) := by
        rw [Real.log_div (by positivity) hs'.ne']
      rw [h1]
      have := Real.log_le_sub_one_of_pos
        (show (0:ℝ) < ((Nat.sqrt T : ℝ) + 1) / (Nat.sqrt T) by positivity)
      have heq : ((Nat.sqrt T : ℝ) + 1) / (Nat.sqrt T) - 1 = 1 / (Nat.sqrt T : ℝ) := by
        field_simp
        ring
      linarith [this, heq.le, heq.ge]
    have : (2 : ℝ) / (Nat.sqrt T) = 2 * (1 / (Nat.sqrt T : ℝ)) := by ring
    rw [this]
    linarith

/-- `2·H_{⌊√T⌋} − H_T → γ`. -/
theorem tendsto_two_harmonic_sqrt_sub_harmonic :
    Tendsto (fun T : ℕ => 2 * (harmonic (Nat.sqrt T) : ℝ) - (harmonic T : ℝ))
      atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun T : ℕ => (harmonic (Nat.sqrt T) : ℝ) - Real.log (Nat.sqrt T))
      atTop (𝓝 eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp tendsto_nat_sqrt_atTop
  have h2 : Tendsto (fun T : ℕ => (harmonic T : ℝ) - Real.log T)
      atTop (𝓝 eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hcomb := ((h1.const_mul 2).sub h2).sub tendsto_log_sqrt_gap
  have hval : 2 * eulerMascheroniConstant - eulerMascheroniConstant - 0
      = eulerMascheroniConstant := by ring
  rw [hval] at hcomb
  refine hcomb.congr fun T => ?_
  ring

end GammaDivisors
