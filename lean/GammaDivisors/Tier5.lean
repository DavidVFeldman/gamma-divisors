/-
Tier 5: windows on the scale of `q`, at `α = 1/2`, in both endpoint conventions.
Thresholds `√(q/2)` and `q/2`, phrased through `2d² vs q` and `2d vs q`.
-/
import Mathlib
import GammaDivisors.Counting
import GammaDivisors.Asymptotics
import GammaDivisors.Tier4

open Finset Filter Real Topology

namespace GammaDivisors

/-- Open right endpoint: divisors below `√(q/2)` minus divisors strictly
between `√(q/2)` and `q/2`. -/
noncomputable def Zhalf_open (q : ℕ) : ℤ :=
  (#{d ∈ q.divisors | 2 * d ^ 2 < q} : ℤ) -
    #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d < q}

/-- Closed right endpoint: the window `(√(q/2), q/2]`. -/
noncomputable def Zhalf_closed (q : ℕ) : ℤ :=
  (#{d ∈ q.divisors | 2 * d ^ 2 < q} : ℤ) -
    #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d ≤ q}

/-! ### Local abbreviations -/

/-- Divisors below `√(q/2)`. -/
noncomputable def gcount (q : ℕ) : ℕ := #{d ∈ q.divisors | 2 * d ^ 2 < q}

/-- Divisors below `q/2`. -/
noncomputable def tcount (q : ℕ) : ℕ := #{d ∈ q.divisors | 2 * d < q}

/-- Divisors sitting exactly at `√(q/2)` (and below `q/2`). -/
noncomputable def betacount (q : ℕ) : ℕ := #{d ∈ q.divisors | 2 * d ^ 2 = q ∧ 2 * d < q}

/-- Divisors sitting exactly at `q/2` (and above `√(q/2)`). -/
noncomputable def rhocount (q : ℕ) : ℕ := #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d = q}

/-- Divisors sitting exactly at `√q`. -/
noncomputable def sqcount (q : ℕ) : ℕ := #{d ∈ q.divisors | d ^ 2 = q}

/-! ### Splitting the divisor counts -/

lemma card_split_half (q : ℕ) :
    gcount q + #{d ∈ q.divisors | q ≤ 2 * d ^ 2 ∧ 2 * d < q} = tcount q := by
  have hsub : ∀ d ∈ q.divisors, 2 * d ^ 2 < q → 2 * d < q := by
    intro d hd h
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.1 hd).1
      (Nat.pos_of_ne_zero (Nat.mem_divisors.1 hd).2)
    nlinarith [h, hd1]
  have e1 : {d ∈ q.divisors | 2 * d ^ 2 < q}
      = {d ∈ ({d ∈ q.divisors | 2 * d < q}) | 2 * d ^ 2 < q} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d hd => ?_
    constructor
    · intro h
      exact ⟨hsub d hd h, h⟩
    · intro h
      exact h.2
  have e2 : {d ∈ q.divisors | q ≤ 2 * d ^ 2 ∧ 2 * d < q}
      = {d ∈ ({d ∈ q.divisors | 2 * d < q}) | ¬ (2 * d ^ 2 < q)} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    simp only [not_lt]
    tauto
  rw [gcount, tcount, e1, e2]
  exact Finset.card_filter_add_card_filter_not
    (s := {d ∈ q.divisors | 2 * d < q}) (p := fun d => 2 * d ^ 2 < q)

lemma card_split_beta (q : ℕ) :
    #{d ∈ q.divisors | q ≤ 2 * d ^ 2 ∧ 2 * d < q}
      = #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d < q} + betacount q := by
  have e1 : {d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d < q}
      = {d ∈ ({d ∈ q.divisors | q ≤ 2 * d ^ 2 ∧ 2 * d < q}) | q < 2 * d ^ 2} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    constructor
    · intro h
      exact ⟨⟨le_of_lt h.1, h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  have e2 : {d ∈ q.divisors | 2 * d ^ 2 = q ∧ 2 * d < q}
      = {d ∈ ({d ∈ q.divisors | q ≤ 2 * d ^ 2 ∧ 2 * d < q}) | ¬ (q < 2 * d ^ 2)} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    simp only [not_lt]
    constructor
    · intro h
      exact ⟨⟨le_of_eq h.1.symm, h.2⟩, le_of_eq h.1⟩
    · intro h
      exact ⟨le_antisymm h.2 h.1.1, h.1.2⟩
  rw [betacount, e1, e2]
  exact (Finset.card_filter_add_card_filter_not
    (s := {d ∈ q.divisors | q ≤ 2 * d ^ 2 ∧ 2 * d < q}) (p := fun d => q < 2 * d ^ 2)).symm

lemma card_split_rho (q : ℕ) :
    #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d ≤ q}
      = #{d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d < q} + rhocount q := by
  have e1 : {d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d < q}
      = {d ∈ ({d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d ≤ q}) | 2 * d < q} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    constructor
    · intro h
      exact ⟨⟨h.1, le_of_lt h.2⟩, h.2⟩
    · intro h
      exact ⟨h.1.1, h.2⟩
  have e2 : {d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d = q}
      = {d ∈ ({d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d ≤ q}) | ¬ (2 * d < q)} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    simp only [not_lt]
    constructor
    · intro h
      exact ⟨⟨h.1, le_of_eq h.2⟩, le_of_eq h.2.symm⟩
    · intro h
      exact ⟨h.1.1, le_antisymm h.1.2 h.2⟩
  rw [rhocount, e1, e2]
  exact (Finset.card_filter_add_card_filter_not
    (s := {d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d ≤ q}) (p := fun d => 2 * d < q)).symm

/-! ### The count below `q/2` via the divisor reflection -/

lemma card_le_two_divisors (q : ℕ) (hq : 1 ≤ q) :
    #{d ∈ q.divisors | d ≤ 2} = 1 + (if 2 ∣ q then 1 else 0) := by
  by_cases h2 : 2 ∣ q
  · rw [if_pos h2]
    have : {d ∈ q.divisors | d ≤ 2} = {1, 2} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hd, -⟩, hle⟩
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (by omega)
        omega
      · rintro (rfl | rfl)
        · exact ⟨⟨one_dvd _, by omega⟩, by norm_num⟩
        · exact ⟨⟨h2, by omega⟩, le_refl 2⟩
    rw [this]
    simp
  · rw [if_neg h2]
    have : {d ∈ q.divisors | d ≤ 2} = {1} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hd, -⟩, hle⟩
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (by omega)
        rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
        · rfl
        · exact absurd hd h2
      · rintro rfl
        exact ⟨⟨one_dvd _, by omega⟩, by norm_num⟩
    rw [this, Finset.card_singleton]

lemma card_ge_half (q : ℕ) (hq : 1 ≤ q) :
    #{d ∈ q.divisors | q ≤ 2 * d} = 1 + (if 2 ∣ q then 1 else 0) := by
  have step : {d ∈ q.divisors | q ≤ 2 * d} = {d ∈ q.divisors | q / d ≤ 2} := by
    refine Finset.filter_congr fun d hd => ?_
    simp only [Nat.mem_divisors] at hd
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    have hqd : q = d * (q / d) := (Nat.mul_div_cancel' hd.1).symm
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      have : 3 ≤ q / d := hcon
      nlinarith [hqd, h, hd1, this]
    · intro h
      nlinarith [hqd, h, hd1]
  rw [step, card_filter_divisors_refl q (fun e => e ≤ 2), card_le_two_divisors q hq]

lemma tcount_eq (q : ℕ) (hq : 1 ≤ q) :
    (tcount q : ℤ) = 2 * (Ndiv 2 q : ℤ) + (sqcount q : ℤ) - 1 - (if 2 ∣ q then 1 else 0) := by
  have hsplit : tcount q + #{d ∈ q.divisors | ¬ (2 * d < q)} = #q.divisors :=
    Finset.card_filter_add_card_filter_not (s := q.divisors) (p := fun d => 2 * d < q)
  have hcompl : {d ∈ q.divisors | ¬ (2 * d < q)} = {d ∈ q.divisors | q ≤ 2 * d} := by
    refine Finset.filter_congr fun d _ => ?_
    simp only [not_lt]
  have hge := card_ge_half q hq
  rw [hcompl, hge] at hsplit
  have hdiv := card_divisors_eq q hq
  simp only [Ndiv, sqcount]
  split_ifs at hsplit ⊢ with h2
  · omega
  · omega

/-! ### The two `Z`'s in terms of the basic counts -/

lemma Zhalf_open_eq (q : ℕ) :
    Zhalf_open q = 2 * (gcount q : ℤ) - (tcount q : ℤ) + (betacount q : ℤ) := by
  have h1 := card_split_half q
  have h2 := card_split_beta q
  simp only [Zhalf_open, gcount] at *
  omega

lemma Zhalf_closed_eq (q : ℕ) :
    Zhalf_closed q = Zhalf_open q - (rhocount q : ℤ) := by
  have h := card_split_rho q
  simp only [Zhalf_closed, Zhalf_open]
  omega

/-! ### Summing -/

lemma sum_gcount (B : ℕ) : ∑ q ∈ Icc 1 B, gcount q = S 2 2 B := by
  simp only [gcount]
  rw [sum_card_const_mul_sq 2 B, S]
  simp

lemma sum_betacount_le (B : ℕ) : ∑ q ∈ Icc 1 B, betacount q ≤ Nat.sqrt B := by
  refine le_trans (Finset.sum_le_sum fun q _ => ?_)
    (sum_card_eq_le B (fun d => 2 * d ^ 2) ?_ ?_)
  · exact Finset.card_le_card (Finset.monotone_filter_right _ (fun d _ h => h.1))
  · intro a b _ _ hab
    simp only at hab
    have h2 : a ^ 2 = b ^ 2 := by omega
    exact Nat.pow_left_injective (by norm_num) h2
  · intro d hd hdB
    simp only [pow_two] at hdB
    exact Nat.le_sqrt.2 (by omega)

lemma sum_sqcount_le (B : ℕ) : ∑ q ∈ Icc 1 B, sqcount q ≤ Nat.sqrt B := by
  refine le_trans (le_of_eq ?_) (sum_card_eq_le B (fun d => d ^ 2) ?_ ?_)
  · rfl
  · intro a b _ _ hab
    simp only at hab
    exact Nat.pow_left_injective (by norm_num) hab
  · intro d hd hdB
    simp only [pow_two] at hdB
    exact Nat.le_sqrt.2 (by omega)

lemma sum_indicator_two (B : ℕ) :
    ∑ q ∈ Icc 1 B, (if 2 ∣ q then 1 else 0) = B / 2 := sum_indicator_dvd B 2

lemma sum_rhocount (B : ℕ) (hB : 2 ≤ B) :
    ∑ q ∈ Icc 1 B, rhocount q = B / 2 - 1 := by
  have hval : ∀ q : ℕ, 1 ≤ q → rhocount q = (if 2 ∣ q ∧ 2 < q then 1 else 0) := by
    intro q hq
    by_cases h : 2 ∣ q ∧ 2 < q
    · rw [if_pos h]
      obtain ⟨⟨k, hk⟩, hq2⟩ := h
      have hk2 : 2 ≤ k := by omega
      have : {d ∈ q.divisors | q < 2 * d ^ 2 ∧ 2 * d = q} = {k} := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
        constructor
        · rintro ⟨-, -, hd2⟩
          omega
        · rintro rfl
          refine ⟨⟨⟨2, by omega⟩, by omega⟩, ?_, by omega⟩
          nlinarith [hk2]
      rw [rhocount, this, Finset.card_singleton]
    · rw [if_neg h]
      refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_)
      intro d hd
      simp only [Nat.mem_divisors] at hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
      rintro ⟨hlt, heq⟩
      refine h ⟨⟨d, by omega⟩, ?_⟩
      have hd2 : 2 ≤ d := by
        by_contra hcon
        push_neg at hcon
        have hd11 : d = 1 := by omega
        subst hd11
        norm_num at hlt
        omega
      omega
  have hset : {q ∈ Icc 1 B | 2 ∣ q ∧ 2 < q} = ({q ∈ Icc 1 B | 2 ∣ q}).erase 2 := by
    ext q
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hq, h2, hlt⟩
      exact ⟨by omega, hq, h2⟩
    · rintro ⟨hne, hq, h2⟩
      have : 2 ≤ q := Nat.le_of_dvd (by omega) h2
      exact ⟨hq, h2, by omega⟩
  have hmem : (2 : ℕ) ∈ {q ∈ Icc 1 B | 2 ∣ q} := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hB⟩, dvd_refl 2⟩
  have hcard : #{q ∈ Icc 1 B | 2 ∣ q} = B / 2 := by
    rw [Finset.card_filter]
    exact sum_indicator_dvd B 2
  calc ∑ q ∈ Icc 1 B, rhocount q
      = ∑ q ∈ Icc 1 B, (if 2 ∣ q ∧ 2 < q then 1 else 0) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        simp only [Finset.mem_Icc] at hq
        exact hval q hq.1
    _ = #{q ∈ Icc 1 B | 2 ∣ q ∧ 2 < q} := (Finset.card_filter _ _).symm
    _ = #(({q ∈ Icc 1 B | 2 ∣ q}).erase 2) := by rw [hset]
    _ = B / 2 - 1 := by rw [Finset.card_erase_of_mem hmem, hcard]

/-! ### The averages -/

lemma sum_Zhalf_open_real (B : ℕ) :
    ∑ q ∈ Icc 1 B, (Zhalf_open q : ℝ)
      = 2 * (S 2 2 B : ℝ) - 2 * (S 1 2 B : ℝ)
        - ((∑ q ∈ Icc 1 B, sqcount q : ℕ) : ℝ) + B + ((B / 2 : ℕ) : ℝ)
        + ((∑ q ∈ Icc 1 B, betacount q : ℕ) : ℝ) := by
  have key : ∀ q ∈ Icc 1 B, (Zhalf_open q : ℝ)
      = 2 * (gcount q : ℝ) - 2 * (Ndiv 2 q : ℝ) - (sqcount q : ℝ) + 1
        + (if 2 ∣ q then (1 : ℝ) else 0) + (betacount q : ℝ) := by
    intro q hq
    simp only [Finset.mem_Icc] at hq
    have h1 := Zhalf_open_eq q
    have h2 := tcount_eq q hq.1
    have h3 : (Zhalf_open q : ℤ)
        = 2 * (gcount q : ℤ) - (2 * (Ndiv 2 q : ℤ) + (sqcount q : ℤ) - 1
          - (if 2 ∣ q then 1 else 0)) + (betacount q : ℤ) := by rw [h1, h2]
    have h4 := congrArg (fun z : ℤ => (z : ℝ)) h3
    push_cast at h4
    rw [h4]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have e1 : ∑ q ∈ Icc 1 B, (gcount q : ℝ) = (S 2 2 B : ℝ) := by
    rw [← Nat.cast_sum, sum_gcount B]
  have e2 : ∑ q ∈ Icc 1 B, (Ndiv 2 q : ℝ) = (S 1 2 B : ℝ) := by
    rw [← Nat.cast_sum, sum_Ndiv_eq_S 2 B (by norm_num)]
  have e3 : ∑ q ∈ Icc 1 B, (sqcount q : ℝ) = ((∑ q ∈ Icc 1 B, sqcount q : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
  have e4 : ∑ _q ∈ Icc 1 B, (1 : ℝ) = (B : ℝ) := by simp
  have e5 : ∑ q ∈ Icc 1 B, (if 2 ∣ q then (1 : ℝ) else 0) = ((B / 2 : ℕ) : ℝ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) (sum_indicator_two B)
    push_cast at hcast
    exact hcast
  have e6 : ∑ q ∈ Icc 1 B, (betacount q : ℝ) = ((∑ q ∈ Icc 1 B, betacount q : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
  rw [e1, e2, e3, e4, e5, e6]

/-- **Tier 5, open convention.** The average tends to `H₂ - log 2 = 3/2 - log 2`. -/
theorem tendsto_average_Zhalf_open :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Zhalf_open q : ℝ)) / B)
      atTop (𝓝 (3 / 2 - Real.log 2)) := by
  have h22 := tendsto_S 2 2 (by norm_num) (by norm_num)
  have h12 := tendsto_S 1 2 (by norm_num) (by norm_num)
  have hsq : Tendsto (fun B : ℕ => ((∑ q ∈ Icc 1 B, sqcount q : ℕ) : ℝ) / B) atTop (𝓝 0) :=
    tendsto_div_of_le_sqrt _ sum_sqcount_le
  have hbeta : Tendsto (fun B : ℕ => ((∑ q ∈ Icc 1 B, betacount q : ℕ) : ℝ) / B) atTop (𝓝 0) :=
    tendsto_div_of_le_sqrt _ sum_betacount_le
  have hhalf : Tendsto (fun B : ℕ => ((B / 2 : ℕ) : ℝ) / B) atTop (𝓝 ((1 : ℝ) / 2)) :=
    tendsto_div_div 2 (by norm_num)
  have hcomb := ((((h22.const_mul (2 : ℝ)).sub (h12.const_mul (2 : ℝ))).sub hsq).add
    hhalf).add hbeta
  rw [show (2 : ℝ) * 0 - 2 * 0 - 0 + 1 / 2 + 0 = 1 / 2 by ring] at hcomb
  have hshift := hcomb.add_const (1 - Real.log 2)
  rw [show (1 : ℝ) / 2 + (1 - Real.log 2) = 3 / 2 - Real.log 2 by ring] at hshift
  refine hshift.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hB0 : (B : ℝ) ≠ 0 := by
    have : (0 : ℝ) < B := by exact_mod_cast hB
    exact ne_of_gt this
  rw [sum_Zhalf_open_real B]
  simp only [Nat.cast_one, Real.log_one, Nat.cast_ofNat]
  field_simp
  ring

/-- **Tier 5, closed convention.** The average tends to `H₁ - log 2 = 1 - log 2`. -/
theorem tendsto_average_Zhalf_closed :
    Tendsto (fun B : ℕ => (∑ q ∈ Icc 1 B, (Zhalf_closed q : ℝ)) / B)
      atTop (𝓝 (1 - Real.log 2)) := by
  have hopen := tendsto_average_Zhalf_open
  have hrho : Tendsto (fun B : ℕ => ((B / 2 : ℕ) : ℝ) / B - 1 / B) atTop (𝓝 ((1 : ℝ) / 2 - 0)) :=
    (tendsto_div_div 2 (by norm_num)).sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at hrho
  have hcomb := hopen.sub hrho
  rw [show (3 : ℝ) / 2 - Real.log 2 - 1 / 2 = 1 - Real.log 2 by ring] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with B hB
  have hB0 : (B : ℝ) ≠ 0 := by
    have : (0 : ℝ) < B := by exact_mod_cast (by omega : 1 ≤ B)
    exact ne_of_gt this
  have hZ : ∑ q ∈ Icc 1 B, (Zhalf_closed q : ℝ)
      = (∑ q ∈ Icc 1 B, (Zhalf_open q : ℝ)) - ((∑ q ∈ Icc 1 B, rhocount q : ℕ) : ℝ) := by
    rw [Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have := congrArg (fun z : ℤ => (z : ℝ)) (Zhalf_closed_eq q)
    push_cast at this
    exact this
  have hrhosum : ((∑ q ∈ Icc 1 B, rhocount q : ℕ) : ℝ) = ((B / 2 : ℕ) : ℝ) - 1 := by
    rw [sum_rhocount B hB]
    have h1 : 1 ≤ B / 2 := Nat.one_le_div_iff (by omega) |>.2 hB
    push_cast [Nat.cast_sub h1]
    ring
  rw [hZ, hrhosum]
  field_simp

end GammaDivisors
