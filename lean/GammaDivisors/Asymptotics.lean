/-
Asymptotics for the truncated divisor sums appearing in Commission 2.

For `c ≥ 1` and `j ≥ 2` the basic sum is

  `S c j B = ∑_{d ≤ B} (⌊B/d⌋ - c·d^(j-1))₊`,

which (by the swap lemma in `Counting.lean`) counts the divisors `d` of `q ≤ B`
with `c·d^j < q`.  The main result of this file is that

  `S c j B / B - ((1/j)(log B - log c) + γ - 1/j) → 0`.
-/
import Mathlib
import GammaDivisors.Targets

open Finset Filter Real Topology

namespace GammaDivisors

/-! ### The threshold -/

/-- The largest `d` with `c·d^j + d ≤ B`; beyond it the truncated terms vanish. -/
noncomputable def thr (c j B : ℕ) : ℕ := Nat.findGreatest (fun d => c * d ^ j + d ≤ B) B

lemma thr_le (c j B : ℕ) : thr c j B ≤ B := Nat.findGreatest_le B

lemma thr_spec (c j B : ℕ) (hj : 1 ≤ j) :
    c * (thr c j B) ^ j + thr c j B ≤ B := by
  refine Nat.findGreatest_spec (P := fun d => c * d ^ j + d ≤ B) (m := 0) (Nat.zero_le B) ?_
  simp [Nat.zero_pow (show 0 < j by omega)]

lemma le_thr {c j B d : ℕ} (h : c * d ^ j + d ≤ B) : d ≤ thr c j B :=
  Nat.le_findGreatest (by omega) h

/-- Monotonicity: below the threshold the defining inequality holds. -/
lemma thr_mono_spec {c j B d : ℕ} (hd : d ≤ thr c j B) (hj : 1 ≤ j) :
    c * d ^ j + d ≤ B := by
  have h1 : c * d ^ j ≤ c * (thr c j B) ^ j :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd j)
  have := thr_spec c j B hj
  omega

lemma thr_lt_self {c j B : ℕ} (hc : 1 ≤ c) (hj : 1 ≤ j) (hB : 1 ≤ B) : thr c j B < B := by
  rcases lt_or_eq_of_le (thr_le c j B) with h | h
  · exact h
  · exfalso
    have := thr_spec c j B hj
    rw [h] at this
    have hBj : B ≤ B ^ j := Nat.le_self_pow (by omega) B
    nlinarith [this, hBj, hc]

lemma lt_thr_succ {c j B : ℕ} (hc : 1 ≤ c) (hj : 1 ≤ j) (hB : 1 ≤ B) :
    B < c * (thr c j B + 1) ^ j + (thr c j B + 1) := by
  have hlt := thr_lt_self hc hj hB
  have := Nat.findGreatest_is_greatest (P := fun d => c * d ^ j + d ≤ B)
    (n := B) (k := thr c j B + 1) (by simp [thr]) (by omega)
  omega

/-- The threshold tends to infinity. -/
lemma tendsto_thr (c j : ℕ) :
    Tendsto (fun B => thr c j B) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun N => ⟨c * N ^ j + N, fun B hB => ?_⟩
  exact le_thr (le_trans (le_refl _) hB)

/-! ### The truncated sum -/

/-- The basic truncated sum. -/
noncomputable def S (c j B : ℕ) : ℕ := ∑ d ∈ Icc 1 B, (B / d - c * d ^ (j - 1))

lemma S_eq_sum_thr (c j B : ℕ) (hj : 1 ≤ j) :
    S c j B = ∑ d ∈ Icc 1 (thr c j B), (B / d - c * d ^ (j - 1)) := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, le_trans hd.2 (thr_le c j B)⟩
  · intro d hd hd'
    simp only [Finset.mem_Icc, not_and, not_le] at hd hd'
    have hdthr : thr c j B < d := hd' hd.1
    have hnot : ¬ (c * d ^ j + d ≤ B) := fun h => absurd (le_thr h) (by omega)
    have hpow : c * d ^ j = c * d ^ (j - 1) * d := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    have : B < d * (c * d ^ (j - 1) + 1) := by nlinarith [hnot, hpow]
    have hdiv : B / d < c * d ^ (j - 1) + 1 :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by linarith [this, mul_comm d (c * d ^ (j-1) + 1)])
    omega

/-- For `d` below the threshold the subtraction is honest. -/
lemma le_div_of_le_thr {c j B d : ℕ} (hd1 : 1 ≤ d) (hd : d ≤ thr c j B) (hj : 1 ≤ j) :
    c * d ^ (j - 1) ≤ B / d := by
  have h := thr_mono_spec hd hj
  have hpow : c * d ^ j = c * d ^ (j - 1) * d := by
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega
  exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)

/-- The real-valued form of the truncated sum. -/
lemma S_real (c j B : ℕ) (hj : 1 ≤ j) :
    (S c j B : ℝ)
      = (∑ d ∈ Icc 1 (thr c j B), ((B / d : ℕ) : ℝ))
        - ∑ d ∈ Icc 1 (thr c j B), (c : ℝ) * (d : ℝ) ^ (j - 1) := by
  rw [S_eq_sum_thr c j B hj, ← Finset.sum_sub_distrib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_Icc] at hd
  have h := le_div_of_le_thr hd.1 hd.2 hj
  push_cast [Nat.cast_sub h]
  ring

/-! ### Approximating `∑_{d ≤ D} ⌊B/d⌋` by `B · H_D` -/

lemma abs_sum_floor_sub_harmonic (B D : ℕ) :
    |(∑ d ∈ Icc 1 D, ((B / d : ℕ) : ℝ)) - B * (harmonic D : ℝ)| ≤ D := by
  rw [harmonic_eq_sum_Icc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ d ∈ Icc 1 D, (((B / d : ℕ) : ℝ) - B * ((1 : ℝ) / d))|
      ≤ ∑ d ∈ Icc 1 D, |((B / d : ℕ) : ℝ) - B * ((1 : ℝ) / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Icc 1 D, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        simp only [Finset.mem_Icc] at hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
        have hmod := Nat.div_add_mod B d
        have hlt : B % d < d := Nat.mod_lt _ (by omega)
        have hB : (B : ℝ) = d * ((B / d : ℕ) : ℝ) + ((B % d : ℕ) : ℝ) := by
          exact_mod_cast hmod.symm
        have h1 : (0 : ℝ) ≤ ((B % d : ℕ) : ℝ) := by positivity
        have h2 : ((B % d : ℕ) : ℝ) < d := by exact_mod_cast hlt
        have hkey : (B : ℝ) / d = ((B / d : ℕ) : ℝ) + ((B % d : ℕ) : ℝ) / d := by
          field_simp
          linarith [hB]
        have hq1 : 0 ≤ ((B % d : ℕ) : ℝ) / d := by positivity
        have hq2 : ((B % d : ℕ) : ℝ) / d < 1 := by rw [div_lt_one hd0]; exact h2
        rw [abs_le, mul_one_div]
        constructor <;> linarith
    _ = D := by simp

/-! ### Bernoulli estimates for power sums -/

lemma bernoulli_pow_lower (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    ((m : ℝ) + 1) * y ^ m ≤ (y + 1) ^ (m + 1) - y ^ (m + 1) := by
  rcases eq_or_lt_of_le hy with h | hy'
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← h]
      simp [zero_pow (by omega : m ≠ 0)]
  · have hy1 : (0 : ℝ) < y := hy'
    have hnn : (0 : ℝ) ≤ 1 / y := by positivity
    have hb := one_add_mul_le_pow (a := 1 / y) (by linarith) (m + 1)
    have hpow : (1 + 1 / y) ^ (m + 1) * y ^ (m + 1) = (y + 1) ^ (m + 1) := by
      rw [← mul_pow]
      congr 1
      field_simp
    have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt (pow_pos hy1 (m + 1)))
    rw [hpow] at hmul
    have hexp : (1 + (↑(m + 1) : ℝ) * (1 / y)) * y ^ (m + 1)
        = y ^ (m + 1) + ((m : ℝ) + 1) * y ^ m := by
      push_cast
      field_simp
      ring
    rw [hexp] at hmul
    linarith

lemma bernoulli_pow_upper (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (y + 1) ^ (m + 1) - y ^ (m + 1) ≤ ((m : ℝ) + 1) * (y + 1) ^ m := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hb := one_add_mul_le_pow (a := -(1 / (y + 1)))
    (by
      have : (0 : ℝ) < 1 / (y + 1) := by positivity
      have h2 : 1 / (y + 1) ≤ 1 := by
        rw [div_le_one hy1]; linarith
      linarith) (m + 1)
  have hpow : (1 + -(1 / (y + 1))) ^ (m + 1) * (y + 1) ^ (m + 1) = y ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt (pow_pos hy1 (m + 1)))
  rw [hpow] at hmul
  have hexp : (1 + (↑(m + 1) : ℝ) * -(1 / (y + 1))) * (y + 1) ^ (m + 1)
      = (y + 1) ^ (m + 1) - ((m : ℝ) + 1) * (y + 1) ^ m := by
    push_cast
    field_simp
    ring
  rw [hexp] at hmul
  linarith

lemma sum_pow_lower (k D : ℕ) :
    (D : ℝ) ^ (k + 1) ≤ ((k : ℝ) + 1) * ∑ d ∈ Icc 1 D, (d : ℝ) ^ k := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ D + 1), mul_add]
      have hb := bernoulli_pow_upper k (D : ℝ) (by positivity)
      push_cast
      push_cast at ih hb
      linarith

lemma sum_pow_upper (k D : ℕ) :
    ((k : ℝ) + 1) * ∑ d ∈ Icc 1 D, (d : ℝ) ^ k ≤ ((D : ℝ) + 1) ^ (k + 1) - 1 := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ D + 1), mul_add]
      have hb := bernoulli_pow_lower k ((D : ℝ) + 1) (by positivity)
      push_cast
      push_cast at ih hb
      linarith


/-! ### Elementary limits -/

lemma tendsto_add_div_nat (a : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + a) / n) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 + a * (1 / (n : ℝ))) atTop (𝓝 (1 + a * 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat.const_mul a)
  rw [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

lemma tendsto_log_gap (a : ℝ) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + a) - Real.log n) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => Real.log (((n : ℝ) + a) / n)) atTop (𝓝 (Real.log 1)) :=
    (Real.continuousAt_log one_ne_zero).tendsto.comp (tendsto_add_div_nat a)
  rw [Real.log_one] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop (max 1 (Nat.ceil (-a) + 1))] with n hn
  have hn1 : (1 : ℕ) ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hna : (0 : ℝ) < (n : ℝ) + a := by
    have h2 : (Nat.ceil (-a) + 1 : ℕ) ≤ n := le_trans (le_max_right _ _) hn
    have h3 : (-a) ≤ (Nat.ceil (-a) : ℝ) := Nat.le_ceil _
    have h4 : ((Nat.ceil (-a) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  rw [Real.log_div (by linarith) (by linarith)]

lemma tendsto_ratio_pow (j : ℕ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) / n) ^ j) atTop (𝓝 1) := by
  have := (tendsto_add_div_nat 1).pow j
  simpa using this

lemma tendsto_succ_div_pow (c j : ℕ) (hc : 1 ≤ c) (hj : 2 ≤ j) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((c : ℝ) * (n : ℝ) ^ j)) atTop (𝓝 0) := by
  have hub : Tendsto (fun n : ℕ => 2 * (1 / (n : ℝ))) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero' ?_ ?_ hub
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ j := pow_le_pow_right₀ hn0 hj
    have hden : (n : ℝ) ^ 2 ≤ (c : ℝ) * (n : ℝ) ^ j := by nlinarith [pow_pos (by linarith : (0:ℝ) < n) j]
    have h1 : ((n : ℝ) + 1) / ((c : ℝ) * (n : ℝ) ^ j) ≤ ((n : ℝ) + 1) / (n : ℝ) ^ 2 := by
      refine div_le_div_of_nonneg_left (by linarith) (by nlinarith) hden
    have h2 : ((n : ℝ) + 1) / (n : ℝ) ^ 2 ≤ 2 * (1 / n) := by
      rw [div_le_iff₀ (by nlinarith)]
      field_simp
      nlinarith
    linarith


/-- `√B / B → 0`: all boundary counts in the campaign are `o(B)`. -/
lemma tendsto_sqrt_div : Tendsto (fun B : ℕ => (Nat.sqrt B : ℝ) / B) atTop (𝓝 0) := by
  have hinv : Tendsto (fun B : ℕ => 1 / (Nat.sqrt B : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp tendsto_nat_sqrt_atTop
  refine squeeze_zero' ?_ ?_ hinv
  · filter_upwards [eventually_ge_atTop 1] with B hB
    positivity
  · filter_upwards [tendsto_nat_sqrt_atTop.eventually_ge_atTop 1] with B hB1
    have hs : (Nat.sqrt B) ^ 2 ≤ B := Nat.sqrt_le' B
    have hs' : (Nat.sqrt B : ℝ) ^ 2 ≤ (B : ℝ) := by exact_mod_cast hs
    have hx : (1 : ℝ) ≤ (Nat.sqrt B : ℝ) := by exact_mod_cast hB1
    rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith

/-- A sequence of naturals bounded by `√B` is `o(B)`. -/
lemma tendsto_div_of_le_sqrt (X : ℕ → ℕ) (hX : ∀ B, X B ≤ Nat.sqrt B) :
    Tendsto (fun B : ℕ => (X B : ℝ) / B) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_sqrt_div
  · filter_upwards [eventually_ge_atTop 1] with B hB
    positivity
  · filter_upwards [eventually_ge_atTop 1] with B hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have : (X B : ℝ) ≤ (Nat.sqrt B : ℝ) := by exact_mod_cast hX B
    gcongr

/-! ### The master asymptotic -/

/-- Comparing quotients with both numerator and denominator moving. -/
lemma div_le_div_aux {p P b q : ℝ} (hp : 0 ≤ p) (hpP : p ≤ P) (hb : 0 < b) (hbq : b ≤ q) :
    p / q ≤ P / b := by
  have hq : 0 < q := lt_of_lt_of_le hb hbq
  rw [div_le_div_iff₀ hq hb]
  nlinarith

lemma thr_pow_le {c j B : ℕ} (hj : 1 ≤ j) :
    c * (thr c j B) ^ j ≤ B := by
  have := thr_spec c j B hj
  omega

lemma le_thr_add_two {c j B : ℕ} (hc : 1 ≤ c) (hj : 2 ≤ j) (hB : 1 ≤ B) :
    B ≤ c * (thr c j B + 2) ^ j := by
  set D := thr c j B with hD
  have h1 : B < c * (D + 1) ^ j + (D + 1) := lt_thr_succ hc (by omega) hB
  have h2 : (D + 1) ^ (j - 1) * (D + 2) = (D + 1) ^ j + (D + 1) ^ (j - 1) := by
    have : (D + 1) ^ (j - 1) * (D + 1) = (D + 1) ^ j := by
      rw [← pow_succ]
      congr 1
      omega
    ring_nf
    ring_nf at this
    omega
  have h3 : (D + 1) ≤ (D + 1) ^ (j - 1) := Nat.le_self_pow (by omega) _
  have h4 : (D + 1) ^ (j - 1) * (D + 2) ≤ (D + 2) ^ j := by
    calc (D + 1) ^ (j - 1) * (D + 2) ≤ (D + 2) ^ (j - 1) * (D + 2) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ = (D + 2) ^ j := by rw [← pow_succ]; congr 1; omega
  have h5 : (D + 1) ^ j + (D + 1) ≤ (D + 2) ^ j := by omega
  calc B ≤ c * (D + 1) ^ j + (D + 1) := by omega
    _ ≤ c * ((D + 1) ^ j + (D + 1)) := by nlinarith
    _ ≤ c * (D + 2) ^ j := Nat.mul_le_mul_left _ h5

lemma tendsto_thr_div (c j : ℕ) (hc : 1 ≤ c) (hj : 2 ≤ j) :
    Tendsto (fun B : ℕ => (thr c j B : ℝ) / B) atTop (𝓝 0) := by
  have hD := tendsto_thr c j
  have hinv : Tendsto (fun B : ℕ => 1 / (thr c j B : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hD
  refine squeeze_zero' ?_ ?_ hinv
  · filter_upwards [eventually_ge_atTop 1] with B hB
    positivity
  · filter_upwards [hD.eventually_ge_atTop 1] with B hD1
    have hsq : (thr c j B) ^ 2 ≤ B := by
      have h1 : (thr c j B) ^ 2 ≤ (thr c j B) ^ j := Nat.pow_le_pow_right (by omega) hj
      have h2 := thr_pow_le (c := c) (j := j) (B := B) (by omega)
      nlinarith [h1, h2, hc]
    have hx : (1 : ℝ) ≤ (thr c j B : ℝ) := by exact_mod_cast hD1
    have hsq' : (thr c j B : ℝ) ^ 2 ≤ (B : ℝ) := by exact_mod_cast hsq
    rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith

lemma tendsto_log_thr (c j : ℕ) (hc : 1 ≤ c) (hj : 2 ≤ j) :
    Tendsto (fun B : ℕ => Real.log (thr c j B) - (1 / j) * (Real.log B - Real.log c))
      atTop (𝓝 0) := by
  have hD := tendsto_thr c j
  have hj0 : (0 : ℝ) < j := by positivity
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hlow : Tendsto (fun B : ℕ =>
      -(Real.log ((thr c j B : ℝ) + 2) - Real.log (thr c j B))) atTop (𝓝 0) := by
    have := (tendsto_log_gap 2).comp hD
    simpa using this.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hD.eventually_ge_atTop 1, eventually_ge_atTop 1] with B hD1 hB
    have hx : (1 : ℝ) ≤ (thr c j B : ℝ) := by exact_mod_cast hD1
    have hup : (B : ℕ) ≤ c * (thr c j B + 2) ^ j := le_thr_add_two hc hj hB
    have hup' : (B : ℝ) ≤ (c : ℝ) * ((thr c j B : ℝ) + 2) ^ j := by exact_mod_cast hup
    have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have hlog : Real.log B ≤ Real.log c + j * Real.log ((thr c j B : ℝ) + 2) := by
      have h := Real.log_le_log (by positivity) hup'
      rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
    rw [neg_le_sub_iff_le_add] at *
    have : (1 / (j : ℝ)) * (Real.log B - Real.log c) ≤ Real.log ((thr c j B : ℝ) + 2) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hjR]
      linarith
    linarith
  · filter_upwards [hD.eventually_ge_atTop 1, eventually_ge_atTop 1] with B hD1 hB
    have hx : (1 : ℝ) ≤ (thr c j B : ℝ) := by exact_mod_cast hD1
    have hlow2 : c * (thr c j B) ^ j ≤ B := thr_pow_le (by omega)
    have hlow2' : (c : ℝ) * ((thr c j B : ℝ)) ^ j ≤ (B : ℝ) := by exact_mod_cast hlow2
    have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
    have hlog : Real.log c + j * Real.log (thr c j B) ≤ Real.log B := by
      have h := Real.log_le_log (by positivity) hlow2'
      rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
    have : Real.log (thr c j B) ≤ (1 / (j : ℝ)) * (Real.log B - Real.log c) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hjR]
      linarith
    linarith

lemma tendsto_pow_sum_div (c j : ℕ) (hc : 1 ≤ c) (hj : 2 ≤ j) :
    Tendsto (fun B : ℕ =>
        (∑ d ∈ Icc 1 (thr c j B), (c : ℝ) * (d : ℝ) ^ (j - 1)) / B) atTop (𝓝 (1 / j)) := by
  have hD := tendsto_thr c j
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  -- upper bounding sequence
  have hup : Tendsto (fun B : ℕ => (1 / (j : ℝ)) * ((((thr c j B : ℝ)) + 1) / (thr c j B)) ^ j)
      atTop (𝓝 (1 / j)) := by
    have := ((tendsto_ratio_pow j).comp hD).const_mul (1 / (j : ℝ))
    simpa using this
  have hlo : Tendsto (fun B : ℕ => (1 / (j : ℝ)) *
      (((((thr c j B : ℝ)) + 1) / (thr c j B)) ^ j
        + (((thr c j B : ℝ)) + 1) / ((c : ℝ) * (thr c j B : ℝ) ^ j))⁻¹)
      atTop (𝓝 (1 / j)) := by
    have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / n) ^ j
        + ((n : ℝ) + 1) / ((c : ℝ) * (n : ℝ) ^ j)) atTop (𝓝 1) := by
      have := (tendsto_ratio_pow j).add (tendsto_succ_div_pow c j hc hj)
      simpa using this
    have h2 := ((h1.comp hD).inv₀ (by norm_num)).const_mul (1 / (j : ℝ))
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [hD.eventually_ge_atTop 1, eventually_ge_atTop 1] with B hD1 hB
    set D := thr c j B with hDdef
    have hx : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    -- P ≥ (c/j) D^j
    have hPlow : (c : ℝ) / j * (D : ℝ) ^ j ≤ ∑ d ∈ Icc 1 D, (c : ℝ) * (d : ℝ) ^ (j - 1) := by
      have h := sum_pow_lower (j - 1) D
      have hj1 : ((j : ℝ) - 1) + 1 = (j : ℝ) := by ring
      have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        have : (1 : ℕ) ≤ j := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [show j - 1 + 1 = j by omega, hcast] at h
      rw [← Finset.mul_sum, div_mul_eq_mul_div, div_le_iff₀ hjR]
      nlinarith [h, hcR]
    -- B ≤ c(D+1)^j + D + 1
    have hBup : (B : ℝ) ≤ (c : ℝ) * ((D : ℝ) + 1) ^ j + (D : ℝ) + 1 := by
      have h := lt_thr_succ (c := c) (j := j) (B := B) hc (by omega) hB
      have h' : (B : ℝ) < (c : ℝ) * ((D : ℝ) + 1) ^ j + ((D : ℝ) + 1) := by
        exact_mod_cast h
      linarith
    have hden : (0 : ℝ) < (c : ℝ) * ((D : ℝ) + 1) ^ j + (D : ℝ) + 1 := by positivity
    have hdiv : (1 / (j : ℝ)) *
        ((((D : ℝ) + 1) / D) ^ j + ((D : ℝ) + 1) / ((c : ℝ) * (D : ℝ) ^ j))⁻¹
          = ((c : ℝ) / j * (D : ℝ) ^ j) / ((c : ℝ) * ((D : ℝ) + 1) ^ j + (D : ℝ) + 1) := by
      rw [div_pow]
      field_simp
      ring
    rw [hdiv]
    exact div_le_div_aux (by positivity) hPlow hB0 hBup
  · filter_upwards [hD.eventually_ge_atTop 1, eventually_ge_atTop 1] with B hD1 hB
    set D := thr c j B with hDdef
    have hx : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have hPup : ∑ d ∈ Icc 1 D, (c : ℝ) * (d : ℝ) ^ (j - 1) ≤ (c : ℝ) / j * ((D : ℝ) + 1) ^ j := by
      have h := sum_pow_upper (j - 1) D
      have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        have : (1 : ℕ) ≤ j := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [show j - 1 + 1 = j by omega, hcast] at h
      rw [← Finset.mul_sum, div_mul_eq_mul_div, le_div_iff₀ hjR] at *
      nlinarith [h, hcR]
    have hBlow : (c : ℝ) * (D : ℝ) ^ j ≤ (B : ℝ) := by
      have h := thr_pow_le (c := c) (j := j) (B := B) (by omega)
      exact_mod_cast h
    have hDj : (0 : ℝ) < (c : ℝ) * (D : ℝ) ^ j := by positivity
    have hstep : (∑ d ∈ Icc 1 D, (c : ℝ) * (d : ℝ) ^ (j - 1)) / B
        ≤ ((c : ℝ) / j * ((D : ℝ) + 1) ^ j) / ((c : ℝ) * (D : ℝ) ^ j) := by
      refine div_le_div_aux (by positivity) hPup hDj hBlow
    have heq : ((c : ℝ) / j * ((D : ℝ) + 1) ^ j) / ((c : ℝ) * (D : ℝ) ^ j)
        = (1 / (j : ℝ)) * (((D : ℝ) + 1) / D) ^ j := by
      rw [div_pow]
      field_simp
    rw [← heq]
    exact hstep


/-- **Master asymptotic.** For `c ≥ 1` and `j ≥ 2`, the truncated sum `S c j B`
(which counts the divisors `d` of `q ≤ B` with `c·d^j < q`) satisfies

  `S c j B / B = (1/j)(log B - log c) + γ - 1/j + o(1)`. -/
theorem tendsto_S (c j : ℕ) (hc : 1 ≤ c) (hj : 2 ≤ j) :
    Tendsto (fun B : ℕ => (S c j B : ℝ) / B
        - ((1 / j) * (Real.log B - Real.log c) + eulerMascheroniConstant - 1 / j))
      atTop (𝓝 0) := by
  have hD := tendsto_thr c j
  have hA : Tendsto (fun B : ℕ =>
      (∑ d ∈ Icc 1 (thr c j B), ((B / d : ℕ) : ℝ)) / B - (harmonic (thr c j B) : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_thr_div c j hc hj)
    filter_upwards [eventually_ge_atTop 1] with B hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have hbound := abs_sum_floor_sub_harmonic B (thr c j B)
    have hrw : (∑ d ∈ Icc 1 (thr c j B), ((B / d : ℕ) : ℝ)) / B - (harmonic (thr c j B) : ℝ)
        = ((∑ d ∈ Icc 1 (thr c j B), ((B / d : ℕ) : ℝ)) - B * (harmonic (thr c j B) : ℝ)) / B := by
      field_simp
    rw [hrw, Real.norm_eq_abs, abs_div, abs_of_pos hB0, div_le_div_iff₀ hB0 hB0]
    nlinarith [hbound, hB0]
  have hharm : Tendsto (fun B : ℕ =>
      (harmonic (thr c j B) : ℝ) - Real.log (thr c j B) - eulerMascheroniConstant)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_harmonic_sub_log.comp hD).sub_const eulerMascheroniConstant
    simpa using h
  have hlog := tendsto_log_thr c j hc hj
  have hpow : Tendsto (fun B : ℕ =>
      1 / (j : ℝ) - (∑ d ∈ Icc 1 (thr c j B), (c : ℝ) * (d : ℝ) ^ (j - 1)) / B)
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ) / (j : ℝ)) (f := (atTop : Filter ℕ))).sub
      (tendsto_pow_sum_div c j hc hj)
    simpa using h
  have hsum := ((hA.add hharm).add hlog).add hpow
  rw [show (0 : ℝ) + 0 + 0 + 0 = 0 by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hB0 : (B : ℝ) ≠ 0 := by
    have : (0 : ℝ) < B := by exact_mod_cast hB
    exact ne_of_gt this
  have hSR := S_real c j B (by omega)
  rw [hSR]
  field_simp
  ring

end GammaDivisors
