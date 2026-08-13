/-
Commission 2, Tier 6 (stretch): the rate of the logarithm-free approximation
to the Euler-Mascheroni constant.

`γₙ := H_{n−1} + H_n − H_{n²}` satisfies `n²(γ − γₙ) → 2/3`.

The proof runs through the second-order Euler-Maclaurin approximation
`y m := H_m − log m − 1/(2m) + 1/(12m²)`, which converges to `γ` with error
`O(1/m³)`.  The error bound is obtained by a monotonicity sandwich:
`y m − 10/m³` increases and `y m + 10/m³` decreases (for `m ≥ 2`), and both
tend to `γ`.
-/
import Mathlib

open Finset Filter Real Topology

namespace GammaDivisors

/-! ### The refined approximating sequence -/

/-- Second-order approximation to `γ`: `H_m − log m − 1/(2m) + 1/(12m²)`. -/
noncomputable def yseq (m : ℕ) : ℝ :=
  (harmonic m : ℝ) - Real.log m - 1 / (2 * m) + 1 / (12 * m ^ 2)

/-- A cubic Taylor bound for `log(m+1) − log m`, valid for real `m ≥ 2`. -/
theorem log_step_bound (m : ℝ) (hm : 2 ≤ m) :
    |Real.log (m + 1) - Real.log m - (1 / m - 1 / (2 * m ^ 2) + 1 / (3 * m ^ 3))| ≤ 2 / m ^ 4 := by
  have hm0 : (0:ℝ) < m := by linarith
  have habs : |(-(1/m) : ℝ)| = 1/m := by
    rw [abs_neg, abs_of_pos (by positivity)]
  have hx : |(-(1/m) : ℝ)| < 1 := by
    rw [habs, div_lt_one hm0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 3
  rw [habs] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have hlog : (1 : ℝ) - -(1/m) = (m+1)/m := by field_simp; ring
  rw [hlog, Real.log_div (by linarith) (by linarith)] at h
  have h5 : (1:ℝ)/m ≤ 1/2 := by rw [div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have h5' : m⁻¹ ≤ (1:ℝ)/2 := by rwa [one_div] at h5
  have hb : (1/m:ℝ)^(3+1)/(1 - 1/m) ≤ 2/m^4 := by
    have hstep : (1/m:ℝ)^(3+1)/(1 - 1/m) ≤ (1/m:ℝ)^(3+1)/(1/2) := by
      gcongr
      all_goals first | positivity | linarith
    calc (1/m:ℝ)^(3+1)/(1 - 1/m) ≤ (1/m:ℝ)^(3+1)/(1/2) := hstep
      _ = 2/m^4 := by rw [show ((1:ℝ)/m)^(3+1) = 1/m^4 by ring]; ring
  refine le_trans (le_of_eq ?_) (le_trans h hb)
  congr 1
  push_cast
  ring

/-- The rational part of the increment of `yseq`, compared with the cubic Taylor
polynomial of `log(1 + 1/m)`: the discrepancy is smaller than the decrement of
`10/m³` minus the Taylor error `2/m⁴`. -/
theorem rational_step_bound (m : ℝ) (hm : 2 ≤ m) :
    |(1/(2*(m+1)) + 1/(2*m) + 1/(12*(m+1)^2) - 1/(12*m^2)) - (1/m - 1/(2*m^2) + 1/(3*m^3))|
      ≤ (10/m^3 - 10/(m+1)^3) - 2/m^4 := by
  have hm0 : (0:ℝ) < m := by linarith
  have hden : (0:ℝ) < 12*m^4*(m+1)^3 := by positivity
  have h1 : (0:ℝ) ≤ (-24 + 44*m + 281*m^2 + 333*m^3) / (12*m^4*(m+1)^3) :=
    div_nonneg (by nlinarith) hden.le
  have h2 : (0:ℝ) ≤ (-24 + 52*m + 295*m^2 + 339*m^3) / (12*m^4*(m+1)^3) :=
    div_nonneg (by nlinarith) hden.le
  have k1 : ((10/m^3 - 10/(m+1)^3) - 2/m^4) +
      ((1/(2*(m+1)) + 1/(2*m) + 1/(12*(m+1)^2) - 1/(12*m^2)) - (1/m - 1/(2*m^2) + 1/(3*m^3)))
      = (-24 + 44*m + 281*m^2 + 333*m^3) / (12*m^4*(m+1)^3) := by
    field_simp; ring
  have k2 : ((10/m^3 - 10/(m+1)^3) - 2/m^4) -
      ((1/(2*(m+1)) + 1/(2*m) + 1/(12*(m+1)^2) - 1/(12*m^2)) - (1/m - 1/(2*m^2) + 1/(3*m^3)))
      = (-24 + 52*m + 295*m^2 + 339*m^3) / (12*m^4*(m+1)^3) := by
    field_simp; ring
  rw [abs_le]
  constructor <;> linarith

/-- The increment of `yseq` is at most the decrement of `10/m³`. -/
theorem abs_yseq_step (m : ℕ) (hm : 2 ≤ m) :
    |yseq (m + 1) - yseq m| ≤ 10 / (m : ℝ) ^ 3 - 10 / ((m : ℝ) + 1) ^ 3 := by
  have hx2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hx0 : (0:ℝ) < (m:ℝ) := by linarith
  have hharm : (harmonic (m+1) : ℝ) = (harmonic m : ℝ) + 1/((m:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  have hyd : yseq (m+1) - yseq m
      = (1/(2*((m:ℝ)+1)) + 1/(2*(m:ℝ)) + 1/(12*((m:ℝ)+1)^2) - 1/(12*(m:ℝ)^2))
        - (Real.log ((m:ℝ)+1) - Real.log (m:ℝ)) := by
    simp only [yseq]
    push_cast
    rw [hharm]
    field_simp
    ring
  rw [hyd]
  have h1 := abs_le.mp (log_step_bound (m:ℝ) hx2)
  have h2 := abs_le.mp (rational_step_bound (m:ℝ) hx2)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem tendsto_yseq : Tendsto yseq atTop (𝓝 eulerMascheroniConstant) := by
  have h0 := Real.tendsto_harmonic_sub_log
  have hA : Tendsto (fun m : ℕ => 2*(m:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hB : Tendsto (fun m : ℕ => 12*(m:ℝ)^2) atTop atTop := by
    refine Filter.tendsto_atTop_mono (fun m => ?_) hA
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast h
      nlinarith
  have h1 : Tendsto (fun m : ℕ => 1/(2*(m:ℝ))) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hA
  have h2 : Tendsto (fun m : ℕ => 1/(12*(m:ℝ)^2)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hB
  have h3 := (h0.sub h1).add h2
  simp only [sub_zero, add_zero] at h3
  exact h3

theorem tendsto_ten_div_shift :
    Tendsto (fun k : ℕ => 10 / ((k : ℝ) + 2) ^ 3) atTop (𝓝 0) := by
  have hA : Tendsto (fun k : ℕ => ((k:ℝ) + 2)^3) atTop atTop := by
    refine Filter.tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have e : ((k:ℝ)+2)^3 = (k:ℝ)^3 + 6*(k:ℝ)^2 + 12*(k:ℝ) + 8 := by ring
    have h3 : (0:ℝ) ≤ (k:ℝ)^3 := by positivity
    have h2 : (0:ℝ) ≤ (k:ℝ)^2 := by positivity
    rw [e]; linarith
  exact Filter.Tendsto.div_atTop tendsto_const_nhds hA

/-- The second-order approximation has error `O(1/m³)`. -/
theorem abs_yseq_sub_gamma (m : ℕ) (hm : 2 ≤ m) :
    |yseq m - eulerMascheroniConstant| ≤ 10 / (m : ℝ) ^ 3 := by
  have hshift : Tendsto (fun k : ℕ => yseq (k+2)) atTop (𝓝 eulerMascheroniConstant) :=
    tendsto_yseq.comp (tendsto_add_atTop_nat 2)
  have hmono : Monotone (fun k : ℕ => yseq (k+2) - 10 / ((k : ℝ) + 2)^3) := by
    apply monotone_nat_of_le_succ
    intro k
    have h := abs_le.mp (abs_yseq_step (k+2) (by omega))
    have e : k+1+2 = (k+2)+1 := by omega
    simp only [e]
    push_cast at h ⊢
    have e2 : ((k:ℝ)+1+2)^3 = ((k:ℝ)+2+1)^3 := by ring
    rw [e2]
    linarith [h.1]
  have hanti : Antitone (fun k : ℕ => yseq (k+2) + 10 / ((k : ℝ) + 2)^3) := by
    apply antitone_nat_of_succ_le
    intro k
    have h := abs_le.mp (abs_yseq_step (k+2) (by omega))
    have e : k+1+2 = (k+2)+1 := by omega
    simp only [e]
    push_cast at h ⊢
    have e2 : ((k:ℝ)+1+2)^3 = ((k:ℝ)+2+1)^3 := by ring
    rw [e2]
    linarith [h.2]
  have hlo : Tendsto (fun k : ℕ => yseq (k+2) - 10 / ((k : ℝ) + 2)^3) atTop
      (𝓝 eulerMascheroniConstant) := by
    simpa using hshift.sub tendsto_ten_div_shift
  have hhi : Tendsto (fun k : ℕ => yseq (k+2) + 10 / ((k : ℝ) + 2)^3) atTop
      (𝓝 eulerMascheroniConstant) := by
    simpa using hshift.add tendsto_ten_div_shift
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 := hmono.ge_of_tendsto hlo k
  have h2 := hanti.le_of_tendsto hhi k
  simp only at h1 h2
  rw [abs_le]
  push_cast
  constructor <;> linarith

/-- Quantitative form of the rate theorem: `|n²(γ − γₙ) − 2/3| ≤ 31/n` for `n ≥ 2`. -/
theorem rate_bound (n : ℕ) (hn : 2 ≤ n) :
    |(n : ℝ) ^ 2 * (eulerMascheroniConstant -
        ((harmonic (n - 1) : ℝ) + (harmonic n : ℝ) - (harmonic (n ^ 2) : ℝ))) - 2 / 3|
      ≤ 31 / (n : ℝ) := by
  have ht : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have ht0 : (0:ℝ) < (n:ℝ) := by linarith
  have hH0 : (harmonic (n-1) : ℝ) = (harmonic n : ℝ) - 1/(n:ℝ) := by
    have e : n - 1 + 1 = n := by omega
    have hs := harmonic_succ (n-1)
    rw [e] at hs
    rw [hs]
    push_cast
    rw [show ((n:ℝ))⁻¹ = 1/(n:ℝ) by ring]
    ring
  have hlog2 : Real.log ((n^2 : ℕ) : ℝ) = 2 * Real.log (n:ℝ) := by
    push_cast
    rw [Real.log_pow]
    push_cast; ring
  have hH1 : (harmonic n : ℝ) = (yseq n) + Real.log (n:ℝ) + 1/(2*(n:ℝ)) - 1/(12*(n:ℝ)^2) := by
    simp only [yseq]; ring
  have hH2 : (harmonic (n^2) : ℝ)
      = (yseq (n^2)) + 2*Real.log (n:ℝ) + 1/(2*(n:ℝ)^2) - 1/(12*(n:ℝ)^4) := by
    simp only [yseq, hlog2]
    push_cast
    ring
  have hE : (n : ℝ) ^ 2 * (eulerMascheroniConstant -
        ((harmonic (n - 1) : ℝ) + (harmonic n : ℝ) - (harmonic (n ^ 2) : ℝ))) - 2 / 3
      = -2*((n:ℝ)^2*(yseq n - eulerMascheroniConstant))
        + ((n:ℝ)^2*(yseq (n^2) - eulerMascheroniConstant)) - 1/(12*(n:ℝ)^2) := by
    rw [hH0, hH1, hH2]
    field_simp
    ring
  rw [hE]
  have b1 := abs_yseq_sub_gamma n hn
  have b2 := abs_yseq_sub_gamma (n^2) (by nlinarith)
  rw [show (((n^2 : ℕ)) : ℝ) = (n:ℝ)^2 by push_cast; ring] at b2
  have hu : |(n:ℝ)^2*(yseq n - eulerMascheroniConstant)| ≤ 10/(n:ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)^2)]
    calc (n:ℝ)^2 * |yseq n - eulerMascheroniConstant| ≤ (n:ℝ)^2 * (10/(n:ℝ)^3) := by gcongr
      _ = 10/(n:ℝ) := by field_simp
  have hv : |(n:ℝ)^2*(yseq (n^2) - eulerMascheroniConstant)| ≤ 10/(n:ℝ)^4 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)^2)]
    calc (n:ℝ)^2 * |yseq (n^2) - eulerMascheroniConstant| ≤ (n:ℝ)^2 * (10/((n:ℝ)^2)^3) := by
          gcongr
      _ = 10/(n:ℝ)^4 := by field_simp
  have hnum : 2*(10/(n:ℝ)) + 10/(n:ℝ)^4 + 1/(12*(n:ℝ)^2) ≤ 31/(n:ℝ) := by
    have key : 31/(n:ℝ) - (2*(10/(n:ℝ)) + 10/(n:ℝ)^4 + 1/(12*(n:ℝ)^2))
        = (132*(n:ℝ)^3 - 120 - (n:ℝ)^2)/(12*(n:ℝ)^4) := by
      field_simp; ring
    have hpos : (0:ℝ) ≤ (132*(n:ℝ)^3 - 120 - (n:ℝ)^2)/(12*(n:ℝ)^4) :=
      div_nonneg (by nlinarith) (by positivity)
    linarith
  have h12 : (0:ℝ) < 1/(12*(n:ℝ)^2) := by positivity
  rw [abs_le] at hu hv ⊢
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- `γₙ := H_{n−1} + H_n − H_{n²}` satisfies `n²(γ − γₙ) → 2/3`. -/
theorem tendsto_rate_gamma_seq :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 *
        (eulerMascheroniConstant -
          ((harmonic (n - 1) : ℝ) + (harmonic n : ℝ) - (harmonic (n ^ 2) : ℝ))))
      atTop (𝓝 (2 / 3)) := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 *
      (eulerMascheroniConstant -
        ((harmonic (n - 1) : ℝ) + (harmonic n : ℝ) - (harmonic (n ^ 2) : ℝ))) - 2/3)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat 31)
    filter_upwards [eventually_ge_atTop 2] with n hn
    simpa [Real.norm_eq_abs] using rate_bound n hn
  have h1 := h0.add (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (2:ℝ)/3) atTop (𝓝 (2/3)))
  simpa using h1

end GammaDivisors
