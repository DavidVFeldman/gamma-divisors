/-
Counting infrastructure for the gamma-divisors campaign (Commission 2).

The basic device is the divisor/codivisor swap: writing `q = d * e`, a condition
on the divisor `d` relative to `q` becomes a condition relating `d` and the
codivisor `e`, and the sum over `q ≤ B` becomes a sum over `d` of counts of `e`.
-/
import Mathlib

open Finset Filter Real Topology

namespace GammaDivisors

/-- Counting the integers in `[1, M]` exceeding `m`. -/
lemma card_filter_lt_Icc (M m : ℕ) : #{e ∈ Icc 1 M | m < e} = M - m := by
  have : {e ∈ Icc 1 M | m < e} = Ioc m M := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [this, Nat.card_Ioc]

/-- The multiples of `d` in `[1, B]`, indexed by the cofactor. -/
lemma card_filter_dvd_codiv (B d : ℕ) (hd : 1 ≤ d) (f : ℕ → ℕ) :
    #{q ∈ Icc 1 B | d ∣ q ∧ f d < q / d} = #{e ∈ Icc 1 (B / d) | f d < e} := by
  refine Finset.card_nbij' (fun q => q / d) (fun e => d * e) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hq ⊢
    obtain ⟨⟨hq1, hq2⟩, hdvd, hf⟩ := hq
    refine ⟨⟨?_, Nat.div_le_div_right hq2⟩, hf⟩
    exact Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd (by omega) hdvd)
  · intro e he
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at he ⊢
    obtain ⟨⟨he1, he2⟩, hf⟩ := he
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩, ⟨e, rfl⟩, ?_⟩
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le (by omega)).1 he2
    · rwa [Nat.mul_div_cancel_left _ (by omega)]
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hq
    exact Nat.mul_div_cancel' hq.2.1
  · intro e _
    exact Nat.mul_div_cancel_left _ (by omega)

/-- The divisor/codivisor swap, in the form needed throughout: for any `f`,
summing over `q ≤ B` the number of divisors `d` of `q` whose codivisor `q / d`
exceeds `f d` yields `∑_{d ≤ B} (⌊B/d⌋ - f d)` (truncated subtraction). -/
theorem sum_card_divisors_codiv (B : ℕ) (f : ℕ → ℕ) :
    ∑ q ∈ Icc 1 B, #{d ∈ q.divisors | f d < q / d} = ∑ d ∈ Icc 1 B, (B / d - f d) := by
  have step1 : ∀ q ∈ Icc 1 B, #{d ∈ q.divisors | f d < q / d}
      = ∑ d ∈ Icc 1 B, (if d ∣ q ∧ f d < q / d then 1 else 0) := by
    intro q hq
    simp only [Finset.mem_Icc] at hq
    rw [show {d ∈ q.divisors | f d < q / d}
        = {d ∈ Icc 1 B | d ∣ q ∧ f d < q / d} by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hd, -⟩, hf⟩
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (by omega)
        exact ⟨⟨hd1, le_trans (Nat.le_of_dvd (by omega) hd) hq.2⟩, hd, hf⟩
      · rintro ⟨-, hd, hf⟩
        exact ⟨⟨hd, by omega⟩, hf⟩]
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_Icc] at hd
  rw [← Finset.card_filter, card_filter_dvd_codiv B d hd.1 f, card_filter_lt_Icc]

/-! ### Divisor conditions as codivisor conditions -/

/-- For `q ≥ 1` and `j ≥ 1`, the divisors `d` of `q` with `d ^ j < q` are exactly the
divisors whose codivisor exceeds `d ^ (j - 1)`. -/
lemma filter_pow_lt (j q : ℕ) (hj : 1 ≤ j) (hq : 1 ≤ q) :
    {d ∈ q.divisors | d ^ j < q} = {d ∈ q.divisors | d ^ (j - 1) < q / d} := by
  refine Finset.filter_congr fun d hd => ?_
  simp only [Nat.mem_divisors] at hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
  have hqd : q = d * (q / d) := (Nat.mul_div_cancel' hd.1).symm
  obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  subst hk
  simp only [Nat.add_sub_cancel]
  constructor
  · intro h
    rw [hqd] at h
    rw [pow_succ, mul_comm (d ^ k) d] at h
    exact lt_of_mul_lt_mul_left h (by omega)
  · intro h
    calc d ^ (k + 1) = d * d ^ k := by ring
      _ < d * (q / d) := by
          exact mul_lt_mul_of_pos_left h (by omega : 0 < d)
      _ = q := hqd.symm


/-- For `q ≥ 1`, the divisors `d` of `q` with `c * d ^ 2 < q` are exactly the divisors
whose codivisor exceeds `c * d`. -/
lemma filter_const_mul_sq_lt (c q : ℕ) (hq : 1 ≤ q) :
    {d ∈ q.divisors | c * d ^ 2 < q} = {d ∈ q.divisors | c * d < q / d} := by
  refine Finset.filter_congr fun d hd => ?_
  simp only [Nat.mem_divisors] at hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
  have hqd : q = d * (q / d) := (Nat.mul_div_cancel' hd.1).symm
  constructor
  · intro h
    rw [hqd] at h
    have : d * (c * d) < d * (q / d) := by ring_nf; ring_nf at h; linarith [h]
    exact lt_of_mul_lt_mul_left this (by omega)
  · intro h
    calc c * d ^ 2 = d * (c * d) := by ring
      _ < d * (q / d) := mul_lt_mul_of_pos_left h (by omega : 0 < d)
      _ = q := hqd.symm

/-- For `q ≥ 1`, the divisors `d` of `q` with `c * d < q` are exactly the divisors
whose codivisor exceeds `c`. -/
lemma filter_const_mul_lt (c q : ℕ) (hq : 1 ≤ q) :
    {d ∈ q.divisors | c * d < q} = {d ∈ q.divisors | c < q / d} := by
  refine Finset.filter_congr fun d hd => ?_
  simp only [Nat.mem_divisors] at hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
  have hqd : q = d * (q / d) := (Nat.mul_div_cancel' hd.1).symm
  constructor
  · intro h
    rw [hqd] at h
    have : d * c < d * (q / d) := by rw [mul_comm d c]; exact h
    exact lt_of_mul_lt_mul_left this (by omega)
  · intro h
    calc c * d = d * c := by ring
      _ < d * (q / d) := mul_lt_mul_of_pos_left h (by omega : 0 < d)
      _ = q := hqd.symm

/-! ### The three main counting sums -/

/-- The number of divisors of `q` below `q ^ (1/j)`. -/
noncomputable def Ndiv (j q : ℕ) : ℕ := #{d ∈ q.divisors | d ^ j < q}

/-- Summed count of divisors below the `j`-th root. -/
theorem sum_Ndiv (j B : ℕ) (hj : 1 ≤ j) :
    ∑ q ∈ Icc 1 B, Ndiv j q = ∑ d ∈ Icc 1 B, (B / d - d ^ (j - 1)) := by
  rw [← sum_card_divisors_codiv B (fun d => d ^ (j - 1))]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [Finset.mem_Icc] at hq
  rw [Ndiv, filter_pow_lt j q hj (by omega)]

/-- Summed count of divisors `d` with `c * d ^ 2 < q`. -/
theorem sum_card_const_mul_sq (c B : ℕ) :
    ∑ q ∈ Icc 1 B, #{d ∈ q.divisors | c * d ^ 2 < q}
      = ∑ d ∈ Icc 1 B, (B / d - c * d) := by
  rw [← sum_card_divisors_codiv B (fun d => c * d)]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [Finset.mem_Icc] at hq
  rw [filter_const_mul_sq_lt c q (by omega)]


/-- Splitting the divisors below the `i`-th root at the `j`-th root (`i ≤ j`). -/
lemma card_divisors_split_pows (q i j : ℕ) (hij : i ≤ j) :
    #{d ∈ q.divisors | d ^ j < q} + #{d ∈ q.divisors | q ≤ d ^ j ∧ d ^ i < q}
      = #{d ∈ q.divisors | d ^ i < q} := by
  have hsub : ∀ d ∈ q.divisors, d ^ j < q → d ^ i < q := by
    intro d hd h
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.1 hd).1
      (Nat.pos_of_ne_zero (Nat.mem_divisors.1 hd).2)
    exact lt_of_le_of_lt (Nat.pow_le_pow_right hd1 hij) h
  have e1 : {d ∈ q.divisors | d ^ j < q}
      = {d ∈ ({d ∈ q.divisors | d ^ i < q}) | d ^ j < q} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d hd => ?_
    constructor
    · intro h
      exact ⟨hsub d hd h, h⟩
    · intro h
      exact h.2
  have e2 : {d ∈ q.divisors | q ≤ d ^ j ∧ d ^ i < q}
      = {d ∈ ({d ∈ q.divisors | d ^ i < q}) | ¬ (d ^ j < q)} := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d hd => ?_
    simp only [not_lt]
    tauto
  rw [e1, e2]
  exact Finset.card_filter_add_card_filter_not
    (s := {d ∈ q.divisors | d ^ i < q}) (p := fun d => d ^ j < q)


/-- Reflection `d ↦ q / d` on the divisors of `q ≥ 1`. -/
lemma card_filter_divisors_refl (q : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    #{d ∈ q.divisors | P (q / d)} = #{d ∈ q.divisors | P d} := by
  simp only [Finset.card_filter]
  exact Nat.sum_div_divisors q (fun d => if P d then 1 else 0)

/-- Counting solutions of `g d = q`: at most one per `q`, and only for `q` in the
image of `g`, which for our `g`'s is a sparse set. -/
lemma sum_card_eq_le (B : ℕ) (g : ℕ → ℕ)
    (hginj : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → g a = g b → a = b)
    (hgle : ∀ d, 1 ≤ d → g d ≤ B → d ≤ Nat.sqrt B) :
    ∑ q ∈ Icc 1 B, #{d ∈ q.divisors | g d = q} ≤ Nat.sqrt B := by
  have hone : ∀ q : ℕ, 1 ≤ q → q ≤ B → #{d ∈ q.divisors | g d = q}
      ≤ (if q ∈ (Icc 1 (Nat.sqrt B)).image g then 1 else 0) := by
    intro q hq hqB
    by_cases hex : q ∈ (Icc 1 (Nat.sqrt B)).image g
    · rw [if_pos hex]
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [Finset.mem_filter, Nat.mem_divisors] at ha hb
      have ha1 : 1 ≤ a := Nat.pos_of_dvd_of_pos ha.1.1 (by omega)
      have hb1 : 1 ≤ b := Nat.pos_of_dvd_of_pos hb.1.1 (by omega)
      exact hginj a b ha1 hb1 (by rw [ha.2, hb.2])
    · rw [if_neg hex]
      refine Nat.le_zero.2 (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_))
      intro d hd
      simp only [Nat.mem_divisors] at hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
      intro hgd
      exact hex (Finset.mem_image.2 ⟨d, Finset.mem_Icc.2 ⟨hd1, hgle d hd1 (by omega)⟩, hgd⟩)
  calc ∑ q ∈ Icc 1 B, #{d ∈ q.divisors | g d = q}
      ≤ ∑ q ∈ Icc 1 B, (if q ∈ (Icc 1 (Nat.sqrt B)).image g then 1 else 0) := by
        refine Finset.sum_le_sum fun q hq => ?_
        simp only [Finset.mem_Icc] at hq
        exact hone q hq.1 hq.2
    _ = #{q ∈ Icc 1 B | q ∈ (Icc 1 (Nat.sqrt B)).image g} := (Finset.card_filter _ _).symm
    _ ≤ #((Icc 1 (Nat.sqrt B)).image g) := by
        refine Finset.card_le_card fun q hq => ?_
        exact (Finset.mem_filter.1 hq).2
    _ ≤ #(Icc 1 (Nat.sqrt B)) := Finset.card_image_le
    _ = Nat.sqrt B := by simp

/-! ### The divisor reflection -/

/-- Reflection `d ↦ q / d` matches the divisors below `√q` with those above. -/
lemma card_filter_sq_lt_eq (q : ℕ) (hq : 1 ≤ q) :
    #{d ∈ q.divisors | d ^ 2 < q} = #{d ∈ q.divisors | q < d ^ 2} := by
  have h := Nat.sum_div_divisors q (fun d => if q < d ^ 2 then 1 else 0)
  simp only [Finset.card_filter]
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Nat.mem_divisors] at hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
  have hqd : q = d * (q / d) := (Nat.mul_div_cancel' hd.1).symm
  have he1 : 1 ≤ q / d := Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd (by omega) hd.1)
  have key : (d ^ 2 < q) ↔ (q < (q / d) ^ 2) := by
    constructor
    · intro h2
      nlinarith [hqd, h2, hd1, he1]
    · intro h2
      nlinarith [hqd, h2, hd1, he1]
  by_cases h2 : d ^ 2 < q
  · simp [h2, key.1 h2]
  · have : ¬ (q < (q / d) ^ 2) := fun hc => h2 (key.2 hc)
    simp [h2, this]

/-- Every `q ≥ 1` has `τ(q) = 2 · #{d ∣ q : d² < q} + [q is a square]`. -/
lemma card_divisors_eq (q : ℕ) (hq : 1 ≤ q) :
    #q.divisors = 2 * #{d ∈ q.divisors | d ^ 2 < q} + #{d ∈ q.divisors | d ^ 2 = q} := by
  have hsplit : #{d ∈ q.divisors | d ^ 2 < q} + #{d ∈ q.divisors | ¬ d ^ 2 < q}
      = #q.divisors :=
    Finset.card_filter_add_card_filter_not (s := q.divisors) (p := fun d => d ^ 2 < q)
  have hsplit2 : #{d ∈ q.divisors | d ^ 2 = q} + #{d ∈ q.divisors | q < d ^ 2}
      = #{d ∈ q.divisors | ¬ d ^ 2 < q} := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext d
      simp only [Finset.mem_union, Finset.mem_filter, not_lt]
      constructor
      · rintro (⟨hd, h⟩ | ⟨hd, h⟩) <;> exact ⟨hd, by omega⟩
      · rintro ⟨hd, h⟩
        rcases eq_or_lt_of_le h with h' | h'
        · exact Or.inl ⟨hd, h'.symm⟩
        · exact Or.inr ⟨hd, h'⟩
    · refine Finset.disjoint_filter.2 fun d _ h => ?_
      omega
  rw [← card_filter_sq_lt_eq q hq] at hsplit2
  omega

end GammaDivisors
