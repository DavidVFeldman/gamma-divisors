/-
Axiom audit for the commissioned targets.
Each target must show only `propext`, `Classical.choice`, `Quot.sound`.
-/
import GammaDivisors.Targets
import GammaDivisors.Tier4
import GammaDivisors.Tier5
import GammaDivisors.Tier6Window
import GammaDivisors.Tier6Rate

-- Commission 1 (Tiers 1-3)
#print axioms GammaDivisors.sum_card_divisors_le
#print axioms GammaDivisors.tendsto_average_Zfix
#print axioms GammaDivisors.tendsto_two_harmonic_sqrt_sub_harmonic

-- Commission 2 (Tiers 4-6)
#print axioms GammaDivisors.tendsto_average_Z
#print axioms GammaDivisors.tendsto_average_Zhalf_open
#print axioms GammaDivisors.tendsto_average_Zhalf_closed
#print axioms GammaDivisors.tendsto_rate_gamma_seq
#print axioms GammaDivisors.tendsto_average_window_difference
