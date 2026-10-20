module

public import P161Formal.BranchingFueled

/-! Uniform maximum, underfloor barrier and prepared-founder bound for the
selected beta4m witness. The underfloor check is32 simple rational values;
no binomial moment is enumerated here. -/

@[expose] public section
namespace P161Formal

theorem branching_A_initial_max (a : ℕ) : branchingAQ a ≤ branchingAQ 0 := by
  by_cases ha : a ≤ 12
  · have hp : (3/4 : ℚ)^a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h := mul_le_mul_of_nonneg_left hp (show (0 : ℚ) ≤ 1275068416/16120377 by norm_num)
    simpa [branchingAQ,ha] using h
  · have h := branching_A_high_antitone (a := 13) (b := a) (by omega) (by omega)
    have h0 : branchingAQ 13 ≤ branchingAQ 0 := by
      norm_num [branchingAQ,branchingReciprocalFiveQ]
    exact h.trans h0

theorem branching_fuel_factor_max (fuel : Bool) :
    branchingFuelFactorQ fuel ≤ branchingFuelFactorQ false := by
  cases fuel <;> norm_num [branchingFuelFactorQ]

theorem branching_witness_max (a : ℕ) (fuel : Bool) : branchingWitnessQ a fuel ≤ 80 := by
  have hA := (branching_A_positive a).le
  have hc := (branching_fuel_factor_positive false).le
  calc
    _ ≤ branchingFuelFactorQ fuel*branchingAQ a := branching_witness_upper a fuel
    _ ≤ branchingFuelFactorQ false*branchingAQ a :=
      mul_le_mul_of_nonneg_right (branching_fuel_factor_max fuel) hA
    _ ≤ branchingFuelFactorQ false*branchingAQ 0 :=
      mul_le_mul_of_nonneg_left (branching_A_initial_max a) hc
    _ ≤ 80 := by norm_num [branchingFuelFactorQ,branchingAQ]

theorem branching_underfloor_barrier (a : ℕ) (ha : a < 16) (fuel : Bool) :
    1 ≤ branchingWitnessQ a fuel := by
  have hchecked : (List.range 16).all (fun k => decide
      (1 ≤ branchingWitnessQ k false ∧ 1 ≤ branchingWitnessQ k true)) = true := by
    decide +kernel
  have h := of_decide_eq_true
    (List.all_eq_true.mp hchecked a (by simpa only [List.mem_range] using ha))
  cases fuel
  · exact h.1
  · exact h.2

theorem branching_prepared_upper (a : ℕ) (ha : 512 ≤ a) (fuel : Bool) :
    branchingWitnessQ a fuel ≤ 6/100000000 := by
  have hA := (branching_A_positive a).le
  have hc := (branching_fuel_factor_positive false).le
  calc
    _ ≤ branchingFuelFactorQ fuel*branchingAQ a := branching_witness_upper a fuel
    _ ≤ branchingFuelFactorQ false*branchingAQ a :=
      mul_le_mul_of_nonneg_right (branching_fuel_factor_max fuel) hA
    _ ≤ branchingFuelFactorQ false*branchingAQ 512 :=
      mul_le_mul_of_nonneg_left (branching_A_high_antitone (by omega) ha) hc
    _ ≤ 6/100000000 := by
      norm_num [branchingFuelFactorQ,branchingAQ,branchingReciprocalFiveQ]

end P161Formal
