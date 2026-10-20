module

public import P161Formal.BranchingReciprocal
public import Mathlib.Tactic.Ring

/-! Structural full-daughter moment bounds for the selected beta4m branching
witness. The only finite check is the13 low-count gluing comparisons. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators

def branchingFuelFactorQ (fuel : Bool) : ℚ := if fuel then 1 else 1+70/4000000

theorem branching_A_positive (a : ℕ) : 0 < branchingAQ a := by
  unfold branchingAQ
  split_ifs
  · positivity
  · exact mul_pos (by norm_num) (branching_reciprocal_positive a)

theorem branching_A_reciprocal_bound (a : ℕ) :
    branchingAQ a ≤ 1860480*branchingReciprocalFiveQ a := by
  by_cases ha : a ≤ 12
  · have hchecked : (List.range 13).all (fun k => decide
        (branchingAQ k ≤ 1860480*branchingReciprocalFiveQ k)) = true := by
      decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp hchecked a (by
      simp only [List.mem_range]
      omega))
  · simp [branchingAQ,ha]

theorem branching_fuel_correction_bounds (a : ℕ) :
    -branchingAQ a/2 ≤ branchingFuelCorrectionQ a ∧
      branchingFuelCorrectionQ a ≤ 70*branchingAQ a := by
  have hA := (branching_A_positive a).le
  unfold branchingFuelCorrectionQ
  by_cases ha : a = 0
  · subst a
    simp only [ite_true]
    constructor
    · exact le_rfl
    · nlinarith
  · simp only [ha,ite_false]
    have hm0 : (0 : ℚ) ≤ (min (6*a) 70 : ℕ) := Nat.cast_nonneg _
    have hm1 : ((min (6*a) 70 : ℕ) : ℚ) ≤ 70 := by exact_mod_cast min_le_right (6*a) 70
    constructor
    · nlinarith [mul_nonneg hA hm0]
    · nlinarith [mul_le_mul_of_nonneg_left hm1 hA]

theorem branching_witness_positive (a : ℕ) (fuel : Bool) :
    0 < branchingWitnessQ a fuel := by
  have hA := branching_A_positive a
  have hg := (branching_fuel_correction_bounds a).1
  cases fuel <;> norm_num only [branchingWitnessQ,Bool.false_eq_true,ite_false,ite_true]
  · nlinarith
  · simpa only [add_zero] using hA

theorem branching_witness_upper (a : ℕ) (fuel : Bool) :
    branchingWitnessQ a fuel ≤ branchingFuelFactorQ fuel*branchingAQ a := by
  have hg := (branching_fuel_correction_bounds a).2
  cases fuel <;>
    norm_num only [branchingWitnessQ,branchingFuelFactorQ,Bool.false_eq_true,
      ite_false,ite_true,one_mul,add_zero]
  · nlinarith
  · exact le_rfl

theorem branching_fuel_factor_positive (fuel : Bool) : 0 < branchingFuelFactorQ fuel := by
  cases fuel <;> norm_num [branchingFuelFactorQ]

theorem branching_moment_reciprocal_bound (a : ℕ) (fuel : Bool) :
    branchingMomentQ a fuel ≤
      (32*branchingFuelFactorQ fuel*1860480)*branchingReciprocalFiveQ a := by
  have hc := (branching_fuel_factor_positive fuel).le
  have hpoint (k : ℕ) : branchingWitnessQ k fuel ≤
      (branchingFuelFactorQ fuel*1860480)*branchingReciprocalFiveQ k := by
    have h := (branching_witness_upper k fuel).trans
      (mul_le_mul_of_nonneg_left (branching_A_reciprocal_bound k) hc)
    simpa only [mul_assoc] using h
  calc
    branchingMomentQ a fuel ≤ ∑ k ∈ Finset.range (a+1),
        (a.choose k : ℚ)/2^a*((branchingFuelFactorQ fuel*1860480)*branchingReciprocalFiveQ k) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hpoint k) (by positivity))
    _ = (branchingFuelFactorQ fuel*1860480)*
        (∑ k ∈ Finset.range (a+1), (a.choose k : ℚ)/2^a*branchingReciprocalFiveQ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (branchingFuelFactorQ fuel*1860480)*(32*branchingReciprocalFiveQ a) :=
      mul_le_mul_of_nonneg_left (branching_binomial_reciprocal a) (by positivity)
    _ = _ := by ring

theorem branching_high_moment_bound (a : ℕ) (ha : 13 ≤ a) (fuel : Bool) :
    branchingMomentQ a fuel ≤ 32*branchingFuelFactorQ fuel*branchingAQ a := by
  have h := branching_moment_reciprocal_bound a fuel
  have hA : branchingAQ a = 1860480*branchingReciprocalFiveQ a := by
    simp [branchingAQ,show ¬a ≤ 12 by omega]
  rw [hA]
  simpa only [mul_assoc] using h

end P161Formal
