module

public import P161Formal.BranchingWitnessShape
public import P161Formal.BranchingHighEnvelope
public import P161Formal.BranchingLowCertificate

/-! High-count ingredients for the beta4m branching supersolution. Low seed6 states use the checked
affine rectangle; high states use full-daughter reciprocal moments and the
polynomial certificate. Seed0 decay is restricted to the live floor domain. -/

@[expose] public section
namespace P161Formal
open scoped BigOperators

theorem branching_reciprocal_succ (a : ℕ) :
    branchingReciprocalFiveQ (a+1) =
      branchingReciprocalFiveQ a*((a+1 : ℚ)/(a+6)) := by
  unfold branchingReciprocalFiveQ
  push_cast
  field_simp
  all_goals ring

theorem branching_reciprocal_pred (a : ℕ) (ha : 1 ≤ a) :
    branchingReciprocalFiveQ (a-1) =
      branchingReciprocalFiveQ a*((a+5 : ℚ)/a) := by
  cases a with
  | zero => omega
  | succ b =>
      simp only [Nat.add_sub_cancel]
      unfold branchingReciprocalFiveQ
      push_cast
      field_simp
      all_goals ring

theorem branching_reciprocal_antitone {a b : ℕ} (hab : a ≤ b) :
    branchingReciprocalFiveQ b ≤ branchingReciprocalFiveQ a := by
  unfold branchingReciprocalFiveQ
  have h : (a : ℚ) ≤ b := by exact_mod_cast hab
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem branching_A_high12 (a : ℕ) (ha : 12 ≤ a) :
    branchingAQ a = 1860480*branchingReciprocalFiveQ a := by
  by_cases he : a = 12
  · subst a
    norm_num [branchingAQ,branchingReciprocalFiveQ]
  · simp [branchingAQ,show ¬a ≤ 12 by omega]

theorem branching_A_succ (a : ℕ) (ha : 12 ≤ a) :
    branchingAQ (a+1) = branchingAQ a*((a+1 : ℚ)/(a+6)) := by
  rw [branching_A_high12 (a+1) (by omega),branching_A_high12 a ha,
    branching_reciprocal_succ]
  ring

theorem branching_A_pred (a : ℕ) (ha : 13 ≤ a) :
    branchingAQ (a-1) = branchingAQ a*((a+5 : ℚ)/a) := by
  rw [branching_A_high12 (a-1) (by omega),branching_A_high12 a (by omega),
    branching_reciprocal_pred a (by omega)]
  ring

theorem branching_witness_high12 (a : ℕ) (ha : 12 ≤ a) (fuel : Bool) :
    branchingWitnessQ a fuel = branchingFuelFactorQ fuel*branchingAQ a := by
  have ha0 : ¬a = 0 := by omega
  have hm : (min (6*a) 70 : ℕ) = 70 := min_eq_right (by omega)
  cases fuel <;>
    norm_num [branchingWitnessQ,branchingFuelCorrectionQ,branchingFuelFactorQ,ha0,hm]
  all_goals ring

theorem branching_A_high_antitone {a b : ℕ} (ha : 12 ≤ a) (hab : a ≤ b) :
    branchingAQ b ≤ branchingAQ a := by
  rw [branching_A_high12 b (by omega),branching_A_high12 a ha]
  exact mul_le_mul_of_nonneg_left (branching_reciprocal_antitone hab) (by norm_num)

theorem branching_high_seed_nonpositive (a : ℕ) (ha : 13 ≤ a) (hN : a ≤ 2048)
    (fuel : Bool) (seed : ℚ) (hs : 0 ≤ seed) :
    seed*(1-(a : ℚ)/2048)*(branchingWitnessQ (a+1) fuel-branchingWitnessQ a fuel) ≤ 0 := by
  have hA := branching_A_high_antitone (a := a) (b := a+1) (by omega) (by omega)
  have hc := (branching_fuel_factor_positive fuel).le
  have hW := mul_le_mul_of_nonneg_left hA hc
  rw [← branching_witness_high12 (a+1) (by omega) fuel,
    ← branching_witness_high12 a (by omega) fuel] at hW
  have hn : (a : ℚ) ≤ 2048 := by exact_mod_cast hN
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hs (by linarith)) (sub_nonpos.mpr hW)

theorem branching_high_unfueled_passive (a : ℕ) (ha : 13 ≤ a) :
    (a : ℚ)*(branchingWitnessQ (a-1) false-branchingWitnessQ a false) =
      5*branchingFuelFactorQ false*branchingAQ a := by
  rw [branching_witness_high12 (a-1) (by omega) false,
    branching_witness_high12 a (by omega) false,branching_A_pred a ha]
  have hn : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  field_simp
  all_goals ring

theorem branching_high_recharge (a : ℕ) (ha : 13 ≤ a) :
    4000000*(branchingWitnessQ a true-branchingWitnessQ a false) = -70*branchingAQ a := by
  rw [branching_witness_high12 a (by omega) true,
    branching_witness_high12 a (by omega) false]
  norm_num [branchingFuelFactorQ]
  all_goals ring

theorem branching_unfueled_envelope_eq (a : ℕ) (ha : 13 ≤ a) :
    branchingHighUnfueledEnvelope (a : ℚ) =
      branchingAQ a*(branchingFuelFactorQ false*(135/2)-70) := by
  rw [branching_A_high12 a (by omega)]
  unfold branchingHighUnfueledEnvelope branchingReciprocalFiveQ branchingFuelFactorQ
  norm_num
  field_simp

theorem branching_high_unfueled_bound (a : ℕ) (ha : 13 ≤ a) (hN : a ≤ 2048)
    (U v seed : ℚ) (hs : 0 ≤ seed) :
    branchingSiteOperatorQ a false U v seed+branchingWitnessQ a false/2 ≤
      branchingHighUnfueledEnvelope (a : ℚ) := by
  have hseed := branching_high_seed_nonpositive a ha hN false seed hs
  have hmoment := branching_high_moment_bound a ha false
  change seed*(1-(a : ℚ)/2048)*(branchingWitnessQ (a+1) false-branchingWitnessQ a false)+
    (a : ℚ)*(branchingWitnessQ (a-1) false-branchingWitnessQ a false)+
    4000000*(branchingWitnessQ a true-branchingWitnessQ a false)+
    2*branchingMomentQ a false-2*branchingWitnessQ a false+branchingWitnessQ a false/2 ≤ _
  rw [branching_high_unfueled_passive a ha,branching_high_recharge a ha,
    branching_unfueled_envelope_eq a ha]
  rw [branching_witness_high12 a (by omega) false] at hseed ⊢
  nlinarith

end P161Formal
