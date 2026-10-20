module

public import P161Formal.BranchingScalar

/-! Fueled high-count scalar docking. All full-daughter moments are the
checked, untruncated binomial moments. No source or path law is assumed. -/

@[expose] public section
namespace P161Formal

theorem branching_true_value (a : ℕ) : branchingWitnessQ a true = branchingAQ a := by
  simp [branchingWitnessQ]

theorem branching_high_fuel_gap (a : ℕ) (ha : 13 ≤ a) :
    branchingWitnessQ a false-branchingAQ a = (70/4000000 : ℚ)*branchingAQ a := by
  rw [branching_witness_high12 a (by omega) false]
  norm_num [branchingFuelFactorQ]
  all_goals ring

theorem branching_high_true_passive (a : ℕ) (ha : 13 ≤ a) :
    (a : ℚ)*(branchingAQ (a-1)-branchingAQ a) = 5*branchingAQ a := by
  have h := branching_high_unfueled_passive a ha
  rw [branching_witness_high12 (a-1) (by omega) false,
    branching_witness_high12 a (by omega) false] at h
  norm_num [branchingFuelFactorQ] at h
  nlinarith

theorem branching_high_active_death (a : ℕ) (ha : 13 ≤ a) :
    400*(a : ℚ)*(branchingWitnessQ (a-1) false-branchingAQ a) =
      (400*a*(branchingFuelFactorQ false-1)+2000*branchingFuelFactorQ false)*branchingAQ a := by
  have h := branching_high_unfueled_passive a ha
  rw [branching_witness_high12 a (by omega) false] at h
  nlinarith

theorem branching_high_active_birth (a : ℕ) (ha : 13 ≤ a) :
    800*(a : ℚ)*(1-(a : ℚ)/2048)*(branchingWitnessQ (a+1) false-branchingAQ a) =
      branchingAQ a*(800*a*(1-(a : ℚ)/2048)*
        (branchingFuelFactorQ false*(a+1)/(a+6)-1)) := by
  rw [branching_witness_high12 (a+1) (by omega) false,branching_A_succ a (by omega)]
  ring

theorem branching_high_other_fuel_bound (a : ℕ) (ha : 13 ≤ a) (U v : ℚ)
    (hU : U ≤ 2) (hv : v ≤ 1843200) :
    (4000000*(1+(a : ℚ)/2048+U)+v)*(branchingWitnessQ a false-branchingAQ a) ≤
      (70*(3+(a : ℚ)/2048)+70*1843200/4000000)*branchingAQ a := by
  rw [branching_high_fuel_gap a ha]
  have hA := (branching_A_positive a).le
  have hc : 4000000*(1+(a : ℚ)/2048+U)+v ≤
      4000000*(3+(a : ℚ)/2048)+1843200 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (70/4000000 : ℚ)*branchingAQ a by positivity)
  nlinarith

theorem branching_high_basal_bound (a : ℕ) (ha : 13 ≤ a) :
    branchingMomentQ a false+branchingMomentQ a true-2*branchingAQ a ≤
      (32*branchingFuelFactorQ false+30)*branchingAQ a := by
  have hf := branching_high_moment_bound a ha false
  have ht := branching_high_moment_bound a ha true
  norm_num only [branchingFuelFactorQ,ite_true,one_mul,mul_one] at ht
  nlinarith

theorem branching_high_trigger_bound (a : ℕ) (ha : 13 ≤ a) (U : ℚ)
    (hU0 : 0 ≤ U) (hU1 : U ≤ 2) :
    ((a : ℚ)/2048+U)*(2*branchingMomentQ a false-branchingAQ a) ≤
      ((a : ℚ)/2048+2)*(64*branchingFuelFactorQ false-1)*branchingAQ a := by
  have hm := branching_high_moment_bound a ha false
  have hg : 2*branchingMomentQ a false-branchingAQ a ≤
      (64*branchingFuelFactorQ false-1)*branchingAQ a := by nlinarith
  have hfactor : 0 ≤ (a : ℚ)/2048+U := by positivity
  have h1 := mul_le_mul_of_nonneg_left hg hfactor
  have hA := (branching_A_positive a).le
  have hgap : 0 ≤ (64*branchingFuelFactorQ false-1)*branchingAQ a :=
    mul_nonneg (by norm_num [branchingFuelFactorQ]) hA
  have h2 := mul_le_mul_of_nonneg_right
    (show (a : ℚ)/2048+U ≤ (a : ℚ)/2048+2 by linarith) hgap
  exact h1.trans (by simpa only [mul_assoc] using h2)

theorem branching_high_A_ratio (a : ℕ) (ha : 13 ≤ a) :
    1860480/(((a : ℚ)+1)*(a+2)*(a+3)*(a+4)*(a+5)) = branchingAQ a := by
  rw [branching_A_high12 a (by omega)]
  simp only [branchingReciprocalFiveQ,div_eq_mul_inv,one_mul]

theorem branching_fueled_envelope_eq (a : ℕ) (ha : 13 ≤ a) :
    branchingHighFueledEnvelope (a : ℚ) =
      branchingAQ a*(5+800*a*(1-(a : ℚ)/2048)*
        (branchingFuelFactorQ false*(a+1)/(a+6)-1)+
        400*a*(branchingFuelFactorQ false-1)+2000*branchingFuelFactorQ false+
        70*(3+(a : ℚ)/2048)+70*1843200/4000000+
        32*branchingFuelFactorQ false+30+
        ((a : ℚ)/2048+2)*(64*branchingFuelFactorQ false-1)+1/2) := by
  unfold branchingHighFueledEnvelope
  rw [branching_high_A_ratio a ha]
  rfl

theorem branching_high_fueled_bound (a : ℕ) (ha : 13 ≤ a) (hN : a ≤ 2048)
    (U v seed : ℚ) (hU0 : 0 ≤ U) (hU1 : U ≤ 2) (hv : v ≤ 1843200) (hs : 0 ≤ seed) :
    branchingSiteOperatorQ a true U v seed+branchingWitnessQ a true/2 ≤
      branchingHighFueledEnvelope (a : ℚ) := by
  have hseed := branching_high_seed_nonpositive a ha hN true seed hs
  have hother := branching_high_other_fuel_bound a ha U v hU1 hv
  have hbasal := branching_high_basal_bound a ha
  have htrigger := branching_high_trigger_bound a ha U hU0 hU1
  change seed*(1-(a : ℚ)/2048)*(branchingWitnessQ (a+1) true-branchingWitnessQ a true)+
    (a : ℚ)*(branchingWitnessQ (a-1) true-branchingWitnessQ a true)+
    800*a*(1-(a : ℚ)/2048)*(branchingWitnessQ (a+1) false-branchingWitnessQ a true)+
    400*a*(branchingWitnessQ (a-1) false-branchingWitnessQ a true)+
    (4000000*(1+(a : ℚ)/2048+U)+v)*(branchingWitnessQ a false-branchingWitnessQ a true)+
    branchingMomentQ a false+branchingMomentQ a true-2*branchingWitnessQ a true+
    ((a : ℚ)/2048+U)*(2*branchingMomentQ a false-branchingWitnessQ a true)+
    branchingWitnessQ a true/2 ≤ _
  simp only [branching_true_value] at hseed ⊢
  rw [branching_high_true_passive a ha,branching_high_active_birth a ha,
    branching_high_active_death a ha,branching_fueled_envelope_eq a ha]
  nlinarith

theorem branching_high_scalar_drift (a : ℕ) (ha : 13 ≤ a) (hN : a ≤ 2048)
    (fuel : Bool) (U v seed : ℚ) (hU0 : 0 ≤ U) (hU1 : U ≤ 2)
    (hv : v ≤ 1843200) (hs : 0 ≤ seed) :
    branchingSiteOperatorQ a fuel U v seed ≤ -branchingWitnessQ a fuel/2+13/10000000 := by
  have h := branching_high_envelopes (a : ℚ) (by exact_mod_cast ha) (by exact_mod_cast hN)
  cases fuel
  · have he := branching_high_unfueled_bound a ha hN U v seed hs
    nlinarith [h.1]
  · have he := branching_high_fueled_bound a ha hN U v seed hU0 hU1 hv hs
    linarith [h.2]

theorem branching_seeded_scalar_drift (a : ℕ) (hN : a ≤ 2048) (fuel : Bool)
    (U v : ℚ) (hU0 : 0 ≤ U) (hU1 : U ≤ 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1843200) :
    branchingSiteOperatorQ a fuel U v 6 ≤ -branchingWitnessQ a fuel/2+13/10000000 := by
  by_cases ha : a ≤ 12
  · exact branching_low_seeded_drift a ha fuel U v hU0 hU1 hv0 hv1
  · exact branching_high_scalar_drift a (by omega) hN fuel U v 6 hU0 hU1 hv1 (by norm_num)

theorem branching_seed_free_live_scalar_drift (a : ℕ) (ha : 16 ≤ a) (hN : a ≤ 2048)
    (fuel : Bool) (U v : ℚ) (hU0 : 0 ≤ U) (hU1 : U ≤ 2) (hv : v ≤ 1843200) :
    branchingSiteOperatorQ a fuel U v 0 ≤ -branchingWitnessQ a fuel/2+13/10000000 :=
  branching_high_scalar_drift a (by omega) hN fuel U v 0 hU0 hU1 hv (by norm_num)

end P161Formal
