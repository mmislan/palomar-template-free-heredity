module

public import P161Formal.Quantitative

/-! Exact beta4m ordinary-credit tilt premises and block allowance.
This is scalar arithmetic; the complete physical generator and killed-path
expectation argument are separate obligations. -/

@[expose] public section
namespace P161Formal
noncomputable section
set_option exponentiation.threshold 1024

def serviceRho : ℝ := 79967/80000
def serviceZ : ℝ := 3/4
def serviceTheta : ℝ := 1650
def serviceLoad : ℝ := 14764808

theorem service_parameters :
    0 < serviceZ ∧ serviceZ ≤ serviceRho ∧ serviceRho ≤ 1 ∧
    4000000*(1-serviceRho)=serviceTheta ∧
    serviceLoad=800*3*2048*(9/16 : ℝ)+3*4000000+8 ∧
    4000000*(16/2048 : ℝ)*(serviceZ-serviceRho)+
      serviceLoad*(1-serviceRho)+serviceTheta*serviceRho = -(598067/10000 : ℝ) := by
  norm_num [serviceZ,serviceRho,serviceTheta,serviceLoad]

theorem service_fueled_live_drift (a : ℝ) (ha : 16 ≤ a) :
    4000000*(a/2048)*(serviceZ-serviceRho)+serviceLoad*(1-serviceRho) ≤
      -serviceTheta*serviceRho := by
  norm_num [serviceZ,serviceRho,serviceTheta,serviceLoad] at *
  linarith

theorem service_block_scalar_allowance :
    (12/serviceRho)*(4/3 : ℝ)^500 / Real.exp 165 ≤ (1/100000000 : ℝ) := by
  have hpos : 0 < expOneLower := by norm_num [expOneLower]
  have h165 : expOneLower^165 ≤ Real.exp 165 := by
    have h := pow_le_pow_left₀ (le_of_lt hpos) exp_one_lower 165
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat] using h
  have hN : 0 ≤ (12/serviceRho)*(4/3 : ℝ)^500 := by norm_num [serviceRho]
  have h := div_le_div_of_nonneg_left hN (pow_pos hpos 165) h165
  have hr : (12/serviceRho)*(4/3 : ℝ)^500 / expOneLower^165 ≤
      (1/100000000 : ℝ) := by norm_num [serviceRho,expOneLower]
  exact le_trans h hr

end
end P161Formal
