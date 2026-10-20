module

public import P161Formal.Quantitative

/-! The retained complete acquisition/floor/service/division allowance.
All physical-event bounds giving these summands remain separate obligations;
this checks their original scalar allocation without changing the mission. -/

@[expose] public section
namespace P161Formal
noncomputable section

def branchingB0 : ℝ := 13/10^7

theorem exp_one_lower_pow_le (n : ℕ) : expOneLower^n ≤ Real.exp n := by
  have hpos : 0 < expOneLower := by norm_num [expOneLower]
  have h := pow_le_pow_left₀ (le_of_lt hpos) exp_one_lower n
  simpa only [←Real.exp_nat_mul,mul_one] using h

theorem mission_exp_fifteen : Real.exp (-15) ≤ (1/2900000 : ℝ) := by
  have hpos : 0 < expOneLower := by norm_num [expOneLower]
  have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (pow_pos hpos 15) (exp_one_lower_pow_le 15)
  have hr : 1/expOneLower^15 ≤ (1/2900000 : ℝ) := by norm_num [expOneLower]
  rw [Real.exp_neg]
  norm_num only [Nat.cast_ofNat] at h
  simp only [one_div] at h hr ⊢
  linarith

theorem mission_exp_twenty_five : Real.exp (-25) ≤ (1/10^10 : ℝ) := by
  have hpos : 0 < expOneLower := by norm_num [expOneLower]
  have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (pow_pos hpos 25) (exp_one_lower_pow_le 25)
  have hr : 1/expOneLower^25 ≤ (1/10^10 : ℝ) := by norm_num [expOneLower]
  rw [Real.exp_neg]
  norm_num only [Nat.cast_ofNat] at h
  simp only [one_div] at h hr ⊢
  linarith

theorem retained_g60_allocation :
    (48/10^8 : ℝ)+320/2900000+600*((6/5)*branchingB0+1/10^8)+5184/10^10 =
      9545923/9062500000 := by norm_num [branchingB0]

theorem direct_g60_scalar_allowance :
    (48/10^8 : ℝ)+320*Real.exp (-15)+608*branchingB0+600/10^8+
      5184*Real.exp (-25) ≤ 9545923/9062500000 := by
  have h15 := mission_exp_fifteen
  have h25 := mission_exp_twenty_five
  norm_num [branchingB0] at *
  linarith

end
end P161Formal
