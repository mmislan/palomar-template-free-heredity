module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
The final outward failure comparison in manuscript H.9. This proves the scalar
arithmetic, not the stochastic estimates supplying its four summands. A degree20
lower Taylor polynomial for exp(1), raised to8 and20, suffices; no floating-point
approximation, native evaluation or inherited numerical assertion is used.
-/

@[expose] public section
namespace P161Formal
noncomputable section
open scoped BigOperators

def expOneLower : ℝ := 6613313319248080001 / 2432902008176640000

theorem exp_one_lower : expOneLower ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) 21
  norm_num [Finset.sum_range_succ, Nat.factorial_succ, expOneLower] at h ⊢
  exact h

theorem complete_failure_arithmetic :
    (9545923 : ℝ) / 9062500000 + 11 / 100000 +
      10 * Real.exp (-8) + 3 * Real.exp (-20) ≤
      4517975690072193 / 10^18 := by
  have hpos : 0 < expOneLower := by norm_num [expOneLower]
  have h8 : expOneLower ^ 8 ≤ Real.exp 8 := by
    have h := pow_le_pow_left₀ (le_of_lt hpos) exp_one_lower 8
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat] using h
  have h20 : expOneLower ^ 20 ≤ Real.exp 20 := by
    have h := pow_le_pow_left₀ (le_of_lt hpos) exp_one_lower 20
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat] using h
  have hinv8 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 10 by norm_num)
    (pow_pos hpos 8) h8
  have hinv20 := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 3 by norm_num)
    (pow_pos hpos 20) h20
  have hrat : (9545923 : ℝ) / 9062500000 + 11 / 100000 +
      10 / expOneLower ^ 8 + 3 / expOneLower ^ 20 ≤
      4517975690072193 / 10^18 := by norm_num [expOneLower]
  rw [Real.exp_neg, Real.exp_neg]
  simp only [← div_eq_mul_inv]
  linarith

end
end P161Formal
